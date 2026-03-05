use serde_json::{json, Value};
use tokio::io::{AsyncBufReadExt, AsyncReadExt, AsyncWriteExt, BufReader};
use tower_lsp::{LspService, Server};

use purescript_fast_compiler::lsp::Backend;

/// Send a JSON-RPC request with Content-Length framing.
async fn send_request(
    writer: &mut (impl AsyncWriteExt + Unpin),
    id: u64,
    method: &str,
    params: Value,
) {
    let msg = json!({
        "jsonrpc": "2.0",
        "id": id,
        "method": method,
        "params": params,
    });
    let body = serde_json::to_string(&msg).unwrap();
    let framed = format!("Content-Length: {}\r\n\r\n{}", body.len(), body);
    writer.write_all(framed.as_bytes()).await.unwrap();
}

/// Send a JSON-RPC notification (no id) with Content-Length framing.
async fn send_notification(
    writer: &mut (impl AsyncWriteExt + Unpin),
    method: &str,
    params: Value,
) {
    let msg = json!({
        "jsonrpc": "2.0",
        "method": method,
        "params": params,
    });
    let body = serde_json::to_string(&msg).unwrap();
    let framed = format!("Content-Length: {}\r\n\r\n{}", body.len(), body);
    writer.write_all(framed.as_bytes()).await.unwrap();
}

/// Read one JSON-RPC message from the stream (parses Content-Length header).
async fn read_message(reader: &mut BufReader<impl AsyncReadExt + Unpin>) -> Value {
    // Read headers until empty line
    let mut content_length: usize = 0;
    loop {
        let mut line = String::new();
        reader.read_line(&mut line).await.unwrap();
        let line = line.trim();
        if line.is_empty() {
            break;
        }
        if let Some(len) = line.strip_prefix("Content-Length: ") {
            content_length = len.trim().parse().unwrap();
        }
    }
    assert!(content_length > 0, "No Content-Length header found");

    let mut body = vec![0u8; content_length];
    reader.read_exact(&mut body).await.unwrap();
    serde_json::from_slice(&body).unwrap()
}

/// Read messages until we find a response with the given id.
/// Skips notifications (server→client messages like window/logMessage).
async fn read_response(
    reader: &mut BufReader<impl AsyncReadExt + Unpin>,
    expected_id: u64,
) -> Value {
    loop {
        let msg = read_message(reader).await;
        // Responses have an "id" field; notifications don't (or have method)
        if let Some(id) = msg.get("id") {
            if id.as_u64() == Some(expected_id) {
                return msg;
            }
        }
        // Otherwise it's a notification from the server — skip it
    }
}

struct TestServer {
    writer: tokio::io::DuplexStream,
    reader: BufReader<tokio::io::DuplexStream>,
}

impl TestServer {
    async fn start() -> Self {
        let (req_client, req_server) = tokio::io::duplex(1024 * 64);
        let (resp_server, resp_client) = tokio::io::duplex(1024 * 64);

        let (service, socket) = LspService::new(|client| Backend::new(client, None));

        tokio::spawn(Server::new(req_server, resp_server, socket).serve(service));

        let mut server = TestServer {
            writer: req_client,
            reader: BufReader::new(resp_client),
        };

        // Perform LSP handshake
        server.initialize().await;

        server
    }

    async fn initialize(&mut self) {
        send_request(
            &mut self.writer,
            1,
            "initialize",
            json!({
                "capabilities": {},
                "rootUri": null,
                "processId": null,
            }),
        )
        .await;

        let resp = read_response(&mut self.reader, 1).await;
        assert!(resp.get("result").is_some(), "initialize should succeed");

        // Send initialized notification
        send_notification(&mut self.writer, "initialized", json!({})).await;

        // Give the server a moment to process initialized (sets ready=true)
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;
    }

    async fn open_file(&mut self, uri: &str, text: &str) {
        send_notification(
            &mut self.writer,
            "textDocument/didOpen",
            json!({
                "textDocument": {
                    "uri": uri,
                    "languageId": "purescript",
                    "version": 1,
                    "text": text,
                }
            }),
        )
        .await;
        // Give the server time to process
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;
    }

    async fn goto_definition(&mut self, id: u64, uri: &str, line: u32, character: u32) -> Value {
        send_request(
            &mut self.writer,
            id,
            "textDocument/definition",
            json!({
                "textDocument": { "uri": uri },
                "position": { "line": line, "character": character },
            }),
        )
        .await;

        read_response(&mut self.reader, id).await
    }
}

#[tokio::test]
async fn test_lsp_initialize_capabilities() {
    let (req_client, req_server) = tokio::io::duplex(1024 * 64);
    let (resp_server, resp_client) = tokio::io::duplex(1024 * 64);

    let (service, socket) = LspService::new(|client| Backend::new(client, None));

    tokio::spawn(Server::new(req_server, resp_server, socket).serve(service));

    let mut writer = req_client;
    let mut reader = BufReader::new(resp_client);

    send_request(
        &mut writer,
        1,
        "initialize",
        json!({
            "capabilities": {},
            "rootUri": null,
            "processId": null,
        }),
    )
    .await;

    let resp = read_response(&mut reader, 1).await;
    let result = resp.get("result").expect("should have result");
    let caps = result.get("capabilities").expect("should have capabilities");

    // Check definitionProvider is true
    let def_provider = caps.get("definitionProvider").expect("should have definitionProvider");
    assert_eq!(def_provider, &json!(true));

    // Check textDocumentSync
    let sync = caps.get("textDocumentSync").expect("should have textDocumentSync");
    assert_eq!(sync, &json!(1)); // FULL = 1

    // Check server info
    let info = result.get("serverInfo").expect("should have serverInfo");
    assert_eq!(info.get("name").unwrap(), "pfc");
}

#[tokio::test]
async fn test_lsp_goto_def_local_value() {
    let mut server = TestServer::start().await;

    let uri = "file:///test/Test.purs";
    let src = "module Test where\n\nfoo = 1\n\nbar = foo";
    server.open_file(uri, src).await;

    // "foo" in "bar = foo" is at line 4, col 6
    let resp = server.goto_definition(10, uri, 4, 6).await;
    let result = resp.get("result").expect("should have result");

    // Should be a location pointing to the definition of foo
    assert!(result.is_object(), "result should be a Location object, got: {result}");
    let range = result.get("range").expect("should have range");
    let start = range.get("start").expect("should have start");
    // foo is defined on line 2 (0-indexed), col 0
    assert_eq!(start.get("line").unwrap(), 2);
    assert_eq!(start.get("character").unwrap(), 0);

    // URI should match
    assert_eq!(result.get("uri").unwrap(), uri);
}

#[tokio::test]
async fn test_lsp_goto_def_local_constructor() {
    let mut server = TestServer::start().await;

    let uri = "file:///test/Test.purs";
    let src = "module Test where\n\ndata Color = Red | Green | Blue\n\nfoo = Red";
    server.open_file(uri, src).await;

    // "Red" in "foo = Red" is at line 4, col 6
    let resp = server.goto_definition(10, uri, 4, 6).await;
    let result = resp.get("result").expect("should have result");

    assert!(result.is_object(), "result should be a Location, got: {result}");
    let range = result.get("range").expect("should have range");
    let start = range.get("start").expect("should have start");
    // Red is defined on line 2 (0-indexed)
    assert_eq!(start.get("line").unwrap(), 2);
    assert_eq!(result.get("uri").unwrap(), uri);
}

#[tokio::test]
async fn test_lsp_goto_def_local_type_in_signature() {
    let mut server = TestServer::start().await;

    let uri = "file:///test/Test.purs";
    let src = "module Test where\n\ndata Foo = MkFoo\n\nbar :: Foo\nbar = MkFoo";
    server.open_file(uri, src).await;

    // "Foo" in "bar :: Foo" is at line 4, col 7
    let resp = server.goto_definition(10, uri, 4, 7).await;
    let result = resp.get("result").expect("should have result");

    assert!(result.is_object(), "result should be a Location, got: {result}");
    let range = result.get("range").expect("should have range");
    let start = range.get("start").expect("should have start");
    // data Foo on line 2 (0-indexed)
    assert_eq!(start.get("line").unwrap(), 2);
}

#[tokio::test]
async fn test_lsp_goto_def_returns_null_for_unknown() {
    let mut server = TestServer::start().await;

    let uri = "file:///test/Test.purs";
    let src = "module Test where\n\nfoo = unknownThing";
    server.open_file(uri, src).await;

    // "unknownThing" at line 2, col 6
    let resp = server.goto_definition(10, uri, 2, 6).await;
    let result = resp.get("result").expect("should have result");
    assert!(result.is_null(), "result should be null for unknown, got: {result}");
}

#[tokio::test]
async fn test_lsp_goto_def_returns_null_on_whitespace() {
    let mut server = TestServer::start().await;

    let uri = "file:///test/Test.purs";
    let src = "module Test where\n\nfoo = 1";
    server.open_file(uri, src).await;

    // Blank line at line 1, col 0
    let resp = server.goto_definition(10, uri, 1, 0).await;
    let result = resp.get("result").expect("should have result");
    assert!(result.is_null(), "result should be null on whitespace, got: {result}");
}
