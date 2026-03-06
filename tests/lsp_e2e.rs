use std::path::{Path, PathBuf};

use regex::Regex;
use serde_json::{json, Value};
use tokio::io::{AsyncBufReadExt, AsyncReadExt, AsyncWriteExt, BufReader};
use tokio::sync::{mpsc, Mutex};
use tower_lsp::lsp_types::Url;
use tower_lsp::{LspService, Server};

use purescript_fast_compiler::lsp::Backend;

/// Send a JSON-RPC message with Content-Length framing.
async fn send_framed(writer: &mut (impl AsyncWriteExt + Unpin), msg: &Value) {
    let body = serde_json::to_string(msg).unwrap();
    let framed = format!("Content-Length: {}\r\n\r\n{}", body.len(), body);
    writer.write_all(framed.as_bytes()).await.unwrap();
}

/// Read one JSON-RPC message from the stream (parses Content-Length header).
async fn read_message(reader: &mut BufReader<impl AsyncReadExt + Unpin>) -> Value {
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

struct TestServer {
    writer: std::sync::Arc<Mutex<tokio::io::DuplexStream>>,
    responses: mpsc::UnboundedReceiver<Value>,
}

impl TestServer {
    async fn start() -> Self {
        Self::start_with_sources(None).await
    }

    async fn start_with_sources(sources_cmd: Option<String>) -> Self {
        let (req_client, req_server) = tokio::io::duplex(1024 * 64);
        let (resp_server, resp_client) = tokio::io::duplex(1024 * 64);

        let (service, socket) = LspService::new(|client| Backend::new(client, sources_cmd));
        tokio::spawn(Server::new(req_server, resp_server, socket).serve(service));

        let writer = std::sync::Arc::new(Mutex::new(req_client));
        let (tx, rx) = mpsc::unbounded_channel();

        // Background reader: auto-responds to server→client requests, forwards responses
        let writer_clone = writer.clone();
        tokio::spawn(async move {
            let mut reader = BufReader::new(resp_client);
            loop {
                let msg = read_message(&mut reader).await;
                let has_method = msg.get("method").is_some();
                let has_id = msg.get("id").is_some();

                if has_method && has_id {
                    // Server→client request (e.g. window/workDoneProgress/create)
                    let resp = json!({
                        "jsonrpc": "2.0",
                        "id": msg["id"],
                        "result": null,
                    });
                    let mut w = writer_clone.lock().await;
                    send_framed(&mut *w, &resp).await;
                } else if has_id && !has_method {
                    // Response to our request
                    let _ = tx.send(msg);
                }
                // Notifications (method but no id): silently drop
            }
        });

        let mut server = TestServer {
            writer,
            responses: rx,
        };

        server.initialize().await;
        server
    }

    async fn initialize(&mut self) {
        self.send_request(1, "initialize", json!({
            "capabilities": {},
            "rootUri": null,
            "processId": null,
        }))
        .await;

        let resp = self.read_response(1).await;
        assert!(resp.get("result").is_some(), "initialize should succeed");

        self.send_notification("initialized", json!({})).await;
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;
    }

    async fn send_request(&mut self, id: u64, method: &str, params: Value) {
        let msg = json!({
            "jsonrpc": "2.0",
            "id": id,
            "method": method,
            "params": params,
        });
        let mut w = self.writer.lock().await;
        send_framed(&mut *w, &msg).await;
    }

    async fn send_notification(&mut self, method: &str, params: Value) {
        let msg = json!({
            "jsonrpc": "2.0",
            "method": method,
            "params": params,
        });
        let mut w = self.writer.lock().await;
        send_framed(&mut *w, &msg).await;
    }

    async fn read_response(&mut self, expected_id: u64) -> Value {
        loop {
            let msg = self.responses.recv().await.expect("response channel closed");
            if msg.get("id").and_then(|id| id.as_u64()) == Some(expected_id) {
                return msg;
            }
        }
    }

    async fn open_file(&mut self, uri: &str, text: &str) {
        self.send_notification(
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
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;
    }

    async fn goto_definition(&mut self, id: u64, uri: &str, line: u32, character: u32) -> Value {
        self.send_request(
            id,
            "textDocument/definition",
            json!({
                "textDocument": { "uri": uri },
                "position": { "line": line, "character": character },
            }),
        )
        .await;
        self.read_response(id).await
    }

    async fn hover(&mut self, id: u64, uri: &str, line: u32, character: u32) -> Value {
        self.send_request(
            id,
            "textDocument/hover",
            json!({
                "textDocument": { "uri": uri },
                "position": { "line": line, "character": character },
            }),
        )
        .await;
        self.read_response(id).await
    }

    async fn completion(&mut self, id: u64, uri: &str, line: u32, character: u32) -> Value {
        self.send_request(
            id,
            "textDocument/completion",
            json!({
                "textDocument": { "uri": uri },
                "position": { "line": line, "character": character },
            }),
        )
        .await;
        self.read_response(id).await
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

    send_framed(
        &mut writer,
        &json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": {
                "capabilities": {},
                "rootUri": null,
                "processId": null,
            },
        }),
    )
    .await;

    let resp = read_message(&mut reader).await;
    let result = resp.get("result").expect("should have result");
    let caps = result.get("capabilities").expect("should have capabilities");

    let def_provider = caps.get("definitionProvider").expect("should have definitionProvider");
    assert_eq!(def_provider, &json!(true));

    let sync = caps.get("textDocumentSync").expect("should have textDocumentSync");
    assert_eq!(sync, &json!(1));

    let info = result.get("serverInfo").expect("should have serverInfo");
    assert_eq!(info.get("name").unwrap(), "pfc");
}

#[tokio::test]
async fn test_lsp_goto_def_local_value() {
    let mut server = TestServer::start().await;

    let uri = "file:///test/Test.purs";
    let src = "module Test where\n\nfoo = 1\n\nbar = foo";
    server.open_file(uri, src).await;

    let resp = server.goto_definition(10, uri, 4, 6).await;
    let result = resp.get("result").expect("should have result");

    assert!(result.is_object(), "result should be a Location object, got: {result}");
    let range = result.get("range").expect("should have range");
    let start = range.get("start").expect("should have start");
    assert_eq!(start.get("line").unwrap(), 2);
    assert_eq!(start.get("character").unwrap(), 0);
    assert_eq!(result.get("uri").unwrap(), uri);
}

#[tokio::test]
async fn test_lsp_goto_def_local_constructor() {
    let mut server = TestServer::start().await;

    let uri = "file:///test/Test.purs";
    let src = "module Test where\n\ndata Color = Red | Green | Blue\n\nfoo = Red";
    server.open_file(uri, src).await;

    let resp = server.goto_definition(10, uri, 4, 6).await;
    let result = resp.get("result").expect("should have result");

    assert!(result.is_object(), "result should be a Location, got: {result}");
    let range = result.get("range").expect("should have range");
    let start = range.get("start").expect("should have start");
    assert_eq!(start.get("line").unwrap(), 2);
    assert_eq!(result.get("uri").unwrap(), uri);
}

#[tokio::test]
async fn test_lsp_goto_def_local_type_in_signature() {
    let mut server = TestServer::start().await;

    let uri = "file:///test/Test.purs";
    let src = "module Test where\n\ndata Foo = MkFoo\n\nbar :: Foo\nbar = MkFoo";
    server.open_file(uri, src).await;

    let resp = server.goto_definition(10, uri, 4, 7).await;
    let result = resp.get("result").expect("should have result");

    assert!(result.is_object(), "result should be a Location, got: {result}");
    let range = result.get("range").expect("should have range");
    let start = range.get("start").expect("should have start");
    assert_eq!(start.get("line").unwrap(), 2);
}

#[tokio::test]
async fn test_lsp_goto_def_returns_null_for_unknown() {
    let mut server = TestServer::start().await;

    let uri = "file:///test/Test.purs";
    let src = "module Test where\n\nfoo = unknownThing";
    server.open_file(uri, src).await;

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

    let resp = server.goto_definition(10, uri, 1, 0).await;
    let result = resp.get("result").expect("should have result");
    assert!(result.is_null(), "result should be null on whitespace, got: {result}");
}

// --- Fixture-driven go-to-definition test ---

struct GotoDefTestCase {
    line: u32,
    col: u32,
    name: String,
    expected: GotoDefExpected,
}

enum GotoDefExpected {
    NoSource,
    Location {
        uri: String,
        start_line: u32,
        start_col: u32,
        end_line: u32,
        end_col: u32,
    },
}

/// Parse test comments from a fixture file.
/// Format: `-- line:col (name) => file start_line:start_col-end_line:end_col`
/// Or: `-- line:col (name) => Prim (no source)`
fn parse_goto_def_comments(source: &str, fixture_dir: &Path) -> Vec<GotoDefTestCase> {
    let re = Regex::new(r"^-- (\d+):(\d+) \(([^)]+)\) => (.+)$").unwrap();
    let mut cases = Vec::new();

    for line in source.lines() {
        let line = line.trim();
        let Some(caps) = re.captures(line) else {
            continue;
        };

        let test_line: u32 = caps[1].parse().unwrap();
        let test_col: u32 = caps[2].parse().unwrap();
        let name = caps[3].to_string();
        let target = &caps[4];

        let expected = if target == "Prim (no source)" {
            GotoDefExpected::NoSource
        } else {
            let (file, positions) =
                target.rsplit_once(' ').expect("expected 'file line:col-line:col'");
            let pos_re = Regex::new(r"^(\d+):(\d+)-(\d+):(\d+)$").unwrap();
            let pos_caps = pos_re
                .captures(positions)
                .unwrap_or_else(|| panic!("bad position format: {positions}"));

            let start_line: u32 = pos_caps[1].parse().unwrap();
            let start_col: u32 = pos_caps[2].parse().unwrap();
            let end_line: u32 = pos_caps[3].parse().unwrap();
            let end_col: u32 = pos_caps[4].parse().unwrap();

            let file_path = fixture_dir
                .join(file)
                .canonicalize()
                .unwrap_or_else(|e| panic!("cannot resolve fixture path {file}: {e}"));
            let uri = Url::from_file_path(&file_path)
                .expect("valid file path")
                .to_string();

            GotoDefExpected::Location {
                uri,
                start_line,
                start_col,
                end_line,
                end_col,
            }
        };

        cases.push(GotoDefTestCase {
            line: test_line,
            col: test_col,
            name,
            expected,
        });
    }

    cases
}

#[tokio::test]
async fn test_lsp_goto_definition_fixture() {
    let fixture_dir = std::fs::canonicalize(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/lsp/goto_definition"),
    )
    .unwrap();

    let packages_dir = std::fs::canonicalize(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/packages"),
    )
    .unwrap();

    // Read fixture source and parse test comments
    let simple_path = fixture_dir.join("Simple.purs");
    let simple_source = std::fs::read_to_string(&simple_path).unwrap();
    let test_cases = parse_goto_def_comments(&simple_source, &fixture_dir);
    assert!(
        !test_cases.is_empty(),
        "should find test cases in fixture comments"
    );

    let simple_uri = Url::from_file_path(&simple_path).unwrap().to_string();

    // Start server with sources_cmd that loads fixture files + prelude
    let sources_cmd = format!(
        "echo '{}'; echo '{}'",
        fixture_dir.join("**/*.purs").display(),
        packages_dir.join("prelude/src/**/*.purs").display(),
    );
    let mut server = TestServer::start_with_sources(Some(sources_cmd)).await;

    // Open Simple.purs so it's in self.files
    server.open_file(&simple_uri, &simple_source).await;

    // Wait for source loading to complete by polling a known-good local definition.
    // Line 6 col 6 = "fn" reference which should resolve to a local def.
    let mut ready = false;
    for _ in 0..100 {
        let resp = server.goto_definition(99, &simple_uri, 6, 6).await;
        let result = resp.get("result").unwrap();
        if !result.is_null() {
            ready = true;
            break;
        }
        tokio::time::sleep(std::time::Duration::from_millis(200)).await;
    }
    assert!(ready, "server did not become ready within timeout");

    // Run each test case
    let mut id = 200u64;
    let mut passed = 0;
    let mut failed = 0;

    for case in &test_cases {
        let resp = server
            .goto_definition(id, &simple_uri, case.line, case.col)
            .await;
        let result = resp.get("result").unwrap();
        id += 1;

        match &case.expected {
            GotoDefExpected::NoSource => {
                if !result.is_null() {
                    eprintln!(
                        "FAIL {}:{} ({}) — expected null (Prim), got: {}",
                        case.line, case.col, case.name, result
                    );
                    failed += 1;
                } else {
                    passed += 1;
                }
            }
            GotoDefExpected::Location {
                uri: expected_uri,
                start_line,
                start_col,
                end_line,
                end_col,
            } => {
                if result.is_null() {
                    eprintln!(
                        "FAIL {}:{} ({}) — expected location at {expected_uri} {}:{}-{}:{}, got null",
                        case.line, case.col, case.name, start_line, start_col, end_line, end_col
                    );
                    failed += 1;
                    continue;
                }

                let result_uri = result
                    .get("uri")
                    .and_then(|v| v.as_str())
                    .unwrap_or("");
                let range = result.get("range").expect("should have range");
                let start = range.get("start").unwrap();
                let end = range.get("end").unwrap();

                let got_start_line = start.get("line").unwrap().as_u64().unwrap() as u32;
                let got_start_col =
                    start.get("character").unwrap().as_u64().unwrap() as u32;
                let got_end_line = end.get("line").unwrap().as_u64().unwrap() as u32;
                let got_end_col = end.get("character").unwrap().as_u64().unwrap() as u32;

                let mut case_ok = true;

                if result_uri != expected_uri {
                    eprintln!(
                        "FAIL {}:{} ({}) — wrong URI\n  expected: {expected_uri}\n  got:      {result_uri}",
                        case.line, case.col, case.name
                    );
                    case_ok = false;
                }

                if got_start_line != *start_line
                    || got_start_col != *start_col
                    || got_end_line != *end_line
                    || got_end_col != *end_col
                {
                    eprintln!(
                        "FAIL {}:{} ({}) — wrong range\n  expected: {}:{}-{}:{}\n  got:      {}:{}-{}:{}",
                        case.line, case.col, case.name,
                        start_line, start_col, end_line, end_col,
                        got_start_line, got_start_col, got_end_line, got_end_col,
                    );
                    case_ok = false;
                }

                if case_ok {
                    passed += 1;
                } else {
                    failed += 1;
                }
            }
        }
    }

    eprintln!(
        "\nGoto definition fixture results: {passed} passed, {failed} failed out of {} total",
        test_cases.len()
    );

    assert_eq!(
        failed, 0,
        "{failed} goto-definition test case(s) failed (see above)"
    );
}

// --- Hover tests ---

#[tokio::test]
async fn test_lsp_hover_simple_value() {
    let mut server = TestServer::start().await;

    let uri = "file:///test/Test.purs";
    let src = "module Test where\n\nfoo = 42";
    server.open_file(uri, src).await;

    let resp = server.hover(10, uri, 2, 0).await;
    let result = resp.get("result").expect("should have result");

    assert!(!result.is_null(), "hover result should not be null, got: {result}");
    let contents = result.get("contents").expect("should have contents");
    let value = contents.get("value").expect("should have value").as_str().unwrap();
    assert!(value.contains("foo"), "hover should contain name 'foo': {value}");
    assert!(value.contains("Int"), "hover should contain type 'Int': {value}");
}

#[tokio::test]
async fn test_lsp_hover_returns_null_on_whitespace() {
    let mut server = TestServer::start().await;

    let uri = "file:///test/Test.purs";
    let src = "module Test where\n\nfoo = 42";
    server.open_file(uri, src).await;

    let resp = server.hover(10, uri, 1, 0).await;
    let result = resp.get("result").expect("should have result");
    assert!(result.is_null(), "hover on whitespace should be null, got: {result}");
}

#[tokio::test]
async fn test_lsp_hover_with_doc_comment() {
    let mut server = TestServer::start().await;

    let uri = "file:///test/Test.purs";
    let src = "module Test where\n\n-- | This is documented\nfoo = 42";
    server.open_file(uri, src).await;

    let resp = server.hover(10, uri, 3, 0).await;
    let result = resp.get("result").expect("should have result");

    assert!(!result.is_null(), "hover result should not be null, got: {result}");
    let contents = result.get("contents").expect("should have contents");
    let value = contents.get("value").expect("should have value").as_str().unwrap();
    assert!(value.contains("foo"), "hover should contain name: {value}");
    assert!(value.contains("Int"), "hover should contain type: {value}");
    assert!(value.contains("This is documented"), "hover should contain doc-comment: {value}");
}

#[tokio::test]
async fn test_lsp_hover_function_type() {
    let mut server = TestServer::start().await;

    let uri = "file:///test/Test.purs";
    let src = "module Test where\n\nfoo :: Int -> Int\nfoo x = x";
    server.open_file(uri, src).await;

    let resp = server.hover(10, uri, 3, 0).await;
    let result = resp.get("result").expect("should have result");

    assert!(!result.is_null(), "hover result should not be null, got: {result}");
    let contents = result.get("contents").expect("should have contents");
    let value = contents.get("value").expect("should have value").as_str().unwrap();
    assert!(value.contains("Int -> Int"), "hover should contain function type: {value}");
}

// --- Fixture-driven hover test ---

struct HoverTestCase {
    line: u32,
    col: u32,
    name: String,
    expected: HoverExpected,
}

enum HoverExpected {
    Null,
    Contains {
        type_substr: String,
        doc_substr: Option<String>,
    },
}

/// Parse test comments from a hover fixture file.
/// Format: `-- line:col (name) => hover: <type_substring>`
/// Or: `-- line:col (name) => hover: <type_substring> | doc: <doc_substring>`
/// Or: `-- line:col (name) => hover: null`
fn parse_hover_comments(source: &str) -> Vec<HoverTestCase> {
    let re = Regex::new(r"^-- (\d+):(\d+) \(([^)]+)\) => hover: (.+)$").unwrap();
    let mut cases = Vec::new();

    for line in source.lines() {
        let line = line.trim();
        let Some(caps) = re.captures(line) else {
            continue;
        };

        let test_line: u32 = caps[1].parse().unwrap();
        let test_col: u32 = caps[2].parse().unwrap();
        let name = caps[3].to_string();
        let target = caps[4].trim();

        let expected = if target == "null" {
            HoverExpected::Null
        } else if let Some((type_part, doc_part)) = target.split_once(" | doc: ") {
            HoverExpected::Contains {
                type_substr: type_part.trim().to_string(),
                doc_substr: Some(doc_part.trim().to_string()),
            }
        } else {
            HoverExpected::Contains {
                type_substr: target.to_string(),
                doc_substr: None,
            }
        };

        cases.push(HoverTestCase {
            line: test_line,
            col: test_col,
            name,
            expected,
        });
    }

    cases
}

#[tokio::test]
async fn test_lsp_hover_fixture() {
    let fixture_dir = std::fs::canonicalize(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/lsp/hover"),
    )
    .unwrap();

    let packages_dir = std::fs::canonicalize(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/packages"),
    )
    .unwrap();

    let simple_path = fixture_dir.join("Simple.purs");
    let simple_source = std::fs::read_to_string(&simple_path).unwrap();
    let test_cases = parse_hover_comments(&simple_source);
    assert!(
        !test_cases.is_empty(),
        "should find test cases in fixture comments"
    );

    let simple_uri = Url::from_file_path(&simple_path).unwrap().to_string();

    let sources_cmd = format!(
        "echo '{}'; echo '{}'",
        fixture_dir.join("**/*.purs").display(),
        packages_dir.join("prelude/src/**/*.purs").display(),
    );
    let mut server = TestServer::start_with_sources(Some(sources_cmd)).await;

    server.open_file(&simple_uri, &simple_source).await;

    // Wait for source loading by polling a known-good hover
    // Line 5 col 0 = "x" which should have type Int
    let mut ready = false;
    for _ in 0..100 {
        let resp = server.hover(99, &simple_uri, 5, 0).await;
        let result = resp.get("result").unwrap();
        if !result.is_null() {
            ready = true;
            break;
        }
        tokio::time::sleep(std::time::Duration::from_millis(200)).await;
    }
    assert!(ready, "server did not become ready within timeout");

    let mut id = 200u64;
    let mut passed = 0;
    let mut failed = 0;

    for case in &test_cases {
        let resp = server
            .hover(id, &simple_uri, case.line, case.col)
            .await;
        let result = resp.get("result").unwrap();
        id += 1;

        match &case.expected {
            HoverExpected::Null => {
                if !result.is_null() {
                    eprintln!(
                        "FAIL {}:{} ({}) — expected null, got: {}",
                        case.line, case.col, case.name, result
                    );
                    failed += 1;
                } else {
                    passed += 1;
                }
            }
            HoverExpected::Contains { type_substr, doc_substr } => {
                if result.is_null() {
                    eprintln!(
                        "FAIL {}:{} ({}) — expected hover containing '{}', got null",
                        case.line, case.col, case.name, type_substr
                    );
                    failed += 1;
                    continue;
                }

                let contents = result.get("contents").expect("should have contents");
                let value = contents
                    .get("value")
                    .and_then(|v| v.as_str())
                    .unwrap_or("");

                let mut case_ok = true;

                if !value.contains(type_substr.as_str()) {
                    eprintln!(
                        "FAIL {}:{} ({}) — hover does not contain '{}'\n  got: {}",
                        case.line, case.col, case.name, type_substr, value
                    );
                    case_ok = false;
                }

                if let Some(doc) = doc_substr {
                    if !value.contains(doc.as_str()) {
                        eprintln!(
                            "FAIL {}:{} ({}) — hover does not contain doc '{}'\n  got: {}",
                            case.line, case.col, case.name, doc, value
                        );
                        case_ok = false;
                    }
                }

                if case_ok {
                    passed += 1;
                } else {
                    failed += 1;
                }
            }
        }
    }

    eprintln!(
        "\nHover fixture results: {passed} passed, {failed} failed out of {} total",
        test_cases.len()
    );

    assert_eq!(
        failed, 0,
        "{failed} hover test case(s) failed (see above)"
    );
}

// --- Completion tests ---

#[tokio::test]
async fn test_lsp_completion_local_values() {
    let mut server = TestServer::start().await;

    let uri = "file:///test/Test.purs";
    let src = "module Test where\n\nfooBar = 1\n\nfooBaz = 2\n\nresult = foo";
    server.open_file(uri, src).await;

    // Cursor at end of "foo" on line 6 (0-indexed), column 12
    let resp = server.completion(10, uri, 6, 12).await;
    let result = resp.get("result").expect("should have result");

    assert!(!result.is_null(), "completion result should not be null, got: {result}");
    let items = result.get("items").expect("should have items");
    let items = items.as_array().expect("items should be array");

    let labels: Vec<&str> = items.iter().filter_map(|i| i.get("label").and_then(|l| l.as_str())).collect();
    assert!(labels.contains(&"fooBar"), "should contain fooBar, got: {labels:?}");
    assert!(labels.contains(&"fooBaz"), "should contain fooBaz, got: {labels:?}");
}

#[tokio::test]
async fn test_lsp_completion_cross_module_with_auto_import() {
    let fixture_dir = std::fs::canonicalize(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/lsp/hover"),
    )
    .unwrap();

    let packages_dir = std::fs::canonicalize(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/packages"),
    )
    .unwrap();

    let sources_cmd = format!(
        "echo '{}'; echo '{}'",
        fixture_dir.join("**/*.purs").display(),
        packages_dir.join("prelude/src/**/*.purs").display(),
    );
    let mut server = TestServer::start_with_sources(Some(sources_cmd)).await;

    let uri = "file:///test/Comp.purs";
    let src = "module Comp where\n\nresult = times";
    server.open_file(uri, src).await;

    // Wait for source loading
    let mut ready = false;
    for _ in 0..100 {
        let resp = server.completion(99, uri, 2, 14).await;
        let result = resp.get("result").unwrap();
        if !result.is_null() {
            if let Some(items) = result.get("items").and_then(|i| i.as_array()) {
                if !items.is_empty() {
                    ready = true;
                    break;
                }
            }
        }
        tokio::time::sleep(std::time::Duration::from_millis(200)).await;
    }
    assert!(ready, "server did not return completions within timeout");

    let resp = server.completion(100, uri, 2, 14).await;
    let result = resp.get("result").unwrap();
    let items = result.get("items").unwrap().as_array().unwrap();

    // Should find "times2" from Simple.Lib
    let times2_item = items.iter().find(|i| {
        i.get("label").and_then(|l| l.as_str()) == Some("times2")
    });
    assert!(times2_item.is_some(), "should find times2 in completions, got labels: {:?}",
        items.iter().filter_map(|i| i.get("label").and_then(|l| l.as_str())).collect::<Vec<_>>());

    let times2_item = times2_item.unwrap();

    // Should show module and type in detail
    let detail = times2_item.get("detail").and_then(|d| d.as_str()).unwrap_or("");
    assert!(detail.contains("Simple.Lib"), "detail should contain module name, got: {detail}");

    // Should have auto-import edit
    let edits = times2_item.get("additionalTextEdits");
    assert!(edits.is_some(), "should have additionalTextEdits for auto-import");
    let edits = edits.unwrap().as_array().unwrap();
    assert!(!edits.is_empty(), "additionalTextEdits should not be empty");

    let edit_text = edits[0].get("newText").and_then(|t| t.as_str()).unwrap_or("");
    assert!(edit_text.contains("import Simple.Lib"), "auto-import should import Simple.Lib, got: {edit_text}");
    assert!(edit_text.contains("times2"), "auto-import should include times2, got: {edit_text}");
}

#[tokio::test]
async fn test_lsp_completion_already_imported_no_auto_import() {
    let fixture_dir = std::fs::canonicalize(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/lsp/hover"),
    )
    .unwrap();

    let packages_dir = std::fs::canonicalize(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/packages"),
    )
    .unwrap();

    let sources_cmd = format!(
        "echo '{}'; echo '{}'",
        fixture_dir.join("**/*.purs").display(),
        packages_dir.join("prelude/src/**/*.purs").display(),
    );
    let mut server = TestServer::start_with_sources(Some(sources_cmd)).await;

    let uri = "file:///test/Comp2.purs";
    let src = "module Comp2 where\n\nimport Simple.Lib (times2)\n\nresult = times";
    server.open_file(uri, src).await;

    // Wait for source loading
    let mut ready = false;
    for _ in 0..100 {
        let resp = server.completion(99, uri, 4, 14).await;
        let result = resp.get("result").unwrap();
        if !result.is_null() {
            if let Some(items) = result.get("items").and_then(|i| i.as_array()) {
                if !items.is_empty() {
                    ready = true;
                    break;
                }
            }
        }
        tokio::time::sleep(std::time::Duration::from_millis(200)).await;
    }
    assert!(ready, "server did not return completions within timeout");

    let resp = server.completion(100, uri, 4, 14).await;
    let result = resp.get("result").unwrap();
    let items = result.get("items").unwrap().as_array().unwrap();

    let times2_item = items.iter().find(|i| {
        i.get("label").and_then(|l| l.as_str()) == Some("times2")
    });
    assert!(times2_item.is_some(), "should find times2 in completions");

    let times2_item = times2_item.unwrap();

    // Already imported — should NOT have additionalTextEdits
    let edits = times2_item.get("additionalTextEdits");
    let has_edits = edits.map_or(false, |e| {
        e.as_array().map_or(false, |a| !a.is_empty())
    });
    assert!(!has_edits, "already-imported value should not have auto-import edits");
}
