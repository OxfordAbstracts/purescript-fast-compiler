use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;

use super::super::Backend;

impl Backend {
    pub(crate) async fn handle_formatting(
        &self,
        params: DocumentFormattingParams,
    ) -> Result<Option<Vec<TextEdit>>> {
        let formatter_cmd = match &self.formatter_command {
            Some(cmd) => cmd.clone(),
            None => return Ok(None),
        };

        let uri = &params.text_document.uri;

        // Get the file path from the URI
        let file_path = match uri.to_file_path() {
            Ok(path) => path,
            Err(_) => {
                self.client
                    .log_message(MessageType::ERROR, format!("Cannot convert URI to file path: {uri}"))
                    .await;
                return Ok(None);
            }
        };

        // Get current source content
        let source = {
            let files = self.files.read().await;
            files.get(&uri.to_string()).map(|f| f.source.clone())
        };
        let source = match source {
            Some(s) => s,
            None => {
                // Try reading from disk
                match std::fs::read_to_string(&file_path) {
                    Ok(s) => s,
                    Err(e) => {
                        self.client
                            .log_message(MessageType::ERROR, format!("Cannot read file: {e}"))
                            .await;
                        return Ok(None);
                    }
                }
            }
        };

        // Split the command into program and args
        let parts: Vec<&str> = formatter_cmd.split_whitespace().collect();
        if parts.is_empty() {
            return Ok(None);
        }
        let program = parts[0];
        let args: Vec<&str> = parts[1..].to_vec();

        // Run the formatter command, piping source code via stdin
        let mut child = match std::process::Command::new(program)
            .args(&args)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
        {
            Ok(child) => child,
            Err(e) => {
                self.client
                    .log_message(
                        MessageType::ERROR,
                        format!("Formatter command failed to execute: {e}"),
                    )
                    .await;
                return Ok(None);
            }
        };

        // Write source to stdin
        if let Some(mut stdin) = child.stdin.take() {
            use std::io::Write;
            if let Err(e) = stdin.write_all(source.as_bytes()) {
                self.client
                    .log_message(
                        MessageType::ERROR,
                        format!("Failed to write to formatter stdin: {e}"),
                    )
                    .await;
                return Ok(None);
            }
        }

        let output = match child.wait_with_output() {
            Ok(output) => output,
            Err(e) => {
                self.client
                    .log_message(
                        MessageType::ERROR,
                        format!("Formatter command failed to execute: {e}"),
                    )
                    .await;
                return Ok(None);
            }
        };

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            self.client
                .log_message(
                    MessageType::WARNING,
                    format!("Formatter exited with {}: {stderr}", output.status),
                )
                .await;
            return Ok(None);
        }

        let formatted = match String::from_utf8(output.stdout) {
            Ok(s) => s,
            Err(e) => {
                self.client
                    .log_message(
                        MessageType::ERROR,
                        format!("Formatter output is not valid UTF-8: {e}"),
                    )
                    .await;
                return Ok(None);
            }
        };

        // If the formatted output is the same, return no edits
        if formatted == source {
            return Ok(Some(Vec::new()));
        }

        // Replace the entire document content
        let line_count = source.lines().count() as u32;
        let last_line_len = source.lines().last().map_or(0, |l| l.len()) as u32;

        Ok(Some(vec![TextEdit {
            range: Range {
                start: Position {
                    line: 0,
                    character: 0,
                },
                end: Position {
                    line: line_count,
                    character: last_line_len,
                },
            },
            new_text: formatted,
        }]))
    }
}
