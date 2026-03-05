import * as vscode from "vscode";
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
} from "vscode-languageclient/node";

let client: LanguageClient | undefined;

export function activate(context: vscode.ExtensionContext) {
  const config = vscode.workspace.getConfiguration("pfc");
  const serverPath = config.get<string>("serverPath", "pfc");
  const sourcesCommand = config.get<string>("sourcesCommand", "");

  const args = ["lsp"];
  if (sourcesCommand) {
    args.push("--sources-cmd", sourcesCommand);
  }

  const serverOptions: ServerOptions = {
    command: serverPath,
    args,
  };

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: "file", language: "purescript" }],
  };

  client = new LanguageClient(
    "pfc",
    "PureScript Fast Compiler",
    serverOptions,
    clientOptions
  );

  client.start();
}

export function deactivate(): Thenable<void> | undefined {
  return client?.stop();
}
