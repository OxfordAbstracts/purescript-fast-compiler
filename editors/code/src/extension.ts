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

  context.subscriptions.push(
    vscode.commands.registerCommand("pfc.rebuildModule", async () => {
      const editor = vscode.window.activeTextEditor;
      if (!editor) {
        vscode.window.showWarningMessage("No active editor");
        return;
      }
      if (!client) {
        vscode.window.showWarningMessage("Language server not running");
        return;
      }
      await client.sendRequest("pfc/rebuildModule", {
        uri: editor.document.uri.toString(),
      });
    }),
    vscode.commands.registerCommand("pfc.rebuildProject", async () => {
      if (!client) {
        vscode.window.showWarningMessage("Language server not running");
        return;
      }
      await client.sendRequest("pfc/rebuildProject");
    })
  );

  client.start();
}

export function deactivate(): Thenable<void> | undefined {
  return client?.stop();
}
