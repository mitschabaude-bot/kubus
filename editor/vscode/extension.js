// Starts `kubus --lsp` for .ktt files.
const path = require('path');
const fs = require('fs');
const vscode = require('vscode');
const { LanguageClient } = require('vscode-languageclient/node');

let client;

function activate(context) {
  const cfg = vscode.workspace.getConfiguration('kubus');
  const env = Object.assign({}, process.env);
  let libPath = cfg.get('libraryPath');
  if (!libPath) {
    const folders = (vscode.workspace.workspaceFolders || []).map(f => path.join(f.uri.fsPath, 'lib'));
    libPath = folders.filter(d => fs.existsSync(d)).join(':');
  }
  if (libPath) env.KUBUS_PATH = env.KUBUS_PATH ? `${libPath}:${env.KUBUS_PATH}` : libPath;
  const server = { command: cfg.get('path') || 'kubus', args: ['--lsp'], options: { env } };
  client = new LanguageClient('kubus', 'Kubus', server, { documentSelector: [{ language: 'kubus' }] });
  client.start();
  context.subscriptions.push({ dispose: () => client && client.stop() });
}

function deactivate() {
  return client ? client.stop() : undefined;
}

module.exports = { activate, deactivate };
