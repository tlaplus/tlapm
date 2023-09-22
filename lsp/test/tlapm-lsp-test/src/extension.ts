import * as path from 'path';
import * as vscode from 'vscode';
import { Executable, LanguageClient, LanguageClientOptions, ServerOptions, TransportKind } from 'vscode-languageclient/node';

let client: LanguageClient;

export function activate(context: vscode.ExtensionContext) {
	console.log('Congratulations, your extension "tlapm-lsp-test" is now active!');
	context.subscriptions.push(vscode.commands.registerCommand('tlapm-lsp-test.helloWorld', () => {
		vscode.window.showInformationMessage('Key there from tlapm-lsp-test!');
	}));

	const serverPath = '/home/karolis/CODE/pub/tlapm-lsp/_build/default/lsp/bin/tlapm_lsp.exe';
	let serverOptions: Executable = {
		command: serverPath + ' --trace 2>/tmp/lsp-log-tlapm',
		transport: TransportKind.stdio,
		args: [],
		// args: [
		// 	'--stdio',
		// 	// '--trace',
		// ],
		options: { shell: true } // TODO: Remove.
	};
	let clientOptions: LanguageClientOptions = {
		documentSelector: [{ scheme: 'file', language: 'tlaplus' }],
	};
	client = new LanguageClient(
		'tlapm-lsp-example',
		'TLAPM LSP Example',
		serverOptions,
		clientOptions,
		true,
	);
	client.start();
}

export function deactivate() {
	if (!client) {
		return undefined;
	}
	return client.stop();
}
