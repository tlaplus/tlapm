import * as vscode from 'vscode';
import { Executable, LanguageClient, LanguageClientOptions, ServerOptions, TransportKind } from 'vscode-languageclient/node';

let client: LanguageClient;

export function activate(context: vscode.ExtensionContext) {
	console.log('Congratulations, your extension "tlapm-lsp-test" is now active!');
	context.subscriptions.push(vscode.commands.registerCommand('tlapm-lsp-test.helloWorld', () => {
		vscode.window.showInformationMessage('Key there from tlapm-lsp-test!');
	}));

	const serverPath = context.asAbsolutePath('../../../_build/default/lsp/bin/tlapm_lsp.exe');
	const logPath = context.asAbsolutePath('tlapm_lsp.log');
	const serverOptions: Executable = {
		command: serverPath,
		transport: TransportKind.stdio,
		args: ['--log-io', '--log-to=' + logPath],
	};
	const clientOptions: LanguageClientOptions = {
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
