import * as vscode from 'vscode';
import { Executable, LanguageClient, LanguageClientOptions, TransportKind } from 'vscode-languageclient/node';

let client: LanguageClient;

export function activate(context: vscode.ExtensionContext) {
	console.log('Congratulations, your extension "tlapm-lsp-test" is now active!');

	pocTestCases();

	context.subscriptions.push(vscode.commands.registerTextEditorCommand('tlapm-lsp-test.prove-step', (te, ed, args) => {
		console.log("CMD: tlapm-lsp-test.prove-step invoked.");
		vscode.commands.executeCommand("tlapm-lsp-test.prove-step.lsp", [
			{
				uri: te.document.uri,
				version: te.document.version,
				cursor: te.selection.active,
				selection: {from: te.selection.start, till: te.selection.end}
			}
		]);
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

function pocTestCases() {
	const poController = vscode.tests.createTestController(
		'tlapm_proof_obligations',
		'TLA Proof Obligations'
	);
	const poExampleItem = poController.createTestItem("some", "My Proof Obligation", undefined);
	poExampleItem.range = new vscode.Range(new vscode.Position(1, 3), new vscode.Position(1, 7));
	poController.items.add(poExampleItem);
}
