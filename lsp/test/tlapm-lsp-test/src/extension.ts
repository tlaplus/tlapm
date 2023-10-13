// cSpell:words tlaplus opam tlapm

import * as vscode from 'vscode';
import { Executable, LanguageClient, LanguageClientOptions, TransportKind, VersionedTextDocumentIdentifier } from 'vscode-languageclient/node';

let client: LanguageClient;

export function activate(context: vscode.ExtensionContext) {
	console.log('Congratulations, your extension "tlapm-lsp-test" is now active!');

	pocTestCases();

	context.subscriptions.push(vscode.commands.registerTextEditorCommand('tlaplus.tlaps.check-step', (te, ed, args) => {
		console.log("CMD: tlaplus.tlaps.check-step invoked.");
		vscode.commands.executeCommand("tlaplus.tlaps.check-step.lsp",
			{ uri: te.document.uri.toString(), version: te.document.version } as VersionedTextDocumentIdentifier,
			{ start: te.selection.start, end: te.selection.end } as vscode.Range,
		);
	}));

	// `tlapm` (and `tlapm_lsp`) should be installed to the opam switch.
	// You can do that by running `make install` at the root project dir.
	const serverPath = 'opam';
	const logPath = context.asAbsolutePath('tlapm_lsp.log');
	const serverOptions: Executable = {
		command: serverPath,
		transport: TransportKind.stdio,
		args: ['exec', 'tlapm_lsp', '--', '--log-io', '--log-to=' + logPath],
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
