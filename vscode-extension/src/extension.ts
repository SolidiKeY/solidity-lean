import * as path from "path";
import * as vscode from "vscode";
import {
  computeVerdicts,
  generateLean,
  generatedFileName,
  parseLeanOutput,
  parseSolj,
} from "./core";
import {
  findPackageDirUp,
  runLakeBuild,
  runLean,
  scanForPackageDir,
  writeGeneratedFile,
} from "./detect";
import {
  compileSpecFile,
  computeVerdicts as computeSpecVerdicts,
  generatedFileName as specFileName,
  parseLeanOutput as parseSpecLeanOutput,
} from "./spec/pipeline";

/** Lean module the generated SolSpec obligation files import. */
const SPEC_TARGET = "Solidity.Spec.Tactic";

let statusBar: vscode.StatusBarItem;
let diagnostics: vscode.DiagnosticCollection;
let log: vscode.OutputChannel;

/** latest-wins: at most one verify in flight per uri, newest doc queued behind it. */
const inFlight = new Set<string>();
const queued = new Map<string, vscode.TextDocument>();

function isSolj(doc: vscode.TextDocument): boolean {
  return doc.languageId === "soljudge" || doc.fileName.endsWith(".solj");
}

function isSol(doc: vscode.TextDocument): boolean {
  return doc.fileName.endsWith(".sol");
}

/** Files SolLoom takes an interest in. */
function isVerifiable(doc: vscode.TextDocument): boolean {
  return isSolj(doc) || isSol(doc);
}

/**
 * A `.sol` file with no `@custom:` line has nothing to prove. Checking
 * for the marker before doing any work keeps the extension quiet in a
 * workspace full of ordinary contracts.
 */
function hasSpecClauses(doc: vscode.TextDocument): boolean {
  return /@custom:/.test(doc.getText());
}

function setStatus(text: string, tooltip?: string, warn = false): void {
  statusBar.text = text;
  statusBar.tooltip = tooltip;
  statusBar.backgroundColor = warn
    ? new vscode.ThemeColor("statusBarItem.warningBackground")
    : undefined;
  statusBar.show();
}

function resolvePackageDir(doc: vscode.TextDocument): string | undefined {
  const configured = vscode.workspace.getConfiguration("solloom").get<string>("packageDir");
  if (configured && configured.trim() !== "") {
    return configured;
  }
  if (doc.uri.scheme === "file") {
    const up = findPackageDirUp(path.dirname(doc.uri.fsPath));
    if (up) {
      return up;
    }
  }
  const roots = (vscode.workspace.workspaceFolders ?? [])
    .filter((f) => f.uri.scheme === "file")
    .map((f) => f.uri.fsPath);
  return scanForPackageDir(roots);
}

async function verifyDocument(doc: vscode.TextDocument): Promise<void> {
  if (!isVerifiable(doc)) {
    return;
  }
  const uri = doc.uri.toString();
  if (inFlight.has(uri)) {
    queued.set(uri, doc);
    return;
  }
  inFlight.add(uri);
  try {
    if (isSol(doc)) {
      await runSpecVerification(doc);
    } else {
      await runVerification(doc);
    }
  } catch (err) {
    const message = err instanceof Error ? err.message : String(err);
    log.appendLine(`verify failed: ${message}`);
    setStatus("$(error) SolLoom: error", message, true);
  } finally {
    inFlight.delete(uri);
    const next = queued.get(uri);
    queued.delete(uri);
    if (next) {
      void verifyDocument(next);
    }
  }
}

async function runVerification(doc: vscode.TextDocument): Promise<void> {
  const packageDir = resolvePackageDir(doc);
  if (!packageDir) {
    setStatus("$(warning) SolLoom: set solloom.packageDir", undefined, true);
    log.appendLine("no Lake package with Solidity.lean found; set solloom.packageDir");
    return;
  }

  const judgments = parseSolj(doc.getText());
  if (judgments.length === 0) {
    diagnostics.set(doc.uri, []);
    setStatus("SolLoom: no judgments", doc.fileName);
    return;
  }

  const gen = generateLean(judgments);
  let diags: ReturnType<typeof parseLeanOutput> = [];
  let infraError: string | undefined;

  if (gen.spans.length > 0) {
    const genPath = writeGeneratedFile(packageDir, generatedFileName(path.basename(doc.fileName)), gen.text);
    const lakeCommand = vscode.workspace.getConfiguration("solloom").get<string>("lakeCommand") || "lake";
    setStatus("$(sync~spin) SolLoom: verifying…", doc.fileName);
    log.appendLine(`$ ${lakeCommand} env lean --json ${genPath}  (cwd ${packageDir})`);
    const run = await runLean(lakeCommand, packageDir, genPath);
    if (run.stdout.trim() !== "") {
      log.appendLine(run.stdout.trimEnd());
    }
    if (run.stderr.trim() !== "") {
      log.appendLine(run.stderr.trimEnd());
    }
    log.appendLine(`exit code: ${run.exitCode}`);
    if (run.spawnError) {
      infraError = `lean invocation failed: ${run.spawnError}`;
    } else {
      diags = parseLeanOutput(run.stdout);
      if (run.exitCode !== 0 && diags.length === 0) {
        infraError = `lean exited with code ${run.exitCode}:\n${run.stderr}`;
      }
    }
  }

  if (infraError) {
    setStatus("$(error) SolLoom: error", infraError, true);
    const diag = new vscode.Diagnostic(
      new vscode.Range(0, 0, 0, 1),
      `SolLoom: ${infraError}`,
      vscode.DiagnosticSeverity.Error,
    );
    diag.source = "solloom";
    diagnostics.set(doc.uri, [diag]);
    return;
  }

  const { verdicts, globalErrors } = computeVerdicts(judgments, gen.spans, diags);
  const items: vscode.Diagnostic[] = [];
  for (const v of verdicts) {
    if (v.status === "failed") {
      const range = new vscode.Range(v.startLine, v.startCol, v.endLine, v.endCol);
      const diag = new vscode.Diagnostic(
        range,
        v.message ?? `j${v.index} failed to verify`,
        vscode.DiagnosticSeverity.Error,
      );
      diag.source = "solloom";
      items.push(diag);
    }
  }
  for (const e of globalErrors) {
    const diag = new vscode.Diagnostic(
      new vscode.Range(0, 0, 0, 1),
      `SolLoom (outside judgment spans): ${e}`,
      vscode.DiagnosticSeverity.Error,
    );
    diag.source = "solloom";
    items.push(diag);
  }
  diagnostics.set(doc.uri, items);

  const verified = verdicts.filter((v) => v.status === "verified").length;
  const n = verdicts.length;
  const details = verdicts
    .map((v) => `${v.status === "verified" ? "✓" : "✗"} j${v.index} (lines ${v.startLine + 1}-${v.endLine + 1})`)
    .join("\n");
  setStatus(`SolLoom: ${verified}/${n} verified`, details, verified < n);
}

/**
 * Verify a `.sol` file against its NatSpec specification: generate one
 * Lean theorem per `@custom:` clause, elaborate the file, and map each
 * diagnostic back to the clause line that produced it.
 */
async function runSpecVerification(doc: vscode.TextDocument): Promise<void> {
  if (!hasSpecClauses(doc)) {
    diagnostics.set(doc.uri, []);
    return;
  }

  const compiled = compileSpecFile(doc.getText());
  if (compiled.error) {
    const { message, loc } = compiled.error;
    const diag = new vscode.Diagnostic(
      new vscode.Range(loc.line, loc.col, loc.endLine, loc.endCol),
      `SolLoom: ${message}`,
      vscode.DiagnosticSeverity.Error,
    );
    diag.source = "solloom";
    diagnostics.set(doc.uri, [diag]);
    setStatus("$(error) SolLoom: parse error", message, true);
    return;
  }
  const gen = compiled.generated!;

  const items: vscode.Diagnostic[] = [];
  const addSkips = (): void => {
    for (const skip of gen.skipped) {
      const diag = new vscode.Diagnostic(
        new vscode.Range(skip.loc.line, skip.loc.col, skip.loc.endLine, skip.loc.endCol),
        `SolLoom: ${skip.reason}`,
        skip.why === "free"
          ? vscode.DiagnosticSeverity.Information
          : vscode.DiagnosticSeverity.Warning,
      );
      diag.source = "solloom";
      items.push(diag);
    }
  };

  if (gen.obligations.length === 0) {
    addSkips();
    diagnostics.set(doc.uri, items);
    setStatus("SolLoom: nothing to prove", doc.fileName);
    return;
  }

  const packageDir = resolvePackageDir(doc);
  if (!packageDir) {
    setStatus("$(warning) SolLoom: set solloom.packageDir", undefined, true);
    log.appendLine("no Lake package with Solidity.lean found; set solloom.packageDir");
    return;
  }

  const lakeCommand =
    vscode.workspace.getConfiguration("solloom").get<string>("lakeCommand") || "lake";

  setStatus("$(sync~spin) SolLoom: building the spec layer…", doc.fileName);
  log.appendLine(`$ ${lakeCommand} build ${SPEC_TARGET}  (cwd ${packageDir})`);
  const build = await runLakeBuild(lakeCommand, packageDir, SPEC_TARGET);
  if (build.spawnError || build.exitCode !== 0) {
    const message = build.spawnError ?? `lake build ${SPEC_TARGET} failed:\n${build.stderr}`;
    log.appendLine(message);
    setStatus("$(error) SolLoom: error", message, true);
    return;
  }

  const genPath = writeGeneratedFile(
    packageDir,
    specFileName(path.basename(doc.fileName)),
    gen.text,
  );
  setStatus("$(sync~spin) SolLoom: verifying…", doc.fileName);
  log.appendLine(`$ ${lakeCommand} env lean --json ${genPath}  (cwd ${packageDir})`);
  const run = await runLean(lakeCommand, packageDir, genPath);
  if (run.stdout.trim() !== "") {
    log.appendLine(run.stdout.trimEnd());
  }
  if (run.stderr.trim() !== "") {
    log.appendLine(run.stderr.trimEnd());
  }
  if (run.spawnError) {
    setStatus("$(error) SolLoom: error", run.spawnError, true);
    return;
  }

  const diags = parseSpecLeanOutput(run.stdout);
  if (run.exitCode !== 0 && diags.length === 0) {
    const message = `lean exited with code ${run.exitCode}:\n${run.stderr}`;
    setStatus("$(error) SolLoom: error", message, true);
    return;
  }

  const result = computeSpecVerdicts(gen.obligations, gen.skipped, diags);
  for (const v of result.verdicts) {
    if (v.status !== "failed") {
      continue;
    }
    const diag = new vscode.Diagnostic(
      new vscode.Range(v.loc.line, v.loc.col, v.loc.endLine, v.loc.endCol),
      `${v.label}: ${v.message ?? "not proved"}`,
      vscode.DiagnosticSeverity.Error,
    );
    diag.source = "solloom";
    items.push(diag);
  }
  addSkips();
  for (const e of result.globalErrors) {
    const diag = new vscode.Diagnostic(
      new vscode.Range(0, 0, 0, 1),
      `SolLoom (outside every obligation): ${e}`,
      vscode.DiagnosticSeverity.Error,
    );
    diag.source = "solloom";
    items.push(diag);
  }
  diagnostics.set(doc.uri, items);

  const details = result.verdicts.map((v) => `${v.status === "verified" ? "\u2713" : "\u2717"} ${v.label}`).join("\n");
  setStatus(
    `SolLoom: ${result.verified}/${result.attempted} proved`,
    details,
    result.verified < result.attempted,
  );
}

async function showGeneratedLean(): Promise<void> {
  const editor = vscode.window.activeTextEditor;
  if (!editor || !isVerifiable(editor.document)) {
    void vscode.window.showInformationMessage("Open a .sol or .solj file first.");
    return;
  }
  const doc = editor.document;
  const packageDir = resolvePackageDir(doc);
  if (!packageDir) {
    void vscode.window.showErrorMessage("SolLoom: no Lake package found; set solloom.packageDir.");
    return;
  }
  let genPath: string;
  if (isSol(doc)) {
    const compiled = compileSpecFile(doc.getText());
    if (compiled.error) {
      void vscode.window.showErrorMessage(`SolLoom: ${compiled.error.message}`);
      return;
    }
    genPath = writeGeneratedFile(
      packageDir,
      specFileName(path.basename(doc.fileName)),
      compiled.generated!.text,
    );
  } else {
    const gen = generateLean(parseSolj(doc.getText()));
    genPath = writeGeneratedFile(
      packageDir,
      generatedFileName(path.basename(doc.fileName)),
      gen.text,
    );
  }
  const genDoc = await vscode.workspace.openTextDocument(genPath);
  await vscode.window.showTextDocument(genDoc, { viewColumn: vscode.ViewColumn.Beside, preview: true });
}

export function activate(context: vscode.ExtensionContext): void {
  log = vscode.window.createOutputChannel("SolLoom");
  diagnostics = vscode.languages.createDiagnosticCollection("solloom");
  statusBar = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 90);
  statusBar.command = "solloom.verifyFile";
  context.subscriptions.push(log, diagnostics, statusBar);

  context.subscriptions.push(
    vscode.workspace.onDidOpenTextDocument((doc) => {
      if (isVerifiable(doc)) {
        void verifyDocument(doc);
      }
    }),
    vscode.workspace.onDidSaveTextDocument((doc) => {
      if (isVerifiable(doc)) {
        void verifyDocument(doc);
      }
    }),
    vscode.workspace.onDidCloseTextDocument((doc) => diagnostics.delete(doc.uri)),
    vscode.commands.registerCommand("solloom.verifyFile", () => {
      const doc = vscode.window.activeTextEditor?.document;
      if (doc) {
        void verifyDocument(doc);
      }
    }),
    vscode.commands.registerCommand("solloom.showGeneratedLean", () => void showGeneratedLean()),
  );

  // Verify anything already open at activation time.
  for (const doc of vscode.workspace.textDocuments) {
    if (isVerifiable(doc)) {
      void verifyDocument(doc);
    }
  }
}

export function deactivate(): void {
  // nothing to clean up beyond context.subscriptions
}
