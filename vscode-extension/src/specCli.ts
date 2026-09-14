/**
 * Headless SolSpec verifier.
 *
 *   node out/specCli.js <file.sol> [packageDir] [--show]
 *
 * Prints one line per proof obligation
 * (`<contract>.<function> <what> ... <verdict>`), Lean's message
 * indented under a failure, then a summary. `--show` also prints the
 * generated Lean file, which is what `SolLoom: Show Generated Lean`
 * opens in the editor.
 *
 * Exit codes: 0 = ran ok and every obligation verified (functions
 * reported `unsupported` do not fail the run — they were never
 * attempted); 1 = ran ok and some obligation failed; 2 = infrastructure
 * error (bad usage, no package dir, Lean would not run, or errors
 * outside every obligation).
 */

import * as fs from "fs";
import * as path from "path";
import { findPackageDirUp, runLakeBuild, runLean, writeGeneratedFile } from "./detect";
import {
  Verdict,
  compileSpecFile,
  computeVerdicts,
  generatedFileName,
  parseLeanOutput,
} from "./spec/pipeline";

/** The Lean module a generated obligation file imports. */
const SPEC_TARGET = "Solidity.Spec.Tactic";

const MARK: Record<Verdict["status"], string> = {
  verified: "verified",
  failed: "failed",
  unsupported: "unsupported",
  assumed: "assumed",
};

async function main(): Promise<number> {
  const argv = process.argv.slice(2);
  const show = argv.includes("--show");
  const positional = argv.filter((a) => !a.startsWith("--"));
  const [fileArg, packageDirArg] = positional;
  if (!fileArg) {
    console.error("usage: node out/specCli.js <file.sol> [packageDir] [--show]");
    return 2;
  }

  const solPath = path.resolve(fileArg);
  let source: string;
  try {
    source = fs.readFileSync(solPath, "utf8");
  } catch (err) {
    console.error(`cannot read ${solPath}: ${err instanceof Error ? err.message : err}`);
    return 2;
  }

  const compiled = compileSpecFile(source);
  if (compiled.error) {
    const { message, loc } = compiled.error;
    console.error(`${solPath}:${loc.line + 1}:${loc.col + 1}: ${message}`);
    return 2;
  }
  const gen = compiled.generated!;

  if (show) {
    console.log(gen.text);
  }

  if (gen.obligations.length === 0) {
    for (const s of gen.skipped) {
      console.log(`${s.contract}.${s.fn} ${MARK[s.why === "free" ? "assumed" : "unsupported"]} — ${s.reason}`);
    }
    if (gen.skipped.length === 0) {
      console.log("no @custom: specification found");
    }
    return 0;
  }

  const packageDir = packageDirArg
    ? path.resolve(packageDirArg)
    : findPackageDirUp(path.dirname(solPath));
  if (!packageDir || !fs.existsSync(path.join(packageDir, "lakefile.toml"))) {
    console.error(
      "cannot find the Lake package dir (lakefile.toml + Solidity.lean); pass it as the second argument",
    );
    return 2;
  }

  /* The obligation file imports the Spec layer, which the default `lake
     build` deliberately leaves out (see lakefile.toml), so build it
     first. Cached: only the first run pays. */
  const build = await runLakeBuild("lake", packageDir, SPEC_TARGET);
  if (build.spawnError) {
    console.error(`lake invocation failed: ${build.spawnError}`);
    return 2;
  }
  if (build.exitCode !== 0) {
    console.error(`lake build ${SPEC_TARGET} failed:\n${build.stdout}\n${build.stderr}`);
    return 2;
  }

  const genPath = writeGeneratedFile(
    packageDir,
    generatedFileName(path.basename(solPath)),
    gen.text,
  );
  const run = await runLean("lake", packageDir, genPath);
  if (run.spawnError) {
    console.error(`lean invocation failed: ${run.spawnError}`);
    return 2;
  }
  const diags = parseLeanOutput(run.stdout);
  if (run.exitCode !== 0 && diags.length === 0) {
    console.error(`lean exited with code ${run.exitCode} and no diagnostics:\n${run.stderr}`);
    return 2;
  }

  const result = computeVerdicts(gen.obligations, gen.skipped, diags);
  for (const v of result.verdicts) {
    console.log(`${v.label}: ${MARK[v.status]} (line ${v.loc.line + 1})`);
    if (v.message && v.status !== "verified") {
      for (const line of v.message.split("\n")) {
        console.log(`  ${line}`);
      }
    }
  }
  console.log(`${result.verified}/${result.attempted} obligations verified`);

  if (result.globalErrors.length > 0) {
    console.error("errors outside every obligation (infrastructure problem):");
    for (const e of result.globalErrors) {
      console.error(`  ${e}`);
    }
    return 2;
  }
  return result.verified === result.attempted ? 0 : 1;
}

main().then(
  (code) => process.exit(code),
  (err) => {
    console.error(err instanceof Error ? (err.stack ?? err.message) : String(err));
    process.exit(2);
  },
);
