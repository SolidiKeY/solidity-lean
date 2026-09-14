/**
 * Headless SolLoom verifier.
 *
 *   node out/cli.js <file.solj> [packageDir]
 *
 * Prints one line per judgment: `j<N> <verified|failed> (source lines A-B)`
 * (A-B are 1-based source lines), failure messages indented below, then a
 * summary. Exit codes: 0 = ran ok and all judgments verified; 1 = ran ok and
 * some judgment failed; 2 = infrastructure error (bad usage, missing package
 * dir, lean could not run, or errors outside every judgment).
 */

import * as fs from "fs";
import * as path from "path";
import {
  computeVerdicts,
  generateLean,
  generatedFileName,
  parseLeanOutput,
  parseSolj,
} from "./core";
import { findPackageDirUp, runLean, writeGeneratedFile } from "./detect";

async function main(): Promise<number> {
  const [fileArg, packageDirArg] = process.argv.slice(2);
  if (!fileArg) {
    console.error("usage: node out/cli.js <file.solj> [packageDir]");
    return 2;
  }
  const soljPath = path.resolve(fileArg);
  let source: string;
  try {
    source = fs.readFileSync(soljPath, "utf8");
  } catch (err) {
    console.error(`cannot read ${soljPath}: ${err instanceof Error ? err.message : err}`);
    return 2;
  }

  const packageDir = packageDirArg
    ? path.resolve(packageDirArg)
    : findPackageDirUp(path.dirname(soljPath));
  if (!packageDir || !fs.existsSync(path.join(packageDir, "lakefile.toml"))) {
    console.error(
      "cannot find Lake package dir (lakefile.toml + Solidity.lean); pass it as second argument",
    );
    return 2;
  }

  const judgments = parseSolj(source);
  if (judgments.length === 0) {
    console.log("no judgments found");
    return 0;
  }

  const gen = generateLean(judgments);
  let diags: ReturnType<typeof parseLeanOutput> = [];
  if (gen.spans.length > 0) {
    const genPath = writeGeneratedFile(packageDir, generatedFileName(path.basename(soljPath)), gen.text);
    const run = await runLean("lake", packageDir, genPath);
    if (run.spawnError) {
      console.error(`lean invocation failed: ${run.spawnError}`);
      return 2;
    }
    diags = parseLeanOutput(run.stdout);
    if (run.exitCode !== 0 && diags.length === 0) {
      console.error(`lean exited with code ${run.exitCode} and no diagnostics:\n${run.stderr}`);
      return 2;
    }
  }

  const { verdicts, globalErrors } = computeVerdicts(judgments, gen.spans, diags);
  let verified = 0;
  for (const v of verdicts) {
    console.log(`j${v.index} ${v.status} (source lines ${v.startLine + 1}-${v.endLine + 1})`);
    if (v.status === "verified") {
      verified++;
    } else if (v.message) {
      for (const line of v.message.split("\n")) {
        console.log(`  ${line}`);
      }
    }
  }
  console.log(`${verified}/${verdicts.length} verified`);

  if (globalErrors.length > 0) {
    console.error("errors outside judgment spans (infrastructure problem):");
    for (const e of globalErrors) {
      console.error(`  ${e}`);
    }
    return 2;
  }
  return verified === verdicts.length ? 0 : 1;
}

main().then(
  (code) => process.exit(code),
  (err) => {
    console.error(err instanceof Error ? err.stack ?? err.message : String(err));
    process.exit(2);
  },
);
