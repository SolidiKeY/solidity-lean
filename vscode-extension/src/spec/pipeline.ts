/**
 * The pure SolSpec pipeline: `.sol` source in, Lean obligations and
 * per-clause verdicts out.
 *
 * No node or vscode imports — `specCli.ts` and `extension.ts` both drive
 * this, and the tests drive it directly.
 */

import { Loc, ParseError } from "./ast";
import { Generated, Obligation, Skipped, generateLean } from "./emitLean";
import { parseSourceUnit } from "./parser";

export { Obligation, Skipped, Generated } from "./emitLean";

export interface SpecFile {
  generated?: Generated;
  /** Set when the file could not be parsed at all. */
  error?: { message: string; loc: Loc };
}

/** Parse and generate; a parse error is returned, never thrown. */
export function compileSpecFile(source: string): SpecFile {
  try {
    const unit = parseSourceUnit(source);
    return { generated: generateLean(unit.contracts, unit.fileStructs) };
  } catch (err) {
    if (err instanceof ParseError) {
      return { error: { message: err.message, loc: err.loc } };
    }
    if (err instanceof Error) {
      return {
        error: {
          message: err.message,
          loc: { line: 0, col: 0, endLine: 0, endCol: 0 },
        },
      };
    }
    throw err;
  }
}

/** `Contract.sol` -> `Contract_sol_spec.lean`. */
export function generatedFileName(basename: string): string {
  const stem = basename.replace(/\.sol$/i, "").replace(/[^A-Za-z0-9_]/g, "_");
  return `${stem}_sol_spec.lean`;
}

/* ------------------------------------------------------------------ */
/* Verdicts                                                            */
/* ------------------------------------------------------------------ */

export interface LeanDiag {
  severity: string;
  /** 1-based line span in the generated file. */
  line: number;
  endLine: number;
  message: string;
}

/** Parse the JSON-lines output of `lean --json`; other lines are ignored. */
export function parseLeanOutput(stdout: string): LeanDiag[] {
  const diags: LeanDiag[] = [];
  for (const raw of stdout.split(/\r?\n/)) {
    const line = raw.trim();
    if (!line.startsWith("{")) {
      continue;
    }
    try {
      const obj = JSON.parse(line);
      if (obj && obj.pos && typeof obj.pos.line === "number") {
        diags.push({
          severity: String(obj.severity ?? "error"),
          line: obj.pos.line,
          endLine: typeof obj.endPos?.line === "number" ? obj.endPos.line : obj.pos.line,
          message: String(obj.data ?? "unknown error"),
        });
      }
    } catch {
      /* not a diagnostic line */
    }
  }
  return diags;
}

export type VerdictStatus = "verified" | "failed" | "unsupported" | "assumed";

export interface Verdict {
  label: string;
  status: VerdictStatus;
  contract: string;
  fn: string;
  loc: Loc;
  /** Lean's message for a failure, or the reason for a skip. */
  message?: string;
}

export interface VerdictResult {
  verdicts: Verdict[];
  /** Errors that fell outside every theorem: an infrastructure problem. */
  globalErrors: string[];
  verified: number;
  /** Obligations actually attempted (verified + failed). */
  attempted: number;
}

/**
 * Attribute Lean diagnostics to obligations by generated-line span: an
 * obligation with no error in its span is verified. Skipped functions
 * become `unsupported`/`assumed` verdicts so the report is complete.
 */
export function computeVerdicts(
  obligations: Obligation[],
  skipped: Skipped[],
  diags: LeanDiag[],
): VerdictResult {
  const claimed = new Set<LeanDiag>();
  const verdicts: Verdict[] = [];
  let verified = 0;

  for (const ob of obligations) {
    const errors = diags.filter(
      (d) => d.severity === "error" && d.line >= ob.genStartLine && d.line <= ob.genEndLine,
    );
    for (const e of errors) {
      claimed.add(e);
    }
    if (errors.length === 0) {
      verified++;
      verdicts.push({
        label: ob.label,
        status: "verified",
        contract: ob.contract,
        fn: ob.fn,
        loc: ob.loc,
      });
    } else {
      verdicts.push({
        label: ob.label,
        status: "failed",
        contract: ob.contract,
        fn: ob.fn,
        loc: ob.loc,
        message: errors.map((e) => e.message).join("\n\n"),
      });
    }
  }

  for (const s of skipped) {
    verdicts.push({
      label: `${s.contract}.${s.fn}`,
      status: s.why === "free" ? "assumed" : "unsupported",
      contract: s.contract,
      fn: s.fn,
      loc: s.loc,
      message: s.reason,
    });
  }

  const globalErrors = diags
    .filter((d) => d.severity === "error" && !claimed.has(d))
    .map((d) => `line ${d.line}: ${d.message}`);

  return { verdicts, globalErrors, verified, attempted: obligations.length };
}
