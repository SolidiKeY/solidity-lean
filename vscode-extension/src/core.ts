/**
 * Pure core of SolLoom: parse .solj sources into judgments with source
 * ranges, generate the Lean file text with a line map, parse the JSON-lines
 * output of `lake env lean --json`, and compute per-judgment verdicts.
 *
 * No vscode or node imports — usable from both the extension and the CLI.
 */

export const INVALID_JUDGMENT_MESSAGE =
  "judgment must start with `<` (diamond) or `[` (box)";

export interface Judgment {
  /** 1-based paragraph order; theorem name is j<index>. */
  index: number;
  /** Comment-stripped content lines, spliced verbatim into sol!{ … }. */
  lines: string[];
  /** 0-based source range of the paragraph. */
  startLine: number;
  startCol: number;
  endLine: number;
  endCol: number;
  /** false when the paragraph does not start with `<` or `[`. */
  valid: boolean;
}

/** Strip a `//` line comment (the vocabulary has no string literals). */
function stripComment(line: string): string {
  const i = line.indexOf("//");
  return i >= 0 ? line.slice(0, i) : line;
}

/**
 * Parse a .solj source into judgments. `//` comments are stripped;
 * paragraphs are runs of non-blank (post-strip) lines separated by one or
 * more blank lines.
 */
export function parseSolj(source: string): Judgment[] {
  const rawLines = source.split(/\r?\n/);
  const judgments: Judgment[] = [];

  interface Paragraph {
    lines: string[];
    startLine: number;
    startCol: number;
    endLine: number;
    endCol: number;
  }
  let current: Paragraph | null = null;

  const flush = () => {
    if (!current) {
      return;
    }
    const first = current.lines[0];
    const valid = first.startsWith("<") || first.startsWith("[");
    judgments.push({
      index: judgments.length + 1,
      lines: current.lines,
      startLine: current.startLine,
      startCol: current.startCol,
      endLine: current.endLine,
      endCol: current.endCol,
      valid,
    });
    current = null;
  };

  for (let i = 0; i < rawLines.length; i++) {
    const stripped = stripComment(rawLines[i]);
    if (stripped.trim() === "") {
      flush();
      continue;
    }
    const contentStart = stripped.length - stripped.trimStart().length;
    // First line is trimmed on the left so `sol!{ <line>` reads naturally;
    // continuation lines keep their indentation, trailing whitespace dropped.
    const content: string = current === null ? stripped.trim() : stripped.replace(/\s+$/, "");
    if (current === null) {
      current = {
        lines: [content],
        startLine: i,
        startCol: contentStart,
        endLine: i,
        endCol: rawLines[i].length,
      };
    } else {
      current.lines.push(content);
      current.endLine = i;
      current.endCol = rawLines[i].length;
    }
  }
  flush();
  return judgments;
}

export interface GeneratedSpan {
  /** Judgment index this theorem came from. */
  index: number;
  /** 1-based inclusive line span of the theorem in the generated file. */
  genStartLine: number;
  genEndLine: number;
}

export interface GeneratedLean {
  text: string;
  spans: GeneratedSpan[];
}

/**
 * Generate the Lean file: fixed header, one `theorem j<N>` per valid
 * judgment (names follow paragraph order, invalid paragraphs keep their
 * number but produce no theorem), one blank line between theorems.
 */
export function generateLean(judgments: Judgment[]): GeneratedLean {
  const lines: string[] = [
    "import Solidity",
    "",
    "namespace SolJudgeGen",
    "open Solidity Solidity.Wp",
  ];
  const spans: GeneratedSpan[] = [];

  for (const j of judgments) {
    if (!j.valid) {
      continue;
    }
    lines.push("");
    const genStartLine = lines.length + 1; // 1-based line of the next push
    const body = [...j.lines];
    body[0] = `theorem j${j.index} : (sol!{ ${body[0]}`;
    body[body.length - 1] = `${body[body.length - 1]} }).Holds := by sol_wp`;
    for (const l of body) {
      lines.push(l);
    }
    spans.push({ index: j.index, genStartLine, genEndLine: lines.length });
  }

  lines.push("");
  lines.push("end SolJudgeGen");
  lines.push("");
  return { text: lines.join("\n"), spans };
}

export interface LeanDiag {
  severity: string;
  /** 1-based line span in the generated file. */
  line: number;
  endLine: number;
  message: string;
}

/** Parse the JSON-lines output of `lean --json`; non-JSON lines are ignored. */
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
      // not a diagnostic line; ignore
    }
  }
  return diags;
}

export type VerdictStatus = "verified" | "failed";

export interface Verdict {
  index: number;
  status: VerdictStatus;
  /** Present for failed judgments: the Lean message(s) or the parse error. */
  message?: string;
  /** 0-based source range, copied from the judgment. */
  startLine: number;
  startCol: number;
  endLine: number;
  endCol: number;
}

export interface VerdictResult {
  verdicts: Verdict[];
  /** Error diagnostics outside every theorem span (infrastructure trouble). */
  globalErrors: string[];
}

/**
 * Combine judgments, generated spans and Lean diagnostics into verdicts.
 * A judgment is verified iff no error diagnostic starts within its theorem's
 * generated line span. Invalid paragraphs are failed without Lean.
 */
export function computeVerdicts(
  judgments: Judgment[],
  spans: GeneratedSpan[],
  diags: LeanDiag[],
): VerdictResult {
  const spanByIndex = new Map<number, GeneratedSpan>();
  for (const s of spans) {
    spanByIndex.set(s.index, s);
  }
  const claimed = new Set<LeanDiag>();
  const verdicts: Verdict[] = [];

  for (const j of judgments) {
    const base = {
      index: j.index,
      startLine: j.startLine,
      startCol: j.startCol,
      endLine: j.endLine,
      endCol: j.endCol,
    };
    if (!j.valid) {
      verdicts.push({ ...base, status: "failed", message: INVALID_JUDGMENT_MESSAGE });
      continue;
    }
    const span = spanByIndex.get(j.index);
    const errors = span
      ? diags.filter(
          (d) => d.severity === "error" && d.line >= span.genStartLine && d.line <= span.genEndLine,
        )
      : [];
    for (const e of errors) {
      claimed.add(e);
    }
    if (errors.length === 0) {
      verdicts.push({ ...base, status: "verified" });
    } else {
      verdicts.push({ ...base, status: "failed", message: errors.map((e) => e.message).join("\n\n") });
    }
  }

  const globalErrors = diags
    .filter((d) => d.severity === "error" && !claimed.has(d))
    .map((d) => `line ${d.line}: ${d.message}`);
  return { verdicts, globalErrors };
}

/** `basename.solj` → `basename_solj.lean` (sanitized for Lean/file safety). */
export function generatedFileName(soljBasename: string): string {
  const stem = soljBasename.replace(/\.solj$/i, "").replace(/[^A-Za-z0-9_]/g, "_");
  return `${stem}_solj.lean`;
}
