/**
 * Lexer for the Solidity subset and for specification expressions.
 *
 * Two things distinguish it from a plain tokenizer:
 *
 * - **NatSpec is not thrown away.** Every `///` (and `/** … *\/`) line is
 *   kept and attached to the next token as `docs`, so the parser can read
 *   the doc comment of the declaration that follows. That is the whole
 *   point of the front-end: the specification lives in the comments.
 * - **Ordinary `//` comments are dropped**, so a contract can be
 *   commented normally without any of it reaching the parser.
 */

import { Loc, ParseError } from "./ast";

export type TokKind = "ident" | "number" | "string" | "punct" | "eof";

export interface DocLine {
  /** Text after the `///` or the `*`, trimmed. */
  text: string;
  loc: Loc;
}

export interface Token {
  kind: TokKind;
  text: string;
  loc: Loc;
  /** Doc-comment lines immediately preceding this token. */
  docs: DocLine[];
}

/** Multi-character operators, longest first so the scan is greedy. */
const PUNCT = [
  "<==>",
  "==>",
  "..",
  "::",
  "**=",
  "<<=",
  ">>=",
  "&&",
  "||",
  "==",
  "!=",
  "<=",
  ">=",
  "++",
  "--",
  "+=",
  "-=",
  "*=",
  "/=",
  "%=",
  "=>",
  "**",
  "->",
  "(",
  ")",
  "{",
  "}",
  "[",
  "]",
  ";",
  ",",
  ".",
  "=",
  "+",
  "-",
  "*",
  "/",
  "%",
  "<",
  ">",
  "!",
  "?",
  ":",
  "&",
  "|",
  "^",
  "~",
  "@",
];

const IDENT_START = /[A-Za-z_$]/;
const IDENT_REST = /[A-Za-z0-9_$]/;

export function tokenize(source: string): Token[] {
  const tokens: Token[] = [];
  let pending: DocLine[] = [];

  let i = 0;
  let line = 0;
  let col = 0;

  const here = (): { line: number; col: number } => ({ line, col });
  const advance = (n: number): void => {
    for (let k = 0; k < n; k++) {
      if (source[i] === "\n") {
        line++;
        col = 0;
      } else {
        col++;
      }
      i++;
    }
  };
  const locFrom = (start: { line: number; col: number }): Loc => ({
    line: start.line,
    col: start.col,
    endLine: line,
    endCol: col,
  });

  const push = (kind: TokKind, text: string, loc: Loc): void => {
    tokens.push({ kind, text, loc, docs: pending });
    pending = [];
  };

  while (i < source.length) {
    const ch = source[i];

    if (ch === " " || ch === "\t" || ch === "\r") {
      advance(1);
      continue;
    }
    if (ch === "\n") {
      advance(1);
      continue;
    }

    /* Comments. `///` and `/** … *\/` are documentation and are kept;
       `//` and `/* … *\/` are dropped. A dropped comment does not clear
       the pending docs: `/// @custom:requires x > 0` followed by an
       ordinary `// note to self` still documents the next declaration. */
    if (ch === "/" && source[i + 1] === "/") {
      const isDoc = source[i + 2] === "/" && source[i + 3] !== "/";
      const start = here();
      advance(isDoc ? 3 : 2);
      const textStart = i;
      while (i < source.length && source[i] !== "\n") {
        advance(1);
      }
      if (isDoc) {
        pending.push({
          text: source.slice(textStart, i).trim(),
          loc: locFrom(start),
        });
      }
      continue;
    }
    if (ch === "/" && source[i + 1] === "*") {
      const isDoc = source[i + 2] === "*" && source[i + 3] !== "/";
      const start = here();
      advance(isDoc ? 3 : 2);
      const textStart = i;
      while (i < source.length && !(source[i] === "*" && source[i + 1] === "/")) {
        advance(1);
      }
      const body = source.slice(textStart, i);
      advance(2);
      if (isDoc) {
        /* Each line of a block doc comment is one NatSpec line, with the
           leading `*` gutter removed. Lines are located relative to the
           comment's own start line. */
        const lines = body.split("\n");
        for (let n = 0; n < lines.length; n++) {
          const text = lines[n].replace(/^\s*\*?\s?/, "").trimEnd();
          if (text.trim() === "") {
            continue;
          }
          const ln = start.line + n;
          pending.push({
            text: text.trim(),
            loc: { line: ln, col: 0, endLine: ln, endCol: lines[n].length + 4 },
          });
        }
      }
      continue;
    }

    if (IDENT_START.test(ch)) {
      const start = here();
      const from = i;
      while (i < source.length && IDENT_REST.test(source[i])) {
        advance(1);
      }
      push("ident", source.slice(from, i), locFrom(start));
      continue;
    }

    if (/[0-9]/.test(ch)) {
      const start = here();
      const from = i;
      if (ch === "0" && (source[i + 1] === "x" || source[i + 1] === "X")) {
        advance(2);
        while (i < source.length && /[0-9A-Fa-f_]/.test(source[i])) {
          advance(1);
        }
      } else {
        while (i < source.length && /[0-9_]/.test(source[i])) {
          advance(1);
        }
        /* `1e18` — Solidity's scientific notation for integers. */
        if (source[i] === "e" && /[0-9]/.test(source[i + 1] ?? "")) {
          advance(1);
          while (i < source.length && /[0-9]/.test(source[i])) {
            advance(1);
          }
        }
      }
      push("number", source.slice(from, i), locFrom(start));
      continue;
    }

    if (ch === '"' || ch === "'") {
      const start = here();
      const quote = ch;
      const from = i;
      advance(1);
      while (i < source.length && source[i] !== quote) {
        advance(source[i] === "\\" ? 2 : 1);
      }
      advance(1);
      push("string", source.slice(from, i), locFrom(start));
      continue;
    }

    const op = PUNCT.find((p) => source.startsWith(p, i));
    if (op) {
      const start = here();
      advance(op.length);
      push("punct", op, locFrom(start));
      continue;
    }

    const start = here();
    advance(1);
    throw new ParseError(`unexpected character ${JSON.stringify(ch)}`, locFrom(start));
  }

  tokens.push({
    kind: "eof",
    text: "",
    loc: { line, col, endLine: line, endCol: col },
    docs: pending,
  });
  return tokens;
}
