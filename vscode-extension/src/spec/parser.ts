/**
 * Parser for the Solidity subset the SolSpec front-end verifies, and for
 * specification expressions.
 *
 * The Solidity grammar covered here is deliberately a subset: the
 * verifier's semantics (`Solidity/Semantics.lean`)
 * models storage, memory, locals and the `net` ledger, but has no loops
 * and no inter-contract calls. Anything outside the subset raises
 * `Unsupported`, which the driver turns into an `unsupported` verdict
 * for that one function — the rest of the contract still verifies.
 *
 * Specification expressions extend the program grammar with `old(e)`,
 * implication `==>`, equivalence `<==>` and bounded quantifiers
 * (`forall i in lo .. hi :: P`). They are parsed by the same routines
 * under a flag, so the two languages cannot drift apart.
 */

import {
  BinOpName,
  Clause,
  ClauseTag,
  ContractDef,
  Expr,
  FunctionDef,
  Loc,
  Param,
  ParseError,
  SolType,
  SourceUnit,
  StateVar,
  Stmt,
  StructDef,
  span,
} from "./ast";
import { DocLine, Token, tokenize } from "./lexer";

/** A construct outside the verified fragment: reported, never fatal. */
export class Unsupported extends Error {
  constructor(
    message: string,
    readonly loc: Loc,
  ) {
    super(message);
    this.name = "Unsupported";
  }
}

const TYPE_KEYWORDS = new Set([
  "uint",
  "int",
  "bool",
  "address",
  "mapping",
  "byte",
  "bytes",
  "string",
]);

const VISIBILITY = new Set(["public", "private", "internal", "external"]);
const MUTABILITY = new Set(["pure", "view", "payable", "constant", "immutable"]);
const DATA_LOCATION = new Set(["memory", "storage", "calldata"]);

const CLAUSE_TAGS: ReadonlySet<string> = new Set<ClauseTag>([
  "requires",
  "ensures",
  "invariant",
  "modifies",
  "reverts_when",
  "partial",
  "free",
  "tactic",
  "decreases",
]);

/* ------------------------------------------------------------------ */
/* The cursor                                                          */
/* ------------------------------------------------------------------ */

class Cursor {
  pos = 0;

  constructor(readonly toks: Token[]) {}

  peek(offset = 0): Token {
    return this.toks[Math.min(this.pos + offset, this.toks.length - 1)];
  }

  next(): Token {
    const t = this.peek();
    if (t.kind !== "eof") {
      this.pos++;
    }
    return t;
  }

  at(text: string): boolean {
    const t = this.peek();
    return (t.kind === "punct" || t.kind === "ident") && t.text === text;
  }

  atAny(...texts: string[]): boolean {
    return texts.some((t) => this.at(t));
  }

  eat(text: string): boolean {
    if (this.at(text)) {
      this.pos++;
      return true;
    }
    return false;
  }

  expect(text: string): Token {
    if (!this.at(text)) {
      const t = this.peek();
      throw new ParseError(
        `expected ${JSON.stringify(text)}, found ${JSON.stringify(t.text || "end of file")}`,
        t.loc,
      );
    }
    return this.next();
  }

  expectIdent(what: string): Token {
    const t = this.peek();
    if (t.kind !== "ident") {
      throw new ParseError(`expected ${what}`, t.loc);
    }
    return this.next();
  }
}

/* ------------------------------------------------------------------ */
/* Expressions                                                         */
/* ------------------------------------------------------------------ */

/**
 * Binding powers, loosest first. `==>` and `<==>` sit below the ternary
 * (so `a ==> b ? c : d` parses as `a ==> (b ? c : d)`) and are right
 * associative, as in Dafny.
 */
const BIN_LEVELS: BinOpName[][] = [
  ["||"],
  ["&&"],
  ["==", "!="],
  ["<", ">", "<=", ">="],
  ["+", "-"],
  ["*", "/", "%"],
];

class ExprParser {
  constructor(
    readonly cur: Cursor,
    readonly specMode: boolean,
  ) {}

  parse(): Expr {
    return this.parseEquiv();
  }

  private parseEquiv(): Expr {
    const lhs = this.parseImplies();
    if (this.specMode && this.cur.at("<==>")) {
      const op = this.cur.next();
      const rhs = this.parseEquiv();
      return { k: "bin", op: "<==>", lhs, rhs, loc: span(lhs.loc, rhs.loc) };
    }
    return lhs;
  }

  private parseImplies(): Expr {
    const lhs = this.parseTernary();
    if (this.specMode && this.cur.at("==>")) {
      this.cur.next();
      const rhs = this.parseImplies();
      return { k: "bin", op: "==>", lhs, rhs, loc: span(lhs.loc, rhs.loc) };
    }
    return lhs;
  }

  private parseTernary(): Expr {
    const cond = this.parseBinary(0);
    if (this.cur.at("?")) {
      this.cur.next();
      const thn = this.parseTernary();
      this.cur.expect(":");
      const els = this.parseTernary();
      return { k: "cond", cond, thn, els, loc: span(cond.loc, els.loc) };
    }
    return cond;
  }

  private parseBinary(level: number): Expr {
    if (level >= BIN_LEVELS.length) {
      return this.parsePower();
    }
    let lhs = this.parseBinary(level + 1);
    for (;;) {
      const op = BIN_LEVELS[level].find((o) => this.cur.at(o));
      if (!op) {
        return lhs;
      }
      this.cur.next();
      const rhs = this.parseBinary(level + 1);
      lhs = { k: "bin", op, lhs, rhs, loc: span(lhs.loc, rhs.loc) };
    }
  }

  /** `**` is right associative and binds tighter than `*`. */
  private parsePower(): Expr {
    const base = this.parseUnary();
    if (this.cur.at("**")) {
      this.cur.next();
      const exp = this.parsePower();
      return { k: "bin", op: "**", lhs: base, rhs: exp, loc: span(base.loc, exp.loc) };
    }
    return base;
  }

  private parseUnary(): Expr {
    const t = this.cur.peek();
    if (this.cur.at("!")) {
      this.cur.next();
      const arg = this.parseUnary();
      return { k: "not", arg, loc: span(t.loc, arg.loc) };
    }
    if (this.cur.at("-")) {
      this.cur.next();
      const arg = this.parseUnary();
      return { k: "neg", arg, loc: span(t.loc, arg.loc) };
    }
    if (this.cur.at("+")) {
      this.cur.next();
      return this.parseUnary();
    }
    if (this.cur.atAny("++", "--")) {
      const op = this.cur.next().text as "++" | "--";
      const target = this.parseUnary();
      return { k: "incdec", op, prefix: true, target, loc: span(t.loc, target.loc) };
    }
    return this.parsePostfix(this.parseAtom());
  }

  private parsePostfix(start: Expr): Expr {
    let e = start;
    for (;;) {
      if (this.cur.at(".")) {
        this.cur.next();
        const name = this.cur.expectIdent("a member name");
        e = { k: "member", base: e, name: name.text, loc: span(e.loc, name.loc) };
        continue;
      }
      if (this.cur.at("[")) {
        this.cur.next();
        const index = new ExprParser(this.cur, this.specMode).parse();
        const close = this.cur.expect("]");
        e = { k: "index", base: e, index, loc: span(e.loc, close.loc) };
        continue;
      }
      if (this.cur.at("(")) {
        this.cur.next();
        const args: Expr[] = [];
        if (!this.cur.at(")")) {
          do {
            args.push(new ExprParser(this.cur, this.specMode).parse());
          } while (this.cur.eat(","));
        }
        const close = this.cur.expect(")");
        e = this.mkCall(e, args, span(e.loc, close.loc));
        continue;
      }
      if (this.cur.atAny("++", "--")) {
        const op = this.cur.next().text as "++" | "--";
        e = { k: "incdec", op, prefix: false, target: e, loc: e.loc };
        continue;
      }
      return e;
    }
  }

  private mkCall(callee: Expr, args: Expr[], loc: Loc): Expr {
    if (this.specMode && callee.k === "id" && callee.name === "old") {
      if (args.length !== 1) {
        throw new ParseError("old(...) takes exactly one argument", loc);
      }
      return { k: "old", arg: args[0], loc };
    }
    return { k: "call", callee, args, loc };
  }

  private parseAtom(): Expr {
    const t = this.cur.peek();

    if (this.cur.at("(")) {
      this.cur.next();
      const inner = new ExprParser(this.cur, this.specMode).parse();
      this.cur.expect(")");
      return inner;
    }

    if (t.kind === "number") {
      this.cur.next();
      return { k: "num", value: parseNumber(t), loc: t.loc };
    }

    if (t.kind === "ident") {
      if (t.text === "true" || t.text === "false") {
        this.cur.next();
        return { k: "bool", value: t.text === "true", loc: t.loc };
      }
      if (this.specMode && (t.text === "forall" || t.text === "exists")) {
        return this.parseQuantifier();
      }
      this.cur.next();
      return { k: "id", name: t.text, loc: t.loc };
    }

    throw new ParseError(
      `expected an expression, found ${JSON.stringify(t.text || "end of input")}`,
      t.loc,
    );
  }

  /** `forall i in lo .. hi :: body` — the range is half-open `[lo, hi)`. */
  private parseQuantifier(): Expr {
    const kw = this.cur.next();
    const quantifier = kw.text as "forall" | "exists";
    const binder = this.cur.expectIdent("a quantifier variable").text;
    this.cur.expect("in");
    const lo = new ExprParser(this.cur, this.specMode).parseBinary(0);
    this.cur.expect("..");
    const hi = new ExprParser(this.cur, this.specMode).parseBinary(0);
    this.cur.expect("::");
    const body = new ExprParser(this.cur, this.specMode).parse();
    return { k: "quant", quantifier, binder, lo, hi, body, loc: span(kw.loc, body.loc) };
  }
}

function parseNumber(t: Token): bigint {
  const text = t.text.replace(/_/g, "");
  if (/^0[xX]/.test(text)) {
    return BigInt(text);
  }
  const sci = /^([0-9]+)e([0-9]+)$/.exec(text);
  if (sci) {
    return BigInt(sci[1]) * 10n ** BigInt(sci[2]);
  }
  return BigInt(text);
}

/* ------------------------------------------------------------------ */
/* Types                                                               */
/* ------------------------------------------------------------------ */

function parseType(cur: Cursor, structNames: ReadonlySet<string>): SolType | undefined {
  const t = cur.peek();
  if (t.kind !== "ident") {
    return undefined;
  }

  let base: SolType | undefined;

  if (t.text === "mapping") {
    cur.next();
    cur.expect("(");
    const key = parseType(cur, structNames);
    if (!key) {
      throw new ParseError("expected a mapping key type", cur.peek().loc);
    }
    cur.expect("=>");
    const value = parseType(cur, structNames);
    if (!value) {
      throw new ParseError("expected a mapping value type", cur.peek().loc);
    }
    cur.expect(")");
    base = { kind: "mapping", key, value };
  } else if (t.text === "bool") {
    cur.next();
    base = { kind: "bool" };
  } else if (t.text === "address") {
    cur.next();
    /* `address` is a 160-bit unsigned word; the ledger indexes by it. */
    base = { kind: "uint", bits: 160 };
    if (cur.at("payable")) {
      cur.next();
    }
  } else if (/^uint([0-9]+)?$/.test(t.text)) {
    cur.next();
    base = { kind: "uint", bits: t.text === "uint" ? 256 : Number(t.text.slice(4)) };
  } else if (/^int([0-9]+)?$/.test(t.text)) {
    cur.next();
    base = { kind: "int", bits: t.text === "int" ? 256 : Number(t.text.slice(3)) };
  } else if (structNames.has(t.text)) {
    cur.next();
    base = { kind: "struct", name: t.text };
  } else if (TYPE_KEYWORDS.has(t.text)) {
    /* `bytes`, `string`, `bytesN` — recognized as types, but outside the
       fragment, so the enclosing declaration is reported rather than
       silently mis-parsed. */
    cur.next();
    throw new Unsupported(`type ${t.text} is outside the verified fragment`, t.loc);
  } else {
    return undefined;
  }

  for (;;) {
    if (cur.at("[") && cur.peek(1).kind === "punct" && cur.peek(1).text === "]") {
      cur.next();
      cur.next();
      base = { kind: "array", elem: base };
      continue;
    }
    if (cur.at("[")) {
      throw new Unsupported("fixed-size arrays are outside the verified fragment", cur.peek().loc);
    }
    return base;
  }
}

/* ------------------------------------------------------------------ */
/* NatSpec clauses                                                     */
/* ------------------------------------------------------------------ */

/** Parse one `@custom:<tag> …` doc line; non-`@custom:` lines are skipped. */
export function parseClauseLine(doc: DocLine): Clause | undefined {
  const m = /^@custom:([A-Za-z_][A-Za-z0-9_]*)\s*(.*)$/.exec(doc.text);
  if (!m) {
    return undefined;
  }
  const tag = m[1];
  const raw = m[2].trim();
  if (!CLAUSE_TAGS.has(tag)) {
    /* An unknown @custom: tag is somebody else's annotation (solc allows
       any), not a spec clause. Ignoring it is the right call. */
    return undefined;
  }
  const clause: Clause = { tag: tag as ClauseTag, raw, loc: doc.loc };

  if (tag === "partial" || tag === "free") {
    if (raw !== "") {
      clause.error = `@custom:${tag} takes no argument`;
    }
    return clause;
  }
  if (tag === "tactic") {
    if (raw === "") {
      clause.error = "@custom:tactic needs a Lean tactic";
    }
    return clause;
  }
  if (raw === "") {
    if (tag === "modifies") {
      /* `@custom:modifies` with nothing after it is the empty frame:
         the function changes no storage at all. */
      clause.targets = [];
      return clause;
    }
    clause.error = `@custom:${tag} needs an expression`;
    return clause;
  }

  try {
    if (tag === "modifies") {
      clause.targets = parseSpecExprList(raw, doc.loc);
    } else {
      clause.expr = parseSpecExpr(raw, doc.loc);
    }
  } catch (err) {
    clause.error = err instanceof Error ? err.message : String(err);
  }
  return clause;
}

/** Collect the spec clauses of a run of doc lines. */
export function parseClauses(docs: DocLine[]): Clause[] {
  const out: Clause[] = [];
  for (const doc of docs) {
    const clause = parseClauseLine(doc);
    if (clause) {
      out.push(clause);
    }
  }
  return out;
}

/**
 * Parse a specification expression from clause text. `baseLoc` is the
 * `@custom:` line, and every node of the result carries it: a clause is
 * one line, so line-level attribution is all a diagnostic needs.
 */
export function parseSpecExpr(text: string, baseLoc: Loc): Expr {
  const cur = new Cursor(tokenize(text));
  const e = new ExprParser(cur, true).parse();
  if (cur.peek().kind !== "eof") {
    throw new ParseError(
      `unexpected ${JSON.stringify(cur.peek().text)} after the expression`,
      baseLoc,
    );
  }
  return relocate(e, baseLoc);
}

function parseSpecExprList(text: string, baseLoc: Loc): Expr[] {
  const cur = new Cursor(tokenize(text));
  const out: Expr[] = [];
  do {
    out.push(new ExprParser(cur, true).parse());
  } while (cur.eat(","));
  if (cur.peek().kind !== "eof") {
    throw new ParseError(`unexpected ${JSON.stringify(cur.peek().text)} in the list`, baseLoc);
  }
  return out.map((e) => relocate(e, baseLoc));
}

/** Stamp every node of a clause expression with the clause's own line. */
function relocate(e: Expr, loc: Loc): Expr {
  const go = (x: Expr): Expr => {
    const y = { ...x, loc } as Expr;
    switch (y.k) {
      case "member":
        return { ...y, base: go(y.base) };
      case "index":
        return { ...y, base: go(y.base), index: go(y.index) };
      case "bin":
        return { ...y, lhs: go(y.lhs), rhs: go(y.rhs) };
      case "not":
      case "neg":
        return { ...y, arg: go(y.arg) };
      case "old":
        return { ...y, arg: go(y.arg) };
      case "incdec":
        return { ...y, target: go(y.target) };
      case "cond":
        return { ...y, cond: go(y.cond), thn: go(y.thn), els: go(y.els) };
      case "call":
        return { ...y, callee: go(y.callee), args: y.args.map(go) };
      case "quant":
        return { ...y, lo: go(y.lo), hi: go(y.hi), body: go(y.body) };
      default:
        return y;
    }
  };
  return go(e);
}

/* ------------------------------------------------------------------ */
/* Ghost annotations inside a body                                     */
/* ------------------------------------------------------------------ */

/**
 * `/// @custom:assert e` and `/// @custom:assume e` written between
 * statements. `assert` is an obligation at that program point (and an
 * assumption afterwards, as in Dafny); `assume` is an unchecked
 * assumption.
 */
function parseGhostLines(docs: DocLine[]): Stmt[] {
  const out: Stmt[] = [];
  for (const doc of docs) {
    const m = /^@custom:(assert|assume)\s+(.+)$/.exec(doc.text);
    if (!m) {
      continue;
    }
    out.push({
      k: "ghost",
      ghost: m[1] as "assert" | "assume",
      expr: parseSpecExpr(m[2].trim(), doc.loc),
      loc: doc.loc,
    });
  }
  return out;
}

/* ------------------------------------------------------------------ */
/* Statements                                                          */
/* ------------------------------------------------------------------ */

class BodyParser {
  constructor(
    readonly cur: Cursor,
    readonly structNames: ReadonlySet<string>,
  ) {}

  private expr(): Expr {
    return new ExprParser(this.cur, false).parse();
  }

  parseBlock(): Stmt[] {
    this.cur.expect("{");
    const out: Stmt[] = [];
    while (!this.cur.at("}")) {
      if (this.cur.peek().kind === "eof") {
        throw new ParseError("unterminated block", this.cur.peek().loc);
      }
      out.push(...parseGhostLines(this.cur.peek().docs));
      out.push(...this.parseStatement());
    }
    /* Ghost lines written just before the closing brace still belong to
       the body — they are the postcondition-shaped ones. */
    out.push(...parseGhostLines(this.cur.peek().docs));
    this.cur.expect("}");
    return out;
  }

  /** One source statement; a declaration may expand to several. */
  parseStatement(): Stmt[] {
    const t = this.cur.peek();

    if (this.cur.at("{")) {
      /* A nested bare block has no scope of its own in the semantics
         (locals live in one env), so it flattens. */
      return this.parseBlock();
    }
    if (this.cur.at(";")) {
      this.cur.next();
      return [];
    }

    if (t.kind === "ident") {
      switch (t.text) {
        case "if":
          return [this.parseIf()];
        case "while":
        case "for":
        case "do":
          throw new Unsupported(
            `\`${t.text}\` loops are outside the verified fragment (the semantics has no loop rule)`,
            t.loc,
          );
        case "unchecked":
          throw new Unsupported("`unchecked` blocks are outside the verified fragment", t.loc);
        case "try":
        case "emit":
        case "assembly":
          throw new Unsupported(`\`${t.text}\` is outside the verified fragment`, t.loc);
        case "return":
          return [this.parseReturn()];
        case "delete": {
          this.cur.next();
          const target = this.expr();
          const end = this.cur.expect(";");
          return [{ k: "delete", target, loc: span(t.loc, end.loc) }];
        }
        case "require":
        case "assert": {
          const kw = this.cur.next();
          this.cur.expect("(");
          const cond = this.expr();
          /* `require(c, "reason")` — the reason string has no semantic
             content here, so it is dropped. */
          while (this.cur.eat(",")) {
            this.expr();
          }
          this.cur.expect(")");
          const end = this.cur.expect(";");
          return [
            kw.text === "require"
              ? { k: "require", cond, loc: span(t.loc, end.loc) }
              : { k: "assert", cond, loc: span(t.loc, end.loc) },
          ];
        }
        case "revert": {
          this.cur.next();
          if (this.cur.eat("(")) {
            while (!this.cur.at(")")) {
              this.cur.next();
            }
            this.cur.expect(")");
          } else if (this.cur.peek().kind === "ident") {
            /* `revert CustomError(...);` */
            this.cur.next();
            if (this.cur.eat("(")) {
              let depth = 1;
              while (depth > 0 && this.cur.peek().kind !== "eof") {
                if (this.cur.at("(")) {
                  depth++;
                } else if (this.cur.at(")")) {
                  depth--;
                }
                this.cur.next();
              }
            }
          }
          const end = this.cur.expect(";");
          return [{ k: "revert", loc: span(t.loc, end.loc) }];
        }
      }
    }

    const decl = this.tryParseDeclaration();
    if (decl) {
      return [decl];
    }

    return [this.parseExpressionStatement()];
  }

  /**
   * A local declaration, or `undefined` when the statement turns out to
   * be an expression. Solidity needs the lookahead: `x = 1;` and
   * `uint x = 1;` start the same way once `x` could be a struct name.
   */
  private tryParseDeclaration(): Stmt | undefined {
    const save = this.cur.pos;
    let type: SolType | undefined;
    try {
      type = parseType(this.cur, this.structNames);
    } catch (err) {
      if (err instanceof Unsupported) {
        /* A declaration whose *type* is unsupported is still a
           declaration: report it rather than mis-parsing it as an
           expression. */
        throw err;
      }
      this.cur.pos = save;
      return undefined;
    }
    if (!type) {
      this.cur.pos = save;
      return undefined;
    }
    while (this.cur.peek().kind === "ident" && DATA_LOCATION.has(this.cur.peek().text)) {
      this.cur.next();
    }
    if (this.cur.peek().kind !== "ident") {
      this.cur.pos = save;
      return undefined;
    }
    const name = this.cur.next();
    const start = this.cur.toks[save].loc;
    let init: Expr | undefined;
    if (this.cur.eat("=")) {
      init = this.expr();
    }
    const end = this.cur.expect(";");
    return { k: "vardecl", type, name: name.text, init, loc: span(start, end.loc) };
  }

  private parseIf(): Stmt {
    const kw = this.cur.expect("if");
    this.cur.expect("(");
    const cond = this.expr();
    this.cur.expect(")");
    const thn = this.parseBranch();
    let els: Stmt[] = [];
    let endLoc = thn.length > 0 ? thn[thn.length - 1].loc : cond.loc;
    if (this.cur.eat("else")) {
      els = this.parseBranch();
      endLoc = els.length > 0 ? els[els.length - 1].loc : endLoc;
    }
    return { k: "if", cond, thn, els, loc: span(kw.loc, endLoc) };
  }

  private parseBranch(): Stmt[] {
    if (this.cur.at("{")) {
      return this.parseBlock();
    }
    return this.parseStatement();
  }

  private parseReturn(): Stmt {
    const kw = this.cur.expect("return");
    let value: Expr | undefined;
    if (!this.cur.at(";")) {
      value = this.expr();
    }
    const end = this.cur.expect(";");
    return { k: "return", value, loc: span(kw.loc, end.loc) };
  }

  private parseExpressionStatement(): Stmt {
    const start = this.cur.peek().loc;
    const lhs = this.expr();

    for (const [tok, op] of [
      ["+=", "+"],
      ["-=", "-"],
      ["*=", "*"],
      ["/=", "/"],
      ["%=", "%"],
    ] as const) {
      if (this.cur.at(tok)) {
        this.cur.next();
        const value = this.expr();
        const end = this.cur.expect(";");
        return { k: "compound", op, target: lhs, value, loc: span(start, end.loc) };
      }
    }

    if (this.cur.at("=")) {
      this.cur.next();
      const value = this.expr();
      const end = this.cur.expect(";");
      return { k: "assign", target: lhs, value, loc: span(start, end.loc) };
    }

    const end = this.cur.expect(";");
    const loc = span(start, end.loc);

    /* Method-call statements the semantics has dedicated rules for. */
    if (lhs.k === "call" && lhs.callee.k === "member") {
      const recv = lhs.callee.base;
      switch (lhs.callee.name) {
        case "push":
          return { k: "push", target: recv, value: lhs.args[0], loc };
        case "pop":
          if (lhs.args.length !== 0) {
            throw new ParseError("pop() takes no argument", loc);
          }
          return { k: "pop", target: recv, loc };
        case "transfer":
          if (lhs.args.length !== 1) {
            throw new ParseError("transfer(...) takes one argument", loc);
          }
          return { k: "transfer", recipient: recv, amount: lhs.args[0], loc };
      }
    }
    if (lhs.k === "call") {
      throw new Unsupported(
        "function calls are outside the verified fragment (the interpreter has no call rule; inline the callee)",
        loc,
      );
    }

    return { k: "exprstmt", expr: lhs, loc };
  }
}

/* ------------------------------------------------------------------ */
/* Declarations                                                        */
/* ------------------------------------------------------------------ */

function skipBalanced(cur: Cursor, open: string, close: string): void {
  cur.expect(open);
  let depth = 1;
  while (depth > 0) {
    const t = cur.peek();
    if (t.kind === "eof") {
      throw new ParseError(`unterminated ${open}`, t.loc);
    }
    if (t.kind === "punct" && t.text === open) {
      depth++;
    } else if (t.kind === "punct" && t.text === close) {
      depth--;
    }
    cur.next();
  }
}

function skipToSemicolonOrBlock(cur: Cursor): void {
  for (;;) {
    const t = cur.peek();
    if (t.kind === "eof") {
      return;
    }
    if (t.kind === "punct" && t.text === ";") {
      cur.next();
      return;
    }
    if (t.kind === "punct" && t.text === "{") {
      skipBalanced(cur, "{", "}");
      return;
    }
    cur.next();
  }
}

function collectStructNames(toks: Token[]): Set<string> {
  const names = new Set<string>();
  for (let i = 0; i + 1 < toks.length; i++) {
    if (toks[i].kind === "ident" && toks[i].text === "struct" && toks[i + 1].kind === "ident") {
      names.add(toks[i + 1].text);
    }
  }
  return names;
}

function parseParams(cur: Cursor, structNames: ReadonlySet<string>): Param[] {
  cur.expect("(");
  const out: Param[] = [];
  if (!cur.at(")")) {
    do {
      const start = cur.peek().loc;
      const type = parseType(cur, structNames);
      if (!type) {
        throw new ParseError("expected a parameter type", cur.peek().loc);
      }
      while (cur.peek().kind === "ident" && DATA_LOCATION.has(cur.peek().text)) {
        cur.next();
      }
      let name = "";
      let end = start;
      if (cur.peek().kind === "ident") {
        const tok = cur.next();
        name = tok.text;
        end = tok.loc;
      }
      out.push({ name, type, loc: span(start, end) });
    } while (cur.eat(","));
  }
  cur.expect(")");
  return out;
}

function parseFunction(
  cur: Cursor,
  structNames: ReadonlySet<string>,
  docs: DocLine[],
): FunctionDef {
  const kw = cur.next();
  const isConstructor = kw.text !== "function";
  let name = kw.text;
  if (!isConstructor) {
    name = cur.expectIdent("a function name").text;
  }
  const params = parseParams(cur, structNames);

  let visibility = "public";
  let mutability = "";
  let returns: Param[] = [];
  for (;;) {
    const t = cur.peek();
    if (t.kind === "ident" && VISIBILITY.has(t.text)) {
      visibility = t.text;
      cur.next();
      continue;
    }
    if (t.kind === "ident" && MUTABILITY.has(t.text)) {
      mutability = t.text;
      cur.next();
      continue;
    }
    if (t.kind === "ident" && t.text === "returns") {
      cur.next();
      returns = parseParams(cur, structNames);
      continue;
    }
    if (t.kind === "ident" && t.text === "override") {
      cur.next();
      if (cur.at("(")) {
        skipBalanced(cur, "(", ")");
      }
      continue;
    }
    if (t.kind === "ident" && t.text === "virtual") {
      cur.next();
      continue;
    }
    if (t.kind === "ident" && !cur.at("{")) {
      /* A modifier invocation: `onlyOwner` or `onlyOwner(x)`. Modifiers
         wrap the body with code this front-end cannot see, so a
         specified function may not carry one. */
      throw new Unsupported(
        `modifier \`${t.text}\` is outside the verified fragment (its body is not inlined)`,
        t.loc,
      );
    }
    break;
  }

  const loc = span(kw.loc, cur.peek().loc);
  if (cur.at(";")) {
    cur.next();
    return {
      name,
      isConstructor,
      params,
      returns,
      visibility,
      mutability,
      body: [],
      clauses: parseClauses(docs),
      loc,
    };
  }

  const body = new BodyParser(cur, structNames).parseBlock();
  return {
    name,
    isConstructor,
    params,
    returns,
    visibility,
    mutability,
    body,
    clauses: parseClauses(docs),
    loc,
  };
}

function parseStruct(cur: Cursor, structNames: ReadonlySet<string>): StructDef {
  const kw = cur.expect("struct");
  const name = cur.expectIdent("a struct name");
  cur.expect("{");
  const fields: Param[] = [];
  while (!cur.at("}")) {
    const start = cur.peek().loc;
    const type = parseType(cur, structNames);
    if (!type) {
      throw new ParseError("expected a struct member type", cur.peek().loc);
    }
    const fieldName = cur.expectIdent("a struct member name");
    const end = cur.expect(";");
    fields.push({ name: fieldName.text, type, loc: span(start, end.loc) });
  }
  const close = cur.expect("}");
  return { name: name.text, fields, loc: span(kw.loc, close.loc) };
}

function parseContract(cur: Cursor, structNames: ReadonlySet<string>): ContractDef {
  const kw = cur.next();
  const clauses = parseClauses(kw.docs);
  const name = cur.expectIdent("a contract name");
  if (cur.eat("is")) {
    do {
      cur.expectIdent("a base contract name");
      if (cur.at("(")) {
        skipBalanced(cur, "(", ")");
      }
    } while (cur.eat(","));
  }
  cur.expect("{");

  const structs: StructDef[] = [];
  const stateVars: StateVar[] = [];
  const functions: FunctionDef[] = [];

  while (!cur.at("}")) {
    const t = cur.peek();
    if (t.kind === "eof") {
      throw new ParseError("unterminated contract body", t.loc);
    }
    if (t.kind === "ident") {
      if (t.text === "struct") {
        structs.push(parseStruct(cur, structNames));
        continue;
      }
      if (t.text === "function" || t.text === "constructor") {
        const docs = t.docs;
        const save = cur.pos;
        try {
          functions.push(parseFunction(cur, structNames, docs));
        } catch (err) {
          if (err instanceof Unsupported) {
            /* Record the function as present but unverifiable, and skip
               past its body so the rest of the contract still parses. */
            cur.pos = save;
            const head = cur.next();
            const fname = head.text === "function" ? cur.expectIdent("a function name").text : head.text;
            skipToSemicolonOrBlock(cur);
            functions.push({
              name: fname,
              isConstructor: head.text !== "function",
              params: [],
              returns: [],
              visibility: "public",
              mutability: "",
              body: [],
              clauses: parseClauses(docs),
              unsupported: { reason: err.message, loc: err.loc },
              loc: head.loc,
            });
            continue;
          }
          throw err;
        }
        continue;
      }
      if (
        t.text === "modifier" ||
        t.text === "event" ||
        t.text === "error" ||
        t.text === "enum" ||
        t.text === "using" ||
        t.text === "receive" ||
        t.text === "fallback"
      ) {
        skipToSemicolonOrBlock(cur);
        continue;
      }
    }

    /* State variable. */
    const start = cur.peek().loc;
    const save = cur.pos;
    let type: SolType | undefined;
    try {
      type = parseType(cur, structNames);
    } catch (err) {
      if (err instanceof Unsupported) {
        cur.pos = save;
        skipToSemicolonOrBlock(cur);
        continue;
      }
      throw err;
    }
    if (!type) {
      throw new ParseError(
        `expected a declaration, found ${JSON.stringify(cur.peek().text || "end of file")}`,
        cur.peek().loc,
      );
    }
    while (cur.peek().kind === "ident" && (VISIBILITY.has(cur.peek().text) || MUTABILITY.has(cur.peek().text))) {
      cur.next();
    }
    const varName = cur.expectIdent("a state variable name");
    let init: Expr | undefined;
    if (cur.eat("=")) {
      init = new ExprParser(cur, false).parse();
    }
    const end = cur.expect(";");
    stateVars.push({ name: varName.text, type, init, loc: span(start, end.loc) });
  }

  const close = cur.expect("}");
  return { name: name.text, structs, stateVars, functions, clauses, loc: span(kw.loc, close.loc) };
}

/** Parse a `.sol` source file into the contracts the emitter consumes. */
export function parseSourceUnit(source: string): SourceUnit {
  const toks = tokenize(source);
  const structNames = collectStructNames(toks);
  const cur = new Cursor(toks);
  const contracts: ContractDef[] = [];
  const fileStructs: StructDef[] = [];

  while (cur.peek().kind !== "eof") {
    const t = cur.peek();
    if (t.kind === "ident" && (t.text === "pragma" || t.text === "import")) {
      skipToSemicolonOrBlock(cur);
      continue;
    }
    if (t.kind === "ident" && (t.text === "contract" || t.text === "library" || t.text === "interface")) {
      contracts.push(parseContract(cur, structNames));
      continue;
    }
    if (t.kind === "ident" && t.text === "struct") {
      fileStructs.push(parseStruct(cur, structNames));
      continue;
    }
    if (t.kind === "ident" && (t.text === "enum" || t.text === "error" || t.text === "function")) {
      skipToSemicolonOrBlock(cur);
      continue;
    }
    throw new ParseError(
      `expected a top-level declaration, found ${JSON.stringify(t.text || "end of file")}`,
      t.loc,
    );
  }

  return { contracts, fileStructs };
}
