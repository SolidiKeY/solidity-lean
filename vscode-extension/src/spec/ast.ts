/**
 * Shared AST for the SolSpec front-end: Solidity types, the supported
 * statement/expression subset, specification clauses, and contracts.
 *
 * Pure data — no node or vscode imports, so the whole pipeline is
 * testable in isolation.
 */

/** 0-based line, 0-based column: the shape VS Code diagnostics want. */
export interface Loc {
  line: number;
  col: number;
  endLine: number;
  endCol: number;
}

export function span(a: Loc, b: Loc): Loc {
  return { line: a.line, col: a.col, endLine: b.endLine, endCol: b.endCol };
}

/* ------------------------------------------------------------------ */
/* Types                                                               */
/* ------------------------------------------------------------------ */

export type SolType =
  | { kind: "uint"; bits: number }
  | { kind: "int"; bits: number }
  | { kind: "bool" }
  | { kind: "array"; elem: SolType }
  | { kind: "mapping"; key: SolType; value: SolType }
  | { kind: "struct"; name: string };

export const UINT256: SolType = { kind: "uint", bits: 256 };
export const BOOL: SolType = { kind: "bool" };

export function isPrimitive(t: SolType): boolean {
  return t.kind === "uint" || t.kind === "int" || t.kind === "bool";
}

export function isIntegral(t: SolType): boolean {
  return t.kind === "uint" || t.kind === "int";
}

export function typeEq(a: SolType, b: SolType): boolean {
  if (a.kind !== b.kind) {
    return false;
  }
  switch (a.kind) {
    case "uint":
    case "int":
      return a.bits === (b as { bits: number }).bits;
    case "bool":
      return true;
    case "array":
      return typeEq(a.elem, (b as { elem: SolType }).elem);
    case "mapping": {
      const m = b as { key: SolType; value: SolType };
      return typeEq(a.key, m.key) && typeEq(a.value, m.value);
    }
    case "struct":
      return a.name === (b as { name: string }).name;
  }
}

export function typeName(t: SolType): string {
  switch (t.kind) {
    case "uint":
      return `uint${t.bits}`;
    case "int":
      return `int${t.bits}`;
    case "bool":
      return "bool";
    case "array":
      return `${typeName(t.elem)}[]`;
    case "mapping":
      return `mapping(${typeName(t.key)} => ${typeName(t.value)})`;
    case "struct":
      return t.name;
  }
}

/**
 * Inclusive value range of an integral type, as decimal strings.
 * The generated Lean carries these as numerals so `omega` sees linear
 * arithmetic rather than `2 ^ 256`.
 */
export function rangeOf(t: SolType): { lo: string; hi: string } {
  if (t.kind === "uint") {
    return { lo: "0", hi: ((1n << BigInt(t.bits)) - 1n).toString() };
  }
  if (t.kind === "int") {
    const half = 1n << BigInt(t.bits - 1);
    return { lo: (-half).toString(), hi: (half - 1n).toString() };
  }
  throw new Error(`rangeOf: ${typeName(t)} is not an integral type`);
}

/* ------------------------------------------------------------------ */
/* Expressions                                                         */
/* ------------------------------------------------------------------ */

export type BinOpName =
  | "+" | "-" | "*" | "/" | "%" | "**"
  | "<" | ">" | "<=" | ">=" | "==" | "!="
  | "&&" | "||"
  /* Specification-only connectives. */
  | "==>" | "<==>";

export type Expr =
  | { k: "num"; value: bigint; loc: Loc }
  | { k: "bool"; value: boolean; loc: Loc }
  | { k: "id"; name: string; loc: Loc }
  | { k: "member"; base: Expr; name: string; loc: Loc }
  | { k: "index"; base: Expr; index: Expr; loc: Loc }
  | { k: "bin"; op: BinOpName; lhs: Expr; rhs: Expr; loc: Loc }
  | { k: "not"; arg: Expr; loc: Loc }
  | { k: "neg"; arg: Expr; loc: Loc }
  | { k: "incdec"; op: "++" | "--"; prefix: boolean; target: Expr; loc: Loc }
  | { k: "cond"; cond: Expr; thn: Expr; els: Expr; loc: Loc }
  | { k: "call"; callee: Expr; args: Expr[]; loc: Loc }
  /* Specification-only forms. */
  | { k: "old"; arg: Expr; loc: Loc }
  | {
      k: "quant";
      quantifier: "forall" | "exists";
      binder: string;
      lo: Expr;
      hi: Expr;
      body: Expr;
      loc: Loc;
    };

/* ------------------------------------------------------------------ */
/* Statements                                                          */
/* ------------------------------------------------------------------ */

export type Stmt =
  | { k: "vardecl"; type: SolType; name: string; init?: Expr; loc: Loc }
  | { k: "assign"; target: Expr; value: Expr; loc: Loc }
  | { k: "compound"; op: BinOpName; target: Expr; value: Expr; loc: Loc }
  | { k: "exprstmt"; expr: Expr; loc: Loc }
  | { k: "require"; cond: Expr; loc: Loc }
  | { k: "assert"; cond: Expr; loc: Loc }
  | { k: "revert"; loc: Loc }
  | { k: "if"; cond: Expr; thn: Stmt[]; els: Stmt[]; loc: Loc }
  | { k: "return"; value?: Expr; loc: Loc }
  | { k: "delete"; target: Expr; loc: Loc }
  | { k: "push"; target: Expr; value?: Expr; loc: Loc }
  | { k: "pop"; target: Expr; loc: Loc }
  | { k: "transfer"; recipient: Expr; amount: Expr; loc: Loc }
  /* Ghost steps, written as `/// @custom:assert` / `@custom:assume`
     lines inside a function body. */
  | { k: "ghost"; ghost: "assert" | "assume"; expr: Expr; loc: Loc };

/* ------------------------------------------------------------------ */
/* Specification clauses                                               */
/* ------------------------------------------------------------------ */

export type ClauseTag =
  | "requires"
  | "ensures"
  | "invariant"
  | "modifies"
  | "reverts_when"
  | "partial"
  | "free"
  | "tactic"
  | "decreases";

export interface Clause {
  tag: ClauseTag;
  /** Parsed predicate; absent for `modifies`/`partial`/`free`/`tactic`. */
  expr?: Expr;
  /** `modifies` targets, as written. */
  targets?: Expr[];
  /** Raw text after the tag (used by `tactic`, and in error messages). */
  raw: string;
  /** Location of the whole `@custom:` line, for diagnostics. */
  loc: Loc;
  /** Set when the clause text could not be parsed. */
  error?: string;
}

/* ------------------------------------------------------------------ */
/* Declarations                                                        */
/* ------------------------------------------------------------------ */

export interface Param {
  name: string;
  type: SolType;
  loc: Loc;
}

export interface StructDef {
  name: string;
  fields: Param[];
  loc: Loc;
}

export interface StateVar {
  name: string;
  type: SolType;
  init?: Expr;
  loc: Loc;
}

export interface FunctionDef {
  name: string;
  /** `constructor` has no name in source; we record it as one. */
  isConstructor: boolean;
  params: Param[];
  returns: Param[];
  visibility: string;
  mutability: string;
  body: Stmt[];
  clauses: Clause[];
  /** Set when the body could not be parsed: the construct is outside
      the verified fragment. The function is reported, not verified. */
  unsupported?: { reason: string; loc: Loc };
  /** Location of the `function` keyword through the parameter list. */
  loc: Loc;
}

export interface ContractDef {
  name: string;
  structs: StructDef[];
  stateVars: StateVar[];
  functions: FunctionDef[];
  /** `@custom:invariant` clauses on the contract's own doc comment. */
  clauses: Clause[];
  loc: Loc;
}

export interface SourceUnit {
  contracts: ContractDef[];
  /** Structs declared outside any contract: visible to all of them. */
  fileStructs: StructDef[];
}

/** A hard parse error: the file cannot be turned into obligations. */
export class ParseError extends Error {
  constructor(
    message: string,
    readonly loc: Loc,
  ) {
    super(message);
    this.name = "ParseError";
  }
}
