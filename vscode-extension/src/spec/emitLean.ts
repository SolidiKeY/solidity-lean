/**
 * The code generator: a parsed contract plus its NatSpec clauses become
 * a Lean file of `Spec.totalVC` / `Spec.partialVC` / `Spec.revertsVC`
 * obligations, one theorem per clause.
 *
 * The shape is fixed by `Solidity/Spec/Examples.lean`,
 * which is the same thing written by hand. Three ideas carry the design:
 *
 * 1. **The initial state is symbolic.** Every primitive storage leaf and
 *    every parameter becomes a Lean variable, so an obligation quantifies
 *    over all states rather than running from one fixed store. That is
 *    what makes `requires`/`ensures` mean what they mean in Dafny.
 * 2. **`old(e)` is free.** The pre-state maps each name to its variable,
 *    so reading `e` "at entry" is reading the variables.
 * 3. **The AST is built with explicit types.** The generator never goes
 *    through `sol!{…}`, whose name→type tables are fixed to the worked-example
 *    contracts; it emits `WrappedExpr.var Kind.storage <ty> …` with the
 *    types the Solidity declarations gave. Any contract works.
 */

import {
  Clause,
  ContractDef,
  Expr,
  FunctionDef,
  Loc,
  Param,
  SolType,
  StateVar,
  Stmt,
  StructDef,
  isIntegral,
  isPrimitive,
  rangeOf,
  typeName,
} from "./ast";
import { Unsupported } from "./parser";

/* ------------------------------------------------------------------ */
/* Results                                                             */
/* ------------------------------------------------------------------ */

export type ObligationKind =
  | "ensures"
  | "invariant"
  | "range"
  | "frame"
  | "assert"
  | "reverts";

export interface Obligation {
  /** Lean theorem name; also the key the verdict is reported under. */
  name: string;
  /** Human-readable label, e.g. `Bank.transfer ensures #2`. */
  label: string;
  contract: string;
  fn: string;
  kind: ObligationKind;
  /** Source range the verdict attaches to (the `@custom:` line). */
  loc: Loc;
  /** 1-based inclusive line span of the theorem in the generated file. */
  genStartLine: number;
  genEndLine: number;
}

export interface Skipped {
  contract: string;
  fn: string;
  reason: string;
  loc: Loc;
  /** `unsupported`: outside the fragment. `free`: assumed on request.
      `unspecified`: nothing to prove. */
  why: "unsupported" | "free" | "unspecified" | "clause-error";
}

export interface Generated {
  text: string;
  obligations: Obligation[];
  skipped: Skipped[];
}

/* ------------------------------------------------------------------ */
/* Lean printing helpers                                               */
/* ------------------------------------------------------------------ */

const str = (s: string): string => JSON.stringify(s);

const list = (items: string[]): string => `[${items.join(", ")}]`;

function sanitize(name: string): string {
  const cleaned = name.replace(/[^A-Za-z0-9_]/g, "_");
  return /^[A-Za-z_]/.test(cleaned) ? cleaned : `x_${cleaned}`;
}

/** `Ty` for a Solidity type. Widths collapse; the bounds live in the
    range obligations, because the interpreter computes over `Int`. */
function leanTy(t: SolType): string {
  switch (t.kind) {
    case "uint":
      return "Ty.uint";
    case "int":
      return "Ty.int";
    case "bool":
      return "Ty.bool";
    case "array":
      return `(Ty.ref ${leanRefTy(t)})`;
    case "mapping":
      return `(Ty.ref ${leanRefTy(t)})`;
    case "struct":
      return `(Ty.ref ${leanRefTy(t)})`;
  }
}

function leanRefTy(t: SolType): string {
  switch (t.kind) {
    case "array":
      return `(RefTy.array ${leanTy(t.elem)})`;
    case "mapping":
      return `(RefTy.mapping ${leanTy(t.key)} ${leanTy(t.value)})`;
    case "struct":
      return `(RefTy.struct ${str(t.name)})`;
    default:
      throw new Error(`leanRefTy: ${typeName(t)} is not a reference type`);
  }
}

function leanField(name: string, t: SolType, origin?: "global" | "local"): string {
  const org = origin ? ` (some StorageOrigin.${origin})` : "";
  return isPrimitive(t)
    ? `(Field.primitive ${str(name)} ${leanTy(t)}${org})`
    : `(Field.identity ${str(name)} ${leanRefTy(t)}${org})`;
}

/** The default storage value of a type — mapping defaults, mostly. */
function leanDefault(t: SolType): string {
  switch (t.kind) {
    case "uint":
    case "int":
      return "(SVal.int 0)";
    case "bool":
      return "(SVal.bool false)";
    case "array":
      return "(SVal.array [])";
    case "mapping":
      return `(SVal.map [] ${leanDefault(t.value)})`;
    case "struct":
      return `(Semantics.defaultForRef ${leanRefTy(t)})`;
  }
}

/* ------------------------------------------------------------------ */
/* The symbolic model of a contract's state                            */
/* ------------------------------------------------------------------ */

/** How one Lean variable stands for one piece of the initial state. */
interface ModelVar {
  /** Lean binder name. */
  lean: string;
  /** Lean type of the binder. */
  leanType: "Int" | "Bool" | "List Semantics.SVal" | "List (Int × Semantics.SVal)";
  /** Solidity type it models, for the range hypothesis. */
  solType: SolType;
  /** Storage root it belongs to, and the field path below it. */
  root: string;
  path: string[];
  /** Set for parameters and named returns rather than storage. */
  local?: boolean;
}

interface Scope {
  kind: "storage" | "stack";
  type: SolType;
}

class Model {
  readonly vars: ModelVar[] = [];
  readonly scope = new Map<string, Scope>();
  private readonly used = new Set<string>();
  /** Storage root name -> the `SVal` literal of its entry value. */
  readonly storage: Array<[string, string]> = [];
  /** Env entry name -> the `Binding` literal of its entry value. */
  readonly env: Array<[string, string]> = [];
  /** Path key (`root.f.g`) -> Lean variable, for `old()` shortcuts. */
  private readonly byPath = new Map<string, ModelVar>();

  constructor(readonly structs: Map<string, StructDef>) {}

  private fresh(base: string): string {
    let name = sanitize(base);
    if (LEAN_RESERVED.has(name)) {
      name = `${name}_`;
    }
    let candidate = name;
    let n = 2;
    while (this.used.has(candidate)) {
      candidate = `${name}${n++}`;
    }
    this.used.add(candidate);
    return candidate;
  }

  /** Build the symbolic value of one storage root and record its vars. */
  addGlobal(v: StateVar): void {
    this.scope.set(v.name, { kind: "storage", type: v.type });
    this.storage.push([v.name, this.symbolic(v.type, v.name, v.name, [])]);
  }

  addLocal(p: Param, binding: "symbolic" | "zero"): void {
    if (this.scope.has(p.name)) {
      throw new Unsupported(
        `\`${p.name}\` shadows a state variable; rename it (the interpreter has one flat environment)`,
        p.loc,
      );
    }
    this.scope.set(p.name, { kind: "stack", type: p.type });
    if (!isPrimitive(p.type)) {
      throw new Unsupported(
        `parameter \`${p.name}\` of type ${typeName(p.type)} is outside the verified fragment (only primitive parameters are modelled)`,
        p.loc,
      );
    }
    if (binding === "zero") {
      this.env.push([
        p.name,
        p.type.kind === "bool"
          ? "(Binding.val (Value.bool false))"
          : "(Binding.val (Value.int 0))",
      ]);
      return;
    }
    const lean = this.fresh(p.name);
    const isBool = p.type.kind === "bool";
    const mv: ModelVar = {
      lean,
      leanType: isBool ? "Bool" : "Int",
      solType: p.type,
      root: p.name,
      path: [],
      local: true,
    };
    this.vars.push(mv);
    this.byPath.set(pathKey(p.name, []), mv);
    this.env.push([
      p.name,
      isBool ? `(Binding.val (Value.bool ${lean}))` : `(Binding.val (Value.int ${lean}))`,
    ]);
  }

  /** The `SVal` literal for a declaration, allocating variables. */
  private symbolic(t: SolType, base: string, root: string, path: string[]): string {
    switch (t.kind) {
      case "uint":
      case "int":
      case "bool": {
        const lean = this.fresh(base);
        const mv: ModelVar = {
          lean,
          leanType: t.kind === "bool" ? "Bool" : "Int",
          solType: t,
          root,
          path,
        };
        this.vars.push(mv);
        this.byPath.set(pathKey(root, path), mv);
        return t.kind === "bool" ? `(SVal.bool ${lean})` : `(SVal.int ${lean})`;
      }
      case "array": {
        const lean = this.fresh(base);
        const mv: ModelVar = { lean, leanType: "List Semantics.SVal", solType: t, root, path };
        this.vars.push(mv);
        this.byPath.set(pathKey(root, path), mv);
        return `(SVal.array ${lean})`;
      }
      case "mapping": {
        const lean = this.fresh(base);
        const mv: ModelVar = {
          lean,
          leanType: "List (Int × Semantics.SVal)",
          solType: t,
          root,
          path,
        };
        this.vars.push(mv);
        this.byPath.set(pathKey(root, path), mv);
        return `(SVal.map ${lean} ${leanDefault(t.value)})`;
      }
      case "struct": {
        const def = this.structs.get(t.name);
        if (!def) {
          throw new Error(`unknown struct ${t.name}`);
        }
        const fields = def.fields.map(
          (f) =>
            `(${str(f.name)}, ${this.symbolic(f.type, `${base}_${f.name}`, root, [...path, f.name])})`,
        );
        return `(SVal.struct ${list(fields)})`;
      }
    }
  }

  /** The variable standing for a primitive leaf, if there is one. */
  varAt(root: string, path: string[]): ModelVar | undefined {
    return this.byPath.get(pathKey(root, path));
  }
}

function pathKey(root: string, path: string[]): string {
  return [root, ...path].join(".");
}

const LEAN_RESERVED = new Set([
  "fun", "let", "have", "show", "from", "match", "with", "do", "if", "then",
  "else", "by", "at", "in", "end", "open", "set", "def", "theorem", "example",
  "instance", "class", "structure", "inductive", "where", "deriving", "this",
  "Type", "Prop", "Sort", "s", "true", "false", "and", "or", "not", "forall",
  "exists", "using", "calc", "sorry", "variable", "universe", "namespace",
]);

/* ------------------------------------------------------------------ */
/* Program expressions -> WrappedExpr                                  */
/* ------------------------------------------------------------------ */

const BINOP_LEAN: Record<string, string> = {
  "+": "BinOp.add",
  "-": "BinOp.sub",
  "*": "BinOp.mul",
  "/": "BinOp.div",
  "%": "BinOp.mod",
  "**": "BinOp.pow",
  "<": "BinOp.lt",
  ">": "BinOp.gt",
  "<=": "BinOp.le",
  ">=": "BinOp.ge",
  "==": "BinOp.eqB",
  "!=": "BinOp.neB",
  "&&": "BinOp.and",
  "||": "BinOp.or",
};

class ProgEmitter {
  constructor(
    readonly model: Model,
    readonly structs: Map<string, StructDef>,
  ) {}

  typeOf(e: Expr): SolType {
    switch (e.k) {
      case "num":
        return { kind: "uint", bits: 256 };
      case "bool":
        return { kind: "bool" };
      case "id": {
        const s = this.model.scope.get(e.name);
        if (!s) {
          throw new Unsupported(`unknown name \`${e.name}\``, e.loc);
        }
        return s.type;
      }
      case "member": {
        const base = this.typeOf(e.base);
        if (base.kind === "array" && e.name === "length") {
          return { kind: "uint", bits: 256 };
        }
        if (base.kind !== "struct") {
          throw new Unsupported(`\`.${e.name}\` on ${typeName(base)}`, e.loc);
        }
        const def = this.structs.get(base.name);
        const f = def?.fields.find((x) => x.name === e.name);
        if (!f) {
          throw new Unsupported(`struct ${base.name} has no member \`${e.name}\``, e.loc);
        }
        return f.type;
      }
      case "index": {
        const base = this.typeOf(e.base);
        if (base.kind === "array") {
          return base.elem;
        }
        if (base.kind === "mapping") {
          return base.value;
        }
        throw new Unsupported(`indexing ${typeName(base)}`, e.loc);
      }
      case "bin":
        if (["<", ">", "<=", ">=", "==", "!=", "&&", "||", "==>", "<==>"].includes(e.op)) {
          return { kind: "bool" };
        }
        return this.typeOf(e.lhs);
      case "not":
        return { kind: "bool" };
      case "neg":
        return this.typeOf(e.arg);
      case "incdec":
        return this.typeOf(e.target);
      case "cond":
        return this.typeOf(e.thn);
      default:
        throw new Unsupported("expression form not available in a program", e.loc);
    }
  }

  kindOf(e: Expr): "storage" | "stack" {
    switch (e.k) {
      case "id": {
        const s = this.model.scope.get(e.name);
        if (!s) {
          throw new Unsupported(`unknown name \`${e.name}\``, e.loc);
        }
        return s.kind;
      }
      case "member":
        return this.kindOf(e.base);
      case "index":
        return this.kindOf(e.base);
      default:
        return "stack";
    }
  }

  expr(e: Expr): string {
    switch (e.k) {
      case "num":
        return `(WrappedExpr.intLit Ty.uint ${e.value.toString()})`;
      case "bool":
        return `(WrappedExpr.bool ${e.value})`;
      case "id": {
        const s = this.model.scope.get(e.name);
        if (!s) {
          throw new Unsupported(`unknown name \`${e.name}\``, e.loc);
        }
        const origin = s.kind === "storage" ? "global" : undefined;
        return `(WrappedExpr.var Kind.${s.kind} ${leanTy(s.type)} ${leanField(e.name, s.type, origin)})`;
      }
      case "member": {
        const baseTy = this.typeOf(e.base);
        const kind = this.kindOf(e.base);
        if (baseTy.kind === "array" && e.name === "length") {
          return `(WrappedExpr.field Kind.${kind} Ty.uint ${this.expr(e.base)} ${leanField("length", { kind: "uint", bits: 256 })})`;
        }
        const ty = this.typeOf(e);
        return `(WrappedExpr.field Kind.${kind} ${leanTy(ty)} ${this.expr(e.base)} ${leanField(e.name, ty)})`;
      }
      case "index": {
        const kind = this.kindOf(e.base);
        const ty = this.typeOf(e);
        return `(WrappedExpr.index Kind.${kind} ${leanTy(ty)} ${this.expr(e.base)} ${this.expr(e.index)})`;
      }
      case "bin": {
        const op = BINOP_LEAN[e.op];
        if (!op) {
          throw new Unsupported(`operator \`${e.op}\` is specification-only`, e.loc);
        }
        return `(WrappedExpr.binop ${op} ${this.expr(e.lhs)} ${this.expr(e.rhs)})`;
      }
      case "not":
        return `(WrappedExpr.unop UnOp.not ${this.expr(e.arg)})`;
      case "neg":
        return `(WrappedExpr.unop UnOp.neg ${this.expr(e.arg)})`;
      case "incdec": {
        const which =
          e.op === "++"
            ? e.prefix
              ? "IncDec.preInc"
              : "IncDec.postInc"
            : e.prefix
              ? "IncDec.preDec"
              : "IncDec.postDec";
        return `(WrappedExpr.incDec ${which} ${this.expr(e.target)})`;
      }
      case "cond":
        return `(WrappedExpr.ternary ${this.expr(e.cond)} ${this.expr(e.thn)} ${this.expr(e.els)})`;
      case "call":
        throw new Unsupported(
          "function calls are outside the verified fragment (inline the callee)",
          e.loc,
        );
      default:
        throw new Unsupported("this expression cannot appear in a program", e.loc);
    }
  }

  place(e: Expr): string {
    switch (e.k) {
      case "id": {
        const s = this.model.scope.get(e.name);
        if (!s) {
          throw new Unsupported(`unknown name \`${e.name}\``, e.loc);
        }
        const origin = s.kind === "storage" ? "global" : undefined;
        return `(PlaceExpr.var Kind.${s.kind} ${leanTy(s.type)} ${leanField(e.name, s.type, origin)})`;
      }
      case "member": {
        const kind = this.kindOf(e.base);
        const ty = this.typeOf(e);
        return `(PlaceExpr.field Kind.${kind} ${leanTy(ty)} ${this.expr(e.base)} ${leanField(e.name, ty)})`;
      }
      case "index": {
        const kind = this.kindOf(e.base);
        const ty = this.typeOf(e);
        return `(PlaceExpr.index Kind.${kind} ${leanTy(ty)} ${this.expr(e.base)} ${this.expr(e.index)})`;
      }
      default:
        throw new Unsupported("this expression is not assignable", e.loc);
    }
  }
}

/* ------------------------------------------------------------------ */
/* Specification expressions -> Lean propositions                      */
/* ------------------------------------------------------------------ */

type Sort = "int" | "bool" | "prop";

interface Val {
  code: string;
  sort: Sort;
}

interface PathRef {
  root: string;
  /** Lean `Seg` terms below the root. */
  segs: string[];
  /** Field-only path, or `null` once an index appears. */
  fieldPath: string[] | null;
  type: SolType;
  local: boolean;
}

/**
 * Emits a specification expression as a Lean term over a state.
 *
 * `state` is the Lean term to read from, or `null` for the *pre-state*,
 * where every primitive leaf is a bound variable — which is what makes
 * `old(e)` free and keeps preconditions in the vocabulary `omega`
 * understands.
 */
class SpecEmitter {
  /** Well-formedness side conditions collected while emitting. */
  readonly wf: string[] = [];

  constructor(
    readonly model: Model,
    readonly structs: Map<string, StructDef>,
    readonly state: string | null,
    readonly binders: ReadonlySet<string> = new Set(),
    /** Lean term for the entry state, used when a pre-state read cannot
        be shortcut to a variable (an array or mapping element). */
    readonly preTerm: string = "PRE",
  ) {}

  private sub(state: string | null, binders: ReadonlySet<string>): SpecEmitter {
    return new SpecEmitter(this.model, this.structs, state, binders, this.preTerm);
  }

  /** Emit as a proposition, coercing a `Bool` with `= true`. */
  prop(e: Expr): string {
    const v = this.value(e);
    if (v.sort === "prop") {
      return v.code;
    }
    if (v.sort === "bool") {
      return `(${v.code} = true)`;
    }
    throw new Unsupported("expected a boolean expression", e.loc);
  }

  /** Emit as an `Int`. */
  int(e: Expr): string {
    const v = this.value(e);
    if (v.sort !== "int") {
      throw new Unsupported("expected an integer expression", e.loc);
    }
    return v.code;
  }

  value(e: Expr): Val {
    switch (e.k) {
      case "num":
        return { code: `(${e.value.toString()} : Int)`, sort: "int" };
      case "bool":
        return { code: e.value ? "True" : "False", sort: "prop" };
      case "old": {
        const inner = this.sub(null, this.binders);
        const v = inner.value(e.arg);
        this.wf.push(...inner.wf);
        return v;
      }
      case "quant": {
        const child = this.sub(this.state, new Set([...this.binders, e.binder]));
        const body = child.prop(e.body);
        this.wf.push(...child.wf);
        const fn = e.quantifier === "forall" ? "Spec.forallIn" : "Spec.existsIn";
        return {
          code: `(${fn} ${this.int(e.lo)} ${this.int(e.hi)} (fun ${sanitize(e.binder)} => ${body}))`,
          sort: "prop",
        };
      }
      case "not":
        return { code: `(¬ ${this.prop(e.arg)})`, sort: "prop" };
      case "neg":
        return { code: `(-${this.int(e.arg)})`, sort: "int" };
      case "cond": {
        const t = this.value(e.thn);
        const f = this.value(e.els);
        const cond = this.prop(e.cond);
        if (t.sort === "int" && f.sort === "int") {
          return { code: `(if ${cond} then ${t.code} else ${f.code})`, sort: "int" };
        }
        return {
          code: `((${cond} → ${this.prop(e.thn)}) ∧ (¬ ${cond} → ${this.prop(e.els)}))`,
          sort: "prop",
        };
      }
      case "bin":
        return this.binary(e);
      case "id":
      case "member":
      case "index":
        return this.readPath(e);
      case "call":
        throw new Unsupported(
          `\`${e.callee.k === "id" ? e.callee.name : "call"}(...)\` is not available in a specification`,
          e.loc,
        );
      default:
        throw new Unsupported("this expression is not available in a specification", e.loc);
    }
  }

  private binary(e: Expr & { k: "bin" }): Val {
    switch (e.op) {
      case "+":
      case "-":
      case "*":
        return {
          code: `(${this.int(e.lhs)} ${e.op} ${this.int(e.rhs)})`,
          sort: "int",
        };
      case "/":
        return { code: `(Int.tdiv ${this.int(e.lhs)} ${this.int(e.rhs)})`, sort: "int" };
      case "%":
        return { code: `(Int.tmod ${this.int(e.lhs)} ${this.int(e.rhs)})`, sort: "int" };
      case "**": {
        if (e.rhs.k !== "num") {
          throw new Unsupported(
            "`**` in a specification needs a literal exponent",
            e.loc,
          );
        }
        return { code: `(${this.int(e.lhs)} ^ ${e.rhs.value.toString()})`, sort: "int" };
      }
      case "<":
        return { code: `(${this.int(e.lhs)} < ${this.int(e.rhs)})`, sort: "prop" };
      case ">":
        return { code: `(${this.int(e.rhs)} < ${this.int(e.lhs)})`, sort: "prop" };
      case "<=":
        return { code: `(${this.int(e.lhs)} ≤ ${this.int(e.rhs)})`, sort: "prop" };
      case ">=":
        return { code: `(${this.int(e.rhs)} ≤ ${this.int(e.lhs)})`, sort: "prop" };
      case "==":
      case "!=": {
        const l = this.value(e.lhs);
        const r = this.value(e.rhs);
        if (l.sort === "prop" || r.sort === "prop") {
          const eq = `(${this.prop(e.lhs)} ↔ ${this.prop(e.rhs)})`;
          return { code: e.op === "==" ? eq : `(¬ ${eq})`, sort: "prop" };
        }
        const eq = `(${l.code} = ${r.code})`;
        return { code: e.op === "==" ? eq : `(${l.code} ≠ ${r.code})`, sort: "prop" };
      }
      case "&&":
        return { code: `(${this.prop(e.lhs)} ∧ ${this.prop(e.rhs)})`, sort: "prop" };
      case "||":
        return { code: `(${this.prop(e.lhs)} ∨ ${this.prop(e.rhs)})`, sort: "prop" };
      case "==>":
        return { code: `(${this.prop(e.lhs)} → ${this.prop(e.rhs)})`, sort: "prop" };
      case "<==>":
        return { code: `(${this.prop(e.lhs)} ↔ ${this.prop(e.rhs)})`, sort: "prop" };
    }
  }

  /** Resolve a location expression to a storage root plus a path. */
  private path(e: Expr): PathRef {
    switch (e.k) {
      case "id": {
        const s = this.model.scope.get(e.name);
        if (!s) {
          throw new Unsupported(`unknown name \`${e.name}\` in a specification`, e.loc);
        }
        return {
          root: e.name,
          segs: [],
          fieldPath: [],
          type: s.type,
          local: s.kind === "stack",
        };
      }
      case "member": {
        const base = this.path(e.base);
        if (base.type.kind === "array" && e.name === "length") {
          throw new Error("internal: .length is read by `readPath`");
        }
        if (base.type.kind !== "struct") {
          throw new Unsupported(`\`.${e.name}\` on ${typeName(base.type)}`, e.loc);
        }
        const def = this.structs.get(base.type.name);
        const f = def?.fields.find((x) => x.name === e.name);
        if (!f) {
          throw new Unsupported(`struct ${base.type.name} has no member \`${e.name}\``, e.loc);
        }
        return {
          root: base.root,
          segs: [...base.segs, `(Seg.field ${str(e.name)})`],
          fieldPath: base.fieldPath ? [...base.fieldPath, e.name] : null,
          type: f.type,
          local: base.local,
        };
      }
      case "index": {
        const base = this.path(e.base);
        const idx = this.int(e.index);
        if (base.type.kind === "array") {
          /* Dafny's discipline: reading `a[i]` in a proved clause carries
             the obligation that `i` is in range. */
          this.wf.push(`(0 ≤ ${idx} ∧ ${idx} < ${this.lenCode(base, e.loc)})`);
          return {
            root: base.root,
            segs: [...base.segs, `(Seg.at ${idx})`],
            fieldPath: null,
            type: base.type.elem,
            local: base.local,
          };
        }
        if (base.type.kind === "mapping") {
          return {
            root: base.root,
            segs: [...base.segs, `(Seg.at ${idx})`],
            fieldPath: null,
            type: base.type.value,
            local: base.local,
          };
        }
        throw new Unsupported(`indexing ${typeName(base.type)}`, e.loc);
      }
      default:
        throw new Unsupported("this expression does not name a location", e.loc);
    }
  }

  private stateTerm(): string {
    return this.state ?? this.preTerm;
  }

  private lenCode(p: PathRef, loc: Loc): string {
    if (p.local) {
      throw new Unsupported(`\`.length\` of the local \`${p.root}\` is not modelled`, loc);
    }
    /* In the pre-state the array *is* a Lean list variable, so its
       length is `xs.length` rather than a state read — which is what
       `omega` needs to relate it to the post-state length. */
    if (this.state === null && p.fieldPath !== null) {
      const mv = this.model.varAt(p.root, p.fieldPath);
      if (mv && mv.leanType === "List Semantics.SVal") {
        return `((${mv.lean}).length : Int)`;
      }
    }
    return `(Spec.lenAt ${this.stateTerm()} ${str(p.root)} ${list(p.segs)})`;
  }

  private readPath(e: Expr): Val {
    /* `a.length` is a read of the array, not a member of a struct. */
    if (e.k === "member") {
      const baseType = this.tryTypeOf(e.base);
      if (baseType && baseType.kind === "array" && e.name === "length") {
        const p = this.path(e.base);
        if (this.state === null && p.local) {
          throw new Unsupported("`.length` of a local is not modelled", e.loc);
        }
        return { code: this.lenCode(p, e.loc), sort: "int" };
      }
    }

    if (e.k === "id" && this.binders.has(e.name)) {
      return { code: sanitize(e.name), sort: "int" };
    }

    const p = this.path(e);
    if (!isPrimitive(p.type)) {
      throw new Unsupported(
        `a specification cannot compare whole ${typeName(p.type)} values; read a primitive member`,
        e.loc,
      );
    }
    const isBool = p.type.kind === "bool";

    /* In the pre-state a primitive leaf is a bound variable — the whole
       point of the symbolic model, and what makes `old(e)` free. */
    if (this.state === null && p.fieldPath !== null) {
      const mv = this.model.varAt(p.root, p.fieldPath);
      if (mv && (mv.leanType === "Int" || mv.leanType === "Bool")) {
        return { code: mv.lean, sort: isBool ? "bool" : "int" };
      }
      if (p.local) {
        /* A named return value: bound to the type's zero on entry. */
        return isBool ? { code: "false", sort: "bool" } : { code: "(0 : Int)", sort: "int" };
      }
    }

    const S = this.stateTerm();
    if (p.local) {
      return isBool
        ? { code: `(Spec.localBool ${S} ${str(p.root)})`, sort: "bool" }
        : { code: `(Spec.localInt ${S} ${str(p.root)})`, sort: "int" };
    }
    return isBool
      ? { code: `(Spec.boolAt ${S} ${str(p.root)} ${list(p.segs)})`, sort: "bool" }
      : { code: `(Spec.intAt ${S} ${str(p.root)} ${list(p.segs)})`, sort: "int" };
  }

  /** Type of a location expression, with no side effect on `wf`:
      `readPath` asks before it commits, and the real `path` call that
      follows is the one that records the range obligations. */
  private tryTypeOf(e: Expr): SolType | undefined {
    const mark = this.wf.length;
    try {
      return this.path(e).type;
    } catch {
      return undefined;
    } finally {
      this.wf.length = mark;
    }
  }
}

/* ------------------------------------------------------------------ */
/* Statements -> annotated blocks                                      */
/* ------------------------------------------------------------------ */

interface GhostAssert {
  /** Index into the annotated block: the assert sits at this position. */
  index: number;
  /** `fun s => …` predicate. */
  pred: string;
  loc: Loc;
}

class BodyEmitter {
  readonly anns: string[] = [];
  readonly asserts: GhostAssert[] = [];

  constructor(
    readonly prog: ProgEmitter,
    readonly model: Model,
    readonly structs: Map<string, StructDef>,
    readonly returnVar: Param | undefined,
  ) {}

  private ghostPred(e: Expr): string {
    const em = new SpecEmitter(this.model, this.structs, "s");
    const body = em.prop(e);
    const conds = [...em.wf, body];
    return `(fun s => ${conds.join(" ∧ ")})`;
  }

  emitBody(stmts: Stmt[]): void {
    for (let i = 0; i < stmts.length; i++) {
      const st = stmts[i];
      if (st.k === "ghost") {
        const pred = this.ghostPred(st.expr);
        if (st.ghost === "assert") {
          this.asserts.push({ index: this.anns.length, pred, loc: st.loc });
        }
        /* In the block every other obligation runs against, a proved
           `assert` is available as an assumption — Dafny's reading, and
           sound because the assert has its own obligation. */
        this.anns.push(`Spec.Ann.assume ${pred}`);
        continue;
      }
      if (st.k === "return") {
        if (i !== stmts.length - 1) {
          throw new Unsupported(
            "`return` is only supported as the last statement of a function (the semantics has no early exit)",
            st.loc,
          );
        }
        if (!st.value) {
          continue;
        }
        if (!this.returnVar) {
          throw new Unsupported("`return <value>` in a function with no return type", st.loc);
        }
        this.anns.push(
          `Spec.Ann.stmt (Stmt.assign (PlaceExpr.var Kind.stack ${leanTy(this.returnVar.type)} ${leanField(this.returnVar.name, this.returnVar.type)}) ${this.prog.expr(st.value)})`,
        );
        continue;
      }
      this.anns.push(`Spec.Ann.stmt ${this.stmt(st)}`);
    }
  }

  /** A plain (non-ghost) statement as a `Stmt` term. */
  private stmt(st: Stmt): string {
    switch (st.k) {
      case "vardecl": {
        if (!isPrimitive(st.type)) {
          throw new Unsupported(
            `local \`${st.name}\` of type ${typeName(st.type)} is outside the verified fragment (memory and storage aliases are not modelled by the front-end)`,
            st.loc,
          );
        }
        this.model.scope.set(st.name, { kind: "stack", type: st.type });
        const init = st.init ? `(some ${this.prog.expr(st.init)})` : "none";
        return `(Stmt.stackDecl ${leanTy(st.type)} ${str(st.name)} ${init})`;
      }
      case "assign":
        return `(Stmt.assign ${this.prog.place(st.target)} ${this.prog.expr(st.value)})`;
      case "compound": {
        const op = BINOP_LEAN[st.op];
        return `(Stmt.compoundAssign ${op} ${this.prog.place(st.target)} ${this.prog.expr(st.value)})`;
      }
      case "exprstmt":
        return `(Stmt.expr ${this.prog.expr(st.expr)})`;
      case "require":
        return `(Stmt.requireStmt ${this.prog.expr(st.cond)})`;
      case "assert":
        return `(Stmt.assertStmt ${this.prog.expr(st.cond)})`;
      case "revert":
        return `(Stmt.revert none)`;
      case "delete":
        return `(Stmt.delete ${this.prog.place(st.target)})`;
      case "push":
        return `(Stmt.push ${this.prog.place(st.target)} ${st.value ? `(some ${this.prog.expr(st.value)})` : "none"})`;
      case "pop":
        return `(Stmt.pop ${this.prog.place(st.target)})`;
      case "transfer":
        return `(Stmt.transfer ${this.prog.expr(st.recipient)} ${this.prog.expr(st.amount)})`;
      case "if": {
        const thn = st.thn.map((s) => this.nestedStmt(s));
        const els = st.els.map((s) => this.nestedStmt(s));
        return `(Stmt.ite ${this.prog.expr(st.cond)} ${list(thn)} ${list(els)})`;
      }
      case "ghost":
      case "return":
        throw new Error("internal: handled by emitBody");
    }
  }

  /** Inside an `if` branch there is no room for ghost steps: the
      semantics' `Stmt.ite` carries plain `Stmt` lists. */
  private nestedStmt(st: Stmt): string {
    if (st.k === "ghost") {
      throw new Unsupported(
        "a ghost `@custom:assert`/`@custom:assume` inside an `if` branch is not supported (move it after the `if`)",
        st.loc,
      );
    }
    if (st.k === "return") {
      throw new Unsupported(
        "`return` inside an `if` branch is not supported (the semantics has no early exit)",
        st.loc,
      );
    }
    return this.stmt(st);
  }
}

/* ------------------------------------------------------------------ */
/* Obligation assembly                                                 */
/* ------------------------------------------------------------------ */

const HEADER = [
  "import Solidity.Spec.Tactic",
  "",
  "/-! Generated by the SolLoom SolSpec front-end. Do not edit: rerun the",
  "verifier on the `.sol` source instead. -/",
  "",
  "namespace SolSpecGen",
  "",
  "open Solidity",
  "open Solidity.Semantics",
  "open Solidity.Spec",
  "",
];

class Writer {
  readonly lines: string[] = [];

  push(...ls: string[]): void {
    this.lines.push(...ls);
  }

  /** 1-based line number the next pushed line will occupy. */
  get nextLine(): number {
    return this.lines.length + 1;
  }

  get lastLine(): number {
    return this.lines.length;
  }

  text(): string {
    return `${this.lines.join("\n")}\n`;
  }
}

interface FnPlan {
  fn: FunctionDef;
  model: Model;
  prog: ProgEmitter;
  body: BodyEmitter;
  stateName: string;
  bodyName: string;
  /** `(a b : Int) (m : List …)` binder groups. */
  binders: string;
  /** Argument list for the state definition. */
  args: string;
  /** Named hypotheses shared by every obligation of this function. */
  hyps: string[];
  partial: boolean;
  tactic: string;
  returnVar?: Param;
}

function groupBinders(vars: ModelVar[]): { binders: string; args: string } {
  const groups: Array<{ type: string; names: string[] }> = [];
  for (const v of vars) {
    const last = groups[groups.length - 1];
    if (last && last.type === v.leanType) {
      last.names.push(v.lean);
    } else {
      groups.push({ type: v.leanType, names: [v.lean] });
    }
  }
  return {
    binders: groups.map((g) => `(${g.names.join(" ")} : ${g.type})`).join(" "),
    args: vars.map((v) => v.lean).join(" "),
  };
}

/** Split a function's clauses by tag, flagging the ones that cannot be used. */
function classify(fn: FunctionDef): {
  requires: Clause[];
  ensures: Clause[];
  modifies: Clause[];
  reverts: Clause[];
  partial: boolean;
  free: boolean;
  tactic?: string;
  errors: Clause[];
} {
  const out = {
    requires: [] as Clause[],
    ensures: [] as Clause[],
    modifies: [] as Clause[],
    reverts: [] as Clause[],
    partial: false,
    free: false,
    tactic: undefined as string | undefined,
    errors: [] as Clause[],
  };
  for (const c of fn.clauses) {
    if (c.error) {
      out.errors.push(c);
      continue;
    }
    switch (c.tag) {
      case "requires":
        out.requires.push(c);
        break;
      case "ensures":
        out.ensures.push(c);
        break;
      case "modifies":
        out.modifies.push(c);
        break;
      case "reverts_when":
        out.reverts.push(c);
        break;
      case "partial":
        out.partial = true;
        break;
      case "free":
        out.free = true;
        break;
      case "tactic":
        out.tactic = c.raw;
        break;
      case "invariant":
        out.errors.push({
          ...c,
          error:
            "@custom:invariant belongs on the contract, not on a function (there are no loop invariants: the fragment has no loops)",
        });
        break;
      case "decreases":
        out.errors.push({
          ...c,
          error: "@custom:decreases has no effect: the verified fragment has no loops or recursion",
        });
        break;
    }
  }
  return out;
}

/** Does the function carry anything worth generating obligations for? */
function hasSpec(fn: FunctionDef): boolean {
  return fn.clauses.length > 0 || fn.body.some((s) => s.k === "ghost");
}

/**
 * Generate the Lean obligation file for a source unit.
 *
 * `fileStructs` are struct declarations made outside any contract; they
 * are visible to every contract in the file, as in Solidity.
 */
export function generateLean(
  contracts: ContractDef[],
  fileStructs: StructDef[] = [],
): Generated {
  const w = new Writer();
  w.push(...HEADER);
  const obligations: Obligation[] = [];
  const skipped: Skipped[] = [];

  for (const contract of contracts) {
    const structs = new Map<string, StructDef>();
    for (const s of [...fileStructs, ...contract.structs]) {
      structs.set(s.name, s);
    }

    const invariants = contract.clauses.filter((c) => c.tag === "invariant" && !c.error);
    for (const bad of contract.clauses.filter((c) => c.error)) {
      skipped.push({
        contract: contract.name,
        fn: "(contract)",
        reason: bad.error ?? "malformed clause",
        loc: bad.loc,
        why: "clause-error",
      });
    }

    for (const fn of contract.functions) {
      if (!hasSpec(fn)) {
        continue;
      }
      if (fn.unsupported) {
        skipped.push({
          contract: contract.name,
          fn: fn.name,
          reason: fn.unsupported.reason,
          loc: fn.unsupported.loc,
          why: "unsupported",
        });
        continue;
      }
      const info = classify(fn);
      if (info.errors.length > 0) {
        for (const bad of info.errors) {
          skipped.push({
            contract: contract.name,
            fn: fn.name,
            reason: bad.error ?? "malformed clause",
            loc: bad.loc,
            why: "clause-error",
          });
        }
        continue;
      }
      if (info.free) {
        skipped.push({
          contract: contract.name,
          fn: fn.name,
          reason: "@custom:free — the specification is assumed, not proved",
          loc: fn.loc,
          why: "free",
        });
        continue;
      }

      try {
        emitFunction(w, contract, fn, info, invariants, structs, obligations);
      } catch (err) {
        if (err instanceof Unsupported) {
          skipped.push({
            contract: contract.name,
            fn: fn.name,
            reason: err.message,
            loc: err.loc,
            why: "unsupported",
          });
          continue;
        }
        throw err;
      }
    }
  }

  w.push("end SolSpecGen");
  return { text: w.text(), obligations, skipped };
}

function emitFunction(
  w: Writer,
  contract: ContractDef,
  fn: FunctionDef,
  info: ReturnType<typeof classify>,
  invariants: Clause[],
  structs: Map<string, StructDef>,
  obligations: Obligation[],
): void {
  const prefix = `${sanitize(contract.name)}_${sanitize(fn.name)}`;
  const stateName = `${prefix}_state`;
  const bodyName = `${prefix}_body`;

  const model = new Model(structs);
  for (const v of contract.stateVars) {
    model.addGlobal(v);
  }
  for (const p of fn.params) {
    if (p.name === "") {
      throw new Unsupported("unnamed parameters are not supported", p.loc);
    }
    model.addLocal(p, "symbolic");
  }
  /* Return values are stack locals starting at the type's zero. An
     unnamed `returns (uint)` gets the Dafny-ish name `result`. */
  let returnVar: Param | undefined;
  if (fn.returns.length > 1) {
    throw new Unsupported("multiple return values are not supported", fn.loc);
  }
  if (fn.returns.length === 1) {
    returnVar = { ...fn.returns[0], name: fn.returns[0].name || "result" };
    model.addLocal(returnVar, "zero");
  }

  const prog = new ProgEmitter(model, structs);
  const body = new BodyEmitter(prog, model, structs, returnVar);
  body.emitBody(fn.body);

  const { binders, args } = groupBinders(model.vars);
  const stateArgs = args === "" ? "" : ` ${args}`;
  const stateTerm = args === "" ? stateName : `(${stateName} ${args})`;

  /* ---- state and body definitions ---- */
  w.push(
    `/-- Entry state of \`${contract.name}.${fn.name}\`: one Lean variable per`,
    `primitive storage leaf and per parameter. -/`,
    `def ${stateName}${binders === "" ? "" : ` ${binders}`} : State :=`,
    `  { storage := ${list(model.storage.map(([n, v]) => `(${str(n)}, ${v})`))},`,
    `    env := ${list(model.env.map(([n, v]) => `(${str(n)}, ${v})`))} }`,
    "",
    `/-- Annotated body of \`${contract.name}.${fn.name}\`. -/`,
    `def ${bodyName} : List Spec.Ann :=`,
    ...annBlock(body.anns),
    "",
  );

  const unfold = `[${stateName}, ${bodyName}]`;
  const modality = info.partial ? "Spec.partialVC" : "Spec.totalVC";

  /* ---- shared hypotheses ---- */
  const preEmitter = (): SpecEmitter =>
    new SpecEmitter(model, structs, null, new Set(), stateTerm);

  const hyps: string[] = [];
  for (const v of model.vars) {
    if (isIntegral(v.solType)) {
      const { lo, hi } = rangeOf(v.solType);
      hyps.push(`(hrange_${v.lean} : Spec.inRange ${lo} ${hi} ${v.lean})`);
    }
  }
  /* A constructor establishes the contract invariant rather than
     assuming it — the one place the asymmetry matters. */
  if (!fn.isConstructor) {
    invariants.forEach((c, i) => {
      const em = preEmitter();
      hyps.push(`(hinv_${i + 1} : ${em.prop(c.expr!)})`);
    });
  }
  info.requires.forEach((c, i) => {
    const em = preEmitter();
    hyps.push(`(hpre_${i + 1} : ${em.prop(c.expr!)})`);
  });

  const proof = info.tactic ?? `sol_spec ${unfold}`;

  const theorem = (
    name: string,
    label: string,
    kind: ObligationKind,
    loc: Loc,
    goal: string,
    extraHyps: string[] = [],
    docs: string[] = [],
  ): void => {
    const start = w.nextLine;
    w.push(...docs);
    w.push(`theorem ${name}`);
    const allBinders = [binders, ...hyps, ...extraHyps].filter((x) => x !== "");
    for (const b of allBinders) {
      w.push(`    ${b}`);
    }
    w.push(`    : ${goal} := by`);
    w.push(`  ${proof}`);
    w.push("");
    obligations.push({
      name,
      label,
      contract: contract.name,
      fn: fn.name,
      kind,
      loc,
      genStartLine: start,
      genEndLine: w.lastLine,
    });
  };

  const post = (clause: Clause): string => {
    const em = new SpecEmitter(model, structs, "s", new Set(), stateTerm);
    const body = em.prop(clause.expr!);
    return `(fun s => ${[...em.wf, body].join(" ∧ ")})`;
  };

  /* ---- ensures ---- */
  info.ensures.forEach((c, i) => {
    theorem(
      `${prefix}_ensures_${i + 1}`,
      `${contract.name}.${fn.name} ensures #${i + 1}`,
      "ensures",
      c.loc,
      `${modality} ${stateTerm} ${bodyName} ${post(c)}`,
      [],
      [`/-- \`@custom:ensures ${c.raw}\` -/`],
    );
  });

  /* ---- contract invariants, re-established on exit ---- */
  invariants.forEach((c, i) => {
    theorem(
      `${prefix}_invariant_${i + 1}`,
      `${contract.name}.${fn.name} preserves invariant #${i + 1}`,
      "invariant",
      c.loc,
      `${modality} ${stateTerm} ${bodyName} ${post(c)}`,
      [],
      [`/-- Contract invariant \`${c.raw}\`, re-established by ${fn.name}. -/`],
    );
  });

  /* ---- range: what `uintN`/`intN` means on the way out ---- */
  const rangeConjuncts = model.vars
    .filter((v) => !v.local && isIntegral(v.solType))
    .map((v) => {
      const { lo, hi } = rangeOf(v.solType);
      const segs = v.path.map((f) => `(Seg.field ${str(f)})`);
      return `Spec.inRange ${lo} ${hi} (Spec.intAt s ${str(v.root)} ${list(segs)})`;
    });
  if (returnVar && isIntegral(returnVar.type)) {
    const { lo, hi } = rangeOf(returnVar.type);
    rangeConjuncts.push(`Spec.inRange ${lo} ${hi} (Spec.localInt s ${str(returnVar.name)})`);
  }
  if (rangeConjuncts.length > 0) {
    theorem(
      `${prefix}_range`,
      `${contract.name}.${fn.name} stays in range`,
      "range",
      fn.loc,
      `${modality} ${stateTerm} ${bodyName} (fun s => ${rangeConjuncts.join(" ∧ ")})`,
      [],
      [
        "/-- Every bounded integer still fits its declared type on exit.",
        "The official interpreter computes over unbounded `Int`, so this is",
        "where an overflow or an underflow surfaces. -/",
      ],
    );
  }

  /* ---- frame ---- */
  if (info.modifies.length > 0) {
    const allowed = new Set<string>();
    for (const c of info.modifies) {
      for (const t of c.targets ?? []) {
        allowed.add(rootOf(t));
      }
    }
    const frame = model.storage
      .filter(([name]) => !allowed.has(name))
      .map(([name, value]) => `Spec.svalAt s ${str(name)} [] = some ${value}`);
    if (frame.length > 0) {
      theorem(
        `${prefix}_frame`,
        `${contract.name}.${fn.name} modifies only what it declares`,
        "frame",
        info.modifies[0].loc,
        `${modality} ${stateTerm} ${bodyName} (fun s => ${frame.join(" ∧ ")})`,
        [],
        [`/-- \`@custom:modifies\`: every other storage root is untouched. -/`],
      );
    }
  }

  /* ---- ghost asserts ---- */
  body.asserts.forEach((a, i) => {
    const prefixName = `${prefix}_assert_${i + 1}_body`;
    const prefixAnns = body.anns.slice(0, a.index).concat([`Spec.Ann.assert ${a.pred}`]);
    w.push(
      `/-- Body of \`${contract.name}.${fn.name}\` up to ghost assertion #${i + 1}. -/`,
      `def ${prefixName} : List Spec.Ann :=`,
      ...annBlock(prefixAnns),
      "",
    );
    const savedProof = info.tactic ?? `sol_spec [${stateName}, ${prefixName}]`;
    const start = w.nextLine;
    w.push(`theorem ${prefix}_assert_${i + 1}`);
    for (const b of [binders, ...hyps].filter((x) => x !== "")) {
      w.push(`    ${b}`);
    }
    w.push(`    : ${modality} ${stateTerm} ${prefixName} (fun _ => True) := by`);
    w.push(`  ${savedProof}`);
    w.push("");
    obligations.push({
      name: `${prefix}_assert_${i + 1}`,
      label: `${contract.name}.${fn.name} ghost assert #${i + 1}`,
      contract: contract.name,
      fn: fn.name,
      kind: "assert",
      loc: a.loc,
      genStartLine: start,
      genEndLine: w.lastLine,
    });
  });

  /* ---- reverts_when ---- */
  info.reverts.forEach((c, i) => {
    const em = preEmitter();
    theorem(
      `${prefix}_reverts_${i + 1}`,
      `${contract.name}.${fn.name} reverts when #${i + 1}`,
      "reverts",
      c.loc,
      `Spec.revertsVC ${stateTerm} ${bodyName}`,
      [`(hwhen_${i + 1} : ${em.prop(c.expr!)})`],
      [`/-- \`@custom:reverts_when ${c.raw}\` -/`],
    );
  });
}

/** An annotated block, one step per line: the generated file is read by
    people through "SolLoom: Show Generated Lean". */
function annBlock(anns: string[]): string[] {
  if (anns.length === 0) {
    return ["  []"];
  }
  return anns.map((a, i) => `  ${i === 0 ? "[" : ","} ${a}`).concat(["  ]"]);
}

/** The storage root a `@custom:modifies` target names. */
function rootOf(e: Expr): string {
  switch (e.k) {
    case "id":
      return e.name;
    case "member":
      return rootOf(e.base);
    case "index":
      return rootOf(e.base);
    default:
      return "";
  }
}
