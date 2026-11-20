import Solidity.Correctness.Lowering.Total.Contract
import Solidity.Source.Infer
import Solidity.Source.Agreement.Primitive

/-!
# Loop lowering: the concrete raw-to-source decoder (stage 1)

`decode` reads a request's raw input as Source: a chosen Source syntax tree
for the raw statements (`Spelling`), typed by the existing Source inference
(`Source.ItemsD.infer`) and resolved by `ItemsD.toR`, in the Source unit whose
one contract declares the model contract's primitive state variables. Nothing
is checked against the lowered output: the decoder sees only the request.

A `none` is a coverage gap, not an exclusion: admission is fixed separately
(`loopEntry`), so a successful request in a gap leaves the coverage obligation
of `loopResidual_iff` open. The main gaps are listed at each definition; the
lists are not exhaustive (a cast written as a call, `msg.sender` used as a
`uint`, a braced single declaration read unbraced, nested `unchecked`, a `for`
with several initializers or updates are further ones). Each
`some` is a chosen spelling; that it agrees with the model's reading of the
same raw construct is part of the `pipeline` obligation, not shown here. -/
namespace Solidity.Correctness.Lowering.Total

namespace Decode

open Source (Syn SCtx STy)

/-- The contract name of the canonical unit (the model contract has none). -/
def contractName : String := "C"

/-- A decimal literal with no fraction and no exponent. -/
def num (n : Nat) : Syn .expr := .lit (.num (.dec n 0 0))

def uintElem : Source.Elem := .int false 256 (by decide)
def intElem : Source.Elem := .int true 256 (by decide)

/-- Binary operators. The wrapping forms (`addW` …) have no Source operator:
Source wraps by an enclosing `unchecked` block. Model `>>` is spelled `sar`. -/
def binop : BinOp → Option (Syn .expr → Syn .expr → Syn .expr)
  | .add => some (.addSub .add) | .sub => some (.addSub .sub)
  | .mul => some (.mulDivMod .mul) | .div => some (.mulDivMod .div)
  | .mod => some (.mulDivMod .mod) | .pow => some .exp
  | .lt => some (.order .lt) | .gt => some (.order .gt)
  | .le => some (.order .le) | .ge => some (.order .ge)
  | .eqB => some (.equality .eq) | .neB => some (.equality .ne)
  | .and => some .and | .or => some .or
  | .band => some .bitAnd | .bor => some .bitOr | .bxor => some .bitXor
  | .shl => some (.shift .shl) | .shr => some (.shift .sar)
  | .addW | .subW | .mulW | .powW => none

/-- Compound assignment operators (`x op= e`). -/
def assignOp : BinOp → Option Source.AssignOp
  | .add => some .add | .sub => some .sub | .mul => some .mul | .div => some .div
  | .mod => some .mod | .band => some .bitAnd | .bor => some .bitOr | .bxor => some .bitXor
  | .shl => some .shl | .shr => some .sar
  | _ => none

/-- Environment reads. `msg.sender`, `address(this)` and its balance are gaps:
the model has erased the address type and the state relation does not relate
them. -/
def env : EnvKey → Option (Syn .expr)
  | .msgValue => some (.member (.ident "msg") "value")
  | .timestamp => some (.member (.ident "block") "timestamp")
  | .msgSender | .selfBalance | .selfAddress => none

mutual
/-- Expressions. Gaps: `newArr`, `named`, the wrapping operators, a tuple of
fewer than two components, `address(this)`. -/
def expr : RawExpr → Option (Syn .expr)
  | .num n => some (num n)
  | .name x => some (.ident x)
  | .bool b => some (.lit (.bool b))
  | .field e f => (expr e).map (.member · f)
  | .index e k => do pure (.index (← expr e) (.some (← expr k)))
  | .binop op a b => do pure ((← binop op) (← expr a) (← expr b))
  | .unop .neg a => (expr a).map (.unaryPrefix .neg)
  | .unop .not a => (expr a).map (.unaryPrefix .not)
  | .unop .bnot a => (expr a).map (.unaryPrefix .bitNot)
  | .unop .toInt a => (expr a).map fun a =>
      .call (.elemType intElem (by decide)) (.positional (.cons a .nil))
  | .unop .toUint a => (expr a).map fun a =>
      .call (.elemType uintElem (by decide)) (.positional (.cons a .nil))
  | .ternary c a b => do pure (.cond (← expr c) (← expr a) (← expr b))
  | .incDec .preInc e => (expr e).map (.unaryPrefix .inc)
  | .incDec .preDec e => (expr e).map (.unaryPrefix .dec)
  | .incDec .postInc e => (expr e).map (.unarySuffix .inc)
  | .incDec .postDec e => (expr e).map (.unarySuffix .dec)
  | .call f args => (exprs args).map fun args => .call (.ident f) (.positional args)
  | .modular op a b k => do
      pure (.call (.ident op.toStr)
        (.positional (.cons (← expr a) (.cons (← expr b) (.cons (← expr k) .nil)))))
  | .env k => env k
  | .tuple (a :: b :: rest) => do
      pure (.tuple (.some (← expr a)) (.cons (.some (← expr b)) (← components rest)))
  | .assign l r => do pure (.assign .assign (← expr l) (← expr r))
  | .opAssign op l r => do pure (.assign (← assignOp op) (← expr l) (← expr r))
  | _ => none
/-- Argument lists, in order. -/
def exprs : List RawExpr → Option (Syn (.list .expr))
  | [] => some .nil
  | e :: es => do pure (.cons (← expr e) (← exprs es))
/-- The remaining components of a tuple; none is left out. -/
def components : List RawExpr → Option (Syn (.list (.opt .expr)))
  | [] => some .nil
  | e :: es => do pure (.cons (.some (← expr e)) (← components es))
end

/-- Local declaration types: the three primitive types by their canonical
names. Narrow integers, `address`, references and user types are gaps. -/
def typeName : RawTy → Option (Syn .typeName)
  | .named "bool" => some (.elem .bool)
  | .named "uint" | .named "uint256" => some (.elem uintElem)
  | .named "int" | .named "int256" => some (.elem intElem)
  | _ => none

/-- Simple statements: a declaration, an assignment, an update, a builtin
call. `require`, `assert` and `revert()` are spelled as calls of the Source
builtins. The modifier hole is a gap: the context is never a modifier's. -/
def simple : RawStmt → Option (Syn .simple)
  | .assign l r => do pure (.exprStmt (.assign .assign (← expr l) (← expr r)))
  | .decl T x none => (typeName T).map fun T => .declVar (.varDecl T none x) .none
  | .decl T x (some e) => do pure (.declVar (.varDecl (← typeName T) none x) (.some (← expr e)))
  | .opAssign op l r => do pure (.exprStmt (.assign (← assignOp op) (← expr l) (← expr r)))
  | .incDec op l => (expr (.incDec op l)).map .exprStmt
  | .require c => (expr c).map fun c =>
      .exprStmt (.call (.ident "require") (.positional (.cons c .nil)))
  | .assert c => (expr c).map fun c =>
      .exprStmt (.call (.ident "assert") (.positional (.cons c .nil)))
  | .revert => some (.exprStmt (.call (.ident "revert") (.positional .nil)))
  | _ => none

/-- A `for` update: one expression statement. -/
def update : List RawStmt → Option (Syn (.opt .expr))
  | [] => some .none
  | [.assign l r] => do pure (.some (.assign .assign (← expr l) (← expr r)))
  | [.opAssign op l r] => do pure (.some (.assign (← assignOp op) (← expr l) (← expr r)))
  | [.incDec op l] => (expr (.incDec op l)).map .some
  | _ => none

/-- A `for` initializer: one simple statement. -/
def initializer : List RawStmt → Option (Syn (.opt .simple))
  | [] => some .none
  | [s] => (simple s).map .some
  | _ => none

/-- `break` and `continue` exist only inside a loop. -/
def jump (brk : Bool) : (k : SCtx) → Option (Syn (.stmt k))
  | ⟨true, _⟩ => some (if brk then .breakStmt else .continueStmt)
  | ⟨false, _⟩ => none

/-- An `unchecked` block is an item of a checked block only. -/
def uncheckedItem : (k : SCtx) → Syn (.list (.item ⟨k.loop, true⟩)) → Option (Syn (.item k))
  | ⟨_, false⟩, b => some (.uncheckedItem (.block b))
  | ⟨_, true⟩, _ => none

/-- A loop body or a branch from its items. The raw syntax does not record
braces: exactly one statement is read unbraced, anything else as a block. -/
def unbrace {k : SCtx} : Syn (.list (.item k)) → Syn (.stmt k)
  | .cons (.stmtItem s) .nil => s
  | b => .blockStmt (.block b)

mutual
/-- Statements in control context `k`. Bodies and branches are read by
`unbrace`; an empty `else` is read as absent. Loop specifications are
annotations with no Source syntax and are not read. A lowered `loop` is
spelled as a `while`. Gaps: every statement not listed here or in
`simple` (storage and memory declarations, `delete`, pushes, calls as
statements, tuples, `try`, sends, reverts with data, `eval`, `checked`,
`assumeFalse`). -/
def stmt (k : SCtx) : RawStmt → Option (Syn (.stmt k))
  | .ite c thn els => do
      let c ← expr c
      let thn ← items k thn
      match els with
      | [] => pure (.ifStmt c (unbrace thn) .none)
      | e :: els => pure (.ifStmt c (unbrace thn) (.some (unbrace (← items k (e :: els)))))
  | .ret none => some (.returnStmt .none)
  | .ret (some e) => (expr e).map fun e => .returnStmt (.some e)
  | .block b => (items k b).map fun b => .blockStmt (.block b)
  | .whileLoop _ c b | .loop _ c b => do
      pure (.whileStmt (← expr c) (unbrace (← items ⟨true, k.unchecked⟩ b)))
  | .doWhile _ b c => do
      pure (.doWhile (unbrace (← items ⟨true, k.unchecked⟩ b)) (← expr c))
  | .forLoop _ init c upd b => do
      let init ← initializer init
      let c ← match c with
        | none => pure .none
        | some c => (expr c).map Syn.some
      pure (.forStmt init c (← update upd) (unbrace (← items ⟨true, k.unchecked⟩ b)))
  | .brk => jump true k
  | .cont => jump false k
  | s => (simple s).map .simpleStmt
/-- The items of a block. -/
def items (k : SCtx) : List RawStmt → Option (Syn (.list (.item k)))
  | [] => some .nil
  | .unchecked b :: rest => do
      pure (.cons (← uncheckedItem k (← items ⟨k.loop, true⟩ b)) (← items k rest))
  | s :: rest => do pure (.cons (.stmtItem (← stmt k s)) (← items k rest))
end

/-- Source type of a model local: a full-width primitive with no shape rows.
Narrow locals, locals carrying a shape (the marker of an erased `address`,
`bytes32`, enum or function type), references and formula locals are gaps. -/
def localTy : LocalTy → Option STy
  | .val p 256 [] => some (Source.Agreement.sourceTy p)
  | _ => none

/-- The Source locals of a model context, innermost first, by name. -/
def locals : ECtx → Option (List (String × STy))
  | [] => some []
  | (x, t) :: Γ => do pure ((x, ← localTy t) :: (← locals Γ))

/-- State variable types: primitive only (references are gaps). A model `uint`
is spelled `uint256` even where the original declared `address` or an enum:
the model has erased that, and `relates` must absorb it. -/
def stateTy : Ty → Option (Syn .typeName)
  | .prim .bool => some (.elem .bool)
  | .prim .uint => some (.elem uintElem)
  | .prim .int => some (.elem intElem)
  | _ => none

/-- The state variables, in declaration order. Transient roots are gaps. -/
def stateVars : List (Name × Ty) → Option (Syn (.list (.part false)))
  | [] => some .nil
  | (x, T) :: rest => do
      pure (.cons (.stateVar (← stateTy T) none none none false x .none) (← stateVars rest))

/-- The canonical Source unit of a model contract: one contract with its
state variables. Functions, enums, the constructor, initializers and narrow
widths are not spelled, so a request that calls a function, or whose contract
has any of them, is a gap. -/
def unit (C : Contract) : Option (Syn .unit) :=
  if C.transientRoots.isEmpty && C.funs.isEmpty && C.enums.isEmpty && C.ctor.isNone &&
      C.widths.isEmpty && C.inits.isEmpty then
    (stateVars C.vars).map fun parts =>
      .unit (.cons (.contract false contractName .none .nil parts) .nil)
  else none

/-- The request parts the decoder cannot read yet. It reads the contract,
the raw input and the caller's locals only, so a request whose meaning depends
on anything else is a gap, never a guess: a callee body (renaming, modifiers,
constructor initializers, self frame, declared returns), return slots, and a
scope inside `unchecked`, `checked` or `ignoringOverflow`. -/
def plain (r : Request) : Bool :=
  r.callee.isNone && r.input.returnSlots.isNone && !r.input.scope.unchecked &&
    r.input.scope.overflow.isNone

/-- The Source typing context of a request, with no locals yet: the canonical
unit, inside its contract, in a function that returns nothing. -/
def context (r : Request) : Option Source.Ctx :=
  (unit r.contract).map fun u =>
    { env := u.env, scope := some contractName, locals := [], rets := [] }

/-- **The decoder (stage 1).** A plain request's raw input in its canonical
Source spelling, typed and resolved by the Source front end against the
caller's locals. The result is the decoder's choice of Source program: that it
means what the model elaborator gives the same raw input is not proved here;
it is the `pipeline` obligation, once `relates` and the policies are fixed. -/
def decode (r : Request) : Option SourceProgram :=
  if plain r then do
    let C ← context r
    let L ← locals r.input.before.locals.1
    let b ← items .body r.input.raw
    let ⟨L', d⟩ ← Source.ItemsD.infer C L b
    pure ⟨C.env, C.rets, C.inModifier, .body, Source.tysOf L, Source.tysOf L', d.toR⟩
  else none

/-! ## Decoder versions (H1258, additive)

The decoder above is landed and other modules build on it, so it is kept as it
is. Wider decoders are versions of one generic decoder, `Tables.decode`, which
is written to differ from it only in its three type tables: how a
declaration's type name, a model local and a model contract are read:
`decode_tables1` proves that at the landed tables it is the landed decoder.
Expression spelling is shared. `tablesA` (below) also reads marked addresses. `tablesW` reads
integers at their declared widths (`bool` only at 256). -/

/-- The type tables of a decoder version. -/
structure Tables where
  /-- A local declaration's type, by name. -/
  typeName : RawTy → Option (Syn .typeName)
  /-- The Source type of a model local. -/
  localTy : LocalTy → Option STy
  /-- The canonical Source unit of a model contract. -/
  unit : Contract → Option (Syn .unit)
  /-- An environment read (`msg.value`, …). -/
  env : EnvKey → Option (Syn .expr)

namespace Tables

variable (T : Tables)

mutual
/-- Expressions of the version: as `Decode.expr`, with environment reads by
the version's table. -/
def expr : RawExpr → Option (Syn .expr)
  | .num n => some (num n)
  | .name x => some (.ident x)
  | .bool b => some (.lit (.bool b))
  | .field e f => (expr e).map (.member · f)
  | .index e k => do pure (.index (← expr e) (.some (← expr k)))
  | .binop op a b => do pure ((← binop op) (← expr a) (← expr b))
  | .unop .neg a => (expr a).map (.unaryPrefix .neg)
  | .unop .not a => (expr a).map (.unaryPrefix .not)
  | .unop .bnot a => (expr a).map (.unaryPrefix .bitNot)
  | .unop .toInt a => (expr a).map fun a =>
      .call (.elemType intElem (by decide)) (.positional (.cons a .nil))
  | .unop .toUint a => (expr a).map fun a =>
      .call (.elemType uintElem (by decide)) (.positional (.cons a .nil))
  | .ternary c a b => do pure (.cond (← expr c) (← expr a) (← expr b))
  | .incDec .preInc e => (expr e).map (.unaryPrefix .inc)
  | .incDec .preDec e => (expr e).map (.unaryPrefix .dec)
  | .incDec .postInc e => (expr e).map (.unarySuffix .inc)
  | .incDec .postDec e => (expr e).map (.unarySuffix .dec)
  | .call f args => (exprs args).map fun args => .call (.ident f) (.positional args)
  | .modular op a b k => do
      pure (.call (.ident op.toStr)
        (.positional (.cons (← expr a) (.cons (← expr b) (.cons (← expr k) .nil)))))
  | .env k => T.env k
  | .tuple (a :: b :: rest) => do
      pure (.tuple (.some (← expr a)) (.cons (.some (← expr b)) (← components rest)))
  | .assign l r => do pure (.assign .assign (← expr l) (← expr r))
  | .opAssign op l r => do pure (.assign (← assignOp op) (← expr l) (← expr r))
  | _ => none
/-- Argument lists of the version. -/
def exprs : List RawExpr → Option (Syn (.list .expr))
  | [] => some .nil
  | e :: es => do pure (.cons (← expr e) (← exprs es))
/-- Tuple components of the version. -/
def components : List RawExpr → Option (Syn (.list (.opt .expr)))
  | [] => some .nil
  | e :: es => do pure (.cons (.some (← expr e)) (← components es))
end

/-- Simple statements, with declarations typed by the version's table. -/
def simple : RawStmt → Option (Syn .simple)
  | .decl U x none => (T.typeName U).map fun U => .declVar (.varDecl U none x) .none
  | .decl U x (some e) => do
      pure (.declVar (.varDecl (← T.typeName U) none x) (.some (← T.expr e)))
  | .assign l r => do pure (.exprStmt (.assign .assign (← T.expr l) (← T.expr r)))
  | .opAssign op l r => do pure (.exprStmt (.assign (← assignOp op) (← T.expr l) (← T.expr r)))
  | .incDec op l => (T.expr (.incDec op l)).map .exprStmt
  | .require c => (T.expr c).map fun c =>
      .exprStmt (.call (.ident "require") (.positional (.cons c .nil)))
  | .assert c => (T.expr c).map fun c =>
      .exprStmt (.call (.ident "assert") (.positional (.cons c .nil)))
  | .revert => some (.exprStmt (.call (.ident "revert") (.positional .nil)))
  | _ => none

/-- A `for` update of the version. -/
def update : List RawStmt → Option (Syn (.opt .expr))
  | [] => some .none
  | [.assign l r] => do pure (.some (.assign .assign (← T.expr l) (← T.expr r)))
  | [.opAssign op l r] => do pure (.some (.assign (← assignOp op) (← T.expr l) (← T.expr r)))
  | [.incDec op l] => (T.expr (.incDec op l)).map .some
  | _ => none

/-- A `for` initializer of the version. -/
def initializer : List RawStmt → Option (Syn (.opt .simple))
  | [] => some .none
  | [s] => (T.simple s).map .some
  | _ => none

mutual
/-- Statements of the version: as `Decode.stmt`, over `Tables.simple`. -/
def stmt (k : SCtx) : RawStmt → Option (Syn (.stmt k))
  | .ite c thn els => do
      let c ← T.expr c
      let thn ← items k thn
      match els with
      | [] => pure (.ifStmt c (unbrace thn) .none)
      | e :: els => pure (.ifStmt c (unbrace thn) (.some (unbrace (← items k (e :: els)))))
  | .ret none => some (.returnStmt .none)
  | .ret (some e) => (T.expr e).map fun e => .returnStmt (.some e)
  | .block b => (items k b).map fun b => .blockStmt (.block b)
  | .whileLoop _ c b | .loop _ c b => do
      pure (.whileStmt (← T.expr c) (unbrace (← items ⟨true, k.unchecked⟩ b)))
  | .doWhile _ b c => do
      pure (.doWhile (unbrace (← items ⟨true, k.unchecked⟩ b)) (← T.expr c))
  | .forLoop _ init c upd b => do
      let init ← T.initializer init
      let c ← match c with
        | none => pure .none
        | some c => (T.expr c).map Syn.some
      pure (.forStmt init c (← T.update upd) (unbrace (← items ⟨true, k.unchecked⟩ b)))
  | .brk => jump true k
  | .cont => jump false k
  | s => (T.simple s).map .simpleStmt
/-- The items of a block of the version. -/
def items (k : SCtx) : List RawStmt → Option (Syn (.list (.item k)))
  | [] => some .nil
  | .unchecked b :: rest => do
      pure (.cons (← uncheckedItem k (← items ⟨k.loop, true⟩ b)) (← items k rest))
  | s :: rest => do pure (.cons (.stmtItem (← stmt k s)) (← items k rest))
end

/-- The Source locals of a model context under the version. -/
def locals : ECtx → Option (List (String × STy))
  | [] => some []
  | (x, t) :: Γ => do pure ((x, ← T.localTy t) :: (← locals Γ))

/-- The Source typing context of a request under the version. -/
def context (r : Request) : Option Source.Ctx :=
  (T.unit r.contract).map fun u =>
    { env := u.env, scope := some contractName, locals := [], rets := [] }

/-- **The decoder of a version.** As `Decode.decode`, over the version's
tables. -/
def decode (r : Request) : Option SourceProgram :=
  if plain r then do
    let C ← T.context r
    let L ← T.locals r.input.before.locals.1
    let b ← T.items .body r.input.raw
    let ⟨L', d⟩ ← Source.ItemsD.infer C L b
    pure ⟨C.env, C.rets, C.inModifier, .body, Source.tysOf L, Source.tysOf L', d.toR⟩
  else none

end Tables

/-- The landed decoder's tables. -/
def tables1 : Tables := ⟨typeName, localTy, unit, env⟩

/-! ### The landed decoder is the generic decoder at its tables -/

mutual
theorem expr_tables1 : (e : RawExpr) → tables1.expr e = expr e
  | .num _ | .name _ | .bool _ | .env _ | .newArr .. | .named .. => by simp [Tables.expr, expr, tables1]
  | .field e _ => by simp [Tables.expr, expr, expr_tables1 e]
  | .index e k => by simp [Tables.expr, expr, expr_tables1 e, expr_tables1 k]
  | .binop _ a b => by simp [Tables.expr, expr, expr_tables1 a, expr_tables1 b]
  | .unop op a => by cases op <;> simp [Tables.expr, expr, expr_tables1 a]
  | .ternary c a b => by simp [Tables.expr, expr, expr_tables1 c, expr_tables1 a, expr_tables1 b]
  | .incDec op e => by cases op <;> simp [Tables.expr, expr, expr_tables1 e]
  | .call _ args => by simp [Tables.expr, expr, exprs_tables1 args]
  | .modular _ a b k => by
      simp [Tables.expr, expr, expr_tables1 a, expr_tables1 b, expr_tables1 k]
  | .tuple [] | .tuple [_] => by simp [Tables.expr, expr]
  | .tuple (a :: b :: rest) => by
      simp [Tables.expr, expr, expr_tables1 a, expr_tables1 b, components_tables1 rest]
  | .assign l r | .opAssign _ l r => by simp [Tables.expr, expr, expr_tables1 l, expr_tables1 r]
theorem exprs_tables1 : (es : List RawExpr) → tables1.exprs es = exprs es
  | [] => by simp [Tables.exprs, exprs]
  | e :: es => by simp [Tables.exprs, exprs, expr_tables1 e, exprs_tables1 es]
theorem components_tables1 : (es : List RawExpr) → tables1.components es = components es
  | [] => by simp [Tables.components, components]
  | e :: es => by simp [Tables.components, components, expr_tables1 e, components_tables1 es]
end

theorem update_tables1 (b : List RawStmt) : tables1.update b = update b := by
  unfold Tables.update update
  split <;> simp [expr_tables1]

theorem simple_tables1 (s : RawStmt) : tables1.simple s = simple s := by
  cases s with
  | decl U x init => cases init <;> simp only [Tables.simple, simple, expr_tables1] <;> rfl
  | _ => simp [Tables.simple, simple, expr_tables1]

theorem initializer_tables1 : (b : List RawStmt) → tables1.initializer b = initializer b
  | [] => rfl
  | [s] => by simp [Tables.initializer, initializer, simple_tables1]
  | _ :: _ :: _ => rfl

mutual
theorem stmt_tables1 : (k : SCtx) → (s : RawStmt) → tables1.stmt k s = stmt k s
  | k, .ite c thn [] => by simp [Tables.stmt, stmt, expr_tables1, update_tables1, items_tables1 k thn]
  | k, .ite c thn (e :: els) => by
      simp [Tables.stmt, stmt, expr_tables1, update_tables1, items_tables1 k thn, items_tables1 k (e :: els)]
  | k, .ret none | k, .ret (some _) => by simp [Tables.stmt, stmt, expr_tables1, update_tables1]
  | k, .block b => by simp [Tables.stmt, stmt, expr_tables1, update_tables1, items_tables1 k b]
  | k, .whileLoop _ c b | k, .loop _ c b | k, .doWhile _ b c => by
      simp [Tables.stmt, stmt, expr_tables1, update_tables1, items_tables1 ⟨true, k.unchecked⟩ b]
  | k, .forLoop _ init c upd b => by
      simp [Tables.stmt, stmt, expr_tables1, update_tables1, items_tables1 ⟨true, k.unchecked⟩ b, initializer_tables1]
  | k, .brk | k, .cont => by simp [Tables.stmt, stmt, expr_tables1, update_tables1]
  | k, (.assign ..) | k, (.decl ..) | k, (.declStorage ..) | k, (.declMemory ..)
  | k, (.delete ..) | k, (.opAssign ..) | k, (.incDec ..) | k, (.pushOpAssign ..)
  | k, (.pushIncDec ..) | k, (.call ..) | k, (.assignIncDec ..) | k, (.assignPush ..)
  | k, (.declStoragePush ..) | k, (.declPush ..) | k, (.require ..) | k, (.assert ..)
  | k, .revert | k, (.revertMsg ..) | k, (.requireMsg ..) | k, (.revertReason ..)
  | k, (.requireReason ..) | k, (.revertRaw ..) | k, (.revertErr ..) | k, (.requireErr ..)
  | k, .assumeFalse | k, (.eval ..) | k, (.unchecked ..) | k, (.checked ..) | k, (.tryCall ..)
  | k, (.send ..) | k, (.tupleDecl ..) | k, (.tupleAssign ..) | k, .hole => by
      simp [Tables.stmt, stmt, expr_tables1, update_tables1, simple_tables1]
theorem items_tables1 : (k : SCtx) → (b : List RawStmt) → tables1.items k b = items k b
  | k, [] => by simp [Tables.items, items]
  | k, .unchecked b :: rest => by
      simp [Tables.items, items, items_tables1 ⟨k.loop, true⟩ b, items_tables1 k rest]
  | k, (.assign ..) :: rest | k, (.decl ..) :: rest | k, (.declStorage ..) :: rest
  | k, (.declMemory ..) :: rest | k, (.delete ..) :: rest | k, (.opAssign ..) :: rest
  | k, (.incDec ..) :: rest | k, (.pushOpAssign ..) :: rest | k, (.pushIncDec ..) :: rest
  | k, (.call ..) :: rest | k, (.assignIncDec ..) :: rest | k, (.assignPush ..) :: rest
  | k, (.declStoragePush ..) :: rest | k, (.declPush ..) :: rest | k, (.ite ..) :: rest
  | k, (.require ..) :: rest | k, (.assert ..) :: rest | k, .revert :: rest
  | k, (.revertMsg ..) :: rest | k, (.requireMsg ..) :: rest | k, (.revertReason ..) :: rest
  | k, (.requireReason ..) :: rest | k, (.revertRaw ..) :: rest | k, (.revertErr ..) :: rest
  | k, (.requireErr ..) :: rest | k, .assumeFalse :: rest | k, (.ret ..) :: rest
  | k, (.eval ..) :: rest | k, (.checked ..) :: rest | k, (.tryCall ..) :: rest
  | k, (.send ..) :: rest | k, (.tupleDecl ..) :: rest | k, (.tupleAssign ..) :: rest
  | k, (.block ..) :: rest | k, (.whileLoop ..) :: rest | k, (.forLoop ..) :: rest
  | k, (.doWhile ..) :: rest | k, .brk :: rest | k, .cont :: rest | k, (.loop ..) :: rest
  | k, .hole :: rest => by
      simp [Tables.items, items, stmt_tables1, items_tables1 k rest]
end

theorem locals_tables1 : (Γ : ECtx) → tables1.locals Γ = locals Γ
  | [] => rfl
  | (x, t) :: Γ => by
      simp only [Tables.locals, locals, locals_tables1 Γ]
      rfl

/-- **The bridge**: the generic decoder at the landed tables is the landed
decoder. -/
theorem decode_tables1 (r : Request) : tables1.decode r = decode r := by
  simp only [Tables.decode, decode, Tables.context, context, locals_tables1, items_tables1]
  rfl

/-! ### Widths

`tablesW`: a primitive at its declared width. A local `uint8 x` is
`LocalTy.val .uint 8`, a state variable's width is its own row of the
contract's width table, a declaration names its type. -/

/-- The Source elementary type of a model primitive at a width: `bool`, or
`uintN`/`intN` for a width that is a multiple of 8 in `8 … 256`. -/
def primElem : PrimTy → Nat → Option Source.Elem
  | .bool, bits => if bits = 256 then some .bool else none
  | .uint, bits =>
    if h : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 then some (.int false bits h) else none
  | .int, bits =>
    if h : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 then some (.int true bits h) else none

/-- The Source type of a model primitive at a width. -/
def primTy (p : PrimTy) (bits : Nat) : Option STy := (primElem p bits).map (Source.Elem.ty .memory)

/-- Declaration types by name: `bool`, `uint`/`int` (256 bits) and the narrow
`uintN`/`intN`. `address`, `bytesN`, enums, references and user types are gaps. -/
def typeNameW : RawTy → Option (Syn .typeName)
  | .named s =>
    if s = "bool" then some (.elem .bool)
    else if s = "uint" ∨ s = "uint256" then (primElem .uint 256).map .elem
    else if s = "int" ∨ s = "int256" then (primElem .int 256).map .elem
    else match narrowTy? s with
      | some (p, bits) => (primElem p bits).map .elem
      | none => none
  | _ => none

/-- A model local at its declared width, with no shape rows. A local carrying
a shape (the marker of an erased `address`, `bytesN`, enum or function type),
a reference and a formula local are gaps. Not a gap, and possibly a wrong
Source type: a local the elaborator declares without a marker (a pushed value
`T x = b.push()`, a self-call or `try` return, a cast capture) has an empty
shape even when its declared type was `address` or `bytesN`, and is read here
as the integer `uintN` the model also takes it for. A request's locals are
also not tied to any elaborator run. -/
def localTyW : LocalTy → Option STy
  | .val p bits [] => primTy p bits
  | _ => none

/-- The width of a state variable: its row in the width table, or 256. -/
def stateBits (widths : List (Name × Nat)) (x : Name) : Nat :=
  (Semantics.lookupBy x widths).getD 256

/-- The state variables, in declaration order, each a primitive at its width. -/
def stateVarsW (widths : List (Name × Nat)) :
    List (Name × Ty) → Option (Syn (.list (.part false)))
  | [] => some .nil
  | (x, .prim p) :: rest => do
      pure (.cons (.stateVar (.elem (← primElem p (stateBits widths x))) none none none false x
        .none) (← stateVarsW widths rest))
  | _ => none

/-- A width key that is a state variable's own row: no marker (`#`) and no
position below a reference (`[`, `{`). -/
def plainKey (k : String) : Bool := k.data.all fun c => c != '#' && c != '[' && c != '{'

/-- The canonical unit at widths. Transient roots, functions, enums, the
constructor and initializers are gaps, and so are a state variable of a
reference type, a width that is no integer type's (or any width but 256 on a
`bool`), a width table with a marker row or a row below a reference, and a
state variable named like one. A row whose key is no state variable is not
read, as the model does not read it. -/
def unitW (C : Contract) : Option (Syn .unit) :=
  if C.transientRoots.isEmpty && C.funs.isEmpty && C.enums.isEmpty && C.ctor.isNone &&
      C.inits.isEmpty && (C.widths.all fun w => plainKey w.1) &&
      (C.vars.all fun v => plainKey v.1) then
    (stateVarsW C.widths C.vars).map fun parts =>
      .unit (.cons (.contract false contractName .none .nil parts) .nil)
  else none

/-- The width-aware decoder's tables. -/
def tablesW : Tables := ⟨typeNameW, localTyW, unitW, env⟩

/-! ### Addresses

`tablesA`: as `tablesW`, and an erased `address` where the model marks one. A
local marked `#address` (20 bytes, at 256 bits) and a state variable with the
row `x#address` are Source `address`; so is a declaration named `address`.
`address payable` is read as `address`: the model does not record the
difference. Expressions are still the shared ones, so `msg.sender`,
`address(this)` and address casts stay gaps. A captured address, whose shape
carries the marker twice, is a gap; and the caveat at `localTyW` still
applies: a local declared without a marker is read as a plain integer. -/

/-- The marker rows of an erased `address`. -/
def addressShape : List (String × Nat) := [("#address", 20)]

/-- Declaration types by name: `address`, or as `typeNameW`. -/
def typeNameA : RawTy → Option (Syn .typeName)
  | .named s => if s = "address" then some (.elem .address) else typeNameW (.named s)
  | T => typeNameW T

/-- A model local: an `address` where the shape is exactly the address marker
on a full-width `uint`, or as `localTyW`. -/
def localTyA : LocalTy → Option STy
  | .val .uint 256 [("#address", 20)] => some (.address false)
  | t => localTyW t

/-- Whether the width table marks the state variable `x` as an address. -/
def isAddress (widths : List (Name × Nat)) (x : Name) : Bool :=
  Semantics.lookupBy (x ++ "#address") widths == some 20

/-- The elementary type of a state variable: an address where the table
marks one (it must then be a `uint` with no width row of its own), or the
primitive at its width. -/
def elemA (widths : List (Name × Nat)) (x : Name) (p : PrimTy) : Option Source.Elem :=
  if isAddress widths x then
    (if p = .uint ∧ Semantics.lookupBy x widths = none then some .address else none)
  else primElem p (stateBits widths x)

/-- The state variables, an address where the table marks one. -/
def stateVarsA (widths : List (Name × Nat)) :
    List (Name × Ty) → Option (Syn (.list (.part false)))
  | [] => some .nil
  | (x, .prim p) :: rest => do
      pure (.cons (.stateVar (.elem (← elemA widths x p)) none none none false x .none)
        (← stateVarsA widths rest))
  | _ => none

/-- A width key the address version reads: a plain key, or the address marker
of a state variable. -/
def keyA (vars : List (Name × Ty)) (w : Name × Nat) : Bool :=
  plainKey w.1 || vars.any fun v => w.1 == v.1 ++ "#address" && w.2 == 20

/-- The canonical unit with addresses: as `unitW`, but address marker rows of
state variables are read instead of being gaps. -/
def unitA (C : Contract) : Option (Syn .unit) :=
  if C.transientRoots.isEmpty && C.funs.isEmpty && C.enums.isEmpty && C.ctor.isNone &&
      C.inits.isEmpty && (C.widths.all fun w => keyA C.vars w) &&
      (C.vars.all fun v => plainKey v.1) then
    (stateVarsA C.widths C.vars).map fun parts =>
      .unit (.cons (.contract false contractName .none .nil parts) .nil)
  else none

/-- The address-aware decoder's tables. -/
def tablesA : Tables := ⟨typeNameA, localTyA, unitA, env⟩

/-! ### Canonical units from an element table

Later versions build their unit from one function: which elementary type a
state variable has. `unitOf` is the canonical unit over it; the properties of
the unit are proved once (`Total.Versions`). -/

/-- The state variables, each at the elementary type `el` gives it. -/
def stateVarsOf (el : Name → PrimTy → Option Source.Elem) :
    List (Name × Ty) → Option (Syn (.list (.part false)))
  | [] => some .nil
  | (x, .prim p) :: rest => do
      pure (.cons (.stateVar (.elem (← el x p)) none none none false x .none)
        (← stateVarsOf el rest))
  | _ => none

/-- The canonical unit of a contract that passes `ok`, over an element table.
Transient roots, functions, enums, the constructor and initializers are gaps,
and so are a state variable of a reference type, one the table gives no
elementary type, and one named like a marker row. -/
def unitOf (ok : Contract → Bool) (el : Contract → Name → PrimTy → Option Source.Elem)
    (C : Contract) : Option (Syn .unit) :=
  if C.transientRoots.isEmpty && C.funs.isEmpty && C.enums.isEmpty && C.ctor.isNone &&
      C.inits.isEmpty && ok C && (C.vars.all fun v => plainKey v.1) then
    (stateVarsOf (el C) C.vars).map fun parts =>
      .unit (.cons (.contract false contractName .none .nil parts) .nil)
  else none

/-! ### Fixed bytes

`tablesB`: as `tablesA`, and an erased `bytesN` where the model marks one. A
local of `8N` bits marked `#bytes ↦ N`, a state variable with the row
`x#bytes ↦ N` (and its own row `x ↦ 8N` when `N < 32`), and a declaration
named `bytesN` are Source `bytesN`. The model holds a `bytesN` as the number
its bytes spell big-endian, right-aligned in a `uint` of `8N` bits
(`Syntax/Raw.lean`, at `bytesTy?`); that is the reading here, not the
left-aligned word of `Source.Observe`.

Expressions are the shared ones. Between marked operands they spell, and
Source types, indexing `b[i]`, `b.length`, `==`, `!=`, the orderings, `&`,
`|`, `^`, `~`, the shifts, their compound assignments and implicit widening:
these are in the fragment, so their agreement with the model is part of the
simulation obligation. `bytesN(e)` casts and bytes literals are gaps. A
captured `bytesN`, whose shape carries the marker twice, is a gap, and the
caveat at `localTyW` still applies. -/

/-- `bytesN` for `N` in `1 … 32`. -/
def bytesElem (n : Nat) : Option Source.Elem :=
  if h : 1 ≤ n ∧ n ≤ 32 then some (.fixedBytes n h) else none

/-- Declaration types by name: `bytesN`, or as `typeNameA`. -/
def typeNameB : RawTy → Option (Syn .typeName)
  | .named s => match bytesTy? s with
    | some n => (bytesElem n).map .elem
    | none => typeNameA (.named s)
  | T => typeNameA T

/-- A model local: a `bytesN` where the shape is exactly the bytes marker on a
`uint` of `8N` bits, or as `localTyA`. -/
def localTyB : LocalTy → Option STy
  | .val .uint bits [("#bytes", n)] =>
    if bits = 8 * n then (bytesElem n).map (Source.Elem.ty .memory) else none
  | t => localTyA t

/-- The elementary type of a state variable: `bytesN` where the table marks
one (a `uint` whose width is `8N` and that is not also marked an address), or
as `elemA`. -/
def elemB (widths : List (Name × Nat)) (x : Name) (p : PrimTy) : Option Source.Elem :=
  match Semantics.lookupBy (x ++ "#bytes") widths with
  | some n =>
    if p = .uint ∧ stateBits widths x = 8 * n ∧ isAddress widths x = false then bytesElem n
    else none
  | none => elemA widths x p

/-- A width key the bytes version reads: as `keyA`, or the bytes marker of a
state variable. -/
def keyB (vars : List (Name × Ty)) (w : Name × Nat) : Bool :=
  keyA vars w || vars.any fun v => w.1 == v.1 ++ "#bytes"

/-- The canonical unit with fixed bytes. -/
def unitB : Contract → Option (Syn .unit) :=
  unitOf (fun C => C.widths.all fun w => keyB C.vars w) fun C => elemB C.widths

/-- The bytes-aware decoder's tables. -/
def tablesB : Tables := ⟨typeNameB, localTyB, unitB, env⟩

/-! ### The caller

`tablesS`: as `tablesB`, and `msg.sender` is read as the Source `msg.sender`,
an `address`. The version's state relation relates the model's caller to the
Source frame's sender (`Total.Versions`). `address(this)` and its balance stay
gaps. -/

/-- Environment reads with the caller. -/
def envS : EnvKey → Option (Syn .expr)
  | .msgSender => some (.member (.ident "msg") "sender")
  | k => env k

/-- The caller-aware decoder's tables. -/
def tablesS : Tables := { tablesB with env := envS }

end Decode

end Solidity.Correctness.Lowering.Total
