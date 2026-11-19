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
differs from it only in its three type tables: how a declaration's type name,
a model local and a model contract are read. The statement and expression
spelling is shared. `tablesW` reads primitives at their declared widths. -/

/-- The type tables of a decoder version. -/
structure Tables where
  /-- A local declaration's type, by name. -/
  typeName : RawTy → Option (Syn .typeName)
  /-- The Source type of a model local. -/
  localTy : LocalTy → Option STy
  /-- The canonical Source unit of a model contract. -/
  unit : Contract → Option (Syn .unit)

namespace Tables

variable (T : Tables)

/-- Simple statements, with declarations typed by the version's table. -/
def simple : RawStmt → Option (Syn .simple)
  | .decl U x none => (T.typeName U).map fun U => .declVar (.varDecl U none x) .none
  | .decl U x (some e) => do
      pure (.declVar (.varDecl (← T.typeName U) none x) (.some (← expr e)))
  | .assign l r => do pure (.exprStmt (.assign .assign (← expr l) (← expr r)))
  | .opAssign op l r => do pure (.exprStmt (.assign (← assignOp op) (← expr l) (← expr r)))
  | .incDec op l => (expr (.incDec op l)).map .exprStmt
  | .require c => (expr c).map fun c =>
      .exprStmt (.call (.ident "require") (.positional (.cons c .nil)))
  | .assert c => (expr c).map fun c =>
      .exprStmt (.call (.ident "assert") (.positional (.cons c .nil)))
  | .revert => some (.exprStmt (.call (.ident "revert") (.positional .nil)))
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
      let init ← T.initializer init
      let c ← match c with
        | none => pure .none
        | some c => (expr c).map Syn.some
      pure (.forStmt init c (← update upd) (unbrace (← items ⟨true, k.unchecked⟩ b)))
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
def tables1 : Tables := ⟨typeName, localTy, unit⟩

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
a reference and a formula local are gaps. A local the elaborator declares
without a marker (a capture, a pushed value) is read as the plain integer the
model also takes it for. -/
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
constructor and initializers are gaps, and so is a contract whose width table
has a marker row or a row below a reference, or whose state variable is named
like one. -/
def unitW (C : Contract) : Option (Syn .unit) :=
  if C.transientRoots.isEmpty && C.funs.isEmpty && C.enums.isEmpty && C.ctor.isNone &&
      C.inits.isEmpty && (C.widths.all fun w => plainKey w.1) &&
      (C.vars.all fun v => plainKey v.1) then
    (stateVarsW C.widths C.vars).map fun parts =>
      .unit (.cons (.contract false contractName .none .nil parts) .nil)
  else none

/-- The width-aware decoder's tables. -/
def tablesW : Tables := ⟨typeNameW, localTyW, unitW⟩

end Decode

end Solidity.Correctness.Lowering.Total
