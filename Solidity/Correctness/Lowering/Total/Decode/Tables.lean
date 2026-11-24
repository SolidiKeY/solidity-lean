import Solidity.Correctness.Lowering.Total.Decode

namespace Solidity.Correctness.Lowering.Total.Decode

open Source (Syn SCtx STy)

/-! ## Decoder versions (H1258, additive)

The imported decoder is landed and other modules build on it, so it is kept as it
is. Wider decoders are versions of one generic decoder, `Tables.decode`, which
is written to differ from it only in its four tables: how a
declaration's type name, a model local, a model contract and an environment
read are read: `decode_tables1` proves that at the landed tables it is the
landed decoder. Expressions are spelled per version (`Tables.expr`), differing
only in the environment table. Width-aware and address-aware tables can be
provided separately without changing the landed decoder. -/

/-- The tables of a decoder version. -/
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

namespace WithExpr

variable (spell : RawExpr → Option (Syn .expr))

/-- Simple statements, with declarations typed by the version's table. -/
def simple : RawStmt → Option (Syn .simple)
  | .decl U x none => (T.typeName U).map fun U => .declVar (.varDecl U none x) .none
  | .decl U x (some e) => do
      pure (.declVar (.varDecl (← T.typeName U) none x) (.some (← spell e)))
  | .assign l r => do pure (.exprStmt (.assign .assign (← spell l) (← spell r)))
  | .opAssign op l r => do pure (.exprStmt (.assign (← assignOp op) (← spell l) (← spell r)))
  | .incDec op l => (spell (.incDec op l)).map .exprStmt
  | .require c => (spell c).map fun c =>
      .exprStmt (.call (.ident "require") (.positional (.cons c .nil)))
  | .assert c => (spell c).map fun c =>
      .exprStmt (.call (.ident "assert") (.positional (.cons c .nil)))
  | .revert => some (.exprStmt (.call (.ident "revert") (.positional .nil)))
  | _ => none

/-- A `for` update of the version. -/
def update : List RawStmt → Option (Syn (.opt .expr))
  | [] => some .none
  | [.assign l r] => do pure (.some (.assign .assign (← spell l) (← spell r)))
  | [.opAssign op l r] => do pure (.some (.assign (← assignOp op) (← spell l) (← spell r)))
  | [.incDec op l] => (spell (.incDec op l)).map .some
  | _ => none

/-- A `for` initializer of the version. -/
def initializer : List RawStmt → Option (Syn (.opt .simple))
  | [] => some .none
  | [s] => (simple T spell s).map .some
  | _ => none

mutual
/-- Statements use the supplied expression spelling and `Tables.WithExpr.simple`,
retaining the existing loop and block traversal. -/
def stmt (k : SCtx) : RawStmt → Option (Syn (.stmt k))
  | .ite c thn els => do
      let c ← spell c
      let thn ← items k thn
      match els with
      | [] => pure (.ifStmt c (unbrace thn) .none)
      | e :: els => pure (.ifStmt c (unbrace thn) (.some (unbrace (← items k (e :: els)))))
  | .ret none => some (.returnStmt .none)
  | .ret (some e) => (spell e).map fun e => .returnStmt (.some e)
  | .block b => (items k b).map fun b => .blockStmt (.block b)
  | .whileLoop _ c b | .loop _ c b => do
      pure (.whileStmt (← spell c) (unbrace (← items ⟨true, k.unchecked⟩ b)))
  | .doWhile _ b c => do
      pure (.doWhile (unbrace (← items ⟨true, k.unchecked⟩ b)) (← spell c))
  | .forLoop _ init c upd b => do
      let init ← initializer T spell init
      let c ← match c with
        | none => pure .none
        | some c => (spell c).map Syn.some
      pure (.forStmt init c (← update spell upd) (unbrace (← items ⟨true, k.unchecked⟩ b)))
  | .brk => jump true k
  | .cont => jump false k
  | s => (simple T spell s).map .simpleStmt
/-- The items of a block of the version. -/
def items (k : SCtx) : List RawStmt → Option (Syn (.list (.item k)))
  | [] => some .nil
  | .unchecked b :: rest => do
      pure (.cons (← uncheckedItem k (← items ⟨k.loop, true⟩ b)) (← items k rest))
  | s :: rest => do pure (.cons (.stmtItem (← stmt k s)) (← items k rest))
end

end WithExpr

/-- The version traversal specialized to its expression decoder. -/
abbrev simple := WithExpr.simple T T.expr

/-- The version traversal specialized to its expression decoder. -/
abbrev update := WithExpr.update T.expr

/-- The version traversal specialized to its expression decoder. -/
abbrev initializer := WithExpr.initializer T T.expr

/-- The version traversal specialized to its expression decoder. -/
abbrev stmt := WithExpr.stmt T T.expr

/-- The version traversal specialized to its expression decoder. -/
abbrev items := WithExpr.items T T.expr

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
  unfold Tables.update Tables.WithExpr.update update
  split <;> simp [expr_tables1]

theorem simple_tables1 (s : RawStmt) : tables1.simple s = simple s := by
  cases s with
  | decl U x init => cases init <;> simp only [Tables.simple, Tables.WithExpr.simple, simple, expr_tables1] <;> rfl
  | _ => simp [Tables.simple, Tables.WithExpr.simple, simple, expr_tables1]

theorem initializer_tables1 : (b : List RawStmt) → tables1.initializer b = initializer b
  | [] => rfl
  | [s] => by simp [Tables.initializer, Tables.WithExpr.initializer, initializer, simple_tables1]
  | _ :: _ :: _ => rfl

mutual
theorem stmt_tables1 : (k : SCtx) → (s : RawStmt) → tables1.stmt k s = stmt k s
  | k, .ite c thn [] => by simp [Tables.stmt, Tables.WithExpr.stmt, stmt, expr_tables1, items_tables1 k thn]
  | k, .ite c thn (e :: els) => by
      simp [Tables.stmt, Tables.WithExpr.stmt, stmt, expr_tables1, items_tables1 k thn, items_tables1 k (e :: els)]
  | k, .ret none | k, .ret (some _) => by simp [Tables.stmt, Tables.WithExpr.stmt, stmt, expr_tables1]
  | k, .block b => by simp [Tables.stmt, Tables.WithExpr.stmt, stmt, items_tables1 k b]
  | k, .whileLoop _ c b | k, .loop _ c b | k, .doWhile _ b c => by
      simp [Tables.stmt, Tables.WithExpr.stmt, stmt, expr_tables1, items_tables1 ⟨true, k.unchecked⟩ b]
  | k, .forLoop _ init c upd b => by
      cases c <;> simp only [Tables.stmt, Tables.WithExpr.stmt, stmt, expr_tables1, update_tables1,
        items_tables1 ⟨true, k.unchecked⟩ b, initializer_tables1]
  | k, .brk | k, .cont => by simp [Tables.stmt, Tables.WithExpr.stmt, stmt]
  | k, (.assign ..) | k, (.decl ..) | k, (.declStorage ..) | k, (.declMemory ..)
  | k, (.delete ..) | k, (.opAssign ..) | k, (.incDec ..) | k, (.pushOpAssign ..)
  | k, (.pushIncDec ..) | k, (.call ..) | k, (.assignIncDec ..) | k, (.assignPush ..)
  | k, (.declStoragePush ..) | k, (.declPush ..) | k, (.require ..) | k, (.assert ..)
  | k, .revert | k, (.revertMsg ..) | k, (.requireMsg ..) | k, (.revertReason ..)
  | k, (.requireReason ..) | k, (.revertRaw ..) | k, (.revertErr ..) | k, (.requireErr ..)
  | k, .assumeFalse | k, (.eval ..) | k, (.unchecked ..) | k, (.checked ..) | k, (.tryCall ..)
  | k, (.send ..) | k, (.tupleDecl ..) | k, (.tupleAssign ..) | k, .hole => by
      simp [Tables.stmt, Tables.WithExpr.stmt, stmt, simple_tables1]
theorem items_tables1 : (k : SCtx) → (b : List RawStmt) → tables1.items k b = items k b
  | k, [] => by simp [Tables.items, Tables.WithExpr.items, items]
  | k, .unchecked b :: rest => by
      simp [Tables.items, Tables.WithExpr.items, items, items_tables1 ⟨k.loop, true⟩ b, items_tables1 k rest]
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
      simp [Tables.items, Tables.WithExpr.items, items, stmt_tables1, items_tables1 k rest]
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

end Solidity.Correctness.Lowering.Total.Decode
