import Solidity.Correctness.Lowering.Total.Decode.Calls

/-!
A single additive statement traversal parameterized by expression spelling.
It reuses the frozen tables' type names, context and local decoding and the
existing Source inference. Registered-call versions supply Calls.expr; future
expression extensions need no further statement traversal. The frozen v1
Tables and Spells interfaces are unchanged.
-/
namespace Solidity.Correctness.Lowering.Total.Decode.WithExpr

open Source (Syn SCtx)
variable (T : Tables) (spell : RawExpr → Option (Syn .expr))

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
/-- Statements use the supplied expression spelling and `WithExpr.simple`,
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

/-- Run the unchanged request guard, context/local decoding and Source
inference after spelling statements with the supplied expression decoder. -/
def decode (r : Request) : Option SourceProgram :=
  if plain r then do
    let C ← T.context r
    let L ← T.locals r.input.before.locals.1
    let b ← items T spell .body r.input.raw
    let ⟨L', d⟩ ← Source.ItemsD.infer C L b
    pure ⟨C.env, C.rets, C.inModifier, .body, Source.tysOf L, Source.tysOf L', d.toR⟩
  else none

/-- Supplying a new expression spelling cannot bypass the existing request
guard. This preserves the guard; it does not prove producer success. -/
theorem decode_guard {r : Request} {s : SourceProgram}
    (h : decode T spell r = some s) : plain r = true := by
  unfold decode at h
  split at h
  · assumption
  · cases h

variable (T : Tables)

theorem update_original (b : List RawStmt) : update T.expr b = T.update b := rfl

theorem simple_original (s : RawStmt) : simple T T.expr s = T.simple s := rfl

theorem initializer_original (b : List RawStmt) :
    initializer T T.expr b = T.initializer b := rfl

mutual
theorem stmt_original : (k : SCtx) → (s : RawStmt) → stmt T T.expr k s = T.stmt k s
  | k, .ite c thn [] => by simp [Tables.stmt, stmt, items_original k thn]
  | k, .ite c thn (e :: els) => by
      simp [Tables.stmt, stmt, items_original k thn, items_original k (e :: els)]
  | k, .ret none | k, .ret (some _) => by simp [Tables.stmt, stmt]
  | k, .block b => by simp [Tables.stmt, stmt, items_original k b]
  | k, .whileLoop _ c b | k, .loop _ c b | k, .doWhile _ b c => by
      simp [Tables.stmt, stmt, items_original ⟨true, k.unchecked⟩ b]
  | k, .forLoop _ init c upd b => by
      cases c <;> simp only [Tables.stmt, stmt, update_original,
        items_original ⟨true, k.unchecked⟩ b, initializer_original]
  | k, .brk | k, .cont => by simp [Tables.stmt, stmt]
  | k, (.assign ..) | k, (.decl ..) | k, (.declStorage ..) | k, (.declMemory ..)
  | k, (.delete ..) | k, (.opAssign ..) | k, (.incDec ..) | k, (.pushOpAssign ..)
  | k, (.pushIncDec ..) | k, (.call ..) | k, (.assignIncDec ..) | k, (.assignPush ..)
  | k, (.declStoragePush ..) | k, (.declPush ..) | k, (.require ..) | k, (.assert ..)
  | k, .revert | k, (.revertMsg ..) | k, (.requireMsg ..) | k, (.revertReason ..)
  | k, (.requireReason ..) | k, (.revertRaw ..) | k, (.revertErr ..) | k, (.requireErr ..)
  | k, .assumeFalse | k, (.eval ..) | k, (.unchecked ..) | k, (.checked ..) | k, (.tryCall ..)
  | k, (.send ..) | k, (.tupleDecl ..) | k, (.tupleAssign ..) | k, .hole => by
      simp [Tables.stmt, stmt, simple_original]
theorem items_original : (k : SCtx) → (b : List RawStmt) → items T T.expr k b = T.items k b
  | k, [] => by simp [Tables.items, items]
  | k, .unchecked b :: rest => by
      simp [Tables.items, items, items_original ⟨k.loop, true⟩ b, items_original k rest]
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
      simp [Tables.items, items, stmt_original, items_original k rest]
end


/-- With the old expression decoder, the complete request decoder is exactly
v1, including its admission guard and inferred Source program. -/
theorem decode_original (r : Request) : decode T T.expr r = T.decode r := by
  simp only [decode, Tables.decode, items_original]

end Solidity.Correctness.Lowering.Total.Decode.WithExpr

namespace Solidity.Correctness.Lowering.Total.Decode.Calls

/-- The registered-call request decoder uses the one expression-parameterized
statement traversal. Semantic registry faithfulness remains a separate proof. -/
def decode (T : Tables) (R : CallSpellExt.Registry) : Request → Option SourceProgram :=
  WithExpr.decode T (expr T R)

/-- An empty registry recovers the complete frozen decoder, not just its
expression results. -/
theorem decode_empty (T : Tables) (r : Request) : decode T [] r = T.decode r := by
  have same : expr T [] = T.expr := by
    funext e
    apply Option.ext
    intro t
    exact (conformsX e t).trans ((empty_spelling T e t).trans
      ⟨Spells.ExprT.decode, Spells.expr_spellsT e t⟩)
  simp only [decode, same, WithExpr.decode_original]

end Solidity.Correctness.Lowering.Total.Decode.Calls
