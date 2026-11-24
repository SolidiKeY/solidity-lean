import Solidity.Correctness.Lowering.Total.Decode.Calls

/-!
Request decoding with registered expression spelling. The statement traversal
is shared with `Tables`: its ordinary entry points specialize that traversal
to `Tables.expr`, while registered calls supply `Calls.expr`. Context decoding,
local decoding, the request guard and Source inference are shared unchanged.
-/
namespace Solidity.Correctness.Lowering.Total.Decode.WithExpr

open Source (Syn SCtx)
variable (T : Tables) (spell : RawExpr → Option (Syn .expr))

abbrev simple := Tables.WithExpr.simple
abbrev update := Tables.WithExpr.update
abbrev initializer := Tables.WithExpr.initializer
abbrev stmt := Tables.WithExpr.stmt
abbrev items := Tables.WithExpr.items

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

theorem stmt_original (k : SCtx) (s : RawStmt) :
    stmt T T.expr k s = T.stmt k s := rfl

theorem items_original (k : SCtx) (b : List RawStmt) :
    items T T.expr k b = T.items k b := rfl

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
