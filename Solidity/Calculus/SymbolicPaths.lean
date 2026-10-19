import Solidity.Calculus.DecideEval

/-!
# Recognizing existing typed paths without evaluating their keys

Root, field and index syntax becomes the closer's existing `SPath`.
Keys stay as their original terms, so failed computations and read-dependent
locations retain their meaning. Recognition does not assert that an array
location is present or that a key evaluates successfully.
-/

namespace Solidity.Decide

open Semantics

variable {C : Contract}

/-- An existing path term and the closer's symbolic view have exactly the
same optional evaluation in every typed state and atom environment. -/
structure SPath.View {T : Ty} (t : LTm C (.path T)) where
  path : SPath C T
  correct : ∀ (g : State C []) (ν : AEnv), path.eval g ν = t.eval g ν

def SPath.viewFuel? : Nat → {T : Ty} → (t : LTm C (.path T)) → Option (SPath.View t)
  | 0, _, _ => none
  | _ + 1, _, .app0 (.root r h) => some ⟨⟨r, h, .nil⟩, fun _ _ => rfl⟩
  | fuel + 1, _, .app1 (.field h) q => do
    let p ← SPath.viewFuel? fuel q
    return ⟨p.path.snoc (.field h .nil), by
      intro g ν
      rw [SPath.eval_snoc, p.correct g ν, TSegs.eval_field, TSegs.eval_nil, LTm.eval_field]
      cases q.eval g ν <;> rfl⟩
  | fuel + 1, _, .index it q k => do
    let p ← SPath.viewFuel? fuel q
    return ⟨p.path.snoc (TSegs.ofIndex it k), by
      intro g ν
      rw [SPath.eval_snoc, p.correct g ν, TSegs.eval_ofIndex, LTm.eval_index]
      cases q.eval g ν <;> cases k.eval g ν <;> rfl⟩
  | _ + 1, _, _ => none

/-- Bounded recognition of existing rooted syntax. Keys are retained,
rather than evaluated or made into independent constants. -/
def SPath.view? {T : Ty} (t : LTm C (.path T)) : Option (SPath.View t) := SPath.viewFuel? 1024 t

end Solidity.Decide
