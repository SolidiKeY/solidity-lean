import Solidity.Lowering.Readonly.EffectRules
import Solidity.Source.Hoare

/-! Actual primitive Source memory effects for the journal induction.
Memory mutation is permitted in static mode; only the journal is preserved. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
variable {E : Env} {Γ : RCtx}

/-- Both successful heap replacement and its type-refusal branch leave the
journal intact; the captured live state is retained, not an arbitrary setSt. -/
theorem heapPut_effect (mode : Bool) (a : Nat) (x : Σ τ, Data E.layout τ) :
    Effect mode (heapPut (Γ := Γ) a x) := by
  apply Effect.of_same_ex
  intro locals state
  unfold heapPut
  rw [Hoare.run_bind]
  change (((if h : state.heap.ty a = some x.1 then
    EM.setSt {state with heap := state.heap.write a x.2 h}
    else EM.halt (.stuck "memory write type")) : EM E Γ Unit).run
      (locals, state)).2.2.ex = state.ex
  split <;> rfl

/-- Allocation changes the heap even in static mode, without a journal write. -/
theorem alloc_effect {τ : STy} (mode : Bool) (x : Data E.layout τ) :
    Effect mode (alloc (Γ := Γ) x) := by
  apply Effect.of_same_ex
  intro locals state
  rfl

end Solidity.Lowering.Readonly.SourceHistory
