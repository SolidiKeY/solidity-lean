import Solidity.Lowering.Readonly.StoreEffects
import Solidity.Lowering.Readonly.ZeroEffects

/-! Primitive evaluator effects for the Source history induction. Lifting an
already computed result retains its actual halt. State modification is accepted
only with exact ex preservation; there is no arbitrary-state overwrite rule. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
variable {E : Env} {Γ : RCtx}

namespace Effect
theorem lift {α : Type} (mode : Bool) (r : R α) :
    Effect mode (EM.lift (E := E) (Γ := Γ) r) := by
  cases r <;> exact of_same_ex mode _ (fun _ _ => rfl)

theorem get (mode : Bool) :
    Effect mode (MonadStateOf.get : EM E Γ (Locals E.layout Γ × St E)) :=
  of_same_ex mode _ (fun _ _ => rfl)

theorem modSt (mode : Bool) (f : St E → St E) (same : ∀ s, (f s).ex = s.ex) :
    Effect mode (EM.modSt (Γ := Γ) f) :=
  of_same_ex mode _ (fun _ state => same state)
end Effect

end Solidity.Lowering.Readonly.SourceHistory
