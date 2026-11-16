import Solidity.Semantics.IntrinsicStorage.Preimages.Ops

namespace Solidity.Examples.IntrinsicStorage.Preimages.Ops
open Solidity.Semantics Solidity.Semantics.IntrinsicStorage Solidity.Storage

example {C : Contract} {Γ : Ctx} (σ : State C Γ) {T : Ty} (s : Src C Γ T)
    (e : THalt) (h : s.valueT σ = .error e) (f : SVal T → Audit Nat) :
    (Observe.source σ s >>= f).result = .error e ∧
    (Observe.source σ s >>= f).inputs = (Observe.source σ s).inputs := by
  constructor
  · rw [Audit.result_bind, Observe.source_result, h]
    rfl
  · exact Audit.failed_bind _ f ((Observe.source_result σ s).trans h)

example {C : Contract} {T : Ty} (st : Solidity.Storage C) (r : SRef C T)
    {v : SVal T} (hv : st.find r = some v) {p : Pre}
    (hp : ValueInput v (reference r) p) (e : THalt) :
    encoded p ∈ (Audit.follow (Audit.read st r)
      (fun _ => (Audit.lift (.error e) : Audit Nat))).inputs.hashed := by
  apply Inputs.slot_hashed
  exact Audit.follow_slots _ _ (Audit.read_value st r hv hp)

end Solidity.Examples.IntrinsicStorage.Preimages.Ops
