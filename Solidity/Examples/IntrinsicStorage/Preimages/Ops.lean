import Solidity.Semantics.IntrinsicStorage.Preimages.Ops

namespace Solidity.Examples.IntrinsicStorage.Preimages.Ops
open Solidity.Semantics Solidity.Semantics.IntrinsicStorage Solidity.Storage

-- A failed actual storage read skips its continuation without losing the audit.
example {C : Contract} {T : Ty} (st : Solidity.Storage C) (r : SRef C T)
    (e : THalt) (h : TRes.ofOpt (st.find r) = .error e) (f : SVal T → Audit Nat) :
    (Audit.read st r >>= f).result = .error e ∧
    (Audit.read st r >>= f).inputs = (Audit.read st r).inputs := by
  constructor
  · rw [Audit.result_bind, Audit.result_read, h]
    rfl
  · exact Audit.failed_bind _ f ((Audit.result_read st r).trans h)

example {C : Contract} {T : Ty} (st : Solidity.Storage C) (r : SRef C T)
    {v : SVal T} (hv : st.find r = some v) {p : Pre}
    (hp : ValueInput v (reference r) p) (e : THalt) :
    encoded p ∈ (Audit.follow (Audit.read st r)
      (fun _ => (Audit.lift (.error e) : Audit Nat))).inputs.hashed := by
  apply Inputs.slot_hashed
  exact Audit.follow_slots _ _ (Audit.read_value st r hv hp)

-- Both overwritten and replacement aggregate preimages survive a later operation.
example {C : Contract} {T : Ty} (st : Solidity.Storage C) (r : SRef C T)
    (v old : SVal T) (hv : st.find r = some old) {p q : Pre}
    (hp : ValueInput old (reference r) p) (hq : ValueInput v (reference r) q)
    (f : Solidity.Storage C → Audit Nat) :
    encoded p ∈ (Audit.write st r v >>= f).inputs.hashed ∧
    encoded q ∈ (Audit.write st r v >>= f).inputs.hashed := by
  constructor
  · exact Inputs.slot_hashed _ (Audit.bind_slots_left _ _ (Audit.write_old st r v hv hp))
  · exact Inputs.slot_hashed _ (Audit.bind_slots_left _ _ (Audit.write_value st r v hq))

-- A successful read followed by a write includes the write destination preimages.
example {C : Contract} {T : Ty} (st : Solidity.Storage C) (src dst : SRef C T)
    {v : SVal T} (hv : st.find src = some v) {p : Pre}
    (hp : ValueInput v (reference dst) p) :
    encoded p ∈ (Audit.read st src >>= fun x => Audit.write st dst x).inputs.hashed := by
  apply Inputs.slot_hashed
  apply Audit.bind_slots_right (x := v)
  · rw [Audit.result_read, hv]
    rfl
  · exact Audit.write_value st dst v hp

end Solidity.Examples.IntrinsicStorage.Preimages.Ops
