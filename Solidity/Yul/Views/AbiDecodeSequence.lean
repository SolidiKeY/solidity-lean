import Solidity.Yul.Views.AbiUintArrayRun

namespace Solidity.Yul.Views

/-- Actual sequential decoder error law. Successful earlier argument effects
remain in the precise later-error state; no invented whole-call rollback. -/
theorem abiDecodeArgs_late_error {E Γ τ ts} (input : Roadmap.Bytes) (head : Nat)
    (s prior after : Source.EMState E Γ) (value : Source.Val E.layout τ) (reason : Source.Halt)
    (first : (Source.decodeArg input head τ).run s=(.ok value,prior))
    (later : (Source.decodeArgs input ts (head+1)).run prior=(.error reason,after)) :
    (Source.decodeArgs input (τ::ts) head).run s=(.error reason,after) := by
  rw [Source.decodeArgs,Source.Hoare.run_bind,first]
  change (do let tail ← Source.decodeArgs input ts (head+1)
             pure (Source.Vals.cons value tail)).run prior= _
  rw [Source.Hoare.run_bind,later]

end Solidity.Yul.Views
