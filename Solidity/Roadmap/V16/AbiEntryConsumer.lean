import Solidity.Semantics.AbiEntryProofs
import Solidity.Roadmap.V16.FiniteHeapConsumer

/-! Source-level typed decoder consumers. No solc-bytecode/V13 packet adapter,
external entry execution, global profile or lazy-readsOnly theorem is claimed. -/
namespace Solidity.Roadmap.V16
open Solidity.Evm

/-- Preserve the complete typed eager value at the actual lazy reference. -/
theorem abi_eager_observation {I : AbiEntry.Input} (size : I.size ≤ AbiEntry.lim)
    {f : Nat} {s : AbiEntry.Shape} {pos : Nat} {v : AbiEntry.Val s}
    (decoded : AbiEntry.eager I (f + 1) s pos = .ok v)
    (Q : AbiEntry.Val s → Prop) (observed : Q v) :
    ∃ addr len, AbiEntry.cref I s 4 pos = .ok (addr,len) ∧
      AbiEntry.cval I f s addr len = .ok v ∧ Q v := by
  obtain ⟨addr,len,entry,lazy⟩ := AbiEntry.eager_cref size decoded
  exact ⟨addr,len,entry,lazy,observed⟩

theorem abi_certified_revert (I : AbiEntry.Input) (f : Nat) (ps : List AbiEntry.Param)
    (revert : AbiEntry.verdict I f ps = .revert) : AbiEntry.entry I f ps = .error .revert :=
  (AbiEntry.verdict_revert_iff I f ps).mp revert

theorem abi_run_prerequisites {I : AbiEntry.Input} {f : Nat} {ps : List AbiEntry.Param}
    {vs : AbiEntry.Vals (ps.map AbiEntry.Param.shape)} (accepted : AbiEntry.verdict I f ps = .run vs) :
    ∃ es, AbiEntry.entry I f ps = .ok es ∧ AbiEntry.bodyValues I f ps es 0 = .ok vs :=
  AbiEntry.verdict_run_entry accepted

/-- A validated uint256 maps to the existing intrinsic primitive value. -/
def abiUint (v : AbiEntry.Val (.word (.uint 256))) : PrimTy.uint.Denote :=
  match v with
  | .word w => Memory.indexValue ⟨w.val,by simpa only [AbiEntry.W_eq] using w.lt⟩

/-- Only the existing intrinsic local update; no new state/execution semantics. -/
def bindAbiUint {C : Contract} {Γ : Ctx} (σ : State C Γ) (i : Idx Γ (.val .uint))
    (v : AbiEntry.Val (.word (.uint 256))) : State C Γ := σ.setLocal i (abiUint v)

/-- Actual decoder agreement plus a real compiler Input/specification. This
retains the representation obligation rather than assuming it follows from ABI
agreement. Concrete controls construct it from a kernel-decoded scalar. -/
theorem abi_uint_finite_diamond {C : Contract} {Γ Δ : Ctx} {b L frame : Nat} {F : Frag Γ}
    {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemory = true ∨ compiled.isReferenceArray = true ∨ compiled.isObject = true)
    {I : AbiEntry.Input} (size : I.size ≤ AbiEntry.lim) {f pos : Nat}
    {v : AbiEntry.Val (.word (.uint 256))}
    (decoded : AbiEntry.eager I (f + 1) (.word (.uint 256)) pos = .ok v)
    (σ : State C Γ) (i : Idx Γ (.val .uint)) {base : Nat → Fin W} {m : Machine}
    (input : compiled.Input L frame base (bindAbiUint σ i v) m) {φ : Spec C Δ}
    (body : Spec.sat (bindAbiUint σ i v) (.diamond P φ)) :
    ∃ addr len o m', AbiEntry.cref I (.word (.uint 256)) 4 pos = .ok (addr,len) ∧
      AbiEntry.cval I f (.word (.uint 256)) addr len = .ok v ∧
      P.run (bindAbiUint σ i v) = .ok o ∧ run compiled.code m = .ok m' 0 ∧
      m'.stack = m.stack ∧ compiled.Rep L frame base (bindAbiUint σ i v) m o.st m' ∧ Spec.sat o.st φ := by
  obtain ⟨addr,len,entry,lazy⟩ := AbiEntry.eager_cref size decoded
  obtain ⟨o,m',source,target,stack,rep,post⟩ := finite_heap_diamond compiled path input body
  exact ⟨addr,len,o,m',entry,lazy,source,target,stack,rep,post⟩
end Solidity.Roadmap.V16
