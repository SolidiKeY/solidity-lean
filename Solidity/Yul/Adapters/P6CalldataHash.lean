import Solidity.Yul.Adapters.P6Inputs
import Solidity.Yul.Views.CalldataHashBinding

/-! Concrete clipped Source-calldata conversion feeds the published P6 frame
copy and KECCAK256 micro-step. The Source allocation effect is retained.
Concrete hash agreement is an explicit SAME-input Fixed premise, not global
hash injectivity or a replacement whole-state/compiler adequacy predicate. -/
namespace Solidity.Yul.Adapters.P6CalldataHash
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views

/-- Padding adds nothing when copy length is derived from the actual source
slice. Arbitrary reference offset/declared length still use owner clipping. -/
theorem clipped_callBytes (F : Source.Fr) (off len : Nat) :
    P6Inputs.callBytes F off ((F.cd.drop off).take len).length=(F.cd.drop off).take len := by
  unfold P6Inputs.callBytes Source.fitBytes
  have bound : ((F.cd.drop off).take len).length≤(F.cd.drop off).length := by
    simp only [List.length_take]
    omega
  rw [List.take_append_of_le_length bound]
  have clipped : ((F.cd.drop off).take len).length≤len := by
    simp only [List.length_take]
    omega
  have same := List.take_length (l:=(F.cd.drop off).take len)
  rw [List.take_take,Nat.min_eq_left clipped] at same
  exact same

/-- Readback from the ACTUAL typed frame copy is exactly the Source payload. -/
theorem clipped_copy_read {C : Contract} {Γ : Ctx} (μ : FrameMem C Γ) (F : Source.Fr)
    (source : Environment.Word) (len : Nat) (destination : ByteSpan μ.capacity)
    (length : destination.length.val.toNat=((F.cd.drop source.val.toNat).take len).length) :
    Environment.readMemory (frameBytes (P6Inputs.copyCalldata μ F source destination))
      destination.offset.val.toNat destination.length.val.toNat=(F.cd.drop source.val.toNat).take len := by
  rw [P6Inputs.copy_readback,length,clipped_callBytes]

/-- All producers execute on the same actual input slice: Source implicit
allocation, P6 frame copy, and published target opcode. Capacity is supplied
by ByteSpan; target allocation/header/FMP refinement remains a separate goal. -/
theorem source_target_clipped_hash {E : Source.Env} {Ξ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Ξ)
    (index : Source.Idx Ξ (.bytes .calldata)) (source : Environment.Word) (len : Nat)
    (localValue : s.1.get index=Source.Val.cdRef rfl source.val.toNat len)
    (μ : FrameMem C Γ) (destination : ByteSpan μ.capacity) (tail : List Environment.Word)
    (length : destination.length.val.toNat=((F.cd.drop source.val.toNat).take len).length)
    (fixed : G.fixed.evm.keccak ((F.cd.drop source.val.toNat).take len)=
      Roadmap.Evm.keccakWord ((F.cd.drop source.val.toNat).take len)) :
    let bs:=(F.cd.drop source.val.toNat).take len
    let after:=objectAllocatedState s (Source.Data.bytes (l:=.memory) bs)
    let copied:=P6Inputs.copyCalldata μ F source destination
    let value:=Source.mkBytes (D:=E.layout) (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash bs))
    (Source.evalE G F (n+4) (sourceCalldataHashExpr index)).run s=(.ok (.val value),after) ∧
      Environment.cryptoStep (.op .KECCAK256)
        ⟨destination.offset::destination.length::tail,frameBytes copied⟩=
        some ⟨Environment.digest bs::tail,frameBytes copied⟩ ∧
      value.word=some (G.fixed.hash bs) ∧
      (Environment.digest bs).val.toNat=(G.fixed.hash bs).val ∧
      (∀ H : Source.HeapTy,Source.MemOK E H s → Source.MemOK E H after) ∧
      copied.st=μ.st ∧ copied.key=μ.key := by
  have bytes : P6Inputs.callBytes F source.val.toNat destination.length.val.toNat=
      (F.cd.drop source.val.toNat).take len := by rw [length,clipped_callBytes]
  have target:=P6Inputs.hash_after_copy μ F source destination tail
  rw [bytes] at target
  refine ⟨sourceCalldataHash_run G F n s index source.val.toNat len localValue,target,
    hashWord_observe E.layout _,?_,?_,(P6Inputs.copy_carrier μ F source destination).1,
    (P6Inputs.copy_carrier μ F source destination).2⟩
  · rw [Environment.digest_fixed]
    exact fixed.symm
  · intro H ok
    exact (objectAllocRef_MemOK H s (Source.Data.bytes (l:=.memory) ((F.cd.drop source.val.toNat).take len))
      rfl trivial trivial (.bytes _) ok).1
end Solidity.Yul.Adapters.P6CalldataHash
