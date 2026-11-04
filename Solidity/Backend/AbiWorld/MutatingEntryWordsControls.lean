import Solidity.Backend.AbiWorld.MutatingEntryWords

/-! A real mutating/allocating frame-entry application. Bytes below observe the
proved entered state; they do not execute a callee body or emit runtime bytes. -/
namespace Solidity.Backend.AbiWorld.MutatingEntryWordsControls
open Solidity Evm Evm.Memory
open Solidity.Backend.InternalFlow.RuntimeFrame
open RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes
open CountdownWitness
open MutatingEntryWords

theorem applied (suffix : List UInt8) : ∃ after addresses,
 StateRepr 1 2 16 F MutatingActivation.Checks.child addresses after ∧
 after.stack=MutatingActivation.Checks.before.stack ∧
 after.mem ((P.base P.r0.id).val+1+1)=w[2] ∧
 after.mem (lvl 2 (.here : Idx (Parameters MutatingEntryWords.A) (.val .uint)))=w[1] ∧
 AbiEntry.encodeArgs (pair 1 (by decide))=AbiEntry.wordBytes 2++AbiEntry.wordBytes 1 ∧
 ExternalReturnBytes.words 2 (AbiEntry.encodeArgs (pair 1 (by decide))++suffix)=
 .ok [ReturnWordTransport.semanticWord (NativeParentWord.uintWord 2 (by decide)),
 ReturnWordTransport.semanticWord (NativeParentWord.uintWord 1 (by decide))] := by
 obtain ⟨word,after,addresses,wordRepr,source,args,entry,actual,represented,stack,
 extended,growth,newPointer,payload,low,exterior,read,cells,space,childWord,aliasWord,bytes,decoded⟩ :=
  observed_activation callee 1 (by decide) P.r0 rfl rfl
  (by rw [HeapDomain.Checks.length_zero];decide)
  P.base MutatingActivation.Checks.before ParentPrefixes.Checks.initial
  (⟨22,by decide⟩ : Fin W) ParentPrefixes.Checks.ownership
  (by decide) (by decide) 8 8 10
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) suffix rfl
 exact ⟨after,addresses,represented,stack,cells,childWord,bytes,decoded⟩

theorem wrong_order : AbiEntry.encodeArgs (pair 1 (by decide))≠
 AbiEntry.wordBytes 1++AbiEntry.wordBytes 2 := by decide +kernel

theorem stale_array : AbiEntry.encodeArgs (pair 1 (by decide))≠
 AbiEntry.wordBytes 9++AbiEntry.wordBytes 1 := by decide +kernel

theorem child_is_not_mutated_element : AbiEntry.encodeArgs (pair 1 (by decide))≠
 AbiEntry.wordBytes 1++AbiEntry.wordBytes 1 := by decide +kernel

theorem no_old_heap_equality : ¬ Heap.Keeps (List.prefix_refl callee.H)
 callee.heap (MutatingActivation.changed callee P.r0 1).heap :=
 MutatingActivation.Checks.not_keeps

theorem truncated : ExternalReturnBytes.words 2
 ((AbiEntry.encodeArgs (pair 1 (by decide))).take 63)=.error .revert :=
 ReturnWordTransport.truncated [NativeParentWord.uintWord 2 (by decide),
 NativeParentWord.uintWord 1 (by decide)] (by intro impossible; cases impossible)

def render (bs : List UInt8) := "["++String.intercalate "," (bs.map (fun b=>toString b.toNat))++"]"
def row (n : Nat) (fit : n+1<W) := "{\"n\":"++toString n++",\"bytes\":"++
 render (AbiEntry.encodeArgs (pair n fit))++"}"
#eval "MUTATING_ENTRY_CODEC=["++row 1 (by decide +kernel)++"]"
#eval "PAIR_CODEC_ONLY_BOUNDARIES=["++String.intercalate ","
 [row 0 (by decide +kernel),row 299 (by decide +kernel),
 row (2^255-1) (by decide +kernel),row (2^256-2) (by decide +kernel)]++"]"
#print axioms truncated
#print axioms MutatingEntryWords.layout
#print axioms MutatingEntryWords.readback
#print axioms MutatingEntryWords.allocated_read
#print axioms MutatingEntryWords.represented_element
#print axioms MutatingEntryWords.observed_activation
#print axioms applied
#print axioms wrong_order
#print axioms stale_array
#print axioms child_is_not_mutated_element
#print axioms no_old_heap_equality
end Solidity.Backend.AbiWorld.MutatingEntryWordsControls
