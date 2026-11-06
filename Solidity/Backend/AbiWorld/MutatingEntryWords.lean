import Solidity.Backend.InternalFlow.RuntimeFrameV3MutatingActivation
import Solidity.Backend.AbiWorld.NativeParentWord

/-! Ordered ABI observation of a MUTATED old array element and child counter
at the SAME actual allocating frame entry. No Heap.Keeps of the original heap
is assumed: only the real allocation keeps the already mutated heap. These are
pure observations after write/entry, not runtime byte emission or call returns. -/
namespace Solidity.Backend.AbiWorld.MutatingEntryWords
open Solidity Evm Evm.Memory
open Solidity.Backend.InternalFlow.RuntimeFrame
open RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes
abbrev A := MutatingActivation.A

def pair (n : Nat) (fit : n+1<W) := ReturnWordTransport.values
 [NativeParentWord.uintWord (n+1) fit,NativeParentWord.uintWord n (by omega)]

theorem layout (n : Nat) (fit : n+1<W) :
 AbiEntry.encodeArgs (pair n fit)=AbiEntry.wordBytes (n+1)++AbiEntry.wordBytes n := by
 simp only [pair,ReturnWordTransport.encoded_values,List.flatMap_cons,List.flatMap_nil,List.append_nil,NativeParentWord.uintWord]

theorem readback (n : Nat) (fit : n+1<W) (suffix : List UInt8) :
 ExternalReturnBytes.words 2 (AbiEntry.encodeArgs (pair n fit)++suffix)=
 .ok [ReturnWordTransport.semanticWord (NativeParentWord.uintWord (n+1) fit),
  ReturnWordTransport.semanticWord (NativeParentWord.uintWord n (by omega))] :=
 ReturnWordTransport.words_readback [NativeParentWord.uintWord (n+1) fit,NativeParentWord.uintWord n (by omega)] suffix

theorem allocated_read {C : Contract} (σ : State C (Parameters A)) (n : Nat) (fit : n+1<W)
 (ref : HRef σ.H A) (within : n<σ.heap.len ref .dyn) :
 let mutated := MutatingActivation.changed σ ref n
 (AllocatingActivation.allocated mutated).heap.readAddr
 (.index (ref.wk (AllocatingActivation.extension mutated)) .dyn (countValue n (by omega)))=some σ.env.1 := by
 have wrote := MutatingActivation.write_addr σ ref n (by omega) within
 have actual := Heap.readAddr_writeAddr_same wrote
 have kept : Heap.Keeps (AllocatingActivation.extension (MutatingActivation.changed σ ref n))
  (MutatingActivation.changed σ ref n).heap (AllocatingActivation.allocated (MutatingActivation.changed σ ref n)).heap :=
  Heap.keeps_alloc (MutatingActivation.changed σ ref n).heap
  (AllocatingActivation.object (MutatingActivation.changed σ ref n))
 have inherited := kept.readAddr (.index ref .dyn (countValue n (by omega)))
 rw [actual] at inherited
 exact inherited

theorem represented_element {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (σ : State C (Parameters A)) (base : Nat → Fin W) (machine : Machine)
 (ref : HRef σ.H A) (i k : Nat) (ib : i<W) (kb : k<W)
 (repr : StateRepr L b frame F σ base machine)
 (read : σ.heap.readAddr (.index ref .dyn (countValue i ib))=some (countValue k kb)) :
 machine.mem ((base ref.id).val+1+i)=.val (wmod k) ∧ (base ref.id).val+1+i<W := by
 simp only [Heap.readAddr,Heap.index,countValue,indexValue,Int.toNat_natCast] at read
 have represented := (repr.heap.arrays ref).elements i (countValue k kb) read
 have within : i<σ.heap.len ref .dyn := (List.getElem?_eq_some_iff.mp read).1
 have space := (repr.heap.arrays ref).space
 refine ⟨?_,by omega⟩
 have exactWord : machine.mem ((base ref.id).val+1+i)=.val ⟨k,kb⟩ :=
  Restore.uint_unique represented (ReprV.uint_of rfl)
 simpa only [wmod,Nat.mod_eq_of_lt kb] using exactWord

theorem observed_activation {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (σ : State C (Parameters A)) (n : Nat) (fit : n+1<W) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue (n+1) fit)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (within : n<σ.heap.len ref .dyn)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (cursor : Fin W) (owner : StructAllocatorRepr σ.heap base frame cursor before)
 (positive : 0<b) (heapSpace : cursor.val+4<W)
 (lo pointer start : Nat) (localBound : b+2<lo) (pointerAbove : lo≤pointer)
 (pointerBelow : pointer<frame) (payloadAbove : lo≤start) (payloadBelow : start+2≤frame)
 (pointerBefore : pointer<start) (fits : start+2<W)
 (suffix : List UInt8)
 (current : before.mem pointer=.val (wmod start)) :
 let mutated := MutatingActivation.changed σ ref n
 let parent := AllocatingActivation.allocated mutated
 let child := parent.withEnv (Δ:=Parameters A)
   (countValue n (by omega),(some (ref.wk (AllocatingActivation.extension mutated)),()))
 ∃ (word : Word) (after : Machine) (addresses : Nat → Fin W),
 ReprV .uint σ.env.1 word ∧
 (MutatingActivation.write (C:=C)).run σ=.ok ⟨mutated,List.prefix_refl _⟩ ∧
 (nextArgs A rfl).evalT parent=.ok child.env ∧
 ((CallRet.none : CallRet (Parameters A) [] (Parameters A)).enterT (parent.withEnv child.env)).st=child ∧
 run (MutatingActivation.code (C:=C) b F pointer) before=.ok after 0 ∧
 StateRepr L b frame F child addresses after ∧ after.stack=before.stack ∧
 BaseExtends σ.H base addresses ∧ GrowsAllocator b frame 4 σ base before child addresses after ∧
 after.mem pointer=.val (wmod (start+2)) ∧
 (∀ i,i<2 → after.mem (start+i)=before.mem (b+i)) ∧
 (∀ x,0<x → x<frame → x≠b+1 → x≠b+2 → x≠pointer →
   (x<start ∨ start+2≤x) → after.mem x=before.mem x) ∧
 (∀ x,x≠pointer → x≠b+1 → (x<start ∨ start+2≤x) →
   after.mem x=(writeMachine (allocateMachine (writeMachine before ((base ref.id).val+1+n) word)
     cursor AllocatingActivation.size) (cell (b+2)) (.val cursor)).mem x) ∧
 child.heap.readAddr (.index (ref.wk (AllocatingActivation.extension mutated)) .dyn (countValue n (by omega)))=some σ.env.1 ∧
 after.mem ((base ref.id).val+1+n)=.val (wmod (n+1)) ∧
 (base ref.id).val+1+n<W ∧
 after.mem (lvl b (.here : Idx (Parameters A) (.val .uint)))=.val (wmod n) ∧
 after.mem (cellOf b (.there .here : Idx (Parameters A) (.mem A)))=.val (base ref.id) ∧
 AbiEntry.encodeArgs (pair n fit)=AbiEntry.wordBytes (n+1)++AbiEntry.wordBytes n ∧
 ExternalReturnBytes.words 2 (AbiEntry.encodeArgs (pair n fit)++suffix)=
 .ok [ReturnWordTransport.semanticWord (NativeParentWord.uintWord (n+1) fit),
  ReturnWordTransport.semanticWord (NativeParentWord.uintWord n (by omega))] := by
 obtain ⟨word,after,addresses,wordRepr,source,args,entry,actual,represented,stack,extended,growth,newPointer,payload,low,exterior⟩ :=
  MutatingActivation.activation σ n fit ref counter alias within base before repr cursor owner positive heapSpace
   lo pointer start localBound pointerAbove pointerBelow payloadAbove payloadBelow pointerBefore fits current
 have read := allocated_read σ n fit ref within
 have changedRead : (AllocatingActivation.allocated (MutatingActivation.changed σ ref n)).heap.readAddr
  (.index (ref.wk (AllocatingActivation.extension (MutatingActivation.changed σ ref n))) .dyn (countValue n (by omega)))=
  some (countValue (n+1) fit) := by rw [read];exact congrArg some counter
 have cells := represented_element _ addresses after _ n (n+1) (by omega) fit represented changedRead
 have oldBase := extended ref
 have childWord := NativeParentWord.represented_counter _ addresses after n (by omega) represented rfl
 obtain ⟨aliasRef,same,pointerWord⟩ := represented.pointers (.there .here : Idx (Parameters A) (.mem A))
 have sameRef : aliasRef=ref.wk (AllocatingActivation.extension (MutatingActivation.changed σ ref n)) := Option.some.inj same.symm
 subst aliasRef
 refine ⟨word,after,addresses,wordRepr,source,args,entry,actual,represented,stack,extended,growth,newPointer,payload,low,exterior,
  read,?_,?_,childWord,?_,layout n fit,readback n fit suffix⟩
 · simpa only [HRef.wk, oldBase] using cells.1
 · simpa only [HRef.wk, oldBase] using cells.2
 · simpa only [HRef.wk, oldBase] using pointerWord

end Solidity.Backend.AbiWorld.MutatingEntryWords
