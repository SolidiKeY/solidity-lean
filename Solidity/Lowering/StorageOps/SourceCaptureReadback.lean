import Solidity.Lowering.StorageOps.SourceByteCaptureSuccess

/-! Operation-generated capture heap observations. Existing typed allocation
facts discharge readbacks and old-object frames over an arbitrary finite prefix.
No source/target representation or replacement heap model is introduced. -/
namespace Solidity.Lowering.StorageOps.SourceCaptureReadback
open Solidity

/-- Every returned allocation offset contains the captured payload, while
all older objects retain their exact typed contents. -/
theorem allocation_observations : ∀ {E : Solidity.Source.Env} (state : Solidity.Source.St E) (start count : Nat)
 (length : Nat → Nat) (payload : Nat → Nat → UInt8),
 let after := (List.range' start count).foldl
  (fun state j=>Solidity.Lowering.StorageOps.SourceNestedByteValues.allocateAt (length j) payload state j) state
 after.heap.next=state.heap.next+count ∧
 (∀ a<state.heap.next,after.heap.get a=state.heap.get a) ∧
 (∀ j<count,after.heap.get (state.heap.next+j)=
  some ⟨.bytes .memory,Solidity.Source.Data.bytes ((List.range' 0 (length (start+j))).map (payload (start+j)))⟩) := by
 intro E state start count length payload
 dsimp only
 induction count generalizing start state with
 | zero =>
   simp only [List.range'_zero,List.foldl_nil,Nat.add_zero]
   exact ⟨True.intro,fun _ _=>True.intro,by intro j impossible; omega⟩
 | succ count ih =>
   simp only [List.range'_succ,List.foldl_cons]
   let first := SourceNestedByteValues.allocateAt (length start) payload state start
   have obs := ih first (start+1)
   have next : first.heap.next=state.heap.next+1 := rfl
   refine ⟨?_,?_,?_⟩
   · rw [obs.1,next]
     omega
   · intro a bound
     rw [obs.2.1 a (by rw [next]; omega)]
     change (state.heap.alloc ⟨.bytes .memory,Source.Data.bytes ((List.range' 0 (length start)).map (payload start))⟩).1.get a=state.heap.get a
     exact Source.Heap.alloc_other state.heap _ (by change a≠state.heap.next; omega)
   · intro j bound
     by_cases zero : j=0
     · subst j
       simp only [Nat.add_zero]
       rw [obs.2.1 state.heap.next (by rw [next]; omega)]
       change (state.heap.alloc ⟨.bytes .memory,Source.Data.bytes ((List.range' 0 (length start)).map (payload start))⟩).1.get state.heap.next=_
       exact Source.Heap.alloc_get state.heap _
     · have valid : j-1<count := by omega
       have address : first.heap.next+(j-1)=state.heap.next+j := by rw [next]; omega
       have index : (start+1)+(j-1)=start+j := by omega
       have found := obs.2.2 (j-1) valid
       rw [address,index] at found
       exact found

/-- info: 'Solidity.Lowering.StorageOps.SourceCaptureReadback.allocation_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms allocation_observations
end Solidity.Lowering.StorageOps.SourceCaptureReadback
