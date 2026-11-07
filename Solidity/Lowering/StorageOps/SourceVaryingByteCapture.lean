import Solidity.Lowering.StorageOps.SourceNestedByteValues

/-! Actual nested capture prefixes with independently varying child lengths.
Per-child inequalities state the ORIGINAL runtime fuel needed by successful
captures and the final failure. They impose no admitted-source length cap. -/
namespace Solidity.Lowering.StorageOps.SourceVaryingByteCapture
open Solidity Solidity.Backend.StorageOps

/-- Exact heap prefix for varying runtime lengths and distinct OLD payloads.
The existing typed allocation callback is reused; no new evaluator is defined. -/
theorem timeout_prefix : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (path : Solidity.Source.SPath) (start count budget : Nat)
 (length : Nat → Nat) (payload : Nat → Nat → UInt8)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_enough : ∀ j<count,length (start+j)<count+budget-j)
 (_short : budget≤length (start+count))
 (_headers : ∀ j<count+1,(Solidity.Source.readLen (E:=E) (Γ:=Γ) frame (path.go (.index (start+j)))).run (locals,state)=
  (.ok (length (start+j)),(locals,state)))
 (_reads : ∀ j<count+1,∀ k<length (start+j),(Solidity.Source.readAt (E:=E) (Γ:=Γ) frame ((path.go (.index (start+j))).go (.index k)) (.fixedBytes 1 (by decide))).run (locals,state)=
  (.ok (Solidity.Source.Val.fixedBytes (n:=1) (h:=by decide) [payload (start+j) k] rfl),(locals,state))),
 (Solidity.Source.loadElems (E:=E) (Γ:=Γ) frame (count+budget+3) (.bytes .memory) path start (count+1)).run (locals,state)=
 (.error .timeout,(locals,(List.range' start count).foldl
  (fun state j=>Solidity.Lowering.StorageOps.SourceNestedByteValues.allocateAt (length j) payload state j) state)) := by
 intro E Γ frame path start count budget length payload locals state enough short headers reads
 induction count generalizing start state with
 | zero =>
   have header := headers 0 (by omega)
   simp only [Nat.add_zero] at header short
   simp only [Nat.zero_add,Source.loadElems,Source.loadElem,Source.STy.byRef,Source.STy.loc?,
     Option.isSome_some,if_true,Source.loadMem,Source.Hoare.run_bind,header]
   rw [Solidity.Lowering.StorageOps.SourceByteStorageBarrier.load_timeout frame
     (path.go (.index start)) budget 0 (length start) (payload start) (locals,state) short (by
       simpa only [Nat.add_zero,Nat.zero_add] using reads 0 (by omega))]
   rfl
 | succ count ih =>
   have total : count+1+budget+3=(count+budget+3)+1 := by omega
   rw [total]
   change ((Source.loadElem frame (count+budget+3) (.bytes .memory) (path.go (.index start)) >>= fun x =>
     Source.loadElems frame (count+budget+3) (.bytes .memory) path (start+1) (count+1) >>= fun xs =>
     pure (Source.finCons (.val x) xs)).run (locals,state))=_
   have header := headers 0 (by omega)
   simp only [Nat.add_zero] at header
   have valid := enough 0 (by omega)
   simp only [Nat.add_zero,Nat.sub_zero] at valid
   have fuel : length start+(count+budget-length start)+3=count+budget+3 := by omega
   have first := SourceNestedByteValues.capture frame (path.go (.index start)) (length start)
     (count+budget-length start) (payload start) locals state header (by
       simpa only [Nat.add_zero] using reads 0 (by omega))
   rw [fuel] at first
   change (Source.loadElem frame (count+budget+3) (.bytes .memory) (path.go (.index start))).run (locals,state)=
     (.ok (Source.Val.memRef (τ:=.bytes .memory) rfl state.heap.next),
       (locals,SourceNestedByteValues.allocateAt (length start) payload state start)) at first
   rw [Source.Hoare.run_bind,first]
   dsimp only
   rw [Source.Hoare.run_bind,ih (start+1)
     (SourceNestedByteValues.allocateAt (length start) payload state start) (by
       intro j member
       have found := enough (j+1) (by omega)
       have index : start+(j+1)=(start+1)+j := by omega
       rw [index] at found
       omega) (by
       have index : start+(count+1)=(start+1)+count := by omega
       simpa only [index] using short) (by
       intro j member
       rw [SourceReadFrames.readLen_transport frame (path.go (.index ((start+1)+j))) locals state
         (SourceNestedByteValues.allocateAt (length start) payload state start) rfl rfl]
       have found := headers (j+1) (by omega)
       have index : start+(j+1)=(start+1)+j := by omega
       rw [index] at found
       rw [found]) (by
       intro j member k bound
       rw [SourceReadFrames.readAt_transport frame ((path.go (.index ((start+1)+j))).go (.index k))
         (.fixedBytes 1 (by decide)) locals state
         (SourceNestedByteValues.allocateAt (length start) payload state start) rfl rfl]
       have index : start+(j+1)=(start+1)+j := by omega
       have oldBound : k<length (start+(j+1)) := by simpa only [index] using bound
       have found := reads (j+1) (by omega) k oldBound
       rw [index] at found
       rw [found])]
   simp only [List.range'_succ,List.foldl_cons]

/-- info: 'Solidity.Lowering.StorageOps.SourceVaryingByteCapture.timeout_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms timeout_prefix
end Solidity.Lowering.StorageOps.SourceVaryingByteCapture
