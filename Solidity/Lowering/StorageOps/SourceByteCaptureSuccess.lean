import Solidity.Lowering.StorageOps.SourceVaryingByteCapture

/-! Successful actual Source capture with independently varying child lengths.
Both returned typed reference identities and full heap footprints are retained;
this is not physical pointer/address compilation or allocation-failure closure. -/
namespace Solidity.Lowering.StorageOps.SourceByteCaptureSuccess
open Solidity Solidity.Backend.StorageOps

theorem capture_all : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (path : Solidity.Source.SPath) (start count budget : Nat)
 (length : Nat → Nat) (payload : Nat → Nat → UInt8)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_enough : ∀ j<count,length (start+j)<count+budget-j)
 (_headers : ∀ j<count,(Solidity.Source.readLen (E:=E) (Γ:=Γ) frame (path.go (.index (start+j)))).run (locals,state)=
  (.ok (length (start+j)),(locals,state)))
 (_reads : ∀ j<count,∀ k<length (start+j),(Solidity.Source.readAt (E:=E) (Γ:=Γ) frame ((path.go (.index (start+j))).go (.index k)) (.fixedBytes 1 (by decide))).run (locals,state)=
  (.ok (Solidity.Source.Val.fixedBytes (n:=1) (h:=by decide) [payload (start+j) k] rfl),(locals,state))),
 (Solidity.Source.loadElems (E:=E) (Γ:=Γ) frame (count+budget+3) (.bytes .memory) path start count).run (locals,state)=
 (.ok (fun j : Fin count=>Solidity.Source.Data.val (Solidity.Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl (state.heap.next+j.val))),
  (locals,(List.range' start count).foldl
  (fun state j=>Solidity.Lowering.StorageOps.SourceNestedByteValues.allocateAt (length j) payload state j) state)) := by
 intro E Γ frame path start count budget length payload locals state enough headers reads
 induction count generalizing start state with
 | zero =>
   have empty : (Fin.elim0 : Fin 0 → Source.Data E.layout (.bytes .memory))=
     (fun j : Fin 0=>Source.Data.val (Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl (state.heap.next+j.val))) := by
     funext j
     exact Fin.elim0 j
   simp only [Source.loadElems,List.range'_zero,List.foldl_nil]
   rw [empty]
   rfl
 | succ count ih =>
   have total : count+1+budget+3=(count+budget+3)+1 := by omega
   rw [total]
   change ((Source.loadElem frame (count+budget+3) (.bytes .memory) (path.go (.index start)) >>= fun x =>
     Source.loadElems frame (count+budget+3) (.bytes .memory) path (start+1) count >>= fun xs =>
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
     (.ok (Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl state.heap.next),
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
   dsimp only
   have refs : Source.finCons
     (Source.Data.val (Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl state.heap.next))
     (fun j : Fin count=>Source.Data.val (Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl
       ((SourceNestedByteValues.allocateAt (length start) payload state start).heap.next+j.val)))=
     (fun j : Fin (count+1)=>Source.Data.val (Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl (state.heap.next+j.val))) := by
     funext j
     simp only [Source.finCons]
     split
     · rename_i zero
       simp only [zero,Nat.add_zero]
     · rename_i nonzero
       have address : (SourceNestedByteValues.allocateAt (length start) payload state start).heap.next+(j.val-1)=state.heap.next+j.val := by
         change state.heap.next+1+(j.val-1)=state.heap.next+j.val
         omega
       rw [address]
   rw [refs]
   simp only [List.range'_succ,List.foldl_cons]
   rfl

/-- info: 'Solidity.Lowering.StorageOps.SourceByteCaptureSuccess.capture_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capture_all
end Solidity.Lowering.StorageOps.SourceByteCaptureSuccess
