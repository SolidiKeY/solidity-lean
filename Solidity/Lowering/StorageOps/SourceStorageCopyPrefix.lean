import Solidity.Lowering.StorageOps.SourceCopyFrames

/-! Actual distinct-path Source storage-to-storage copy at every prepared
original fuel count+padding+4. Snapshot and payload phases finish; cleanup
reuses its phase fuel. Timeout retains the exact journal prefix and OLD header;
success commits the header last. No source restriction on runtime count is
introduced. Source AST/address/compiler and eager target realization remain
separate. Published store/capture facts are reused, not reimplemented as G35. -/
namespace Solidity.Lowering.StorageOps.SourceStorageCopyPrefix
open Solidity Solidity.Backend.StorageOps
open SourceStorageCopy

theorem prepared : ∀ {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (_writable : frame.static=false)
 (t : Source.IntTy) (src dst : Source.SPath) (_different : src≠dst)
 (count oldLength padding : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) none))
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (_sourceHeader : (Source.readLen (E:=E) (Γ:=Γ) frame src).run (locals,state)=(.ok count,(locals,state)))
 (_reads : ∀ j<count,(Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index j)) (.int t)).run (locals,state)=(.ok (payload j),(locals,state)))
 (_targetHeader : (Source.readLen (E:=E) (Γ:=Γ) frame dst).run (locals,state)=(.ok oldLength,(locals,state))),
 let trace := SourceStorageCopy.copyLog frame t dst count oldLength payload typed
 let clearBudget := count+padding+1
 let result := (Source.storeVal (E:=E) (Γ:=Γ) frame (count+padding+4)
   (.array .storage (.int t) none) dst
   (Source.Val.storRef (τ:=.array .storage (.int t) none) rfl src)).run (locals,state)
 result = if oldLength-count≤clearBudget then
   (.ok (),(locals,{state with ex:=state.ex.run trace}))
 else
   (.error .timeout,(locals,{state with ex:=state.ex.run (trace.take (count+min (oldLength-count) clearBudget))})) := by
  intro E Γ frame writable t src dst different count oldLength padding payload typed locals state sourceHeader reads targetHeader
  dsimp only
  have captureFuel : count+padding+4=count+(padding+1)+3 := by omega
  rw [captureFuel,captured_copy frame t src dst different count (padding+1) payload (locals,state) sourceHeader reads]
  have phaseFuel : count+(padding+1)+2=(count+padding+2)+1 := by omega
  rw [phaseFuel]
  change ((Source.readLen frame dst >>= fun old =>
    Source.storeElems frame (count+padding+2) (.int t) dst 0 count
      (fun j : Fin count => Source.Data.val (payload j.val)) >>= fun _ =>
    Source.deleteRange frame (count+padding+2) (.int t) dst count (old-count) >>= fun _ =>
    Source.writeLen frame dst count).run (locals,state)) = _
  rw [Source.Hoare.run_bind,targetHeader]
  dsimp only
  rw [Source.Hoare.run_bind]
  have written := store_elems frame writable t dst 0 count padding payload
    (fun j => (element_type t dst typed j).symm) locals state
  simp only [Nat.zero_add] at written
  rw [written]
  dsimp only
  rw [Source.Hoare.run_bind]
  have cleanupFuel : count+padding+2=(count+padding+1)+1 := by omega
  rw [cleanupFuel,SourceScalarDeleteLog.scalar_range_prefix frame writable t dst count
    (oldLength-count) (count+padding+1)]
  by_cases done : oldLength-count≤count+padding+1
  · simp only [if_pos done,Nat.min_eq_left done]
    simp only [Source.writeLen]
    rw [write_run (E:=E) (Γ:=Γ) frame writable dst (Source.intWrap Source.IntTy.u256 count) (by
      simp only [Source.Env.cellTy,typed,Option.map_some,Source.STy.cell,Option.getD_some])]
    simp only [copyLog,Source.run_append,Source.ExecState.run]
  · have fit : count+padding+1≤oldLength-count := by omega
    simp only [if_neg done,Nat.min_eq_right fit]
    have slice :
      (copyLog frame t dst count oldLength payload typed).take (count+(count+padding+1)) =
      writes frame t dst payload (fun j => (element_type t dst typed j).symm) 0 count ++
      (List.range' count (count+padding+1)).map (fun j => SourceScalarDeleteLog.clearOp E frame (dst.go (.index j))) := by
      calc
        _ = writes frame t dst payload (fun j => (element_type t dst typed j).symm) 0 count ++
          (((List.range' count (oldLength-count)).map
            (fun j => SourceScalarDeleteLog.clearOp E frame (dst.go (.index j)))) ++
            [cellOp E frame dst (some ((by
              simp only [Source.Env.cellTy,typed,Option.map_some,Source.STy.cell,Option.getD_some] :
                (.int Source.IntTy.u256 : Source.STy)=E.cellTy dst) ▸ Source.intWrap Source.IntTy.u256 count))]).take (count+padding+1) := by
          simpa only [copyLog,SourceCopyFrames.writes_length,List.append_assoc] using
            (List.take_length_add_append
              (l₁:=writes frame t dst payload (fun j => (element_type t dst typed j).symm) 0 count)
              (l₂:=((List.range' count (oldLength-count)).map
                (fun j => SourceScalarDeleteLog.clearOp E frame (dst.go (.index j)))) ++
                [cellOp E frame dst (some ((by
                  simp only [Source.Env.cellTy,typed,Option.map_some,Source.STy.cell,Option.getD_some] :
                    (.int Source.IntTy.u256 : Source.STy)=E.cellTy dst) ▸ Source.intWrap Source.IntTy.u256 count))])
              (count+padding+1))
        _ = _ := by
          rw [List.take_append_of_le_length (by
            simpa only [List.length_map,List.length_range'] using fit)]
          rw [← List.map_take,List.take_range'_of_length_ge fit]
    rw [slice]
    simp only [Source.run_append]

/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPrefix.prepared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prepared
end Solidity.Lowering.StorageOps.SourceStorageCopyPrefix
