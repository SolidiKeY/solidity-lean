import Solidity.Yul.Views.ResidualMcopy
import Solidity.Yul.Views.ResidualWindowControls

namespace Solidity.Yul.Views.ResidualMcopyControls
open Controls ResidualWindowControls

/-- Real six-object heap geometry derives every window in this residual gap. -/
def gapWindow (destination size : Roadmap.Word) (low : 192≤destination.val)
    (high : destination.val+size.val≤384) : ResidualWindowPlan mixedPlacement :=
  ⟨destination,size,generatedHeapEntries mixedPlacement,generated_mixed_prepared,
    (residualWindowCheck_iff _ _ _ _).mpr ⟨by have bound:=destination.isLt; omega,
      Or.inr (Or.inr (by omega)),by
      intro e member
      by_cases zero : e.id=0
      · have fits:=e.image.fits mixedPlacement e.id e.found
        rw [zero] at fits
        change e.image.span≤64 at fits
        exact Or.inr (Or.inr (Or.inr (by change 128+e.id*256+e.image.span≤destination.val; omega)))
      · exact Or.inr (Or.inr (Or.inl (by change destination.val+size.val≤128+e.id*256; omega)))⟩⟩

def seedCopy : ResidualCopyRequest mixedPlacement := ⟨gapWindow 220 3 (by decide) (by decide),160,Or.inr (by decide)⟩
def forwardCopy : ResidualCopyRequest mixedPlacement := ⟨gapWindow 221 3 (by decide) (by decide),220,Or.inr (by decide)⟩
def backwardCopy : ResidualCopyRequest mixedPlacement := ⟨gapWindow 220 3 (by decide) (by decide),221,Or.inr (by decide)⟩
def noCopy : ResidualCopyRequest mixedPlacement := ⟨zeroPlan,highestUint,Or.inl rfl⟩
def copies : List (ResidualCopyRequest mixedPlacement) := [seedCopy,forwardCopy,backwardCopy,noCopy]

/-- Read laws avoid evaluating opaque dependent image transports. -/
theorem gap_byte (residual : ByteView) (a : Nat) (low : 192≤a) (high : a<384) :
    residualCopyPhysical mixedPlacement residual a=residual a := by
  apply encodeMixedHeap_residual
  intro e member
  by_cases zero : e.id=0
  · have fits:=e.image.fits mixedPlacement e.id e.found
    rw [zero] at fits
    change e.image.span≤64 at fits
    exact Or.inr (by change 128+e.id*256+e.image.span≤a; omega)
  · exact Or.inl (by change a<128+e.id*256; omega)

theorem child_byte (residual : ByteView) (i : Nat) (bound : i<3) :
    residualCopyPhysical mixedPlacement residual (160+i)=calldataBytes mixedChild i := by
  have cases : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases cases with rfl | rfl | rfl
  · exact encodeMixedHeap_source_byte mixedPlacement _ (generatedHeapEntries_nodup _) generated_mixed_coverage
      residual 0 (.bytes .memory) (.bytes mixedChild) rfl 32 0x11 (.bytes mixedChild ⟨0,by decide⟩)
  · exact encodeMixedHeap_source_byte mixedPlacement _ (generatedHeapEntries_nodup _) generated_mixed_coverage
      residual 0 (.bytes .memory) (.bytes mixedChild) rfl 33 0x22 (.bytes mixedChild ⟨1,by decide⟩)
  · exact encodeMixedHeap_source_byte mixedPlacement _ (generatedHeapEntries_nodup _) generated_mixed_coverage
      residual 0 (.bytes .memory) (.bytes mixedChild) rfl 34 0x33 (.bytes mixedChild ⟨2,by decide⟩)

theorem seed_apply (residual : ByteView) : seedCopy.apply residual=copyBytes residual (calldataBytes mixedChild) 220 0 3 := by
  funext a
  change (if 220≤a ∧ a<220+3 then residualCopyPhysical mixedPlacement residual (160+(a-220)) else residual a)=_
  unfold copyBytes
  split
  · rename_i inside
    have bound : a-220<3 := by omega
    simpa only [Nat.zero_add] using child_byte residual (a-220) bound
  · rfl

theorem forward_apply (residual : ByteView) : forwardCopy.apply residual=mcopy residual 221 220 3 := by
  funext a
  change (if 221≤a ∧ a<221+3 then residualCopyPhysical mixedPlacement residual (220+(a-221)) else residual a)=_
  unfold mcopy copyBytes
  split
  · rename_i inside
    exact gap_byte residual _ (by omega) (by omega)
  · rfl

theorem backward_apply (residual : ByteView) : backwardCopy.apply residual=mcopy residual 220 221 3 := by
  funext a
  change (if 220≤a ∧ a<220+3 then residualCopyPhysical mixedPlacement residual (221+(a-220)) else residual a)=_
  unfold mcopy copyBytes
  split
  · rename_i inside
    exact gap_byte residual _ (by omega) (by omega)
  · rfl

theorem no_copy (residual : ByteView) : noCopy.apply residual=residual := copyBytes_zero _ _ _ _

theorem seed_reads_actual_object : readBytes (seedCopy.apply mixedResidual) 219 6=
    [0xa5,0x11,0x22,0x33,0xa5,0xa5] := by rw [seed_apply]; decide

theorem forward_snapshot_overlap : readBytes (residualCopies [seedCopy,forwardCopy] mixedResidual) 219 6=
    [0xa5,0x11,0x11,0x22,0x33,0xa5] := by
  simp only [residualCopies,seed_apply,forward_apply]
  decide

theorem backward_snapshot_overlap : readBytes (residualCopies copies mixedResidual) 219 6=
    [0xa5,0x11,0x22,0x33,0x33,0xa5] := by
  simp only [copies,residualCopies,seed_apply,forward_apply,backward_apply,no_copy]
  decide

theorem chronological_not_initial :
    readBytes (forwardCopy.apply mixedResidual) 220 4≠
      readBytes (residualCopies [seedCopy,forwardCopy] mixedResidual) 220 4 := by
  simp only [residualCopies,seed_apply,forward_apply]
  decide

theorem chronological_not_reverse :
    readBytes (residualCopies copies mixedResidual) 220 4≠
      readBytes (residualCopies copies.reverse mixedResidual) 220 4 := by
  change readBytes (residualCopies [seedCopy,forwardCopy,backwardCopy,noCopy] mixedResidual) 220 4≠
    readBytes (residualCopies [noCopy,backwardCopy,forwardCopy,seedCopy] mixedResidual) 220 4
  simp only [residualCopies,seed_apply,forward_apply,backward_apply,no_copy]
  decide

theorem whole_map : residualCopyPhysical mixedPlacement (residualCopies copies mixedResidual)=
    physicalCopies copies (residualCopyPhysical mixedPlacement mixedResidual) := residualCopies_physical _ _

theorem whole_source : residualCopiesWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _)
    copies mixedResidual=.ok (some ((.ok (),mixedState),residualCopies copies mixedResidual)) :=
  residualCopiesWriteback_exact mixedState mixedPlacement mixedPlacement (retainInitial _ _) copies mixedResidual
    generated_mixed_types_supported generated_mixed_prepared

theorem every_original_H (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H mixedState) :
    ∃ after, residualCopiesWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _) copies mixedResidual=
      .ok (some after) ∧ Source.MemOK mixedEnv H after.1.2 :=
  residualCopiesWriteback_every_H H mixedState mixedPlacement mixedPlacement (retainInitial _ _) copies mixedResidual
    generated_mixed_types_supported ok

theorem every_actual_prefix (before : List (ResidualCopyRequest mixedPlacement)) (request : ResidualCopyRequest mixedPlacement) :
    residualMemoryWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _) request.window
      (residualCopies before mixedResidual) (residualCopyPhysical mixedPlacement (residualCopies before mixedResidual)) request.source.val=
        .ok (some ((.ok (),mixedState),residualCopies (before++[request]) mixedResidual)) :=
  residualCopies_prefix_step mixedState mixedPlacement mixedPlacement (retainInitial _ _) before request mixedResidual
    generated_mixed_types_supported

theorem reserved : ReservedOK (residualCopies copies mixedResidual) 1664 :=
  residualCopies_reserved copies mixedResidual mixed_reserved_initial

theorem unknown_tail : residualCopies copies mixedResidual 225=mixedResidual 225 := by
  apply residualCopies_outside
  intro request member
  simp only [copies,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide

theorem aliases_at_every_horizon (horizon : Nat) :
    (Source.bytesOfRV (E:=mixedEnv) mixedReadFrame horizon (.val (mixedState.1.get .here))).run mixedState=(.ok mixedChild,mixedState) ∧
    (Source.bytesOfRV (E:=mixedEnv) mixedReadFrame horizon (.val (mixedState.1.get (.there .here)))).run mixedState=(.ok mixedChild,mixedState) :=
  mixed_source_alias_reads horizon

/-- Existing range conditions distinguish an empty high-address read from a
nonempty wrap. These are arithmetic preparation boundaries, not verdicts. -/
theorem whole_result_aliases (horizon : Nat) : ∃ after,
    residualCopiesWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _) copies mixedResidual=.ok (some after) ∧
    (Source.bytesOfRV (E:=mixedEnv) mixedReadFrame horizon (.val (after.1.2.1.get .here))).run after.1.2=(.ok mixedChild,after.1.2) ∧
    (Source.bytesOfRV (E:=mixedEnv) mixedReadFrame horizon (.val (after.1.2.1.get (.there .here)))).run after.1.2=(.ok mixedChild,after.1.2) :=
  ⟨((.ok (),mixedState),residualCopies copies mixedResidual),whole_source,mixed_source_alias_reads horizon⟩

theorem empty_source_bound : ValidRange highestUint.val 0 := Or.inl rfl
theorem nonempty_source_wrap : ¬ValidRange highestUint.val 2 := by
  change ¬(2=0 ∨ 2^256-1+2≤2^256)
  omega

end Solidity.Yul.Views.ResidualMcopyControls
