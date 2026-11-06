import Solidity.Yul.Views.OwnedBoolDynamicControls
import Solidity.Yul.Views.OwnedBoolOwnershipReads

namespace Solidity.Yul.Views.Controls

theorem db_bool_member (raw : SlotView) (length : 3 < (raw 3).val) :
    pcB.element pcFixed account 3 ∈ pcLayout.primitiveSnapshot pcFixed raw :=
  pcLayout.primitive_scalar_subset pcFixed raw _
    (pcLayout.scalarFamily_element_member pcFixed raw pcBEntry 3 length)

/-- This real Source location read uses a represented codec for the OWNED byte2,
not the original boolCodec (which still rejects2). -/
theorem db_dirty_source_read_at {Γ written value s r encoding}
    (p : @RepresentedOwnershipPlan pcEnv pcTypes pcDeclarations "PC" Γ packedStepFrame pcLayout pcFixed written value s r encoding)
    {Δ : Source.RCtx} (state : Source.EMState pcEnv Δ) (sameState : state.2=p.step.1.1.2.2)
    (length : 3 < (p.nextRaw 3).val)
    (byte : (pcB.element pcFixed account 3).field.findWord (p.nextRaw (pcB.element pcFixed account 3).slot)=⟨2,by decide⟩) :
    (Source.readLoc (E:=pcEnv) packedStepFrame (Source.Loc.stor (τ:=.bool) ⟨pcName "bs",[.index 3]⟩)).run state=
      (.ok (.bool true),state) := by
  let base := pcB.element pcFixed account 3
  have member : base ∈ pcLayout.primitiveSnapshot pcFixed p.nextRaw := db_bool_member _ length
  let code := p.nextEncoding.cells (ownedByteKey false account base)
  let c := representedPath base code
  have inside : c ∈ p.next := List.mem_map.mpr ⟨base,member,rfl⟩
  have typed : pcEnv.lay account base.path=.bool := pcB.element_type 3
  have view : scalarPathView c.path c.codec c.slot (state.2.ex.world.accounts account).storage p.nextRaw := by
    rw [sameState]
    exact p.view rfl c inside
  dsimp only [c] at view
  unfold representedPath at view
  rw [dif_pos typed] at view
  obtain ⟨v,read,encoded⟩ := Option.map_eq_some_iff.mp view
  change (state.2.ex.world.accounts packedStepFrame.this).storage.read base.path=some v at read
  rw [codec_cast_encode typed] at encoded
  have truth : typed ▸ v=Source.Val.bool true := by
    apply representedBool_nonzero pcEnv.layout base.field (base.bool_width typed) code
    rw [encoded,byte]
    decide
  have raw : (Source.readCell packedStepFrame base.path).run state=(.ok v,state) := by
    unfold Source.readCell
    rw [Source.Hoare.run_bind,show (Source.EM.st (E:=pcEnv) (Γ:=Δ)).run state=(.ok state.2,state) from rfl]
    dsimp only
    rw [show pcEnv.transientRoot base.path=false from rfl]
    simp only [Bool.false_eq_true,if_false,read]
    rfl
  change (Source.readAt packedStepFrame base.path .bool).run state=_
  unfold Source.readAt
  rw [Source.Hoare.run_bind,raw]
  simp only [dif_pos typed]
  rw [truth]
  rfl

theorem db_grow_actual_read : (Source.readLoc (E:=pcEnv) packedStepFrame (Source.Loc.stor (τ:=.bool) ⟨pcName "bs",[.index 3]⟩)).run dbGrow.step.1.1.2=
    (.ok (.bool true),dbGrow.step.1.1.2) :=
  db_dirty_source_read_at dbGrow dbGrow.step.1.1.2 rfl (by rw [db_grow_next]; decide) (by rw [db_grow_next]; rfl)

theorem db_regrow_actual_read : (Source.readLoc (E:=pcEnv) packedStepFrame (Source.Loc.stor (τ:=.bool) ⟨pcName "bs",[.index 3]⟩)).run dbAgain.step.1.1.2=
    (.ok (.bool true),dbAgain.step.1.1.2) :=
  db_dirty_source_read_at dbAgain dbAgain.step.1.1.2 rfl (by rw [db_again_next]; decide) (by rw [db_again_next]; rfl)

theorem db_shrink_exact_residual : dbZero.after.residual.cells (complementKey false account 4000)=pcB0 := by
  have slice := congrFun (dbZero.complement rfl) 4000
  rw [db_zero_next] at slice
  have mask : packedMask dbZero.next dbZeroRaw 4000=pcB0 := by
    unfold RepresentedOwnershipPlan.next
    rw [db_zero_next,representedRegistry_mask]
    rfl
  exact slice.trans mask


end Solidity.Yul.Views.Controls
