import Solidity.Yul.Views.FiniteWorld
import Solidity.Yul.Views.ResidualControls

/-! Heterogeneous actual-path controls. Fixed finite ownership only; raw dirty
bits remain outside canonical preparation. None is not a Yul execution verdict. -/
namespace Solidity.Yul.Views.Controls

def finiteFlag : Source.SPath := ⟨⟨some "Finite", "flag"⟩, []⟩
def finiteSmall : Source.SPath := ⟨⟨some "Finite", "small"⟩, []⟩
def finiteWide : Source.SPath := ⟨⟨some "Finite", "wide"⟩, []⟩
def finiteUnrelated : Source.SPath := ⟨⟨some "Finite", "other"⟩, []⟩
def unsigned16 : Source.IntTy := ⟨false, 16, by decide⟩
def finiteLayout (p : Source.SPath) : Source.STy :=
  if p = finiteFlag then .bool else if p = finiteSmall then .int unsigned16 else .int .u256

def flagPathCodec : ScalarPath layout finiteLayout :=
  ⟨finiteFlag, 7, boolField, boolCodec layout, .bool⟩
def smallPathCodec : ScalarPath layout finiteLayout :=
  ⟨finiteSmall, 7, intField unsigned16 1 (by decide), intCodec layout unsigned16 1 (by decide), .int unsigned16⟩
def widePathCodec : ScalarPath layout finiteLayout :=
  ⟨finiteWide, 8, intField .u256 0 (by decide), intCodec layout .u256 0 (by decide), .int .u256⟩
def finitePaths := [flagPathCodec, smallPathCodec, widePathCodec]

theorem finitePaths_separated : finiteSeparated finitePaths := by
  simp only [finiteSeparated, finitePaths, List.pairwise_cons,
    List.mem_cons, List.not_mem_nil, or_false]
  refine ⟨?_, ?_, ?_, .nil⟩
  · intro d hd
    rcases hd with rfl | rfl
    · exact ⟨by decide, Or.inr (Or.inl (by decide))⟩
    · exact ⟨by decide, Or.inl (by decide)⟩
  · intro d hd
    subst d
    exact ⟨by decide, Or.inl (by decide)⟩
  · intro d hd; cases hd

def finiteEmpty : Source.Storage layout finiteLayout := .empty
def finiteExplicitDefault := ((finiteEmpty.write finiteFlag (.bool false)).write finiteSmall (.int 0 (by decide))).write finiteWide (.int 0 (by decide))
def finiteOriginal := finiteEmpty.write finiteUnrelated (.int 55 (by decide))
def finiteTarget := ((finiteOriginal.write finiteFlag (.bool true)).write finiteSmall (.int 0x1234 (by decide))).write finiteWide (.int 0x112233 (by decide))
def finitePrefixStore := finiteOriginal.write finiteFlag (.bool true)
def finiteZeroMap : SlotView := (finiteEncode finitePaths finiteEmpty nonzeroSlots).getD nonzeroSlots
def finiteTargetMap : SlotView := (finiteEncode finitePaths finiteTarget nonzeroSlots).getD nonzeroSlots
def finitePrefixMap : SlotView := (finiteEncode finitePaths finitePrefixStore nonzeroSlots).getD nonzeroSlots

theorem finite_zero_encoded : finiteEncode finitePaths finiteEmpty nonzeroSlots = some finiteZeroMap := rfl
theorem finite_target_encoded : finiteEncode finitePaths finiteTarget nonzeroSlots = some finiteTargetMap := rfl

theorem finite_administrative_identity :
    finiteWriteback finitePaths finiteZeroMap finiteEmpty = some finiteEmpty ∧
    finiteWriteback finitePaths finiteZeroMap finiteExplicitDefault = some finiteExplicitDefault ∧
    finiteEmpty.cell finiteFlag = none ∧ finiteExplicitDefault.cell finiteFlag = some (.bool false) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem finite_default_same_encoding : finiteEncode finitePaths finiteExplicitDefault nonzeroSlots = some finiteZeroMap := rfl

theorem finite_changed_actual : finiteWriteback finitePaths finiteTargetMap finiteOriginal = some finiteTarget := rfl

theorem finite_reversed_agrees : finiteWriteback finitePaths.reverse finiteTargetMap finiteOriginal = some finiteTarget := by
  rw [finiteWriteback_reverse finitePaths finiteTargetMap finiteOriginal finitePaths_separated]
  exact finite_changed_actual

theorem finite_repeat_identity : finiteWriteback finitePaths finiteTargetMap finiteTarget = some finiteTarget :=
  finiteWriteback_idempotent finitePaths finiteTargetMap finiteOriginal finiteTarget finitePaths_separated finite_changed_actual

theorem finite_encoded_reconstruction : finiteEncode finitePaths finiteTarget finiteTargetMap = some finiteTargetMap :=
  finiteEncode_after_writeback finitePaths finiteTargetMap finiteOriginal finiteTarget finitePaths_separated finite_changed_actual

theorem finite_unrelated_actual : finiteTarget.cell finiteUnrelated = some (.int 55 (by decide)) := rfl

theorem finite_residual_padding : slotBytes finiteTargetMap (7 * 32 + 3) = slotBytes nonzeroSlots (7 * 32 + 3) :=
  finiteEncode_residual finitePaths finiteTarget nonzeroSlots finiteTargetMap finite_target_encoded _ (by decide) (by
    intro c hc
    simp only [finitePaths, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact Or.inr (Or.inr (by decide))
    · exact Or.inr (Or.inr (by decide))
    · exact Or.inl (by decide))

theorem finite_full_words :
    (finiteZeroMap 7).val = 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5000000 ∧
    (finiteTargetMap 7).val = 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5123401 ∧
    (finiteTargetMap 8).val = 0x112233 ∧ (finiteTargetMap 9).val = (nonzeroSlots 9).val := by decide

def finiteInvalidMap := patchScalarSlot finiteTargetMap 7 boolField ⟨2, by decide⟩
theorem finite_invalid_no_request :
    finiteWriteback finitePaths.reverse finiteInvalidMap finiteOriginal = none ∧
    finitePrepare finitePaths.reverse finiteInvalidMap = none := ⟨rfl, rfl⟩

theorem duplicate_path_not_separated : ¬finiteSeparated [flagPathCodec, flagPathCodec] := by
  intro h
  exact ((List.pairwise_cons.mp h).1 flagPathCodec List.mem_cons_self).1 rfl

def concreteFiniteObligations := finiteScalarObligations finitePaths finitePaths_separated (fun _ => 0)
  (fun c => .root c.val.slot.val)
  (by intro c; apply Fin.ext; change c.val.slot.val = c.val.slot.val % (2 ^ 256); exact (Nat.mod_eq_of_lt c.val.slot.isLt).symm)
  (by
    intro c hc
    simp only [finitePaths, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨.bool false, rfl⟩
    · exact ⟨.int 0 (by decide), rfl⟩
    · exact ⟨.int 0 (by decide), rfl⟩) nonzeroSlots

def finitePerAccount : Roadmap.Address → Source.SPath → Source.STy := fun _ => finiteLayout
def finiteInitial : Source.ExecState layout finitePerAccount perAccount :=
  ⟨⟨fun _ => {Source.Account.empty (D := layout) finiteLayout with storage := finiteOriginal}⟩, .empty, []⟩
def finitePrefixUpdate := (finitePrepare finitePaths finitePrefixMap).getD id
def finiteChildUpdate := (finitePrepare finitePaths finiteTargetMap).getD id
def finitePrefixOp : Source.Op layout finitePerAccount perAccount :=
  .account account (fun ac => {ac with storage := finitePrefixUpdate ac.storage})
def finiteChildOp : Source.Op layout finitePerAccount perAccount :=
  .account account (fun ac => {ac with storage := finiteChildUpdate ac.storage})
def finiteTxOp : Source.Op layout finitePerAccount perAccount := .transient account (fun s => s.write txPath (.bool true))
def finiteCaller := finiteInitial.run [finitePrefixOp]
def finiteChildren := [finiteChildOp, finiteTxOp]
def finiteAfterChild := finiteCaller.run finiteChildren

theorem finite_validated_source_ops : finiteAccountWrite? account finitePaths finitePrefixMap = some finitePrefixOp ∧
    finiteAccountWrite? account finitePaths finiteTargetMap = some finiteChildOp := ⟨rfl, rfl⟩

theorem finite_invalid_no_source_op : finiteAccountWrite? (L := finitePerAccount) (T := perAccount) account finitePaths.reverse finiteInvalidMap = none := rfl

theorem finite_source_results : (finiteAfterChild.world.accounts account).storage = finiteTarget ∧
    (finiteAfterChild.transient.cells account).read txPath = some (.bool true) ∧
    finiteAfterChild.journal.length = 3 := ⟨rfl, rfl, rfl⟩

theorem finite_source_inner_revert :
    (finiteCaller.enter account account 0 [] false).rollback finiteAfterChild = finiteCaller ∧
    (finiteCaller.world.accounts account).storage.cell finiteFlag = some (.bool true) ∧
    (finiteCaller.world.accounts account).storage.cell finiteSmall = none :=
  ⟨Source.rollback_run finiteCaller finiteChildren account account 0 [] false, rfl, rfl⟩

theorem finite_source_outer_revert :
    (finiteInitial.enter account account 0 [] false).rollback
      ((finiteCaller.enter account account 0 [] false).commit finiteAfterChild) = finiteInitial := by
  simpa only [Source.ExecState.run] using
    Source.rollback_outer_after_commit finiteInitial [finitePrefixOp] finiteChildren [] account account 0 [] false

theorem finite_source_transaction_reset :
    (finiteAfterChild.endTx.world.accounts account).storage = finiteTarget ∧
    (finiteAfterChild.endTx.transient.cells account).cell txPath = none ∧
    finiteAfterChild.endTx.journal = [] := ⟨rfl, rfl, rfl⟩

#print axioms concreteFiniteObligations
#print axioms finite_changed_actual
#print axioms finite_source_outer_revert
/-- A nonzero within-transaction transient snapshot, not initial reachability. -/
def finiteTransientSnapshot : Source.ExecState layout perAccount finitePerAccount :=
  ⟨initial.world, ⟨fun _ => finiteOriginal⟩, []⟩
def finiteTransientBatch : Source.Op layout perAccount finitePerAccount := .transient account finiteChildUpdate

theorem finite_actual_transient_batch : finiteTransientWrite? account finitePaths finiteTargetMap = some finiteTransientBatch := rfl

theorem finite_transient_effect_and_reset :
    ((finiteTransientSnapshot.apply finiteTransientBatch).transient.cells account) = finiteTarget ∧
    (finiteTransientSnapshot.apply finiteTransientBatch).world = finiteTransientSnapshot.world ∧
    (((finiteTransientSnapshot.apply finiteTransientBatch).endTx.transient.cells account).read finiteFlag = some (.bool false)) ∧
    (((finiteTransientSnapshot.apply finiteTransientBatch).endTx.transient.cells account).read finiteSmall = some (.int 0 (by decide))) ∧
    (((finiteTransientSnapshot.apply finiteTransientBatch).endTx.transient.cells account).read finiteWide = some (.int 0 (by decide))) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem finite_transient_rollback :
    (finiteTransientSnapshot.enter account account 0 [] false).rollback
      (finiteTransientSnapshot.run [finiteTransientBatch]) = finiteTransientSnapshot :=
  Source.rollback_run _ _ _ _ _ _ _

end Solidity.Yul.Views.Controls
