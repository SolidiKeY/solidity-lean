import Solidity.Yul.Views.OwnedBoolDynamicReadControls
import Solidity.Yul.Views.OwnedBoolOwnershipBatch

namespace Solidity.Yul.Views.Controls

theorem db_length_at {Γ written value s r encoding}
    (p : @RepresentedOwnershipPlan pcEnv pcTypes pcDeclarations "PC" Γ packedStepFrame pcLayout pcFixed written value s r encoding)
    {Δ} (state : Source.EMState pcEnv Δ) (same : state.2=p.step.1.1.2.2) :
    (Source.readLen (E:=pcEnv) packedStepFrame (pcPath "bs")).run state=(.ok (p.nextRaw 3).val,state) := by
  have member := pcLayout.primitive_root_member pcFixed p.nextRaw (pcB.registration account)
    (pcLayout.scalarFamilyHeader_member pcBEntry)
  have notBool : pcEnv.lay account (pcB.registration account).path≠.bool := by
    change Source.STy.int .u256≠.bool
    intro impossible
    cases impossible
  have view := represented_view_nonbool _ false account p.nextEncoding _ p.nextRaw (p.view rfl)
    (pcB.registration account) member notBool
  have cell := pcB.view_length_cell account _ p.nextRaw view
  exact pcB.readLen packedStepFrame state (p.nextRaw 3) rfl (by rw [same]; exact cell)

def dbAliasesGrow : Source.EMState pcEnv [pcBoolArray,pcBoolArray] :=
  ⟨.cons pcB.reference (.cons pcB.reference .nil),dbGrow.step.1.1.2.2⟩
def dbAliasesZero : Source.EMState pcEnv [pcBoolArray,pcBoolArray] :=
  ⟨.cons pcB.reference (.cons pcB.reference .nil),dbZero.step.1.1.2.2⟩
def dbAliasesAgain : Source.EMState pcEnv [pcBoolArray,pcBoolArray] :=
  ⟨.cons pcB.reference (.cons pcB.reference .nil),dbAgain.step.1.1.2.2⟩

theorem db_alias_grow_length : (Source.readLen (E:=pcEnv) packedStepFrame (pcPath "bs")).run dbAliasesGrow=(.ok 4,dbAliasesGrow) := by
  have read := db_length_at dbGrow dbAliasesGrow rfl
  rw [db_grow_next] at read
  exact read

theorem db_two_real_aliases :
    (do let loc ← Source.indexLoc (E:=pcEnv) packedStepFrame (dbAliasesGrow.1.get .here) 3
        Source.readLoc packedStepFrame loc).run dbAliasesGrow=(.ok (.bool true),dbAliasesGrow) ∧
    (do let loc ← Source.indexLoc (E:=pcEnv) packedStepFrame (dbAliasesGrow.1.get (.there .here)) 3
        Source.readLoc packedStepFrame loc).run dbAliasesGrow=(.ok (.bool true),dbAliasesGrow) := by
  have read := db_dirty_source_read_at dbGrow dbAliasesGrow rfl (by rw [db_grow_next]; decide) (by rw [db_grow_next]; rfl)
  have first : (Source.indexLoc (E:=pcEnv) packedStepFrame (dbAliasesGrow.1.get .here) 3).run dbAliasesGrow=
      (.ok (.stor ⟨pcName "bs",[.index 3]⟩),dbAliasesGrow) := pcB.indexLoc packedStepFrame dbAliasesGrow 4 db_alias_grow_length 3
  have second : (Source.indexLoc (E:=pcEnv) packedStepFrame (dbAliasesGrow.1.get (.there .here)) 3).run dbAliasesGrow=
      (.ok (.stor ⟨pcName "bs",[.index 3]⟩),dbAliasesGrow) := pcB.indexLoc packedStepFrame dbAliasesGrow 4 db_alias_grow_length 3
  constructor
  · rw [Source.Hoare.run_bind,first]
    exact read
  · rw [Source.Hoare.run_bind,second]
    exact read

theorem db_alias_zero_bounds :
    (Source.indexLoc (E:=pcEnv) packedStepFrame (dbAliasesZero.1.get .here) 3).run dbAliasesZero=
      (.error (.revert (Source.panicData .index)),dbAliasesZero) := by
  have length := db_length_at dbZero dbAliasesZero rfl
  rw [db_zero_next] at length
  exact pcB.indexLoc packedStepFrame dbAliasesZero 0 length 3

theorem db_alias_after_regrow :
    (do let loc ← Source.indexLoc (E:=pcEnv) packedStepFrame (dbAliasesAgain.1.get (.there .here)) 3
        Source.readLoc packedStepFrame loc).run dbAliasesAgain=(.ok (.bool true),dbAliasesAgain) := by
  have length := db_length_at dbAgain dbAliasesAgain rfl
  rw [db_again_next] at length
  have formed : (Source.indexLoc (E:=pcEnv) packedStepFrame (dbAliasesAgain.1.get (.there .here)) 3).run dbAliasesAgain=
      (.ok (.stor ⟨pcName "bs",[.index 3]⟩),dbAliasesAgain) := pcB.indexLoc packedStepFrame dbAliasesAgain 4 length 3
  rw [Source.Hoare.run_bind,formed]
  exact db_dirty_source_read_at dbAgain dbAliasesAgain rfl (by rw [db_again_next]; decide) (by rw [db_again_next]; rfl)

theorem db_alias_MemOK : Source.MemOK pcEnv pcState.2.heap.ty dbAliasesAgain := by
  have ok := db_every_H pcState.2.heap.ty pc_initial_MemOK
  exact ⟨⟨ok.1.1,⟨rfl,rfl,trivial⟩⟩,ok.2⟩

theorem db_actual_three_request_sequence :
    runRepresentedOwnership? packedStepFrame pcLayout pcFixed [(3,4),(3,0),(3,4)] pcState pcResidual boolEncodingInitial=
      (some (.ok ()),dbAgain.step.1.1.2,dbAgain.step.1.2,dbAgain.step.2) := by
  rw [dbGrow.batch_nonstatic _ rfl,dbZero.batch_nonstatic _ rfl,dbAgain.batch_nonstatic _ rfl]
  rfl

theorem db_static_preserves_successful_prefix : dbAgain.asStatic.step=
    (((.error (.revert []),dbZero.step.1.1.2),dbZero.step.1.2),dbZero.step.2) := dbAgain.static_preserves_three

theorem db_child_rollback : companionRollback (companionEnter dbGrow.after account account 0 [] false) dbZero.after=dbGrow.after ∧
    boolEncodingRollback dbGrow.step.2.journal.length dbZero.step.2=dbGrow.step.2 := dbZero.rollback rfl

theorem db_child_commit_outer_rollback :
    companionRollback (companionEnter ⟨pcState.2.ex,pcResidual⟩ account account 0 [] false)
      (companionCommit (companionEnter dbGrow.after account account 0 [] false) dbZero.after)=⟨pcState.2.ex,pcResidual⟩ ∧
    boolEncodingRollback boolEncodingInitial.journal.length dbZero.step.2=boolEncodingInitial := dbGrow.child_outer_rollback dbZero rfl

theorem db_persistent_endTx : finiteEncode
    (representedRegistry (pcLayout.primitiveSnapshot pcFixed dbAgain.nextRaw) false account (boolEncodingEndTx dbAgain.step.2))
    ((companionEndTx dbAgain.after).source.world.accounts account).storage
    (fun q => (companionEndTx dbAgain.after).residual.cells (complementKey false account q))=some dbAgainRaw :=
  (dbAgain.endTx_reencode rfl).trans (congrArg some db_again_next)

theorem db_other_account : dbAgain.after.source.world.accounts ⟨2,by decide⟩=pcState.2.ex.world.accounts ⟨2,by decide⟩ :=
  (dbAgain.other_account _ (by decide)).trans ((dbZero.other_account _ (by decide)).trans (dbGrow.other_account _ (by decide)))

theorem db_other_bank_complement (q : Roadmap.Word) : dbAgain.step.1.2.cells (complementKey true account q)=pcResidual.cells (complementKey true account q) :=
  (dbAgain.other_residual _ (Or.inl (by change true≠false; decide))).trans ((dbZero.other_residual _ (Or.inl (by change true≠false; decide))).trans
    (dbGrow.other_residual _ (Or.inl (by change true≠false; decide))))

end Solidity.Yul.Views.Controls
