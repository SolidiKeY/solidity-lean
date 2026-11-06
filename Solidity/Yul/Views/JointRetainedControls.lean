import Solidity.Yul.Views.JointMemoryControls
import Solidity.Yul.Views.JointSequential

namespace Solidity.Yul.Views.Controls

def jointCanonWords := [Source.intWord (-1),Source.toWord (2^160-1),canonB3NewWord]
def jointCanonZeroPhysical := wordListView jointCanonWords canonZeroPhysical 128
def jointCanonRegrowPhysical := wordListView jointCanonWords canonRegrowPhysical 128

theorem jointCanon_fields (m : ByteView) : decodeCanonicalFields canonPlacement canonEntries (canonLayout.fields canonName)
    (wordListView jointCanonWords m 128) 128 = some canonNewFields :=
  decodeCanonicalFields_reads _ _ canon_coverage canon_new_fields_encoding canon_field_support _ _ (fun i w found => wordList_read _ _ _ i w found)

def jointCanonFirstHeap := canonHeap.write 0 (.struct canonNewFields) (by rfl)
def jointCanonFirstPlacement := structWrittenPlacement canonHeap canonPlacement 0 canonName canonFields canonNewFields rfl
def jointCanonFirstHistory := retainSameShapeWrite canonPlacement canonPlacement (retainInitial _ _) 0
  (.struct canonNewFields) (by rfl) (.strct _)
def jointCanonFirstImage : MemoryImage jointCanonFirstPlacement (.struct (l := .memory) canonNewFields) :=
  .words _ jointCanonWords (.strct _ _ (canon_new_fields_encoding.transport jointCanonFirstPlacement
    (funext (fun a => Source.Heap.write_ty canonHeap 0 a (.struct canonNewFields) (by rfl))) rfl))
def jointCanonFirstEntries := refreshMixedEntries canonPlacement 0 (.struct canonNewFields) (by rfl)
  jointCanonFirstPlacement rfl jointCanonFirstImage canonEntries

def jointCanonZeroHeap := jointCanonFirstHeap.write 2 (dynamicMemberData canonLayout canonB3Ty 0 Fin.elim0) (by rfl)
def jointCanonZeroPlacement := retainedMemberArrayPlacement canonPlacement jointCanonFirstPlacement jointCanonFirstHistory 2 canonB3Ty 2 canonBValues rfl 0 Fin.elim0 (by decide)
def jointCanonZeroHistory := retainedMemberArray_history canonPlacement jointCanonFirstPlacement jointCanonFirstHistory 2 canonB3Ty 2 canonBValues rfl 0 Fin.elim0 (by decide)
def jointCanonZeroImage : MemoryImage jointCanonZeroPlacement (dynamicMemberData canonLayout canonB3Ty 0 Fin.elim0) :=
  .words _ [0] (.array (n := none) 0 (fun _ e => nomatch e) (by decide) Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i))
def jointCanonZeroEntries := refreshMixedEntries jointCanonFirstPlacement 2 (dynamicMemberData canonLayout canonB3Ty 0 Fin.elim0) (by rfl)
  jointCanonZeroPlacement rfl jointCanonZeroImage jointCanonFirstEntries

theorem jointCanon_zero_decoder (τ : Source.STy) (w : Roadmap.Word) :
    decodeExtendedMemoryMember jointCanonZeroPlacement jointCanonZeroEntries τ w = decodeExtendedMemoryMember canonPlacement canonEntries τ w := by
  unfold jointCanonZeroEntries jointCanonFirstEntries
  rw [decodeExtended_refresh,decodeExtended_refresh]

theorem jointCanon_zero_coverage : CoversMixedHeap jointCanonZeroEntries :=
  refreshMixedEntries_coverage _ _ _ _ _ _ _ _ (refreshMixedEntries_coverage _ _ _ _ _ _ _ _ canon_coverage)

def jointCanonZeroState := withSourceHeap canonAliasState jointCanonZeroHeap

theorem jointCanon_zero_source : canonicalJointRetainedState canonAliasState canonPlacement canonPlacement (retainInitial _ _) canonEntries
    0 canonName 2 canonB3Ty false jointCanonZeroPhysical = some (.ok (),jointCanonZeroState) := by
  have header : mload jointCanonZeroPhysical 640 = 0 := by
    rw [mload_congr jointCanonZeroPhysical canonZeroPhysical 640 (fun i => wordList_residual _ _ _ _ (Or.inr (by have hi := i.isLt; change 128 + 3*32 ≤ 640+i.val; omega)))]
    exact mload_mstore _ _ _
  have prepare := canonicalJointRetained_header canonAliasState canonPlacement canonPlacement (retainInitial _ _) canonEntries 0 canonName 2 canonB3Ty false jointCanonZeroPhysical 0 (congrArg Fin.val header) (by decide)
  have step := canonicalJoint_decoded canonAliasState canonPlacement canonEntries 0 canonName 2 canonB3Ty none 0 (fun _ e => nomatch e)
    jointCanonZeroPhysical (by change (mload jointCanonZeroPhysical 640).val = 0; rw [header]; rfl)
    canonNewFields Fin.elim0 (jointCanon_fields _) (by rfl)
  have run := twoHeapPut_run canonAliasState 0 (Source.Data.struct (l := .memory) canonNewFields) 2
    (dynamicMemberData canonLayout canonB3Ty 0 Fin.elim0) (by rfl) (by rfl)
  exact prepare.trans (step.trans (congrArg some run))

theorem jointCanon_regrow_array : decodeCanonicalArray jointCanonZeroPlacement jointCanonZeroEntries canonB3Ty 2 jointCanonRegrowPhysical 672 = some canonBValues := by
  have decoders : decodeExtendedMemoryMember jointCanonZeroPlacement jointCanonZeroEntries = decodeExtendedMemoryMember canonPlacement canonEntries :=
    funext (fun τ => funext (jointCanon_zero_decoder τ))
  unfold decodeCanonicalArray
  rw [decoders]
  apply decodeArrayWith_of_decodes
  intro i
  have reads : mload jointCanonRegrowPhysical (672+i.val*32) = canonB3Word := by
    rw [mload_congr jointCanonRegrowPhysical canonRegrowPhysical _ (fun j => wordList_residual _ _ _ _ (Or.inr (by have hi := j.isLt; change 128 + 3*32 ≤ 672+i.val*32+j.val; omega)))]
    have same : mload canonRegrowPhysical (672+i.val*32) = mload canonPhysical (672+i.val*32) := by
      apply mload_congr
      intro j
      change mstore (mstore canonPhysical 640 0) 640 2 _ = _
      rw [mstore_outside _ _ _ _ (by omega),mstore_outside _ _ _ _ (by omega)]
    rw [same]
    have all := canon_all_reads canonEntry2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    have choices : i=0 ∨ i=1 := by have hi:=i.isLt; apply Or.imp (fun h=>Fin.ext h) (fun h=>Fin.ext h); omega
    rcases choices with eq | eq
    · subst i; exact all 1 canonB3Word rfl
    · subst i; exact all 2 canonB3Word rfl
  rw [reads]
  exact decodeExtendedScalar_encode _ _ canonB3Ty trivial canonB3 canonB3Word (.scalar _ _ (by decide))

def jointCanonRegrowHeap := jointCanonZeroHeap.write 0 (.struct canonNewFields) (by rfl) |>.write 2
  (dynamicMemberData canonLayout canonB3Ty 2 canonBValues) (by rfl)
def jointCanonRegrowState := withSourceHeap jointCanonZeroState jointCanonRegrowHeap

theorem jointCanon_regrow_source : canonicalJointRetainedState jointCanonZeroState canonPlacement jointCanonZeroPlacement jointCanonZeroHistory jointCanonZeroEntries
    0 canonName 2 canonB3Ty false jointCanonRegrowPhysical = some (.ok (),jointCanonRegrowState) := by
  have header : mload jointCanonRegrowPhysical 640 = 2 := by
    rw [mload_congr jointCanonRegrowPhysical canonRegrowPhysical 640 (fun i => wordList_residual _ _ _ _ (Or.inr (by have hi := i.isLt; change 128+3*32 ≤ 640+i.val; omega)))]
    exact mload_mstore _ _ _
  have fields : decodeCanonicalFields jointCanonZeroPlacement jointCanonZeroEntries (canonLayout.fields canonName) jointCanonRegrowPhysical 128 = some canonNewFields := by
    unfold decodeCanonicalFields
    rw [show decodeExtendedMemoryMember jointCanonZeroPlacement jointCanonZeroEntries = decodeExtendedMemoryMember canonPlacement canonEntries from funext (fun τ => funext (jointCanon_zero_decoder τ))]
    exact jointCanon_fields _
  have prepare := canonicalJointRetained_header jointCanonZeroState canonPlacement jointCanonZeroPlacement jointCanonZeroHistory jointCanonZeroEntries 0 canonName 2 canonB3Ty false jointCanonRegrowPhysical 2 (congrArg Fin.val header) (by decide)
  have step := canonicalJoint_decoded jointCanonZeroState jointCanonZeroPlacement jointCanonZeroEntries 0 canonName 2 canonB3Ty none 2 (fun _ e => nomatch e)
    jointCanonRegrowPhysical (by change (mload jointCanonRegrowPhysical 640).val = 2; rw [header]; rfl) canonNewFields canonBValues fields jointCanon_regrow_array
  have run := twoHeapPut_run jointCanonZeroState 0 (Source.Data.struct (l := .memory) canonNewFields) 2
    (dynamicMemberData canonLayout canonB3Ty 2 canonBValues) (by rfl) (by rfl)
  exact prepare.trans (step.trans (congrArg some run))

theorem jointCanon_regrow_MemOK (H : Source.HeapTy) (ok : Source.MemOK canonEnv H canonAliasState) : Source.MemOK canonEnv H jointCanonRegrowState :=
  canonicalJointRetained_MemOK H jointCanonZeroState canonPlacement jointCanonZeroPlacement jointCanonZeroHistory jointCanonZeroEntries 0 canonName 2 canonB3Ty false _ _ jointCanon_regrow_source
    (canonicalJointRetained_MemOK H canonAliasState canonPlacement canonPlacement (retainInitial _ _) canonEntries 0 canonName 2 canonB3Ty false _ _ jointCanon_zero_source ok)

theorem jointCanon_zero_regrow_aliases :
    (readCanonAlias true 0).run jointCanonZeroState = (.error (.revert (Source.panicData .index)),jointCanonZeroState) ∧
    (readCanonAlias false 0).run jointCanonRegrowState = (.ok canonB3,jointCanonRegrowState) ∧
    (readCanonAlias true 1).run jointCanonRegrowState = (.ok canonB3,jointCanonRegrowState) := ⟨rfl,rfl,rfl⟩

theorem jointCanon_inhabited_MemOK : Source.MemOK canonEnv canonHeap.ty jointCanonRegrowState :=
  jointCanon_regrow_MemOK _ canon_alias_initial_MemOK

end Solidity.Yul.Views.Controls
