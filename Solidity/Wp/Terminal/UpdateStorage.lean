import Solidity.Wp.Terminal.UpdateStack

/-!
# Terminal-rule updates: storage targets

The storage writes (`storageRootWrite{Store,CopySource}`,
`memoryToStorageStoreRoot`, `storageFieldWrite{Save,CopySource}`,
`memoryToStorageFieldCopyRoot`, `storageIndexWrite{Array{Save,CopySource}{Box,Diamond},Mapping{Save,
CopySource}`, `memoryToStorageIndex{Mapping,ArrayBox,ArrayDiamond}CopyRoot`),
the local-root rebinds (`storageLocalRootRebind`,
`storage{Field,Index…}ReadBindLocalRoot`) and the global-root stores
(`storage{Field,Index…}ReadStoreRoot`).  All share `storageAssignUpd`.
-/

namespace Solidity
namespace Wp

open Semantics Rules

/-! ## Shape facts -/

/-- A storage-kind assignable place whose path is simple. -/
def storageTargetB : WrappedExpr -> Bool
  | WrappedExpr.var Kind.storage _ _ => true
  | WrappedExpr.field Kind.storage _ base _ => base.simple
  | WrappedExpr.index Kind.storage _ base ix => base.simple && ix.simple
  | _ => false

theorem global_shape {e : WrappedExpr} (h : isGlobal e) :
    ∃ t fld, e = WrappedExpr.var Kind.storage t fld ∧
      fld.origin = some StorageOrigin.global := by
  cases e with
  | var k t fld =>
      cases k with
      | storage =>
          exact ⟨t, fld, rfl, by simpa [isGlobal, Typed.WrappedExpr.isGlobal] using h⟩
      | _ => exact absurd h (by simp [isGlobal, Typed.WrappedExpr.isGlobal])
  | _ => exact absurd h (by simp [isGlobal, Typed.WrappedExpr.isGlobal])

theorem local_shape {e : WrappedExpr} (h : isLocal e) :
    ∃ t fld, e = WrappedExpr.var Kind.storage t fld ∧
      fld.origin = some StorageOrigin.local := by
  cases e with
  | var k t fld =>
      cases k with
      | storage =>
          exact ⟨t, fld, rfl, by simpa [isLocal, Typed.WrappedExpr.isLocal] using h⟩
      | _ => exact absurd h (by simp [isLocal, Typed.WrappedExpr.isLocal])
  | _ => exact absurd h (by simp [isLocal, Typed.WrappedExpr.isLocal])

theorem storageTargetB_of_global {e : WrappedExpr} (h : isGlobal e) :
    storageTargetB e = true := by
  obtain ⟨t, fld, rfl, _⟩ := global_shape h
  rfl

theorem storageTargetB_of_local {e : WrappedExpr} (h : isLocal e) :
    storageTargetB e = true := by
  obtain ⟨t, fld, rfl, _⟩ := local_shape h
  rfl

theorem pathB_of_terminalRhsB {e : WrappedExpr} (h : terminalRhsB e = true) :
    (e.simple || simplePathB e) = true := by
  cases e <;> simp_all [terminalRhsB, simplePathB, Typed.WrappedExpr.simple]
    <;> split at h <;> simp_all

/-! ## The interpreter on a storage target -/

theorem execStmt_assign_storage (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr) (hl : storageTargetB lhs.expr = true)
    (hr : terminalRhsB rhs = true) :
    execStmt s (Stmt.assign lhs rhs) = storageAssignUpd lhs rhs s := by
  show execAssign s lhs rhs = _
  obtain ⟨e, hass⟩ := lhs
  simp only at hl ⊢
  cases e with
  | var k ty fld =>
      cases k with
      | storage =>
          unfold execAssign storageAssignUpd
          simp only []
          by_cases hg : fld.origin = some StorageOrigin.global
          · rw [if_pos hg, if_pos hg, rhsToSVal_rhsSVal s rhs hr]
            simp only [bind, Except.bind, Except.map]
            cases rhsSVal s rhs <;> rfl
          · rw [if_neg hg, if_neg hg, resolveS_pathB s rhs (pathB_of_terminalRhsB hr)]
            simp only [bind, Except.bind, Except.map]
            cases placePath s rhs with
            | error e => rfl
            | ok p => obtain ⟨r, sg⟩ := p; rfl
      | _ => exact absurd hl (by simp [storageTargetB])
  | field k ty base f =>
      cases k with
      | storage =>
          have hp : simplePathB (WrappedExpr.field Kind.storage ty base f) = true := by
            simpa [storageTargetB, simplePathB] using hl
          unfold execAssign storageAssignUpd
          simp only []
          show execAssignNested s _ rhs = _
          unfold execAssignNested
          simp only [Typed.WrappedExpr.kind]
          rw [rhsToSVal_rhsSVal s rhs hr]
          simp only [bind, Except.bind, Except.map]
          cases rhsSVal s rhs with
          | error e => rfl
          | ok sv =>
              simp only []
              rw [resolveLoc_storageField s ty base f hp]
              simp only [bind, Except.bind, Except.map]
              cases placePath s (WrappedExpr.field Kind.storage ty base f) with
              | error e => rfl
              | ok p => obtain ⟨r, sg⟩ := p; rfl
      | _ => exact absurd hl (by simp [storageTargetB])
  | index k ty base ix =>
      cases k with
      | storage =>
          have hp : simplePathB (WrappedExpr.index Kind.storage ty base ix) = true := by
            simpa [storageTargetB, simplePathB] using hl
          unfold execAssign storageAssignUpd
          simp only []
          show execAssignNested s _ rhs = _
          unfold execAssignNested
          simp only [Typed.WrappedExpr.kind]
          rw [rhsToSVal_rhsSVal s rhs hr]
          simp only [bind, Except.bind, Except.map]
          cases rhsSVal s rhs with
          | error e => rfl
          | ok sv =>
              simp only []
              rw [resolveLoc_storageIndex s ty base ix hp]
              simp only [bind, Except.bind, Except.map]
              cases placePath s (WrappedExpr.index Kind.storage ty base ix) with
              | error e => rfl
              | ok p => obtain ⟨r, sg⟩ := p; rfl
      | _ => exact absurd hl (by simp [storageTargetB])
  | pushPlace target => exact absurd hl (by simp [storageTargetB])
  | _ => exact absurd hass (by simp [Typed.WrappedExpr.assignable])

/-! ## Root targets -/

theorem storageRootWriteStore_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageRootWriteStore).cond (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageRootWriteStore (Stmt.assign lhs rhs) s := by
  have hc : isGlobal lhs ∧ isStack rhs ∧ isSimple rhs := hcond
  show execStmt s (Stmt.assign lhs rhs) = storageAssignUpd lhs rhs s
  exact execStmt_assign_storage s lhs rhs (storageTargetB_of_global hc.1)
    (terminalRhsB_of_simple hc.2.2)

theorem storageRootWriteCopySource_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageRootWriteCopySource).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageRootWriteCopySource (Stmt.assign lhs rhs) s := by
  have hc : isGlobal lhs ∧ isStorage rhs ∧ isSimple rhs := hcond
  show execStmt s (Stmt.assign lhs rhs) = storageAssignUpd lhs rhs s
  exact execStmt_assign_storage s lhs rhs (storageTargetB_of_global hc.1)
    (terminalRhsB_of_simple hc.2.2)

theorem memoryToStorageStoreRoot_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryToStorageStoreRoot).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .memoryToStorageStoreRoot (Stmt.assign lhs rhs) s := by
  have hc : isStorage lhs ∧ isSimple lhs ∧ isMemory rhs ∧ isSimple rhs := hcond
  show execStmt s (Stmt.assign lhs rhs) = storageAssignUpd lhs rhs s
  refine execStmt_assign_storage s lhs rhs ?_ (terminalRhsB_of_simple hc.2.2.2)
  obtain ⟨e, hass⟩ := lhs
  have hk : e.isStorage = true := hc.1
  have hs : e.simple = true := hc.2.1
  cases e <;> simp_all [storageTargetB, Typed.WrappedExpr.isStorage,
    Typed.WrappedExpr.kind, Typed.WrappedExpr.simple, Typed.WrappedExpr.assignable]

theorem storageLocalRootRebind_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageLocalRootRebind).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageLocalRootRebind (Stmt.assign lhs rhs) s := by
  have hc : isLocal lhs ∧ isStorage rhs ∧ isSimple rhs := hcond
  show execStmt s (Stmt.assign lhs rhs) = storageAssignUpd lhs rhs s
  exact execStmt_assign_storage s lhs rhs (storageTargetB_of_local hc.1)
    (terminalRhsB_of_simple hc.2.2)

/-! ## Field targets -/

theorem storageFieldWriteSave_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageFieldWriteSave).cond (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageFieldWriteSave (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = storageAssignUpd lhs rhs s
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.field Kind.storage ty path f, hass, hc =>
      have hc' : isSimple path ∧ isStack rhs ∧ isSimple rhs := hc
      have hp' : path.simple = true := hc'.1
      exact execStmt_assign_storage s ⟨_, hass⟩ rhs (by simp [storageTargetB, hp'])
        (terminalRhsB_of_simple hc'.2.2)

theorem storageFieldWriteCopySource_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageFieldWriteCopySource).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageFieldWriteCopySource (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = storageAssignUpd lhs rhs s
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.field Kind.storage ty path f, hass, hc =>
      have hc' : isSimple path ∧ isStorage rhs ∧ isSimple rhs := hc
      have hp' : path.simple = true := hc'.1
      exact execStmt_assign_storage s ⟨_, hass⟩ rhs (by simp [storageTargetB, hp'])
        (terminalRhsB_of_simple hc'.2.2)

theorem memoryToStorageFieldCopyRoot_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryToStorageFieldCopyRoot).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .memoryToStorageFieldCopyRoot (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = storageAssignUpd lhs rhs s
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.field Kind.storage ty path f, hass, hc =>
      have hc' : isSimple path ∧ isMemory rhs ∧ isSimple rhs := hc
      have hp' : path.simple = true := hc'.1
      exact execStmt_assign_storage s ⟨_, hass⟩ rhs (by simp [storageTargetB, hp'])
        (terminalRhsB_of_simple hc'.2.2)

/-! ## Index targets (box/diamond/mapping twins) -/

/-- Shared proof for every index-target write: simple path and index,
simple right-hand side. -/
theorem execStmt_assign_storageIndex (s : State) (ty : Ty) (path ix rhs : WrappedExpr)
    (hass : (WrappedExpr.index Kind.storage ty path ix).assignable = true)
    (hp : isSimple path) (hi : isSimple ix) (hr : isSimple rhs) :
    execStmt s (Stmt.assign ⟨WrappedExpr.index Kind.storage ty path ix, hass⟩ rhs) =
      storageAssignUpd ⟨WrappedExpr.index Kind.storage ty path ix, hass⟩ rhs s := by
  have hp' : path.simple = true := hp
  have hi' : ix.simple = true := hi
  exact execStmt_assign_storage s ⟨_, hass⟩ rhs (by simp [storageTargetB, hp', hi'])
    (terminalRhsB_of_simple hr)

theorem storageIndexWriteArraySaveBox_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageIndexWriteArraySaveBox).cond (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageIndexWriteArraySaveBox (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = storageAssignUpd lhs rhs s
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.index Kind.storage ty path ix, hass, hc =>
      have hc' : isSimple path ∧ isSimple ix ∧ isStack rhs ∧ isSimple rhs ∧
          isArray path := hc
      exact execStmt_assign_storageIndex s ty path ix rhs hass hc'.1 hc'.2.1
        hc'.2.2.2.1

theorem storageIndexWriteArraySaveDiamond_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageIndexWriteArraySaveDiamond).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageIndexWriteArraySaveDiamond (Stmt.assign lhs rhs) s :=
  storageIndexWriteArraySaveBox_update s lhs rhs hcond

theorem storageIndexWriteMappingSave_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageIndexWriteMappingSave).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageIndexWriteMappingSave (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = storageAssignUpd lhs rhs s
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.index Kind.storage ty path ix, hass, hc =>
      have hc' : isSimple path ∧ isSimple ix ∧ isStack rhs ∧ isSimple rhs ∧
          isMapping path := hc
      exact execStmt_assign_storageIndex s ty path ix rhs hass hc'.1 hc'.2.1
        hc'.2.2.2.1

theorem storageIndexWriteArrayCopySourceBox_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageIndexWriteArrayCopySourceBox).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageIndexWriteArrayCopySourceBox (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = storageAssignUpd lhs rhs s
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.index Kind.storage ty path ix, hass, hc =>
      have hc' : isSimple path ∧ isSimple ix ∧ isStorage rhs ∧ isSimple rhs ∧
          isArray path := hc
      exact execStmt_assign_storageIndex s ty path ix rhs hass hc'.1 hc'.2.1
        hc'.2.2.2.1

theorem storageIndexWriteArrayCopySourceDiamond_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageIndexWriteArrayCopySourceDiamond).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageIndexWriteArrayCopySourceDiamond (Stmt.assign lhs rhs) s :=
  storageIndexWriteArrayCopySourceBox_update s lhs rhs hcond

theorem storageIndexWriteMappingCopySource_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageIndexWriteMappingCopySource).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageIndexWriteMappingCopySource (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = storageAssignUpd lhs rhs s
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.index Kind.storage ty path ix, hass, hc =>
      have hc' : isSimple path ∧ isSimple ix ∧ isStorage rhs ∧ isSimple rhs ∧
          isMapping path := hc
      exact execStmt_assign_storageIndex s ty path ix rhs hass hc'.1 hc'.2.1
        hc'.2.2.2.1

theorem memoryToStorageIndexMappingCopyRoot_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryToStorageIndexMappingCopyRoot).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .memoryToStorageIndexMappingCopyRoot (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = storageAssignUpd lhs rhs s
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.index Kind.storage ty path ix, hass, hc =>
      have hc' : isSimple path ∧ isSimple ix ∧ isMemory rhs ∧ isSimple rhs ∧
          isMapping path := hc
      exact execStmt_assign_storageIndex s ty path ix rhs hass hc'.1 hc'.2.1
        hc'.2.2.2.1

theorem memoryToStorageIndexArrayCopyRootBox_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryToStorageIndexArrayCopyRootBox).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .memoryToStorageIndexArrayCopyRootBox (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = storageAssignUpd lhs rhs s
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.index Kind.storage ty path ix, hass, hc =>
      have hc' : isSimple path ∧ isSimple ix ∧ isMemory rhs ∧ isSimple rhs ∧
          isArray path := hc
      exact execStmt_assign_storageIndex s ty path ix rhs hass hc'.1 hc'.2.1
        hc'.2.2.2.1

theorem memoryToStorageIndexArrayCopyRootDiamond_update (s : State)
    (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryToStorageIndexArrayCopyRootDiamond).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .memoryToStorageIndexArrayCopyRootDiamond
        (Stmt.assign lhs rhs) s :=
  memoryToStorageIndexArrayCopyRootBox_update s lhs rhs hcond

/-! ## Reads into a local root (rebind) and into a global root (store) -/

theorem storageFieldReadBindLocalRoot_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageFieldReadBindLocalRoot).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageFieldReadBindLocalRoot (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = storageAssignUpd lhs rhs s
  match rhs, hcond with
  | WrappedExpr.field Kind.storage t path f, hc =>
      have hc' : isLocal lhs ∧ isSimple path := hc
      exact execStmt_assign_storage s lhs _ (storageTargetB_of_local hc'.1)
        (terminalRhsB_storageField hc'.2)

theorem storageIndexReadArrayBindLocalRootBox_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageIndexReadArrayBindLocalRootBox).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageIndexReadArrayBindLocalRootBox (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = storageAssignUpd lhs rhs s
  match rhs, hcond with
  | WrappedExpr.index Kind.storage t path ix, hc =>
      have hc' : isLocal lhs ∧ isSimple path ∧ isSimple ix ∧ isArray path := hc
      exact execStmt_assign_storage s lhs _ (storageTargetB_of_local hc'.1)
        (terminalRhsB_storageIndex hc'.2.1 hc'.2.2.1)

theorem storageIndexReadArrayBindLocalRootDiamond_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageIndexReadArrayBindLocalRootDiamond).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageIndexReadArrayBindLocalRootDiamond (Stmt.assign lhs rhs) s :=
  storageIndexReadArrayBindLocalRootBox_update s lhs rhs hcond

theorem storageIndexReadMappingBindLocalRoot_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageIndexReadMappingBindLocalRoot).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageIndexReadMappingBindLocalRoot (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = storageAssignUpd lhs rhs s
  match rhs, hcond with
  | WrappedExpr.index Kind.storage t path ix, hc =>
      have hc' : isLocal lhs ∧ isSimple path ∧ isSimple ix ∧ isMapping path := hc
      exact execStmt_assign_storage s lhs _ (storageTargetB_of_local hc'.1)
        (terminalRhsB_storageIndex hc'.2.1 hc'.2.2.1)

theorem storageFieldReadStoreRoot_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageFieldReadStoreRoot).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageFieldReadStoreRoot (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = storageAssignUpd lhs rhs s
  match rhs, hcond with
  | WrappedExpr.field Kind.storage t path f, hc =>
      have hc' : isSimple lhs ∧ isGlobal lhs ∧ isSimple path := hc
      exact execStmt_assign_storage s lhs _ (storageTargetB_of_global hc'.2.1)
        (terminalRhsB_storageField hc'.2.2)

theorem storageIndexReadArrayStoreRootBox_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageIndexReadArrayStoreRootBox).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageIndexReadArrayStoreRootBox (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = storageAssignUpd lhs rhs s
  match rhs, hcond with
  | WrappedExpr.index Kind.storage t path ix, hc =>
      have hc' : isSimple lhs ∧ isGlobal lhs ∧ isSimple path ∧ isSimple ix ∧
          isArray path := hc
      exact execStmt_assign_storage s lhs _ (storageTargetB_of_global hc'.2.1)
        (terminalRhsB_storageIndex hc'.2.2.1 hc'.2.2.2.1)

theorem storageIndexReadArrayStoreRootDiamond_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageIndexReadArrayStoreRootDiamond).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageIndexReadArrayStoreRootDiamond (Stmt.assign lhs rhs) s :=
  storageIndexReadArrayStoreRootBox_update s lhs rhs hcond

theorem storageIndexReadMappingStoreRoot_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageIndexReadMappingStoreRoot).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageIndexReadMappingStoreRoot (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = storageAssignUpd lhs rhs s
  match rhs, hcond with
  | WrappedExpr.index Kind.storage t path ix, hc =>
      have hc' : isSimple lhs ∧ isGlobal lhs ∧ isSimple path ∧ isSimple ix ∧
          isMapping path := hc
      exact execStmt_assign_storage s lhs _ (storageTargetB_of_global hc'.2.1)
        (terminalRhsB_storageIndex hc'.2.2.1 hc'.2.2.2.1)

end Wp
end Solidity
