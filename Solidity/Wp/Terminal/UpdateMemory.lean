import Solidity.Wp.Terminal.UpdateStorage

/-!
# Terminal-rule updates: memory targets

`memoryRootAlias`, `memoryStorageCopy`, `memoryFieldRead{,…}AliasRoot`,
`memoryIndexReadAliasRoot{Box,Diamond}` (memory-root targets) and
`memoryFieldWrite{Store,Copy}`, `memoryIndexWrite{Store,Copy}{Box,Diamond}`
(nested targets).  All share `memoryAssignUpd`.
-/

namespace Solidity
namespace Wp

open Semantics Rules

/-! ## Shape facts -/

theorem memoryVar_shape (lhs : PlaceExpr) (hk : lhs.kind = Kind.memory)
    (hs : isSimple lhs) :
    ∃ t fld, lhs.expr = WrappedExpr.var Kind.memory t fld := by
  obtain ⟨e, hass⟩ := lhs
  cases e with
  | var k t fld =>
      have hk' : k = Kind.memory := by
        simpa [PlaceExpr.kind, Typed.WrappedExpr.kind] using hk
      exact ⟨t, fld, by rw [hk']⟩
  | field k t b f =>
      exact absurd (show (WrappedExpr.field k t b f).simple = true from hs)
        (by simp [Typed.WrappedExpr.simple])
  | index k t b ix =>
      exact absurd (show (WrappedExpr.index k t b ix).simple = true from hs)
        (by simp [Typed.WrappedExpr.simple])
  | pushPlace t =>
      exact absurd (show (WrappedExpr.pushPlace t).simple = true from hs)
        (by simp [Typed.WrappedExpr.simple])
  | _ => exact absurd hass (by simp [Typed.WrappedExpr.assignable])

theorem simplePathB_of_memoryRhs {rhs : WrappedExpr} (h : terminalRhsB rhs = true)
    (hk : rhs.kind = Kind.memory) : simplePathB rhs = true := by
  cases rhs <;> simp_all [terminalRhsB, simplePathB, Typed.WrappedExpr.simple,
    Typed.WrappedExpr.kind] <;> split at h <;> simp_all

/-! ## The interpreter on a memory root -/

theorem execStmt_assign_memoryRoot (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr) (t : Ty) (fld : Field)
    (he : lhs.expr = WrappedExpr.var Kind.memory t fld)
    (hr : terminalRhsB rhs = true) :
    execStmt s (Stmt.assign lhs rhs) = memoryAssignUpd lhs rhs s := by
  show execAssign s lhs rhs = _
  obtain ⟨e, hass⟩ := lhs
  simp only at he
  subst he
  unfold execAssign memoryAssignUpd
  simp only []
  cases hk : rhs.kind with
  | memory =>
      rw [readM_readMem s rhs (simplePathB_of_memoryRhs hr hk)]
      simp only [bind, Except.bind, Except.map]
      cases readMem s rhs with
      | error e => rfl
      | ok mv => cases mv <;> rfl
  | storage =>
      rw [resolveS_pathB s rhs (pathB_of_terminalRhsB hr)]
      simp only [bind, Except.bind, Except.map]
      cases placePath s rhs with
      | error e => rfl
      | ok p =>
          obtain ⟨r, sg⟩ := p
          simp only []
          cases s.findStorage r sg with
          | error e => rfl
          | ok sv =>
              simp only []
              cases copyStToM s sv with
              | error e => rfl
              | ok x =>
                  obtain ⟨s', mv⟩ := x
                  cases mv <;> rfl
  | stack => rfl

/-! ## The interpreter on a nested memory place -/

theorem execStmt_assign_memoryField (s : State) (lhs : PlaceExpr) (ty : Ty)
    (base : WrappedExpr) (f : Field) (rhs : WrappedExpr)
    (he : lhs.expr = WrappedExpr.field Kind.memory ty base f)
    (hb : base.simple = true) (hr : terminalRhsB rhs = true) :
    execStmt s (Stmt.assign lhs rhs) = memoryAssignUpd lhs rhs s := by
  show execAssign s lhs rhs = _
  obtain ⟨e, hass⟩ := lhs
  simp only at he
  subst he
  unfold execAssign memoryAssignUpd
  simp only []
  show execAssignNested s _ rhs = _
  unfold execAssignNested
  simp only [Typed.WrappedExpr.kind]
  rw [rhsToMVal_rhsMVal s rhs hr]
  simp only [bind, Except.bind]
  cases rhsMVal s rhs with
  | error e => rfl
  | ok x =>
      obtain ⟨s', mv⟩ := x
      simp only []
      rw [resolveLoc_memoryField s' ty base f hb]
      simp only [writeMemField, bind, Except.bind, Except.map]
      cases memBase s' base with
      | error e => rfl
      | ok id =>
          simp only []
          cases s'.getObj id with
          | error e => rfl
          | ok obj => cases obj <;> rfl

theorem execStmt_assign_memoryIndex (s : State) (lhs : PlaceExpr) (ty : Ty)
    (base ix : WrappedExpr) (rhs : WrappedExpr)
    (he : lhs.expr = WrappedExpr.index Kind.memory ty base ix)
    (hb : base.simple = true) (hi : ix.simple = true)
    (hr : terminalRhsB rhs = true) :
    execStmt s (Stmt.assign lhs rhs) = memoryAssignUpd lhs rhs s := by
  show execAssign s lhs rhs = _
  obtain ⟨e, hass⟩ := lhs
  simp only at he
  subst he
  unfold execAssign memoryAssignUpd
  simp only []
  show execAssignNested s _ rhs = _
  unfold execAssignNested
  simp only [Typed.WrappedExpr.kind]
  rw [rhsToMVal_rhsMVal s rhs hr]
  simp only [bind, Except.bind]
  cases rhsMVal s rhs with
  | error e => rfl
  | ok x =>
      obtain ⟨s', mv⟩ := x
      simp only []
      rw [resolveLoc_memoryIndex s' ty base ix hb hi]
      simp only [writeMemIndex, bind, Except.bind, Except.map]
      cases memBase s' base with
      | error e => rfl
      | ok id =>
          simp only []
          cases simpleInt s' ix with
          | error e => rfl
          | ok i =>
              simp only []
              cases s'.getObj id with
              | error e => rfl
              | ok obj =>
                  cases obj with
                  | struct fields => rfl
                  | array elems =>
                      simp only []

/-! ## Memory-root targets -/

theorem memoryRootAlias_update (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryRootAlias).cond (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .memoryRootAlias (Stmt.assign lhs rhs) s := by
  have hc : lhs.kind = Kind.memory ∧ isSimple lhs ∧ isMemory rhs ∧
      isSimple rhs := hcond
  show execStmt s (Stmt.assign lhs rhs) = memoryAssignUpd lhs rhs s
  obtain ⟨t, fld, he⟩ := memoryVar_shape lhs hc.1 hc.2.1
  exact execStmt_assign_memoryRoot s lhs rhs t fld he
    (terminalRhsB_of_simple hc.2.2.2)

theorem memoryStorageCopy_update (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryStorageCopy).cond (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .memoryStorageCopy (Stmt.assign lhs rhs) s := by
  have hc : lhs.kind = Kind.memory ∧ isSimple lhs ∧ isStorage rhs ∧
      isSimple rhs := hcond
  show execStmt s (Stmt.assign lhs rhs) = memoryAssignUpd lhs rhs s
  obtain ⟨t, fld, he⟩ := memoryVar_shape lhs hc.1 hc.2.1
  exact execStmt_assign_memoryRoot s lhs rhs t fld he
    (terminalRhsB_of_simple hc.2.2.2)

theorem memoryFieldReadAliasRoot_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryFieldReadAliasRoot).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .memoryFieldReadAliasRoot (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = memoryAssignUpd lhs rhs s
  match rhs, hcond with
  | WrappedExpr.field Kind.memory t path f, hc =>
      have hc' : lhs.kind = Kind.memory ∧ isSimple lhs ∧ isSimple path := hc
      obtain ⟨t', fld, he⟩ := memoryVar_shape lhs hc'.1 hc'.2.1
      exact execStmt_assign_memoryRoot s lhs _ t' fld he
        (terminalRhsB_memoryField hc'.2.2)

theorem memoryIndexReadAliasRootBox_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryIndexReadAliasRootBox).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .memoryIndexReadAliasRootBox (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = memoryAssignUpd lhs rhs s
  match rhs, hcond with
  | WrappedExpr.index Kind.memory t path ix, hc =>
      have hc' : lhs.kind = Kind.memory ∧ isSimple lhs ∧ isSimple path ∧
          isSimple ix := hc
      obtain ⟨t', fld, he⟩ := memoryVar_shape lhs hc'.1 hc'.2.1
      exact execStmt_assign_memoryRoot s lhs _ t' fld he
        (terminalRhsB_memoryIndex hc'.2.2.1 hc'.2.2.2)

theorem memoryIndexReadAliasRootDiamond_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryIndexReadAliasRootDiamond).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .memoryIndexReadAliasRootDiamond (Stmt.assign lhs rhs) s :=
  memoryIndexReadAliasRootBox_update s lhs rhs hcond

/-! ## Nested memory targets -/

theorem memoryFieldWriteStore_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryFieldWriteStore).cond (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .memoryFieldWriteStore (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = memoryAssignUpd lhs rhs s
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.field Kind.memory ty path f, hass, hc =>
      have hc' : isSimple path ∧ isStack rhs ∧ isSimple rhs := hc
      exact execStmt_assign_memoryField s ⟨_, hass⟩ ty path f rhs rfl hc'.1
        (terminalRhsB_of_simple hc'.2.2)

theorem memoryFieldWriteCopy_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryFieldWriteCopy).cond (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .memoryFieldWriteCopy (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = memoryAssignUpd lhs rhs s
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.field Kind.memory ty path f, hass, hc =>
      have hc' : isSimple path ∧ isMemory rhs ∧ isSimple rhs := hc
      exact execStmt_assign_memoryField s ⟨_, hass⟩ ty path f rhs rfl hc'.1
        (terminalRhsB_of_simple hc'.2.2)

theorem memoryIndexWriteStoreBox_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryIndexWriteStoreBox).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .memoryIndexWriteStoreBox (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = memoryAssignUpd lhs rhs s
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.index Kind.memory ty path ix, hass, hc =>
      have hc' : isSimple path ∧ isSimple ix ∧ isStack rhs ∧ isSimple rhs := hc
      exact execStmt_assign_memoryIndex s ⟨_, hass⟩ ty path ix rhs rfl hc'.1
        hc'.2.1 (terminalRhsB_of_simple hc'.2.2.2)

theorem memoryIndexWriteStoreDiamond_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryIndexWriteStoreDiamond).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .memoryIndexWriteStoreDiamond (Stmt.assign lhs rhs) s :=
  memoryIndexWriteStoreBox_update s lhs rhs hcond

theorem memoryIndexWriteCopyBox_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryIndexWriteCopyBox).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .memoryIndexWriteCopyBox (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = memoryAssignUpd lhs rhs s
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.index Kind.memory ty path ix, hass, hc =>
      have hc' : isSimple path ∧ isSimple ix ∧ isMemory rhs ∧ isSimple rhs := hc
      exact execStmt_assign_memoryIndex s ⟨_, hass⟩ ty path ix rhs rfl hc'.1
        hc'.2.1 (terminalRhsB_of_simple hc'.2.2.2)

theorem memoryIndexWriteCopyDiamond_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryIndexWriteCopyDiamond).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .memoryIndexWriteCopyDiamond (Stmt.assign lhs rhs) s :=
  memoryIndexWriteCopyBox_update s lhs rhs hcond

end Wp
end Solidity
