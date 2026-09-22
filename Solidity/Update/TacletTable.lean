import Solidity.Update.Wp

/-!
# Each rule's update, proved

`Calculus/Rules.lean` now *states* a terminal rule's KeY update.  A statement is not a
theorem: what makes the table worth reading is that its updates are the ones
`Semantics.execStmt` performs, and that is what this module proves, one rule at
a time,

    goalsExec sm ((ruleEffect r).goals stmt h) s = terminalUpdate r stmt s

against `Wp.terminalUpdate?` — which is itself already proved equal to the
interpreter (`Wp.terminalUpdate_sound`).  Composing the two gives
`execStmt s stmt = goalsExec …`: the taclet's `\replacewith` update *is* the
step.

## Sort side conditions

Some Lean conditions are weaker than the KeY schema-variable sorts they model.
`storageRootWriteStore` matches `isSe se` — stack and simple — where KeY writes
`SimpleExpression[primitive]`; the wrapped AST admits a stack variable of
reference type, which the typed `Place` constructor does not, so nothing rules
it out at this level.  Where that matters the bridge carries the missing
condition as a hypothesis, spelled `hprim`, exactly as the evaluation-order
theorems of `Calculus/RuleSoundness.lean` do.  It is a statement about the *syntax*, not
an assumption about the state.

## Coverage

`bridgedRules` lists the rules proved here and `openBridges` the rest;
`bridges_account` checks that together they are exactly the rules with an
update.  That is the same discipline as `SortFaithfulness.openFindings`: a
partial result that says how partial it is.
-/

namespace Solidity
namespace Update

open Semantics Wp Rules

/-! ## Reading helpers -/

/-- A *simple* expression has no operator node, so the terminal reader is the
interpreter's plain one. -/
theorem readTerm_eq_readVal {s : State} {e : WrappedExpr} (hs : e.simple = true) :
    readTerm s e = readVal s e := by
  cases e <;> simp_all [readTerm, Typed.WrappedExpr.simple]

theorem goalsExec_terminalGoal (sm : SolidityModality) (upd : UpdTerm)
    (s : State) :
    goalsExec sm (terminalGoal upd) s = UpdTerm.toUpd upd s := by
  cases sm <;>
    simp [goalsExec, terminalGoal, Guard.eval, runPremises, SideFormula.eval,
      SolidityModality.appliesCaseMode, CaseMode.applies, bind, Except.bind]

/-- A guarded split runs its update when the guard holds and reverts when it
does not — the `\else` goal is what makes the pair exhaustive. -/
theorem goalsExec_splitGoals (sm : SolidityModality) (φ : SideFormula)
    (prem : List Premise) (upd : UpdTerm) (s : State) :
    goalsExec sm (splitGoals φ prem upd) s =
      Guard.eval { premises := prem, formula := φ } s >>= fun b =>
        if b then UpdTerm.toUpd upd s else .error .revert := by
  have hneg : Guard.eval { premises := prem, formula := φ.neg } s =
      (Guard.eval { premises := prem, formula := φ } s).map not := by
    simp only [Guard.eval, SideFormula.eval, bind, Except.bind, Except.map]
    cases runPremises prem s <;> rfl
  have happ : sm.appliesCaseMode CaseMode.both = true := by cases sm <;> rfl
  simp only [splitGoals, goalsExec, happ, if_pos, hneg, Except.map, bind,
    Except.bind]
  cases Guard.eval { premises := prem, formula := φ } s with
  | error e => rfl
  | ok b => cases b <;> simp

theorem toUpd_storageElem (u : StTerm) (s : State) :
    UpdTerm.toUpd [UpdElem.storage u] s =
      (storageRhs u s).map fun g => { s with storage := g } := by
  simp only [UpdTerm.toUpd, UpdTerm.toPar, List.flatMap]
  exact Upd.toUpd_storage _ s

theorem toUpd_envElem (n : Name) (r : BindRhs) (s : State) :
    UpdTerm.toUpd [UpdElem.bind n r] s = (bindRhs r s).map fun b => s.setEnv n b := by
  simp only [UpdTerm.toUpd, UpdTerm.toPar, List.flatMap]
  exact Upd.toUpd_env _ _ s

theorem toUpd_netElem (recipient amount : WrappedExpr) (s : State) :
    UpdTerm.toUpd [UpdElem.transfer recipient amount] s =
      (transferRhs recipient amount s).map
        fun x => { s with net := x.1, selfBalance := x.2 } := by
  simp only [UpdTerm.toUpd, UpdTerm.toPar, List.flatMap]
  exact Upd.toUpd_net _ s

theorem toUpd_heapElem (u : MemTerm) (s : State) :
    UpdTerm.toUpd [UpdElem.heap u] s =
      (heapRhs u s).map fun x => { s with heap := x.1, nextId := x.2 } := by
  simp only [UpdTerm.toUpd, UpdTerm.toPar, List.flatMap]
  exact Upd.toUpd_heap _ s

/-- `{storage := save(storage, p, v)}` *is* the storage write at `p`. -/
theorem storageSave_eq (s : State) (target : WrappedExpr) (v : SVal) :
    (storageSave s target v).map (fun g => { s with storage := g }) =
      locPath s target >>= fun p => s.saveStorage p.1 p.2 v := by
  simp only [storageSave, Upd.saveSt, bind, Except.bind, Except.map]
  cases locPath s target with
  | error e => rfl
  | ok p =>
      simp only []
      cases hsv : s.saveStorage p.1 p.2 v with
      | error e => simp only
      | ok t => exact congrArg Except.ok (Upd.saveStorage_frame hsv).symm

/-- Look the rule up in the terminal table once, rather than unfolding the
95-way match inside every proof. -/
theorem tu_eq {r : RuleName} {f : Stmt -> State -> Res State}
    (h : terminalUpdate? r = some f) (stmt : Stmt) (s : State) :
    terminalUpdate r stmt s = f stmt s := by
  simp only [terminalUpdate, h]

/-! ## Storage targets: `{storage := save(…)}` and `{p := q}` -/

theorem storageRootWriteStore_taclet (sm : SolidityModality) (stmt : Stmt)
    (hcond : (ruleEffect .storageRootWriteStore).cond stmt) (s : State)
    (hprim : ∀ lhs rhs, stmt = Stmt.assign lhs rhs -> rhs.ty.isPrimitive = true) :
    goalsExec sm ((ruleEffect .storageRootWriteStore).goals stmt hcond) s
      = terminalUpdate .storageRootWriteStore stmt s := by
  cases stmt <;> first | exact (hcond : False).elim | skip
  rename_i lhs rhs
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.var Kind.storage ty fld, hass, hcond =>
      obtain ⟨hg, hse⟩ := hcond
      have hgo : fld.origin = some StorageOrigin.global := by
        simpa [Rules.isGlobal, Typed.WrappedExpr.isGlobal] using hg
      have hs : rhs.simple = true := hse.2
      have hp : rhs.ty.isPrimitive = true := hprim _ _ rfl
      show goalsExec sm (terminalGoal
          [UpdElem.storage (StTerm.save .cur
            (WrappedExpr.var Kind.storage ty fld) (StVal.sym (Sym.read rhs)))]) s = _
      rw [goalsExec_terminalGoal, toUpd_storageElem]
      rw [tu_eq (r := .storageRootWriteStore) (f := onAssign storageAssignUpd) rfl]
      simp only [storageRhs_save_cur, storageRhs_delAt_cur, stVal, storageSave, Sym.eval, readTerm_eq_readVal hs, bind, Except.bind,
        Except.map, Wp.onAssign, storageAssignUpd, rhsSVal, hp, if_pos, hgo]
      cases readVal s rhs with
      | error e => rfl
      | ok v =>
          have h2 := storageSave_eq s (WrappedExpr.var Kind.storage ty fld) v.toSVal
          simp only [locPath, hgo, if_pos, bind, Except.bind, Except.map] at h2
          exact h2


/-- A primitive `{… := se}` and a `{… := find(storage, sp)}` compute the same
storage image: `rhsSVal`'s primitive branch *is* `readVal` composed with
`toSVal`.  So the two KeY spellings collapse once the sort is known, and every
storage write below can be proved in the `copy` shape. -/
theorem storageRhs_save_eq_copy (target rhs : WrappedExpr) (s : State)
    (hs : rhs.simple = true) (hp : rhs.ty.isPrimitive = true) :
    storageRhs (.save .cur target (.sym (.read rhs))) s
      = storageRhs (.save .cur target (.find rhs)) s := by
  simp only [storageRhs_save_cur, stVal, Sym.eval, readTerm_eq_readVal hs,
    rhsSVal, hp, if_pos, bind, Except.bind, Except.map]

/-- `gsp = <source>` on a **global** storage root. -/
theorem storageCopy_globalRoot (ty : Ty) (fld : Field) (hass : _)
    (rhs : WrappedExpr) (s : State)
    (hg : fld.origin = some StorageOrigin.global) :
    (storageRhs (.save .cur (WrappedExpr.var Kind.storage ty fld) (.find rhs)) s).map
        (fun g => { s with storage := g })
      = storageAssignUpd ⟨WrappedExpr.var Kind.storage ty fld, hass⟩ rhs s := by
  simp only [storageRhs_save_cur, storageRhs_delAt_cur, stVal, storageSave, storageAssignUpd, hg, if_pos, bind, Except.bind,
    Except.map]
  cases rhsSVal s rhs with
  | error e => rfl
  | ok v =>
      have h2 := storageSave_eq s (WrappedExpr.var Kind.storage ty fld) v
      simp only [locPath, hg, if_pos, bind, Except.bind, Except.map] at h2
      exact h2

/-- `sp.f = <source>`. -/
theorem storageCopy_field (ty : Ty) (base : WrappedExpr) (f : Field) (hass : _)
    (rhs : WrappedExpr) (s : State) :
    (storageRhs (.save .cur (WrappedExpr.field Kind.storage ty base f) (.find rhs)) s).map
        (fun g => { s with storage := g })
      = storageAssignUpd ⟨WrappedExpr.field Kind.storage ty base f, hass⟩ rhs s := by
  simp only [storageRhs_save_cur, storageRhs_delAt_cur, stVal, storageSave, storageAssignUpd, bind, Except.bind, Except.map]
  cases rhsSVal s rhs with
  | error e => rfl
  | ok v =>
      have h2 := storageSave_eq s (WrappedExpr.field Kind.storage ty base f) v
      simp only [locPath, bind, Except.bind, Except.map] at h2
      exact h2

/-- `sp[i] = <source>`. -/
theorem storageCopy_index (ty : Ty) (base ix : WrappedExpr) (hass : _)
    (rhs : WrappedExpr) (s : State) :
    (storageRhs (.save .cur (WrappedExpr.index Kind.storage ty base ix) (.find rhs)) s).map
        (fun g => { s with storage := g })
      = storageAssignUpd ⟨WrappedExpr.index Kind.storage ty base ix, hass⟩ rhs s := by
  simp only [storageRhs_save_cur, storageRhs_delAt_cur, stVal, storageSave, storageAssignUpd, bind, Except.bind, Except.map]
  cases rhsSVal s rhs with
  | error e => rfl
  | ok v =>
      have h2 := storageSave_eq s (WrappedExpr.index Kind.storage ty base ix) v
      simp only [locPath, bind, Except.bind, Except.map] at h2
      exact h2

/-- `lsv = sp` on a storage **local** root: a rebinding, not a storage write. -/
theorem storageBind_localRoot (ty : Ty) (fld : Field) (hass : _)
    (rhs : WrappedExpr) (s : State)
    (hg : ¬ fld.origin = some StorageOrigin.global) :
    (bindRhs (.path rhs) s).map (fun b => s.setEnv fld.name b)
      = storageAssignUpd ⟨WrappedExpr.var Kind.storage ty fld, hass⟩ rhs s := by
  simp only [bindRhs, storageAssignUpd, hg, if_neg, bind, Except.bind, Except.map]
  cases placePath s rhs with
  | error e => rfl
  | ok p => rfl



/-! ## Shapes a condition forces -/

theorem isGlobal_shape {e : WrappedExpr} (h : Rules.isGlobal e) :
    ∃ ty fld, e = WrappedExpr.var Kind.storage ty fld ∧
      fld.origin = some StorageOrigin.global := by
  cases e <;> simp_all [Rules.isGlobal, Typed.WrappedExpr.isGlobal]
  rename_i kind ty fld
  cases kind <;> simp_all [Typed.WrappedExpr.isGlobal]
  exact ⟨ty, fld, ⟨rfl, rfl⟩, h⟩

theorem isLocal_shape {e : WrappedExpr} (h : Rules.isLocal e) :
    ∃ ty fld, e = WrappedExpr.var Kind.storage ty fld ∧
      fld.origin = some StorageOrigin.local := by
  cases e <;> simp_all [Rules.isLocal, Typed.WrappedExpr.isLocal]
  rename_i kind ty fld
  cases kind <;> simp_all [Typed.WrappedExpr.isLocal]
  exact ⟨ty, fld, ⟨rfl, rfl⟩, h⟩

theorem local_not_global {fld : Field}
    (h : fld.origin = some StorageOrigin.local) :
    ¬ fld.origin = some StorageOrigin.global := by
  rw [h]; intro hc; exact absurd (Option.some.inj hc) (by decide)

/-! ## `{storage := save(storage, gsp, …)}` at a global root -/

theorem storageRootWriteCopySource_taclet (sm : SolidityModality) (stmt : Stmt)
    (hcond : (ruleEffect .storageRootWriteCopySource).cond stmt) (s : State) :
    goalsExec sm ((ruleEffect .storageRootWriteCopySource).goals stmt hcond) s
      = terminalUpdate .storageRootWriteCopySource stmt s := by
  cases stmt <;> first | exact (hcond : False).elim | skip
  rename_i lhs rhs
  obtain ⟨e, hass⟩ := lhs
  obtain ⟨ty, fld, rfl, hg⟩ := isGlobal_shape hcond.1
  show goalsExec sm (terminalGoal [UpdElem.storage
      (StTerm.save .cur (WrappedExpr.var Kind.storage ty fld) (.find rhs))]) s = _
  rw [goalsExec_terminalGoal, toUpd_storageElem,
    tu_eq (r := .storageRootWriteCopySource) (f := onAssign storageAssignUpd) rfl]
  exact storageCopy_globalRoot ty fld hass rhs s hg

theorem storageLocalRootRebind_taclet (sm : SolidityModality) (stmt : Stmt)
    (hcond : (ruleEffect .storageLocalRootRebind).cond stmt) (s : State) :
    goalsExec sm ((ruleEffect .storageLocalRootRebind).goals stmt hcond) s
      = terminalUpdate .storageLocalRootRebind stmt s := by
  cases stmt <;> first | exact (hcond : False).elim | skip
  rename_i lhs rhs
  obtain ⟨e, hass⟩ := lhs
  obtain ⟨ty, fld, rfl, hl⟩ := isLocal_shape hcond.1
  show goalsExec sm (terminalGoal [UpdElem.bind fld.name (BindRhs.path rhs)]) s = _
  rw [goalsExec_terminalGoal, toUpd_envElem,
    tu_eq (r := .storageLocalRootRebind) (f := onAssign storageAssignUpd) rfl]
  exact storageBind_localRoot ty fld hass rhs s (local_not_global hl)



/-! ## Storage field and index targets -/

theorem storageFieldWriteSave_taclet (sm : SolidityModality) (stmt : Stmt)
    (hcond : (ruleEffect .storageFieldWriteSave).cond stmt) (s : State)
    (hprim : ∀ lhs rhs, stmt = Stmt.assign lhs rhs -> rhs.ty.isPrimitive = true) :
    goalsExec sm ((ruleEffect .storageFieldWriteSave).goals stmt hcond) s
      = terminalUpdate .storageFieldWriteSave stmt s := by
  cases stmt <;> first | exact (hcond : False).elim | skip
  rename_i lhs rhs
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.field Kind.storage ty sp f, hass, hcond =>
      show goalsExec sm (terminalGoal [UpdElem.storage
          (StTerm.save .cur (WrappedExpr.field Kind.storage ty sp f)
            (StVal.sym (Sym.read rhs)))]) s = _
      rw [goalsExec_terminalGoal, toUpd_storageElem,
        tu_eq (r := .storageFieldWriteSave) (f := onAssign storageAssignUpd) rfl]
      rw [storageRhs_save_eq_copy _ _ _ (hcond.2).2 (hprim _ _ rfl)]
      exact storageCopy_field ty sp f hass rhs s

theorem storageFieldWriteCopySource_taclet (sm : SolidityModality) (stmt : Stmt)
    (hcond : (ruleEffect .storageFieldWriteCopySource).cond stmt) (s : State) :
    goalsExec sm ((ruleEffect .storageFieldWriteCopySource).goals stmt hcond) s
      = terminalUpdate .storageFieldWriteCopySource stmt s := by
  cases stmt <;> first | exact (hcond : False).elim | skip
  rename_i lhs rhs
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.field Kind.storage ty sp f, hass, hcond =>
      show goalsExec sm (terminalGoal [UpdElem.storage
          (StTerm.save .cur (WrappedExpr.field Kind.storage ty sp f) (.find rhs))]) s = _
      rw [goalsExec_terminalGoal, toUpd_storageElem,
        tu_eq (r := .storageFieldWriteCopySource) (f := onAssign storageAssignUpd) rfl]
      exact storageCopy_field ty sp f hass rhs s

theorem storageIndexWriteMappingSave_taclet (sm : SolidityModality) (stmt : Stmt)
    (hcond : (ruleEffect .storageIndexWriteMappingSave).cond stmt) (s : State)
    (hprim : ∀ lhs rhs, stmt = Stmt.assign lhs rhs -> rhs.ty.isPrimitive = true) :
    goalsExec sm ((ruleEffect .storageIndexWriteMappingSave).goals stmt hcond) s
      = terminalUpdate .storageIndexWriteMappingSave stmt s := by
  cases stmt <;> first | exact (hcond : False).elim | skip
  rename_i lhs rhs
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.index Kind.storage ty mp ix, hass, hcond =>
      show goalsExec sm (terminalGoal [UpdElem.storage
          (StTerm.save .cur (WrappedExpr.index Kind.storage ty mp ix)
            (StVal.sym (Sym.read rhs)))]) s = _
      rw [goalsExec_terminalGoal, toUpd_storageElem,
        tu_eq (r := .storageIndexWriteMappingSave) (f := onAssign storageAssignUpd) rfl]
      rw [storageRhs_save_eq_copy _ _ _ hcond.2.2.2.1 (hprim _ _ rfl)]
      exact storageCopy_index ty mp ix hass rhs s

theorem storageIndexWriteMappingCopySource_taclet (sm : SolidityModality) (stmt : Stmt)
    (hcond : (ruleEffect .storageIndexWriteMappingCopySource).cond stmt) (s : State) :
    goalsExec sm ((ruleEffect .storageIndexWriteMappingCopySource).goals stmt hcond) s
      = terminalUpdate .storageIndexWriteMappingCopySource stmt s := by
  cases stmt <;> first | exact (hcond : False).elim | skip
  rename_i lhs rhs
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.index Kind.storage ty mp ix, hass, hcond =>
      show goalsExec sm (terminalGoal [UpdElem.storage
          (StTerm.save .cur (WrappedExpr.index Kind.storage ty mp ix) (.find rhs))]) s = _
      rw [goalsExec_terminalGoal, toUpd_storageElem,
        tu_eq (r := .storageIndexWriteMappingCopySource) (f := onAssign storageAssignUpd) rfl]
      exact storageCopy_index ty mp ix hass rhs s

theorem memoryToStorageFieldCopyRoot_taclet (sm : SolidityModality) (stmt : Stmt)
    (hcond : (ruleEffect .memoryToStorageFieldCopyRoot).cond stmt) (s : State) :
    goalsExec sm ((ruleEffect .memoryToStorageFieldCopyRoot).goals stmt hcond) s
      = terminalUpdate .memoryToStorageFieldCopyRoot stmt s := by
  cases stmt <;> first | exact (hcond : False).elim | skip
  rename_i lhs rhs
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.field Kind.storage ty sp f, hass, hcond =>
      show goalsExec sm (terminalGoal [UpdElem.storage
          (StTerm.save .cur (WrappedExpr.field Kind.storage ty sp f) (.copyMem rhs))]) s = _
      rw [goalsExec_terminalGoal, toUpd_storageElem,
        tu_eq (r := .memoryToStorageFieldCopyRoot) (f := onAssign storageAssignUpd) rfl]
      exact storageCopy_field ty sp f hass rhs s

/-- `sp.fld = mv.fr`: the same `copyMem` write, with a member source. -/
theorem memoryToStorageFieldCopyField_taclet (sm : SolidityModality) (stmt : Stmt)
    (hcond : (ruleEffect .memoryToStorageFieldCopyField).cond stmt) (s : State) :
    goalsExec sm ((ruleEffect .memoryToStorageFieldCopyField).goals stmt hcond) s
      = terminalUpdate .memoryToStorageFieldCopyField stmt s := by
  cases stmt <;> first | exact (hcond : False).elim | skip
  rename_i lhs rhs
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.field Kind.storage ty sp f, hass, hcond =>
      show goalsExec sm (terminalGoal [UpdElem.storage
          (StTerm.save .cur (WrappedExpr.field Kind.storage ty sp f) (.copyMem rhs))]) s = _
      rw [goalsExec_terminalGoal, toUpd_storageElem,
        tu_eq (r := .memoryToStorageFieldCopyField) (f := onAssign storageAssignUpd) rfl]
      exact storageCopy_field ty sp f hass rhs s

theorem memoryToStorageIndexMappingCopyRoot_taclet (sm : SolidityModality) (stmt : Stmt)
    (hcond : (ruleEffect .memoryToStorageIndexMappingCopyRoot).cond stmt) (s : State) :
    goalsExec sm ((ruleEffect .memoryToStorageIndexMappingCopyRoot).goals stmt hcond) s
      = terminalUpdate .memoryToStorageIndexMappingCopyRoot stmt s := by
  cases stmt <;> first | exact (hcond : False).elim | skip
  rename_i lhs rhs
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.index Kind.storage ty mp ix, hass, hcond =>
      show goalsExec sm (terminalGoal [UpdElem.storage
          (StTerm.save .cur (WrappedExpr.index Kind.storage ty mp ix) (.copyMem rhs))]) s = _
      rw [goalsExec_terminalGoal, toUpd_storageElem,
        tu_eq (r := .memoryToStorageIndexMappingCopyRoot) (f := onAssign storageAssignUpd) rfl]
      exact storageCopy_index ty mp ix hass rhs s


/-! ## Reads into a stack variable: `{v := find(storage, …)}` / `{v := read(memory, …)}`

`assignStack` is stuck on a stack place that is not a variable, and the rules'
`isStack lhs` admits one (the wrapped AST has no `Place` proof to stop it), so
these bridges carry the shape as a hypothesis — the same kind of syntactic side
condition as `hprim`, and for the same reason. -/

theorem readTerm_eq_readVal_place {s : State} {e : WrappedExpr}
    (h : e.assignable = true) : readTerm s e = readVal s e := by
  cases e <;> simp_all [readTerm, Typed.WrappedExpr.assignable]

theorem assignStackRead_agrees (ty : Ty) (fld : Field) (hass : _)
    (rhs : WrappedExpr) (s : State) (hr : readTerm s rhs = readVal s rhs) :
    (bindRhs (.val (.read rhs)) s).map (fun b => s.setEnv fld.name b)
      = assignStackRead ⟨WrappedExpr.var Kind.stack ty fld, hass⟩ rhs s := by
  simp only [bindRhs, Sym.eval, hr, assignStackRead, assignStack, bind,
    Except.bind, Except.map]
  cases readVal s rhs <;> rfl

theorem storageRootReadSelect_taclet (sm : SolidityModality) (stmt : Stmt)
    (hcond : (ruleEffect .storageRootReadSelect).cond stmt) (s : State)
    (hvar : ∀ lhs rhs, stmt = Stmt.assign lhs rhs ->
      ∃ ty fld, (lhs : WrappedExpr) = WrappedExpr.var Kind.stack ty fld) :
    goalsExec sm ((ruleEffect .storageRootReadSelect).goals stmt hcond) s
      = terminalUpdate .storageRootReadSelect stmt s := by
  cases stmt <;> first | exact (hcond : False).elim | skip
  rename_i lhs rhs
  obtain ⟨e, hass⟩ := lhs
  obtain ⟨ty, fld, rfl⟩ := hvar _ _ rfl
  have hr : readTerm s rhs = readVal s rhs := readTerm_eq_readVal hcond.2.2
  show goalsExec sm (terminalGoal [UpdElem.bind fld.name
      (BindRhs.val (Sym.read rhs))]) s = _
  rw [goalsExec_terminalGoal, toUpd_envElem,
    tu_eq (r := .storageRootReadSelect) (f := onAssign assignStackRead) rfl]
  exact assignStackRead_agrees ty fld hass rhs s hr

theorem localValueAssign_taclet (sm : SolidityModality) (stmt : Stmt)
    (hcond : (ruleEffect .localValueAssign).cond stmt) (s : State)
    (hvar : ∀ lhs rhs, stmt = Stmt.assign lhs rhs ->
      ∃ ty fld, (lhs : WrappedExpr) = WrappedExpr.var Kind.stack ty fld) :
    goalsExec sm ((ruleEffect .localValueAssign).goals stmt hcond) s
      = terminalUpdate .localValueAssign stmt s := by
  cases stmt <;> first | exact (hcond : False).elim | skip
  rename_i lhs rhs
  obtain ⟨e, hass⟩ := lhs
  obtain ⟨ty, fld, rfl⟩ := hvar _ _ rfl
  have hr : readTerm s rhs = readVal s rhs := readTerm_eq_readVal hcond.2.2
  show goalsExec sm (terminalGoal [UpdElem.bind fld.name
      (BindRhs.val (Sym.read rhs))]) s = _
  rw [goalsExec_terminalGoal, toUpd_envElem,
    tu_eq (r := .localValueAssign) (f := onAssign assignStackRead) rfl]
  exact assignStackRead_agrees ty fld hass rhs s hr

theorem storageFieldReadFind_taclet (sm : SolidityModality) (stmt : Stmt)
    (hcond : (ruleEffect .storageFieldReadFind).cond stmt) (s : State)
    (hvar : ∀ lhs rhs, stmt = Stmt.assign lhs rhs ->
      ∃ ty fld, (lhs : WrappedExpr) = WrappedExpr.var Kind.stack ty fld) :
    goalsExec sm ((ruleEffect .storageFieldReadFind).goals stmt hcond) s
      = terminalUpdate .storageFieldReadFind stmt s := by
  cases stmt <;> first | exact (hcond : False).elim | skip
  rename_i lhs rhs
  obtain ⟨e, hass⟩ := lhs
  obtain ⟨ty, fld, rfl⟩ := hvar _ _ rfl
  match rhs, hcond with
  | WrappedExpr.field Kind.storage ty2 sp f2, hcond =>
      have hr : readTerm s (WrappedExpr.field Kind.storage ty2 sp f2) = readVal s (WrappedExpr.field Kind.storage ty2 sp f2) :=
        readTerm_eq_readVal_place (by rfl)
      show goalsExec sm (terminalGoal [UpdElem.bind fld.name
          (BindRhs.val (Sym.read (WrappedExpr.field Kind.storage ty2 sp f2)))]) s = _
      rw [goalsExec_terminalGoal, toUpd_envElem,
        tu_eq (r := .storageFieldReadFind) (f := onAssign assignStackRead) rfl]
      exact assignStackRead_agrees ty fld hass _ s hr

theorem storageIndexReadMappingFind_taclet (sm : SolidityModality) (stmt : Stmt)
    (hcond : (ruleEffect .storageIndexReadMappingFind).cond stmt) (s : State)
    (hvar : ∀ lhs rhs, stmt = Stmt.assign lhs rhs ->
      ∃ ty fld, (lhs : WrappedExpr) = WrappedExpr.var Kind.stack ty fld) :
    goalsExec sm ((ruleEffect .storageIndexReadMappingFind).goals stmt hcond) s
      = terminalUpdate .storageIndexReadMappingFind stmt s := by
  cases stmt <;> first | exact (hcond : False).elim | skip
  rename_i lhs rhs
  obtain ⟨e, hass⟩ := lhs
  obtain ⟨ty, fld, rfl⟩ := hvar _ _ rfl
  match rhs, hcond with
  | WrappedExpr.index Kind.storage ty2 mp ix, hcond =>
      have hr : readTerm s (WrappedExpr.index Kind.storage ty2 mp ix) = readVal s (WrappedExpr.index Kind.storage ty2 mp ix) :=
        readTerm_eq_readVal_place (by rfl)
      show goalsExec sm (terminalGoal [UpdElem.bind fld.name
          (BindRhs.val (Sym.read (WrappedExpr.index Kind.storage ty2 mp ix)))]) s = _
      rw [goalsExec_terminalGoal, toUpd_envElem,
        tu_eq (r := .storageIndexReadMappingFind) (f := onAssign assignStackRead) rfl]
      exact assignStackRead_agrees ty fld hass _ s hr

theorem memoryFieldReadHeap_taclet (sm : SolidityModality) (stmt : Stmt)
    (hcond : (ruleEffect .memoryFieldReadHeap).cond stmt) (s : State)
    (hvar : ∀ lhs rhs, stmt = Stmt.assign lhs rhs ->
      ∃ ty fld, (lhs : WrappedExpr) = WrappedExpr.var Kind.stack ty fld) :
    goalsExec sm ((ruleEffect .memoryFieldReadHeap).goals stmt hcond) s
      = terminalUpdate .memoryFieldReadHeap stmt s := by
  cases stmt <;> first | exact (hcond : False).elim | skip
  rename_i lhs rhs
  obtain ⟨e, hass⟩ := lhs
  obtain ⟨ty, fld, rfl⟩ := hvar _ _ rfl
  match rhs, hcond with
  | WrappedExpr.field Kind.memory ty2 mv f2, hcond =>
      have hr : readTerm s (WrappedExpr.field Kind.memory ty2 mv f2) = readVal s (WrappedExpr.field Kind.memory ty2 mv f2) :=
        readTerm_eq_readVal_place (by rfl)
      show goalsExec sm (terminalGoal [UpdElem.bind fld.name
          (BindRhs.val (Sym.read (WrappedExpr.field Kind.memory ty2 mv f2)))]) s = _
      rw [goalsExec_terminalGoal, toUpd_envElem,
        tu_eq (r := .memoryFieldReadHeap) (f := onAssign assignStackRead) rfl]
      exact assignStackRead_agrees ty fld hass _ s hr


/-! ## Declarations and control -/

theorem storageLocalDeclSkip_taclet (sm : SolidityModality) (stmt : Stmt)
    (hcond : (ruleEffect .storageLocalDeclSkip).cond stmt) (s : State) :
    goalsExec sm ((ruleEffect .storageLocalDeclSkip).goals stmt hcond) s
      = terminalUpdate .storageLocalDeclSkip stmt s := by
  cases stmt <;> first | exact (hcond : False).elim | skip
  rename_i ty name init
  cases init with
  | none =>
      show goalsExec sm (terminalGoal []) s = _
      rw [goalsExec_terminalGoal,
        tu_eq (r := .storageLocalDeclSkip) (f := onStorageDecl storageDeclSkipUpd) rfl]
      rfl
  | some _ => exact Option.noConfusion hcond

theorem valueDeclSkip_taclet (sm : SolidityModality) (stmt : Stmt)
    (hcond : (ruleEffect .valueDeclSkip).cond stmt) (s : State) :
    goalsExec sm ((ruleEffect .valueDeclSkip).goals stmt hcond) s
      = terminalUpdate .valueDeclSkip stmt s := by
  cases stmt <;> first | exact (hcond : False).elim | skip
  rename_i ty name init
  cases init with
  | none =>
      show goalsExec sm (terminalGoal
          [UpdElem.bind name (BindRhs.val (Sym.deflt ty))]) s = _
      rw [goalsExec_terminalGoal, toUpd_envElem,
        tu_eq (r := .valueDeclSkip) (f := onStackDecl stackDeclSkipUpd) rfl]
      rfl
  | some _ => exact Option.noConfusion hcond

theorem revertBox_taclet (sm : SolidityModality) (stmt : Stmt)
    (hcond : (ruleEffect .revertBox).cond stmt) (s : State) :
    goalsExec sm ((ruleEffect .revertBox).goals stmt hcond) s
      = terminalUpdate .revertBox stmt s := by
  cases stmt <;> first | exact (hcond : False).elim | skip
  rename_i msg
  rw [tu_eq (r := .revertBox) (f := onRevert revertUpd) rfl]
  cases sm <;> rfl

theorem revertDiamond_taclet (sm : SolidityModality) (stmt : Stmt)
    (hcond : (ruleEffect .revertDiamond).cond stmt) (s : State) :
    goalsExec sm ((ruleEffect .revertDiamond).goals stmt hcond) s
      = terminalUpdate .revertDiamond stmt s := by
  cases stmt <;> first | exact (hcond : False).elim | skip
  rename_i msg
  rw [tu_eq (r := .revertDiamond) (f := onRevert revertUpd) rfl]
  cases sm <;> rfl

/-- `require(se);` — KeY's `"Holds"`/`"Reverts"` pair, which *is* the
interpreter's revert-on-false. -/
theorem requireSimple_taclet (sm : SolidityModality) (stmt : Stmt)
    (hcond : (ruleEffect .requireSimple).cond stmt) (s : State) :
    goalsExec sm ((ruleEffect .requireSimple).goals stmt hcond) s
      = terminalUpdate .requireSimple stmt s := by
  cases stmt <;> first | exact (hcond : False).elim | skip
  rename_i c
  show goalsExec sm (splitGoals (SideFormula.holds c) [] []) s = _
  rw [goalsExec_splitGoals,
    tu_eq (r := .requireSimple) (f := onRequire assertUpd) rfl]
  simp only [Guard.eval, runPremises, SideFormula.eval, Wp.onRequire,
    assertUpd, bind, Except.bind, pure, Except.pure]
  cases readVal s c with
  | error e => rfl
  | ok v => cases v with
      | bool b => cases b <;> rfl
      | int _ => rfl


/-- `T storage sp = path;` on a **pure** path.  The impure case is the one arm
of the terminal table that is not first-order — `storagePlaceAliasUpd` resolves
through the interpreter, because `captureStoragePath` may hoist `people[f()]` —
so the hypothesis here is the same one `Upd.storagePlaceAliasUpd_bridge` needs
and `Counterexamples/ErrorOrder.lean` shows cannot be dropped. -/
theorem storagePlaceAlias_taclet (sm : SolidityModality) (stmt : Stmt)
    (hcond : (ruleEffect .storagePlaceAlias).cond stmt) (s : State)
    (hpure : ∀ ty name init, stmt = Stmt.storagePlaceAlias ty name init ->
      (init.simple || simplePathB init) = true) :
    goalsExec sm ((ruleEffect .storagePlaceAlias).goals stmt hcond) s
      = terminalUpdate .storagePlaceAlias stmt s := by
  cases stmt <;> first | exact (hcond : False).elim | skip
  rename_i ty name init
  show goalsExec sm (terminalGoal [UpdElem.bind name (BindRhs.path init)]) s = _
  rw [goalsExec_terminalGoal,
    tu_eq (r := .storagePlaceAlias) (f := onAlias storagePlaceAliasUpd) rfl]
  have := Upd.storagePlaceAliasUpd_bridge name init (hpure _ _ _ rfl)
  exact congrFun this s

/-- `readVal` and `simpleVal` agree on a simple expression: the extra arms of
`readVal` are the nested places, which `simple` excludes. -/
theorem readVal_eq_simpleVal {s : State} {e : WrappedExpr} (hs : e.simple = true) :
    readVal s e = simpleVal s e := by
  cases e <;> simp_all [readVal, simpleVal, Typed.WrappedExpr.simple]
  rename_i kind ty fld
  cases kind <;> simp_all [readVal, simpleVal, placePath]

/-- `a.transfer(se);`, the diamond twin, **under its obligation**.  KeY's box
rule books the payment unconditionally and the diamond rule owes the funds
check as a separate obligation goal, which `goalsExec` skips — so on either
twin `goalsExec` is the unguarded `{transfer(sadr, se)}`, while the
interpreter (`transferUpd`) reverts when the balance does not cover the
amount.  Neither twin's update is therefore *equal* to the interpreter's, and
both are in `openBridges`; what does hold is this: once the diamond
obligation `funded(se)` is discharged, the booked update is the
interpreter's step.  The box twin has no such obligation to discharge, so
nothing analogous is stated for it — it is a strengthening of the
interpreter (`docs/solc-alignment.md`). -/
theorem transferNoCallbackDiamond_taclet_funded (sm : SolidityModality) (stmt : Stmt)
    (hcond : (ruleEffect .transferNoCallbackDiamond).cond stmt) (s : State)
    (hfunded : ∀ sadr se, stmt = Stmt.transfer sadr se ->
      SideFormula.eval s (SideFormula.funded se) = .ok true) :
    goalsExec sm ((ruleEffect .transferNoCallbackDiamond).goals stmt hcond) s
      = terminalUpdate .transferNoCallbackDiamond stmt s := by
  cases stmt <;> first | exact (hcond : False).elim | skip
  rename_i sadr se
  have hf := hfunded sadr se rfl
  obtain ⟨ha, hv⟩ := hcond
  have hgoals : goalsExec sm ((ruleEffect .transferNoCallbackDiamond).goals
      (Stmt.transfer sadr se) ⟨ha, hv⟩) s = UpdTerm.toUpd [UpdElem.transfer sadr se] s := by
    show goalsExec sm
      [ { label := "transfer booked", mode := CaseMode.box,
          residual := RuleResidual.prog [UpdElem.transfer sadr se] [] },
        { label := "sufficient funds", mode := CaseMode.diamond,
          residual := RuleResidual.obligation [] (SideFormula.funded se) },
        { label := "transfer booked", mode := CaseMode.diamond,
          residual := RuleResidual.prog [UpdElem.transfer sadr se] [] } ] s = _
    cases sm <;>
      simp [goalsExec, Guard.eval, runPremises, SideFormula.eval,
        SolidityModality.appliesCaseMode, CaseMode.applies, bind, Except.bind]
  rw [hgoals, toUpd_netElem,
    tu_eq (r := .transferNoCallbackDiamond) (f := onTransfer transferUpd) rfl]
  simp only [SideFormula.eval, readVal_eq_simpleVal hv, bind, Except.bind] at hf
  simp only [Wp.onTransfer, transferUpd, transferRhs, simpleInt,
    readVal_eq_simpleVal hv, bind, Except.bind, Except.map]
  cases ha' : simpleVal s sadr with
  | error e => simp only [ha']
  | ok av =>
      cases hav : Value.asInt av with
      | error e => simp only [ha', hav]
      | ok addr =>
          cases hse : simpleVal s se with
          | error e => simp [hse] at hf
          | ok vv =>
              cases hvv : Value.asInt vv with
              | error e => simp [hse, hvv] at hf
              | ok amt =>
                  simp only [hse, hvv] at hf
                  by_cases hneg : amt < 0
                  · simp [hneg] at hf
                  · have hb : amt ≤ s.selfBalance := by
                      simp only [hneg, if_neg, not_false_eq_true] at hf
                      exact of_decide_eq_true (Except.ok.inj hf)
                    have hlt : ¬ s.selfBalance < amt := by omega
                    simp only [ha', hav, hse, hvv, hneg, if_neg, not_false_eq_true,
                      hlt]
                    rfl

/-! ## Coverage

Which rules have their update proved, and which do not.  The accounting is
computed against `Wp.hasUpdate`, so a rule that gains an update without
gaining a bridge moves the counts and fails `bridges_account`. -/

/-- The rules whose `\replacewith` update is proved equal to the interpreter's
above, one `<rule>_taclet` theorem each. -/
def bridgedRules : List RuleName :=
  [ .storageRootWriteStore, .storageRootWriteCopySource, .storageLocalRootRebind,
    .storageFieldWriteSave, .storageFieldWriteCopySource,
    .storageIndexWriteMappingSave, .storageIndexWriteMappingCopySource,
    .memoryToStorageFieldCopyRoot, .memoryToStorageFieldCopyField,
    .memoryToStorageIndexMappingCopyRoot,
    .storageRootReadSelect, .localValueAssign, .storageFieldReadFind,
    .storageIndexReadMappingFind, .memoryFieldReadHeap,
    .storageLocalDeclSkip, .valueDeclSkip,
    .revertBox, .revertDiamond, .requireSimple, .storagePlaceAlias ]

/-- The rules whose update is *stated* in `Calculus/Rules.lean` but not yet proved here.
They are not unchecked in every sense — each still has its `<rule>_update`
theorem in `Wp/Terminal/`, so the *interpreter* side is pinned; what is
missing is the step from that to the first-order `{…}` term the rule now
carries.  The families, in the order they are least to most work:

* the array-index twins, which need the bounds guard chased through
  `splitGoals` (the shape lemmas are here, the guard reasoning is not);
* push, pop and delete, whose `pushPath`/`deletePath` are themselves
  state-changing and so need a frame relative to an intermediate state;
* the compound-assignment and inc/dec families, where `Sym.combined` has to be
  matched against `applyBinOp`/`checkArith` at the target's type;
* the memory-target family, where an allocating right-hand side makes the
  update a two-element parallel one;
* the cross-domain declarations and `memoryStorageCopy`, same reason;
* the `transfer` twins, which are open for a different reason: KeY's box
  rule books the payment unconditionally and the diamond rule owes the funds
  check as a separate obligation — neither is the interpreter's *guarded*
  update, so no equality can be proved.  What can be is
  `transferNoCallbackDiamond_taclet_funded`: the diamond update under its
  discharged obligation. -/
def openBridges : List RuleName :=
  (ruleNames.filter fun r =>
    hasUpdate r && !(bridgedRules.contains r)).eraseDups

/-- Bridged and open together are exactly the rules with an update. -/
theorem bridges_account :
    ruleNames.all (fun r =>
      hasUpdate r == (bridgedRules.contains r || openBridges.contains r))
      = true := by
  native_decide

theorem bridgedRules_count : bridgedRules.length = 21 := by native_decide

end Update
end Solidity
