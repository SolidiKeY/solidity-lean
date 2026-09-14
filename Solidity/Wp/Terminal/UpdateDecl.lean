import Solidity.Wp.Terminal.UpdateStorage

/-!
# Terminal-rule updates: declarations and `delete`

`valueDeclSkip`, `storageLocalDeclSkip`, `storagePlaceAlias`,
`memoryDeclFreshAlloc`, `storageToMemoryDeclCopy{Field,Root}`,
`storageDeleteSimpleTarget`, `memoryDeleteSimpleTarget`.
-/

namespace Solidity
namespace Wp

open Semantics Rules

/-! ## Declarations -/

theorem valueDeclSkip_update (s : State) (ty : Ty) (name : Name)
    (init : Option WrappedExpr)
    (hcond : (ruleEffect .valueDeclSkip).cond (Stmt.stackDecl ty name init)) :
    execStmt s (Stmt.stackDecl ty name init) =
      terminalUpdate .valueDeclSkip (Stmt.stackDecl ty name init) s := by
  have hc : init = none := hcond
  subst hc
  show execStmt s (Stmt.stackDecl ty name none) =
    .ok (s.setEnv name (Binding.val (defaultValue ty)))
  cases ty with
  | prim pt => cases pt <;> first | rfl | (rw [execStmt] <;> simp)
  | ref r => first | rfl | (rw [execStmt] <;> simp)

theorem storageLocalDeclSkip_update (s : State) (ty : Ty) (name : Name)
    (init : Option WrappedExpr)
    (hcond : (ruleEffect .storageLocalDeclSkip).cond
      (Stmt.storageDecl ty name init)) :
    execStmt s (Stmt.storageDecl ty name init) =
      terminalUpdate .storageLocalDeclSkip (Stmt.storageDecl ty name init) s := by
  have hc : init = none := hcond
  subst hc
  rw [execStmt]
  rfl

theorem storagePlaceAlias_update (s : State) (ty : Ty) (name : Name)
    (init : WrappedExpr)
    (_hcond : (ruleEffect .storagePlaceAlias).cond
      (Stmt.storagePlaceAlias ty name init)) :
    execStmt s (Stmt.storagePlaceAlias ty name init) =
      terminalUpdate .storagePlaceAlias (Stmt.storagePlaceAlias ty name init) s := by
  show execStmt s (Stmt.storagePlaceAlias ty name init) =
    storagePlaceAliasUpd name init s
  rw [execStmt]
  simp only [storagePlaceAliasUpd, bind, Except.bind]

/-- On a pure (simple-path) alias source the one interpreter call in
`storagePlaceAliasUpd` is the `placePath` reader. -/
theorem storagePlaceAliasUpd_pure (s : State) (name : Name) (init : WrappedExpr)
    (h : (init.simple || simplePathB init) = true) :
    storagePlaceAliasUpd name init s =
      (placePath s init).map fun p => s.setEnv name (Binding.spath p.1 p.2) := by
  simp only [storagePlaceAliasUpd, resolveS_pathB s init h, bind, Except.bind,
    Except.map]
  cases placePath s init with
  | error e => rfl
  | ok p => obtain ⟨r, sg⟩ := p; rfl

theorem memoryDeclFreshAlloc_update (s : State) (ty : Ty) (name : Name)
    (init : Option WrappedExpr)
    (hcond : (ruleEffect .memoryDeclFreshAlloc).cond
      (Stmt.memoryDecl ty name init)) :
    execStmt s (Stmt.memoryDecl ty name init) =
      terminalUpdate .memoryDeclFreshAlloc (Stmt.memoryDecl ty name init) s := by
  have hc : init = none := hcond
  subst hc
  show execStmt s (Stmt.memoryDecl ty name none) = memoryDeclUpd ty name none s
  cases ty with
  | prim pt => first | rfl | (rw [execStmt] <;> simp)
  | ref r =>
      rw [execStmt]
      simp only [memoryDeclUpd, bind, Except.bind]

/-- A memory declaration from a simple storage source. -/
theorem execStmt_memoryDecl_storage (s : State) (ty : Ty) (name : Name)
    (rhs : WrappedExpr) (hk : rhs.kind = Kind.storage)
    (hp : (rhs.simple || simplePathB rhs) = true) :
    execStmt s (Stmt.memoryDecl ty name (some rhs)) =
      memoryDeclUpd ty name (some rhs) s := by
  rw [execStmt]
  simp only [memoryDeclUpd, hk, resolveS_pathB s rhs hp, bind, Except.bind,
    Except.map]
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

theorem storageToMemoryDeclCopyField_update (s : State) (ty : Ty) (name : Name)
    (init : Option WrappedExpr)
    (hcond : (ruleEffect .storageToMemoryDeclCopyField).cond
      (Stmt.memoryDecl ty name init)) :
    execStmt s (Stmt.memoryDecl ty name init) =
      terminalUpdate .storageToMemoryDeclCopyField (Stmt.memoryDecl ty name init) s := by
  show execStmt s (Stmt.memoryDecl ty name init) = memoryDeclUpd ty name init s
  match init, hcond with
  | some (WrappedExpr.field Kind.storage t path f), hc =>
      have hp : isSimple path := hc
      have hp' : path.simple = true := hp
      exact execStmt_memoryDecl_storage s ty name _ rfl (by simp [simplePathB, hp'])

theorem storageToMemoryDeclCopyRoot_update (s : State) (ty : Ty) (name : Name)
    (init : Option WrappedExpr)
    (hcond : (ruleEffect .storageToMemoryDeclCopyRoot).cond
      (Stmt.memoryDecl ty name init)) :
    execStmt s (Stmt.memoryDecl ty name init) =
      terminalUpdate .storageToMemoryDeclCopyRoot (Stmt.memoryDecl ty name init) s := by
  show execStmt s (Stmt.memoryDecl ty name init) = memoryDeclUpd ty name init s
  match init, hcond with
  | some rhs, hc =>
      have hc' : isStorage rhs ∧ isSimple rhs := hc
      have hk : rhs.kind = Kind.storage := by
        simpa [isStorage, Typed.WrappedExpr.isStorage] using hc'.1
      have hs : rhs.simple = true := hc'.2
      exact execStmt_memoryDecl_storage s ty name rhs hk (by simp [hs])

/-! ## `delete` -/

/-- The interpreter's storage `delete` through a resolved path. -/
theorem execStmt_delete_storage (s : State) (target : PlaceExpr)
    (hk : target.expr.kind = Kind.storage)
    (hres : resolveS s target.expr = deletePath s target.expr) :
    execStmt s (Stmt.delete target) = storageDeleteUpd target s := by
  rw [execStmt, hk, hres]
  simp only [storageDeleteUpd, bind, Except.bind]

theorem storageDeleteSimpleTarget_update (s : State) (target : PlaceExpr)
    (hcond : (ruleEffect .storageDeleteSimpleTarget).cond
      (Stmt.delete target)) :
    execStmt s (Stmt.delete target) =
      terminalUpdate .storageDeleteSimpleTarget (Stmt.delete target) s := by
  have hc : isSimpleStorageDeleteTarget target := hcond
  show execStmt s (Stmt.delete target) = storageDeleteUpd target s
  apply execStmt_delete_storage
  all_goals
    obtain ⟨e, hass⟩ := target
    simp only at hc ⊢
  all_goals
    cases e with
    | var k t fld =>
        cases k with
        | storage =>
            first
            | rfl
            | (rw [resolveS_var]; rfl)
        | _ => exact absurd hc (by simp [isSimpleStorageDeleteTarget])
    | field k t base f =>
        cases k with
        | storage =>
            have hp : isSimple base := hc
            have hp' : base.simple = true := hp
            first
            | rfl
            | (rw [resolveS_placePath s _ (by simp [simplePathB, hp'])]; rfl)
        | _ => exact absurd hc (by simp [isSimpleStorageDeleteTarget])
    | index k t base ix =>
        cases k with
        | storage =>
            have hc' : isSimple base ∧ isSimple ix ∧
                (isArray base ∨ isMapping base) := hc
            have hp' : base.simple = true := hc'.1
            have hi' : ix.simple = true := hc'.2.1
            first
            | rfl
            | (rw [resolveS_placePath s _ (by simp [simplePathB, hp', hi'])]; rfl)
        | _ => exact absurd hc (by simp [isSimpleStorageDeleteTarget])
    | pushPlace path =>
        have hc' : path.kind = Kind.storage ∧ isSimple path := hc
        have hp' : path.simple = true := hc'.2
        first
        | rfl
        | exact resolveS_pushPlace s path (by simp [hp'])
    | _ => exact absurd hass (by simp [Typed.WrappedExpr.assignable])

/-- The interpreter's memory `delete` on a nested place, by the slot's type. -/
theorem memoryDeleteSimpleTarget_update (s : State) (target : PlaceExpr)
    (hcond : (ruleEffect .memoryDeleteSimpleTarget).cond
      (Stmt.delete target)) :
    execStmt s (Stmt.delete target) =
      terminalUpdate .memoryDeleteSimpleTarget (Stmt.delete target) s := by
  have hc : isSimpleMemoryDeleteTarget target := hcond
  show execStmt s (Stmt.delete target) = memoryDeleteUpd target s
  obtain ⟨e, hass⟩ := target
  simp only at hc ⊢
  cases e with
  | var k t fld =>
      cases k with
      | memory =>
          rw [execStmt]
          simp only [Typed.WrappedExpr.kind, memoryDeleteUpd]
          cases t with
          | prim pt => rfl
          | ref r =>
              simp only [bind, Except.bind]
      | _ => exact absurd hc (by simp [isSimpleMemoryDeleteTarget])
  | field k t base f =>
      cases k with
      | memory =>
          have hc' : isSimple base ∧ (f.isPrimitive = true ∨ f.isIdentity = true) := hc
          have hb : base.simple = true := hc'.1
          rw [execStmt]
          simp only [Typed.WrappedExpr.kind, memoryDeleteUpd, WrappedExpr.ty,
            Typed.WrappedExpr.ty]
          rw [resolveLoc_memoryField s t base f hb]
          simp only [bind, Except.bind, Except.map]
          cases memBase s base with
          | error e => rfl
          | ok id =>
              simp only [writeMemField, bind, Except.bind]
              cases t with
              | prim pt =>
                  cases pt <;> (cases s.getObj id with
                    | error e => rfl
                    | ok obj => cases obj <;> rfl)
              | ref r =>
                  cases allocDefault s r with
                  | error e => rfl
                  | ok x =>
                      obtain ⟨s', id'⟩ := x
                      simp only []
                      cases s'.getObj id with
                      | error e => rfl
                      | ok obj => cases obj <;> rfl
      | _ => exact absurd hc (by simp [isSimpleMemoryDeleteTarget])
  | index k t base ix =>
      cases k with
      | memory =>
          have hc' : isSimple base ∧ isSimple ix ∧
              (isPrimitive (WrappedExpr.index Kind.memory t base ix) ∨
                isIdentity (WrappedExpr.index Kind.memory t base ix)) := hc
          have hb : base.simple = true := hc'.1
          have hi : ix.simple = true := hc'.2.1
          rw [execStmt]
          simp only [Typed.WrappedExpr.kind, memoryDeleteUpd, WrappedExpr.ty,
            Typed.WrappedExpr.ty]
          rw [resolveLoc_memoryIndex s t base ix hb hi]
          simp only [bind, Except.bind, Except.map]
          cases memBase s base with
          | error e => rfl
          | ok id =>
              simp only []
              cases simpleInt s ix with
              | error e => rfl
              | ok i =>
                  simp only [writeMemIndex, bind, Except.bind]
                  cases t with
                  | prim pt =>
                      cases pt <;> (cases s.getObj id with
                        | error e => rfl
                        | ok obj =>
                            cases obj with
                            | struct fields => rfl
                            | array elems =>
                                first | (simp only []; done) | (split <;> rfl))
                  | ref r =>
                      cases allocDefault s r with
                      | error e => rfl
                      | ok x =>
                          obtain ⟨s', id'⟩ := x
                          simp only []
                          cases s'.getObj id with
                          | error e => rfl
                          | ok obj =>
                              cases obj with
                              | struct fields => rfl
                              | array elems =>
                                first | (simp only []; done) | (split <;> rfl)
      | _ => exact absurd hc (by simp [isSimpleMemoryDeleteTarget])
  | pushPlace path => exact absurd hc (by simp [isSimpleMemoryDeleteTarget])
  | _ => exact absurd hass (by simp [Typed.WrappedExpr.assignable])

end Wp
end Solidity
