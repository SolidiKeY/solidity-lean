import Solidity.Wp.Terminal.UpdateStorage

/-!
# Terminal-rule updates: declarations and `delete`

`valueDeclSkip`, `storageLocalDeclSkip`, `storagePlaceAlias`,
`memoryDeclFreshAlloc`, `storageToMemoryDeclCopy{Field,Root}`,
`storage{Root,Field,Index,PushPlace}Delete`, `memoryRootDeleteFreshRebind`,
`memoryFieldDelete{Primitive,Reference}`,
`memoryIndexDelete{Primitive,Reference}{Box,Diamond}`.
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

/-- `delete(gsp)`: a global storage root; the path is the root itself. -/
theorem storageRootDelete_update (s : State) (target : PlaceExpr)
    (hcond : (ruleEffect .storageRootDelete).cond (Stmt.delete target)) :
    execStmt s (Stmt.delete target) =
      terminalUpdate .storageRootDelete (Stmt.delete target) s := by
  show execStmt s (Stmt.delete target) = storageDeleteUpd target s
  obtain ⟨e, hass⟩ := target
  match e, hass, hcond with
  | WrappedExpr.var Kind.storage t fld, hass, _ =>
      apply execStmt_delete_storage _ _ rfl
      simp only
      first
      | rfl
      | (rw [resolveS_var]; rfl)

/-- `delete(sp.fld)`: a member of a simple storage path. -/
theorem storageFieldDelete_update (s : State) (target : PlaceExpr)
    (hcond : (ruleEffect .storageFieldDelete).cond (Stmt.delete target)) :
    execStmt s (Stmt.delete target) =
      terminalUpdate .storageFieldDelete (Stmt.delete target) s := by
  show execStmt s (Stmt.delete target) = storageDeleteUpd target s
  obtain ⟨e, hass⟩ := target
  match e, hass, hcond with
  | WrappedExpr.field Kind.storage t base f, hass, hc =>
      have hp : isSimple base := hc
      have hp' : base.simple = true := hp
      apply execStmt_delete_storage _ _ rfl
      simp only
      first
      | rfl
      | (rw [resolveS_placePath s _ (by simp [simplePathB, hp'])]; rfl)

/-- `delete(sp[ie])` on an array or a mapping: the two are one shape to the
interpreter, which dispatches on the runtime node. -/
theorem storageIndexDelete_update (s : State) (target : PlaceExpr)
    (hcond : (ruleEffect .storageIndexDelete).cond (Stmt.delete target)) :
    execStmt s (Stmt.delete target) =
      terminalUpdate .storageIndexDelete (Stmt.delete target) s := by
  show execStmt s (Stmt.delete target) = storageDeleteUpd target s
  obtain ⟨e, hass⟩ := target
  match e, hass, hcond with
  | WrappedExpr.index Kind.storage t base ix, hass, hc =>
      have hc' : isSimple base ∧ isSimple ix ∧ (isArray base ∨ isMapping base) := hc
      have hp' : base.simple = true := hc'.1
      have hi' : ix.simple = true := hc'.2.1
      apply execStmt_delete_storage _ _ rfl
      simp only
      first
      | rfl
      | (rw [resolveS_placePath s _ (by simp [simplePathB, hp', hi'])]; rfl)

/-- `delete(arr.push())`: Lean's own shape; the push place resolves by
extending the array first. -/
theorem storagePushPlaceDelete_update (s : State) (target : PlaceExpr)
    (hcond : (ruleEffect .storagePushPlaceDelete).cond (Stmt.delete target)) :
    execStmt s (Stmt.delete target) =
      terminalUpdate .storagePushPlaceDelete (Stmt.delete target) s := by
  have hc : isSimplePushPlaceDeleteTarget target.expr := hcond
  show execStmt s (Stmt.delete target) = storageDeleteUpd target s
  obtain ⟨e, hass⟩ := target
  match e, hass, hc with
  | WrappedExpr.pushPlace path, hass, hc =>
      have hc' : path.kind = Kind.storage ∧ isSimple path := hc
      have hp' : path.simple = true := hc'.2
      apply execStmt_delete_storage _ _ (by simp [Typed.WrappedExpr.kind])
      simp only
      first
      | rfl
      | exact resolveS_pushPlace s path (by simp [hp'])

/-! ### Memory `delete`

One theorem per shape of the paper's rules: the root (fresh default
identity), a primitive or a reference member, and the array slot twins,
whose `inBounds` guard is `writeMemIndex`'s revert. -/

/-- `delete(mv)`: rebind the root to a fresh default identity. -/
theorem memoryRootDeleteFreshRebind_update (s : State) (target : PlaceExpr)
    (hcond : (ruleEffect .memoryRootDeleteFreshRebind).cond (Stmt.delete target)) :
    execStmt s (Stmt.delete target) =
      terminalUpdate .memoryRootDeleteFreshRebind (Stmt.delete target) s := by
  show execStmt s (Stmt.delete target) = memoryDeleteUpd target s
  obtain ⟨e, hass⟩ := target
  match e, hass, hcond with
  | WrappedExpr.var Kind.memory t fld, hass, _ =>
      rw [execStmt]
      simp only [Typed.WrappedExpr.kind, memoryDeleteUpd]
      cases t with
      | prim pt => rfl
      | ref r => simp only [bind, Except.bind]

/-- The interpreter's memory `delete` on a member, by the slot's type. -/
theorem execStmt_delete_memoryField (s : State) (t : Ty) (base : WrappedExpr)
    (f : Field) (hass : (WrappedExpr.field Kind.memory t base f).assignable = true)
    (hb : base.simple = true) :
    execStmt s (Stmt.delete ⟨WrappedExpr.field Kind.memory t base f, hass⟩) =
      memoryDeleteUpd ⟨WrappedExpr.field Kind.memory t base f, hass⟩ s := by
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

/-- `delete(mv.fp)`: a primitive member resets to its type's default. -/
theorem memoryFieldDeletePrimitive_update (s : State) (target : PlaceExpr)
    (hcond : (ruleEffect .memoryFieldDeletePrimitive).cond (Stmt.delete target)) :
    execStmt s (Stmt.delete target) =
      terminalUpdate .memoryFieldDeletePrimitive (Stmt.delete target) s := by
  show execStmt s (Stmt.delete target) = memoryDeleteUpd target s
  obtain ⟨e, hass⟩ := target
  match e, hass, hcond with
  | WrappedExpr.field Kind.memory t base f, hass, hc =>
      have hc' : isSimple base ∧ isPrimitiveMember (WrappedExpr.field Kind.memory t base f) := hc
      exact execStmt_delete_memoryField s t base f hass hc'.1

/-- `delete(mv.fr)`: a reference member is re-pointed at a fresh default. -/
theorem memoryFieldDeleteReference_update (s : State) (target : PlaceExpr)
    (hcond : (ruleEffect .memoryFieldDeleteReference).cond (Stmt.delete target)) :
    execStmt s (Stmt.delete target) =
      terminalUpdate .memoryFieldDeleteReference (Stmt.delete target) s := by
  show execStmt s (Stmt.delete target) = memoryDeleteUpd target s
  obtain ⟨e, hass⟩ := target
  match e, hass, hcond with
  | WrappedExpr.field Kind.memory t base f, hass, hc =>
      have hc' : isSimple base ∧ isReferenceMember (WrappedExpr.field Kind.memory t base f) := hc
      exact execStmt_delete_memoryField s t base f hass hc'.1

/-- The interpreter's memory `delete` on an array slot, by the slot's type;
out of bounds reverts (`writeMemIndex`). -/
theorem execStmt_delete_memoryIndex (s : State) (t : Ty) (base ix : WrappedExpr)
    (hass : (WrappedExpr.index Kind.memory t base ix).assignable = true)
    (hb : base.simple = true) (hi : ix.simple = true) :
    execStmt s (Stmt.delete ⟨WrappedExpr.index Kind.memory t base ix, hass⟩) =
      memoryDeleteUpd ⟨WrappedExpr.index Kind.memory t base ix, hass⟩ s := by
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

/-- `delete(ap[ie])`, box twin: a primitive slot resets to its default; the
rule's `inBounds` split is the update's revert. -/
theorem memoryIndexDeletePrimitiveBox_update (s : State) (target : PlaceExpr)
    (hcond : (ruleEffect .memoryIndexDeletePrimitiveBox).cond (Stmt.delete target)) :
    execStmt s (Stmt.delete target) =
      terminalUpdate .memoryIndexDeletePrimitiveBox (Stmt.delete target) s := by
  show execStmt s (Stmt.delete target) = memoryDeleteUpd target s
  obtain ⟨e, hass⟩ := target
  match e, hass, hcond with
  | WrappedExpr.index Kind.memory t base ix, hass, hc =>
      have hc' : isSimple base ∧ isSimple ix ∧ isPrimArray base := hc
      exact execStmt_delete_memoryIndex s t base ix hass hc'.1 hc'.2.1

theorem memoryIndexDeletePrimitiveDiamond_update (s : State) (target : PlaceExpr)
    (hcond : (ruleEffect .memoryIndexDeletePrimitiveDiamond).cond
      (Stmt.delete target)) :
    execStmt s (Stmt.delete target) =
      terminalUpdate .memoryIndexDeletePrimitiveDiamond (Stmt.delete target) s :=
  memoryIndexDeletePrimitiveBox_update s target hcond

/-- `delete(ar[ie])`, box twin: a reference slot is re-pointed at a fresh
default. -/
theorem memoryIndexDeleteReferenceBox_update (s : State) (target : PlaceExpr)
    (hcond : (ruleEffect .memoryIndexDeleteReferenceBox).cond (Stmt.delete target)) :
    execStmt s (Stmt.delete target) =
      terminalUpdate .memoryIndexDeleteReferenceBox (Stmt.delete target) s := by
  show execStmt s (Stmt.delete target) = memoryDeleteUpd target s
  obtain ⟨e, hass⟩ := target
  match e, hass, hcond with
  | WrappedExpr.index Kind.memory t base ix, hass, hc =>
      have hc' : isSimple base ∧ isSimple ix ∧ isRefArray base := hc
      exact execStmt_delete_memoryIndex s t base ix hass hc'.1 hc'.2.1

theorem memoryIndexDeleteReferenceDiamond_update (s : State) (target : PlaceExpr)
    (hcond : (ruleEffect .memoryIndexDeleteReferenceDiamond).cond
      (Stmt.delete target)) :
    execStmt s (Stmt.delete target) =
      terminalUpdate .memoryIndexDeleteReferenceDiamond (Stmt.delete target) s :=
  memoryIndexDeleteReferenceBox_update s target hcond

end Wp
end Solidity
