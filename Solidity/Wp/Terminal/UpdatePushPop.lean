import Solidity.Wp.Terminal.UpdateStorage

/-!
# Terminal-rule updates: `push` / `pop`

`storagePushValue{Save,CopySource}`, `storagePushLengthSave`,
`storagePopSave{Box,Diamond}`, `storageLocalRootPushBind`.
-/

namespace Solidity
namespace Wp

open Semantics Rules

/-- A simple assignable place is a variable. -/
theorem simplePlace_shape (target : PlaceExpr) (hs : isSimple target) :
    ∃ k t fld, target.expr = WrappedExpr.var k t fld := by
  obtain ⟨e, hass⟩ := target
  cases e with
  | var k t fld => exact ⟨k, t, fld, rfl⟩
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

/-- The interpreter's `push` on a simple target with a terminal (or absent)
value. -/
theorem execStmt_push (s : State) (target : PlaceExpr) (value : Option WrappedExpr)
    (hs : isSimple target)
    (hv : ∀ rhs, value = some rhs -> terminalRhsB rhs = true) :
    execStmt s (Stmt.push target value) = pushUpd target value s := by
  obtain ⟨k, t, fld, he⟩ := simplePlace_shape target hs
  rw [execStmt]
  simp only [pushUpd, he, resolveS_var, placePath, bind, Except.bind, Except.map]
  cases varPath s fld with
  | error e => rfl
  | ok p =>
      obtain ⟨r, sg⟩ := p
      simp only []
      cases s.findStorage r sg with
      | error e => rfl
      | ok arr =>
          simp only []
          cases arr with
          | array elems =>
              cases hty : (WrappedExpr.var k t fld).ty with
              | prim pt => cases pt <;> rfl
              | ref rt =>
                  cases rt with
                  | array elemTy =>
                      simp only []
                      cases value with
                      | none =>
                          simp only [pure, Except.pure, bind, Except.bind]
                      | some rhs =>
                          simp only [rhsToSVal_rhsSVal s rhs (hv rhs rfl), bind,
                            Except.bind, Except.map]
                          cases rhsSVal s rhs <;> rfl
                  | struct n => rfl
                  | mapping kt vt => rfl
          | prim p => cases p <;> rfl
          | struct fields => rfl
          | map entries dflt => rfl

theorem storagePushValueSave_update (s : State) (target : PlaceExpr)
    (value : Option WrappedExpr)
    (hcond : (ruleEffect .storagePushValueSave).cond (Stmt.push target value)) :
    execStmt s (Stmt.push target value) =
      terminalUpdate .storagePushValueSave (Stmt.push target value) s := by
  show execStmt s (Stmt.push target value) = pushUpd target value s
  match value, hcond with
  | some rhs, hc =>
      have hc' : target.kind = Kind.storage ∧ isSimple target ∧
          isStack rhs ∧ isSimple rhs := hc
      exact execStmt_push s target (some rhs) hc'.2.1
        (fun r hr => by cases hr; exact terminalRhsB_of_simple hc'.2.2.2)

theorem storagePushValueCopySource_update (s : State) (target : PlaceExpr)
    (value : Option WrappedExpr)
    (hcond : (ruleEffect .storagePushValueCopySource).cond
      (Stmt.push target value)) :
    execStmt s (Stmt.push target value) =
      terminalUpdate .storagePushValueCopySource (Stmt.push target value) s := by
  show execStmt s (Stmt.push target value) = pushUpd target value s
  match value, hcond with
  | some rhs, hc =>
      have hc' : target.kind = Kind.storage ∧ isSimple target ∧
          isStorage rhs ∧ isSimple rhs := hc
      exact execStmt_push s target (some rhs) hc'.2.1
        (fun r hr => by cases hr; exact terminalRhsB_of_simple hc'.2.2.2)

theorem storagePushLengthSave_update (s : State) (target : PlaceExpr)
    (value : Option WrappedExpr)
    (hcond : (ruleEffect .storagePushLengthSave).cond (Stmt.push target value)) :
    execStmt s (Stmt.push target value) =
      terminalUpdate .storagePushLengthSave (Stmt.push target value) s := by
  have hc : target.kind = Kind.storage ∧ isSimple target ∧ value = none := hcond
  show execStmt s (Stmt.push target value) = pushUpd target value s
  exact execStmt_push s target value hc.2.1
    (fun r hr => by rw [hc.2.2] at hr; exact nomatch hr)

/-- The interpreter's `pop` on a simple target. -/
theorem execStmt_pop (s : State) (target : PlaceExpr) (hs : isSimple target) :
    execStmt s (Stmt.pop target) = popUpd target s := by
  obtain ⟨k, t, fld, he⟩ := simplePlace_shape target hs
  rw [execStmt]
  simp only [popUpd, he, resolveS_var, placePath, bind, Except.bind, Except.map]
  cases varPath s fld with
  | error e => rfl
  | ok p =>
      obtain ⟨r, sg⟩ := p
      simp only []
      cases s.findStorage r sg with
      | error e => rfl
      | ok arr =>
          cases arr with
          | array elems =>
              simp only []
              cases elems.reverse <;> rfl
          | prim p => cases p <;> rfl
          | struct fields => rfl
          | map entries dflt => rfl

theorem storagePopSaveBox_update (s : State) (target : PlaceExpr)
    (hcond : (ruleEffect .storagePopSaveBox).cond (Stmt.pop target)) :
    execStmt s (Stmt.pop target) =
      terminalUpdate .storagePopSaveBox (Stmt.pop target) s := by
  have hc : target.kind = Kind.storage ∧ isSimple target := hcond
  show execStmt s (Stmt.pop target) = popUpd target s
  exact execStmt_pop s target hc.2

theorem storagePopSaveDiamond_update (s : State) (target : PlaceExpr)
    (hcond : (ruleEffect .storagePopSaveDiamond).cond (Stmt.pop target)) :
    execStmt s (Stmt.pop target) =
      terminalUpdate .storagePopSaveDiamond (Stmt.pop target) s :=
  storagePopSaveBox_update s target hcond

theorem storageLocalRootPushBind_update (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageLocalRootPushBind).cond
      (Stmt.assign lhs rhs)) :
    execStmt s (Stmt.assign lhs rhs) =
      terminalUpdate .storageLocalRootPushBind (Stmt.assign lhs rhs) s := by
  show execStmt s (Stmt.assign lhs rhs) = pushBindUpd lhs rhs s
  match rhs, hcond with
  | WrappedExpr.pushPlace target, hc =>
      have hc' : isLocal lhs ∧ target.kind = Kind.storage ∧ isSimple target := hc
      obtain ⟨t, fld, he, hloc⟩ := local_shape hc'.1
      have hp' : target.simple = true := hc'.2.2
      show execAssign s lhs _ = _
      obtain ⟨e, hass⟩ := lhs
      simp only at he
      subst he
      unfold execAssign pushBindUpd
      simp only []
      have hng : ¬ fld.origin = some StorageOrigin.global := by
        rw [hloc]; decide
      rw [if_neg hng, resolveS_pushPlace s target (by simp [hp'])]

end Wp
end Solidity
