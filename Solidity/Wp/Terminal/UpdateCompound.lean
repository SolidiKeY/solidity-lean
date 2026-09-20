import Solidity.Wp.Terminal.UpdateStack

/-!
# Terminal-rule updates: compound assignment and inc/dec statements

`localOpAssign op`, `storage{Root,Field,IndexMapping,IndexArray}OpAssign op`
(`t op= se`), and `localIncrement op`, `storage{Root,Field,Index}Increment op`
(`++t;`); the memory twins `memory{Field,IndexArray}OpAssign op`,
`memory{Field,IndexArray}Increment op`.
-/

namespace Solidity
namespace Wp

open Semantics Rules

/-! ## `++t;` statements -/

theorem execStmt_expr_incDec (s : State) (op : IncDec) (t : WrappedExpr)
    (ht : incDecTargetB t = true) :
    execStmt s (Stmt.expr (WrappedExpr.incDec op t)) =
      incDecStmtUpd op (WrappedExpr.incDec op t) s := by
  rw [execStmt, evalValue_incDec s op t ht]
  simp only [incDecStmtUpd, bind, Except.bind, Except.map]

theorem localIncrement_update (op : IncDec) (s : State) (e : WrappedExpr)
    (hcond : (ruleEffect (.localIncrement op)).cond (Stmt.expr e)) :
    execStmt s (Stmt.expr e) = terminalUpdate (.localIncrement op) (Stmt.expr e) s := by
  show execStmt s (Stmt.expr e) = incDecStmtUpd op e s
  match e, hcond with
  | WrappedExpr.incDec op' t, hc =>
      have hc' : op' = op ∧ isStack t ∧ isSimple t := hc
      obtain ⟨rfl, hk, hs⟩ := hc'
      exact execStmt_expr_incDec s op' t (incDecTargetB_of_stackSimple hk hs)

theorem storageRootIncrement_update (op : IncDec) (s : State) (e : WrappedExpr)
    (hcond : (ruleEffect (.storageRootIncrement op)).cond (Stmt.expr e)) :
    execStmt s (Stmt.expr e) =
      terminalUpdate (.storageRootIncrement op) (Stmt.expr e) s := by
  show execStmt s (Stmt.expr e) = incDecStmtUpd op e s
  match e, hcond with
  | WrappedExpr.incDec op' t, hc =>
      have hc' : op' = op ∧ isGlobal t := hc
      obtain ⟨rfl, hg⟩ := hc'
      exact execStmt_expr_incDec s op' t (incDecTargetB_of_global hg)

theorem storageFieldIncrement_update (op : IncDec) (s : State) (e : WrappedExpr)
    (hcond : (ruleEffect (.storageFieldIncrement op)).cond (Stmt.expr e)) :
    execStmt s (Stmt.expr e) =
      terminalUpdate (.storageFieldIncrement op) (Stmt.expr e) s := by
  show execStmt s (Stmt.expr e) = incDecStmtUpd op e s
  match e, hcond with
  | WrappedExpr.incDec op' (WrappedExpr.field Kind.storage ty path f), hc =>
      have hc' : op' = op ∧ isSimple path := hc
      obtain ⟨rfl, hp⟩ := hc'
      have hp' : path.simple = true := hp
      exact execStmt_expr_incDec s op' _ (by simp [incDecTargetB, hp'])

theorem storageIndexIncrement_update (op : IncDec) (s : State) (e : WrappedExpr)
    (hcond : (ruleEffect (.storageIndexIncrement op)).cond (Stmt.expr e)) :
    execStmt s (Stmt.expr e) =
      terminalUpdate (.storageIndexIncrement op) (Stmt.expr e) s := by
  show execStmt s (Stmt.expr e) = incDecStmtUpd op e s
  match e, hcond with
  | WrappedExpr.incDec op' (WrappedExpr.index Kind.storage ty path ix), hc =>
      have hc' : op' = op ∧ isSimple path ∧ isSimple ix := hc
      obtain ⟨rfl, hp, hi⟩ := hc'
      have hp' : path.simple = true := hp
      have hi' : ix.simple = true := hi
      exact execStmt_expr_incDec s op' _ (by simp [incDecTargetB, hp', hi'])

/-! ## `t op= se` -/

/-- The interpreter's compound assignment on the target shapes the rules
admit (a stack variable, a storage variable, a simple storage place),
with a terminal right-hand side. -/
theorem execStmt_compound (s : State) (op : BinOp) (lhs : PlaceExpr)
    (rhs : WrappedExpr) (ht : incDecTargetB lhs.expr = true)
    (hr : terminalRhsB rhs = true) :
    execStmt s (Stmt.compoundAssign op lhs rhs) = compoundAssignUpd op lhs rhs s := by
  rw [execStmt, evalValue_readVal s rhs hr]
  simp only [compoundAssignUpd, bind, Except.bind, Except.map]
  cases readVal s rhs with
  | error e => rfl
  | ok v =>
      simp only []
      obtain ⟨e, hass⟩ := lhs
      simp only at ht ⊢
      cases e with
      | var k ty fld =>
          cases k with
          | stack =>
              rw [resolveLoc_var]
              simp only [readLoc, writeLoc, stackVal, State.getEnv, bind, Except.bind]
              cases lookupBy fld.name s.env with
              | none => rfl
              | some b =>
                  cases b with
                  | val old =>
                      simp only []
                      cases applyBinOp op old v with
                      | error e => rfl
                      | ok nv0 =>
                          simp only []
                  | spath r sg => rfl
                  | mref id => rfl
          | storage =>
              rw [resolveLoc_var]
              simp only [locPath, bind, Except.bind]
              by_cases hg : fld.origin = some StorageOrigin.global
              · rw [if_pos hg, if_pos hg]
                simp only [readLoc_storage, writeLoc, bind, Except.bind]
                cases s.findStorage fld.name [] with
                | error e => rfl
                | ok sv =>
                    simp only []
                    cases SVal.asValue sv with
                    | error e => rfl
                    | ok old =>
                        simp only []
                        cases applyBinOp op old v with
                        | error e => rfl
                        | ok nv0 =>
                            simp only []
              · rw [if_neg hg, if_neg hg]
                rfl
          | memory => exact absurd ht (by simp [incDecTargetB])
      | field k ty base f =>
          cases k with
          | storage =>
              have hp : simplePathB (WrappedExpr.field Kind.storage ty base f) = true := by
                simpa [incDecTargetB, simplePathB] using ht
              rw [resolveLoc_storageField s ty base f hp]
              simp only [locPath, bind, Except.bind, Except.map]
              cases placePath s (WrappedExpr.field Kind.storage ty base f) with
              | error e => rfl
              | ok p =>
                  obtain ⟨r, sg⟩ := p
                  simp only [readLoc_storage, writeLoc, bind, Except.bind]
                  cases s.findStorage r sg with
                  | error e => rfl
                  | ok sv =>
                      simp only []
                      cases SVal.asValue sv with
                      | error e => rfl
                      | ok old =>
                          simp only []
                          cases applyBinOp op old v with
                          | error e => rfl
                          | ok nv0 =>
                              simp only []
          | memory =>
              have hb : base.simple = true := by simpa [incDecTargetB] using ht
              rw [resolveLoc_memoryField s ty base f hb]
              simp only [bind, Except.bind, Except.map]
              cases memBase s base with
              | error e => rfl
              | ok id =>
                  simp only [readLoc_memoryField, writeLoc_memoryField]
                  cases memFieldVal s id f.name with
                  | error e => rfl
                  | ok old =>
                      simp only []
                      cases applyBinOp op old v with
                      | error e => rfl
                      | ok nv0 => simp only []
          | _ => exact absurd ht (by simp [incDecTargetB])
      | index k ty base ix =>
          cases k with
          | storage =>
              have hp : simplePathB (WrappedExpr.index Kind.storage ty base ix) = true := by
                simpa [incDecTargetB, simplePathB] using ht
              rw [resolveLoc_storageIndex s ty base ix hp]
              simp only [locPath, bind, Except.bind, Except.map]
              cases placePath s (WrappedExpr.index Kind.storage ty base ix) with
              | error e => rfl
              | ok p =>
                  obtain ⟨r, sg⟩ := p
                  simp only [readLoc_storage, writeLoc, bind, Except.bind]
                  cases s.findStorage r sg with
                  | error e => rfl
                  | ok sv =>
                      simp only []
                      cases SVal.asValue sv with
                      | error e => rfl
                      | ok old =>
                          simp only []
                          cases applyBinOp op old v with
                          | error e => rfl
                          | ok nv0 =>
                              simp only []
          | memory =>
              have hbi : base.simple = true ∧ ix.simple = true := by
                simpa [incDecTargetB, Bool.and_eq_true] using ht
              rw [resolveLoc_memoryIndex s ty base ix hbi.1 hbi.2]
              simp only [bind, Except.bind, Except.map]
              cases memBase s base with
              | error e => rfl
              | ok id =>
                  simp only []
                  cases simpleInt s ix with
                  | error e => rfl
                  | ok i =>
                      simp only [readLoc_memoryIndex, writeLoc_memoryIndex]
                      cases memIndexVal s id i with
                      | error e => rfl
                      | ok old =>
                          simp only []
                          cases applyBinOp op old v with
                          | error e => rfl
                          | ok nv0 => simp only []
          | _ => exact absurd ht (by simp [incDecTargetB])
      | pushPlace target => exact absurd ht (by simp [incDecTargetB])
      | _ => exact absurd hass (by simp [Typed.WrappedExpr.assignable])

theorem localOpAssign_update (op op' : BinOp) (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect (.localOpAssign op)).cond
      (Stmt.compoundAssign op' lhs rhs)) :
    execStmt s (Stmt.compoundAssign op' lhs rhs) =
      terminalUpdate (.localOpAssign op) (Stmt.compoundAssign op' lhs rhs) s := by
  have hc : op' = op ∧ op'.hasCompoundAssign = true ∧ isStackVar lhs ∧
      isStack rhs ∧ isSimple rhs := hcond
  obtain ⟨rfl, hc⟩ := hc
  show execStmt s (Stmt.compoundAssign op' lhs rhs) = compoundAssignUpd op' lhs rhs s
  exact execStmt_compound s op' lhs rhs
    (incDecTargetB_of_stackSimple hc.2.1.1 hc.2.1.2)
    (terminalRhsB_of_simple hc.2.2.2)

theorem storageRootOpAssign_update (op op' : BinOp) (s : State)
    (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect (.storageRootOpAssign op)).cond
      (Stmt.compoundAssign op' lhs rhs)) :
    execStmt s (Stmt.compoundAssign op' lhs rhs) =
      terminalUpdate (.storageRootOpAssign op)
        (Stmt.compoundAssign op' lhs rhs) s := by
  have hc : op' = op ∧ op'.hasCompoundAssign = true ∧ isGlobal lhs ∧
      isStack rhs ∧ isSimple rhs := hcond
  obtain ⟨rfl, hc⟩ := hc
  show execStmt s (Stmt.compoundAssign op' lhs rhs) = compoundAssignUpd op' lhs rhs s
  exact execStmt_compound s op' lhs rhs (incDecTargetB_of_global hc.2.1)
    (terminalRhsB_of_simple hc.2.2.2)

theorem storageFieldOpAssign_update (op op' : BinOp) (s : State)
    (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect (.storageFieldOpAssign op)).cond
      (Stmt.compoundAssign op' lhs rhs)) :
    execStmt s (Stmt.compoundAssign op' lhs rhs) =
      terminalUpdate (.storageFieldOpAssign op)
        (Stmt.compoundAssign op' lhs rhs) s := by
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.field Kind.storage ty path f, hass, hc =>
      have hc' : op' = op ∧ op'.hasCompoundAssign = true ∧ isSimple path ∧
          isStack rhs ∧ isSimple rhs := hc
      obtain ⟨rfl, hc'⟩ := hc'
      have hp' : path.simple = true := hc'.2.1
      exact execStmt_compound s op' ⟨_, hass⟩ rhs (by simp [incDecTargetB, hp'])
        (terminalRhsB_of_simple hc'.2.2.2)

/-- `map[ie] ⊕= se`: the mapping twin of the index rule — no bounds branch,
the trailing `isMapping` is what separates it from the array rule. -/
theorem storageIndexMappingOpAssign_update (op op' : BinOp) (s : State)
    (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect (.storageIndexMappingOpAssign op)).cond
      (Stmt.compoundAssign op' lhs rhs)) :
    execStmt s (Stmt.compoundAssign op' lhs rhs) =
      terminalUpdate (.storageIndexMappingOpAssign op)
        (Stmt.compoundAssign op' lhs rhs) s := by
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.index Kind.storage ty path ix, hass, hc =>
      have hc' : op' = op ∧ op'.hasCompoundAssign = true ∧ isSimple path ∧
          isSimple ix ∧ isStack rhs ∧ isSimple rhs ∧ isMapping path := hc
      obtain ⟨rfl, hc'⟩ := hc'
      have hp' : path.simple = true := hc'.2.1
      have hi' : ix.simple = true := hc'.2.2.1
      exact execStmt_compound s op' ⟨_, hass⟩ rhs
        (by simp [incDecTargetB, hp', hi'])
        (terminalRhsB_of_simple hc'.2.2.2.2.1)

/-- `arr[ie] ⊕= se`: the array twin; the bounds split the rule carries is
`SVal.find`/`SVal.save`'s revert inside `compoundAssignUpd`. -/
theorem storageIndexArrayOpAssign_update (op op' : BinOp) (s : State)
    (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect (.storageIndexArrayOpAssign op)).cond
      (Stmt.compoundAssign op' lhs rhs)) :
    execStmt s (Stmt.compoundAssign op' lhs rhs) =
      terminalUpdate (.storageIndexArrayOpAssign op)
        (Stmt.compoundAssign op' lhs rhs) s := by
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.index Kind.storage ty path ix, hass, hc =>
      have hc' : op' = op ∧ op'.hasCompoundAssign = true ∧ isSimple path ∧
          isSimple ix ∧ isStack rhs ∧ isSimple rhs ∧ isArray path := hc
      obtain ⟨rfl, hc'⟩ := hc'
      have hp' : path.simple = true := hc'.2.1
      have hi' : ix.simple = true := hc'.2.2.1
      exact execStmt_compound s op' ⟨_, hass⟩ rhs
        (by simp [incDecTargetB, hp', hi'])
        (terminalRhsB_of_simple hc'.2.2.2.2.1)

/-! ## Memory-target arithmetic

`mv.f op= se;`, `mv[i] op= se;`, `mv.f++;`, `mv[i]++;` — the calculus's
`memoryFieldOpAssign` / `memoryFieldDivAssign` / `memoryIndexArrayOpAssign` /
`memoryFieldIncrement`.  Every proof is its storage twin with `Kind.memory`:
the shared hubs `execStmt_compound` and `evalValue_incDec` do the work, and
what makes them apply is that `incDecTargetB` now admits a simple-path memory
field and a simple-path, simple-index memory slot. -/

theorem memoryFieldOpAssign_update (op op' : BinOp) (s : State)
    (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect (.memoryFieldOpAssign op)).cond
      (Stmt.compoundAssign op' lhs rhs)) :
    execStmt s (Stmt.compoundAssign op' lhs rhs) =
      terminalUpdate (.memoryFieldOpAssign op)
        (Stmt.compoundAssign op' lhs rhs) s := by
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.field Kind.memory ty path f, hass, hc =>
      have hc' : op' = op ∧ op'.hasCompoundAssign = true ∧ isSimple path ∧
          isStack rhs ∧ isSimple rhs := hc
      obtain ⟨rfl, hc'⟩ := hc'
      have hp' : path.simple = true := hc'.2.1
      exact execStmt_compound s op' ⟨_, hass⟩ rhs (by simp [incDecTargetB, hp'])
        (terminalRhsB_of_simple hc'.2.2.2)

theorem memoryIndexArrayOpAssign_update (op op' : BinOp) (s : State)
    (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect (.memoryIndexArrayOpAssign op)).cond
      (Stmt.compoundAssign op' lhs rhs)) :
    execStmt s (Stmt.compoundAssign op' lhs rhs) =
      terminalUpdate (.memoryIndexArrayOpAssign op)
        (Stmt.compoundAssign op' lhs rhs) s := by
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond with
  | WrappedExpr.index Kind.memory ty path ix, hass, hc =>
      have hc' : op' = op ∧ op'.hasCompoundAssign = true ∧ isSimple path ∧
          isSimple ix ∧ isStack rhs ∧ isSimple rhs := hc
      obtain ⟨rfl, hc'⟩ := hc'
      have hp' : path.simple = true := hc'.2.1
      have hi' : ix.simple = true := hc'.2.2.1
      exact execStmt_compound s op' ⟨_, hass⟩ rhs
        (by simp [incDecTargetB, hp', hi'])
        (terminalRhsB_of_simple hc'.2.2.2.2)

theorem memoryFieldIncrement_update (op : IncDec) (s : State) (e : WrappedExpr)
    (hcond : (ruleEffect (.memoryFieldIncrement op)).cond (Stmt.expr e)) :
    execStmt s (Stmt.expr e) =
      terminalUpdate (.memoryFieldIncrement op) (Stmt.expr e) s := by
  show execStmt s (Stmt.expr e) = incDecStmtUpd op e s
  match e, hcond with
  | WrappedExpr.incDec op' (WrappedExpr.field Kind.memory ty path f), hc =>
      have hc' : op' = op ∧ isSimple path := hc
      obtain ⟨rfl, hp⟩ := hc'
      have hp' : path.simple = true := hp
      exact execStmt_expr_incDec s op' _ (by simp [incDecTargetB, hp'])

theorem memoryIndexArrayIncrement_update (op : IncDec) (s : State) (e : WrappedExpr)
    (hcond : (ruleEffect (.memoryIndexArrayIncrement op)).cond (Stmt.expr e)) :
    execStmt s (Stmt.expr e) =
      terminalUpdate (.memoryIndexArrayIncrement op) (Stmt.expr e) s := by
  show execStmt s (Stmt.expr e) = incDecStmtUpd op e s
  match e, hcond with
  | WrappedExpr.incDec op' (WrappedExpr.index Kind.memory ty path ix), hc =>
      have hc' : op' = op ∧ isSimple path ∧ isSimple ix := hc
      obtain ⟨rfl, hp, hi⟩ := hc'
      have hp' : path.simple = true := hp
      have hi' : ix.simple = true := hi
      exact execStmt_expr_incDec s op' _ (by simp [incDecTargetB, hp', hi'])

end Wp
end Solidity
