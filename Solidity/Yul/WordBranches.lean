import Solidity.Yul.WordTerms

/-! Concrete conditional and zero-binder decomposition over completed horizons.
These remain closed words; no Source/external state or termination premise. -/
namespace Solidity.Yul.Logic
open Solidity.Yul.Closed
open Solidity (Modality)

def Program.if_ {F c n} (condition : Term F n 1) (body : Program F c n) : Program F c n :=
  ⟨.if_ condition.code body.code,⟨condition.words,body.words⟩⟩

def ifPost {F c n} (mode : Modality) (model : Model F)
    (body : Program F c n) (post : Flow c → Fml n) (values : Values 1) : Fml n :=
  if (values 0).val = 0 then post .normal else .modal mode model body post

theorem eval_if (fuel : Nat) {F c n} (model : Model F) (condition : Term F n 1)
    (body : Program F c n) (vars : Values n) :
    evalStmt (fuel+1) model.environment model.words (Program.if_ condition body).code
      (Program.if_ condition body).words vars =
    (do let values ← evalExpr fuel model.environment model.words condition.code condition.words vars
        if (values 0).val = 0 then pure ⟨vars,.normal⟩
        else evalStmt fuel model.environment model.words body.code body.words vars) := rfl

theorem if_nonzero {F c n lo hi} (model : Model F) (condition : Term F n 1)
    (body : Program F c n) (vars : Values n) (values : Values 1) (result : Outcome c n)
    (tested : evalExpr lo model.environment model.words condition.code condition.words vars = some values)
    (nonzero : (values 0).val ≠ 0)
    (ran : evalStmt hi model.environment model.words body.code body.words vars = some result) :
    evalStmt (max lo hi+1) model.environment model.words (Program.if_ condition body).code
      (Program.if_ condition body).words vars = some result := by
  rw [eval_if,evalExpr_stable (Nat.le_max_left lo hi)
    model.environment model.words condition.code condition.words vars tested]
  change (if (values 0).val = 0 then _ else _) = _
  rw [if_neg nonzero]
  exact evalStmt_stable (Nat.le_max_right lo hi)
    model.environment model.words body.code body.words vars ran

theorem modal_if {F c n} (mode : Modality) (model : Model F) (condition : Term F n 1)
    (body : Program F c n) (post : Flow c → Fml n) (vars : Values n) :
    (Fml.modal mode model (Program.if_ condition body) post).holds vars ↔
      (Fml.termModal mode model condition (ifPost mode model body post)).holds vars := by
  cases mode with
  | box =>
    constructor
    · intro all fuel values tested
      change (if (values 0).val = 0 then post .normal else Fml.modal .box model body post).holds vars
      by_cases zero : (values 0).val = 0
      · rw [if_pos zero]
        exact all (fuel+1) ⟨vars,.normal⟩ (by rw [eval_if,tested]; exact if_pos zero)
      · rw [if_neg zero]
        intro other result ran
        exact all (max fuel other+1) result (if_nonzero model condition body vars values result tested zero ran)
    · intro all fuel result ran
      cases fuel with
      | zero => cases ran
      | succ fuel =>
        rw [eval_if] at ran
        cases tested : evalExpr fuel model.environment model.words condition.code condition.words vars with
        | none => rw [tested] at ran; cases ran
        | some values =>
          rw [tested] at ran
          change (if (values 0).val = 0 then _ else _) = _ at ran
          have after := all fuel values tested
          change (if (values 0).val = 0 then post .normal else Fml.modal .box model body post).holds vars at after
          by_cases zero : (values 0).val = 0
          · rw [if_pos zero] at ran after
            cases Option.some.inj ran
            exact after
          · rw [if_neg zero] at ran after
            exact after fuel result ran
  | diamond =>
    constructor
    · rintro ⟨fuel,result,ran,after⟩
      cases fuel with
      | zero => cases ran
      | succ fuel =>
        rw [eval_if] at ran
        cases tested : evalExpr fuel model.environment model.words condition.code condition.words vars with
        | none => rw [tested] at ran; cases ran
        | some values =>
          rw [tested] at ran
          change (if (values 0).val = 0 then _ else _) = _ at ran
          refine ⟨fuel,values,tested,?_⟩
          change (if (values 0).val = 0 then post .normal else Fml.modal .diamond model body post).holds vars
          by_cases zero : (values 0).val = 0
          · rw [if_pos zero] at ran ⊢
            cases Option.some.inj ran
            exact after
          · rw [if_neg zero] at ran ⊢
            exact ⟨fuel,result,ran,after⟩
    · rintro ⟨fuel,values,tested,after⟩
      change (if (values 0).val = 0 then post .normal else Fml.modal .diamond model body post).holds vars at after
      by_cases zero : (values 0).val = 0
      · rw [if_pos zero] at after
        exact ⟨fuel+1,⟨vars,.normal⟩,(by rw [eval_if,tested]; exact if_pos zero),after⟩
      · rw [if_neg zero] at after
        rcases after with ⟨other,result,ran,done⟩
        exact ⟨max fuel other+1,result,if_nonzero model condition body vars values result tested zero ran,done⟩

def Program.zero {F c n} (count : Nat) (body : Program F c (count+n)) : Program F c n :=
  ⟨.zero count body.code,body.words⟩

def dropPost {c n} (count : Nat) (post : Flow c → Fml n) (flow : Flow c) : Fml (count+n) :=
  .subst (dropValues count) (post flow)

theorem eval_zero_binder (fuel : Nat) {F c n} (model : Model F) (count : Nat)
    (body : Program F c (count+n)) (vars : Values n) :
    evalStmt (fuel+1) model.environment model.words (Program.zero count body).code
      (Program.zero count body).words vars =
    (do let result ← evalStmt fuel model.environment model.words body.code body.words
          (extendValues (fun _ : Fin count => word 0) vars)
        pure ⟨dropValues count result.vars,result.flow⟩) := rfl

theorem modal_zero {F c n} (mode : Modality) (model : Model F) (count : Nat)
    (body : Program F c (count+n)) (post : Flow c → Fml n) (vars : Values n) :
    (Fml.modal mode model (Program.zero count body) post).holds vars ↔
      (Fml.subst (extendValues (fun _ : Fin count => word 0))
        (Fml.modal mode model body (dropPost count post))).holds vars := by
  cases mode with
  | box =>
    constructor
    · intro all fuel result ran
      exact all (fuel+1) ⟨dropValues count result.vars,result.flow⟩
        (by rw [eval_zero_binder,ran]; rfl)
    · intro all fuel result ran
      cases fuel with
      | zero => cases ran
      | succ fuel =>
        rw [eval_zero_binder] at ran
        cases bodyRan : evalStmt fuel model.environment model.words body.code body.words
          (extendValues (fun _ : Fin count => word 0) vars) with
        | none => rw [bodyRan] at ran; cases ran
        | some actual =>
          rw [bodyRan] at ran
          cases Option.some.inj ran
          exact all fuel actual bodyRan
  | diamond =>
    constructor
    · rintro ⟨fuel,result,ran,after⟩
      cases fuel with
      | zero => cases ran
      | succ fuel =>
        rw [eval_zero_binder] at ran
        cases bodyRan : evalStmt fuel model.environment model.words body.code body.words
          (extendValues (fun _ : Fin count => word 0) vars) with
        | none => rw [bodyRan] at ran; cases ran
        | some actual =>
          rw [bodyRan] at ran
          cases Option.some.inj ran
          exact ⟨fuel,actual,bodyRan,after⟩
    · rintro ⟨fuel,result,ran,after⟩
      exact ⟨fuel+1,⟨dropValues count result.vars,result.flow⟩,
        (by rw [eval_zero_binder,ran]; rfl),after⟩


def Program.let_ {F c n r} (term : Term F n r) (body : Program F c (r+n)) : Program F c n :=
  ⟨.let_ r term.code body.code,⟨term.words,body.words⟩⟩

def letPost {F c n r} (mode : Modality) (model : Model F)
    (body : Program F c (r+n)) (post : Flow c → Fml n) (values : Values r) : Fml n :=
  .subst (extendValues values) (.modal mode model body (dropPost r post))

theorem eval_let_binder (fuel : Nat) {F c n r} (model : Model F) (term : Term F n r)
    (body : Program F c (r+n)) (vars : Values n) :
    evalStmt (fuel+1) model.environment model.words (Program.let_ term body).code
      (Program.let_ term body).words vars =
    (do let values ← evalExpr fuel model.environment model.words term.code term.words vars
        let result ← evalStmt fuel model.environment model.words body.code body.words (extendValues values vars)
        pure (⟨dropValues r result.vars,result.flow⟩ : Outcome c n)) := rfl

theorem let_completed {F c n r lo hi} (model : Model F) (term : Term F n r)
    (body : Program F c (r+n)) (vars : Values n) (values : Values r) (result : Outcome c (r+n))
    (tested : evalExpr lo model.environment model.words term.code term.words vars = some values)
    (ran : evalStmt hi model.environment model.words body.code body.words (extendValues values vars) = some result) :
    evalStmt (max lo hi+1) model.environment model.words (Program.let_ term body).code
      (Program.let_ term body).words vars = some ⟨dropValues r result.vars,result.flow⟩ := by
  rw [eval_let_binder,evalExpr_stable (Nat.le_max_left lo hi)
    model.environment model.words term.code term.words vars tested]
  change (do let result ← evalStmt (max lo hi) model.environment model.words
              body.code body.words (extendValues values vars)
             pure (⟨dropValues r result.vars,result.flow⟩ : Outcome c n)) = _
  rw [evalStmt_stable (Nat.le_max_right lo hi)
    model.environment model.words body.code body.words (extendValues values vars) ran]
  rfl

theorem modal_let {F c n r} (mode : Modality) (model : Model F) (term : Term F n r)
    (body : Program F c (r+n)) (post : Flow c → Fml n) (vars : Values n) :
    (Fml.modal mode model (Program.let_ term body) post).holds vars ↔
      (Fml.termModal mode model term (letPost mode model body post)).holds vars := by
  cases mode with
  | box =>
    constructor
    · intro all fuel values tested other result ran
      exact all (max fuel other+1) ⟨dropValues r result.vars,result.flow⟩
        (let_completed model term body vars values result tested ran)
    · intro all fuel result ran
      cases fuel with
      | zero => cases ran
      | succ fuel =>
        rw [eval_let_binder] at ran
        cases tested : evalExpr fuel model.environment model.words term.code term.words vars with
        | none => rw [tested] at ran; cases ran
        | some values =>
          rw [tested] at ran
          change (do let result ← evalStmt fuel model.environment model.words body.code body.words
                      (extendValues values vars)
                     pure (⟨dropValues r result.vars,result.flow⟩ : Outcome c n)) = _ at ran
          cases bodyRan : evalStmt fuel model.environment model.words body.code body.words (extendValues values vars) with
          | none => rw [bodyRan] at ran; cases ran
          | some actual =>
            rw [bodyRan] at ran
            cases Option.some.inj ran
            exact all fuel values tested fuel actual bodyRan
  | diamond =>
    constructor
    · rintro ⟨fuel,result,ran,after⟩
      cases fuel with
      | zero => cases ran
      | succ fuel =>
        rw [eval_let_binder] at ran
        cases tested : evalExpr fuel model.environment model.words term.code term.words vars with
        | none => rw [tested] at ran; cases ran
        | some values =>
          rw [tested] at ran
          change (do let result ← evalStmt fuel model.environment model.words body.code body.words
                      (extendValues values vars)
                     pure (⟨dropValues r result.vars,result.flow⟩ : Outcome c n)) = _ at ran
          cases bodyRan : evalStmt fuel model.environment model.words body.code body.words (extendValues values vars) with
          | none => rw [bodyRan] at ran; cases ran
          | some actual =>
            rw [bodyRan] at ran
            cases Option.some.inj ran
            exact ⟨fuel,values,tested,fuel,actual,bodyRan,after⟩
    · rintro ⟨fuel,values,tested,other,result,ran,after⟩
      exact ⟨max fuel other+1,⟨dropValues r result.vars,result.flow⟩,
        let_completed model term body vars values result tested ran,after⟩

end Solidity.Yul.Logic
