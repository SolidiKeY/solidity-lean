import Solidity.Yul.WordSwitch

/-! Loop initializer decomposition against the actual closed interpreter.
The loop phase has its own intrinsic formula and uses evalLoop, not a new
execution relation or an assumed termination oracle. -/
namespace Solidity.Yul.Logic
open Solidity.Yul.Closed
open Solidity (Modality)

def Program.for_ {F c n} (pre : Program F ⟨c.function,false⟩ n) (condition : Term F n 1)
    (step : Program F ⟨c.function,false⟩ n) (body : Program F ⟨c.function,true⟩ n) :
    Program F c n :=
  ⟨.for_ pre.code condition.code step.code body.code,⟨pre.words,condition.words,step.words,body.words⟩⟩

def loopPrePost {F c n} (mode : Modality) (model : Model F) (condition : Term F n 1)
    (step : Program F ⟨c.function,false⟩ n) (body : Program F ⟨c.function,true⟩ n)
    (post : Flow c → Fml n) : Flow ⟨c.function,false⟩ → Fml n
  | .normal => .loopModal c mode model condition step body post
  | .leave_ proof => post (.leave_ proof)
  | .break_ impossible => False.elim (by cases impossible)
  | .continue_ impossible => False.elim (by cases impossible)

theorem eval_for (fuel : Nat) {F c n} (model : Model F)
    (pre : Program F ⟨c.function,false⟩ n) (condition : Term F n 1)
    (step : Program F ⟨c.function,false⟩ n) (body : Program F ⟨c.function,true⟩ n) (vars : Values n) :
    evalStmt (fuel+1) model.environment model.words (Program.for_ (c := c) pre condition step body).code
      (Program.for_ (c := c) pre condition step body).words vars =
    (do let result ← evalStmt fuel model.environment model.words pre.code pre.words vars
        match result.flow with
        | .normal => (evalLoop (c := c) fuel model.environment model.words condition.code condition.words
            step.code step.words body.code body.words result.vars)
        | .leave_ proof => pure ⟨result.vars,.leave_ proof⟩
        | .break_ impossible => False.elim (by cases impossible)
        | .continue_ impossible => False.elim (by cases impossible)) := rfl

theorem loop_stable {lo hi : Nat} (bound : lo ≤ hi) {F c n} (model : Model F)
    (condition : Term F n 1) (step : Program F ⟨c.function,false⟩ n)
    (body : Program F ⟨c.function,true⟩ n) (vars : Values n) {result : Outcome c n}
    (done : evalLoop lo model.environment model.words condition.code condition.words
      step.code step.words body.code body.words vars = some result) :
    evalLoop hi model.environment model.words condition.code condition.words
      step.code step.words body.code body.words vars = some result := by
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le bound
  exact evalLoop_refines_add lo extra model.environment model.words condition.code condition.words
    step.code step.words body.code body.words vars result done

theorem for_normal {F c n lo hi} (model : Model F)
    (pre : Program F ⟨c.function,false⟩ n) (condition : Term F n 1)
    (step : Program F ⟨c.function,false⟩ n) (body : Program F ⟨c.function,true⟩ n)
    (vars middle : Values n) (result : Outcome c n)
    (initialized : evalStmt lo model.environment model.words pre.code pre.words vars = some ⟨middle,.normal⟩)
    (ran : evalLoop hi model.environment model.words condition.code condition.words
      step.code step.words body.code body.words middle = some result) :
    evalStmt (max lo hi+1) model.environment model.words (Program.for_ pre condition step body).code
      (Program.for_ pre condition step body).words vars = some result := by
  rw [eval_for,evalStmt_stable (Nat.le_max_left lo hi)
    model.environment model.words pre.code pre.words vars initialized]
  exact loop_stable (Nat.le_max_right lo hi) model condition step body middle ran

theorem for_leave {F c n fuel} (model : Model F)
    (pre : Program F ⟨c.function,false⟩ n) (condition : Term F n 1)
    (step : Program F ⟨c.function,false⟩ n) (body : Program F ⟨c.function,true⟩ n)
    (vars middle : Values n) (proof : c.function = true)
    (initialized : evalStmt fuel model.environment model.words pre.code pre.words vars = some ⟨middle,.leave_ proof⟩) :
    evalStmt (fuel+1) model.environment model.words (Program.for_ (c := c) pre condition step body).code
      (Program.for_ (c := c) pre condition step body).words vars = some ⟨middle,.leave_ proof⟩ := by
  rw [eval_for,initialized]
  rfl

theorem modal_for {F c n} (mode : Modality) (model : Model F)
    (pre : Program F ⟨c.function,false⟩ n) (condition : Term F n 1)
    (step : Program F ⟨c.function,false⟩ n) (body : Program F ⟨c.function,true⟩ n)
    (post : Flow c → Fml n) (vars : Values n) :
    (Fml.modal mode model (Program.for_ pre condition step body) post).holds vars ↔
      (Fml.modal mode model pre (loopPrePost mode model condition step body post)).holds vars := by
  cases mode with
  | box =>
    constructor
    · intro all fuel mid initialized
      rcases mid with ⟨middle,flow⟩
      cases flow with
      | normal =>
        intro other result ran
        exact all (max fuel other+1) result (for_normal model pre condition step body vars middle result initialized ran)
      | leave_ proof =>
        exact all (fuel+1) _ (for_leave model pre condition step body vars middle proof initialized)
      | break_ impossible => cases impossible
      | continue_ impossible => cases impossible
    · intro all fuel result ran
      cases fuel with
      | zero => cases ran
      | succ fuel =>
        rw [eval_for] at ran
        cases initialized : evalStmt fuel model.environment model.words pre.code pre.words vars with
        | none => rw [initialized] at ran; cases ran
        | some mid =>
          rw [initialized] at ran
          have after := all fuel mid initialized
          rcases mid with ⟨middle,flow⟩
          cases flow with
          | normal => exact after fuel result ran
          | leave_ proof => cases Option.some.inj ran; exact after
          | break_ impossible => cases impossible
          | continue_ impossible => cases impossible
  | diamond =>
    constructor
    · rintro ⟨fuel,result,ran,after⟩
      cases fuel with
      | zero => cases ran
      | succ fuel =>
        rw [eval_for] at ran
        cases initialized : evalStmt fuel model.environment model.words pre.code pre.words vars with
        | none => rw [initialized] at ran; cases ran
        | some mid =>
          rw [initialized] at ran
          rcases mid with ⟨middle,flow⟩
          cases flow with
          | normal => exact ⟨fuel,⟨middle,.normal⟩,initialized,fuel,result,ran,after⟩
          | leave_ proof =>
            cases Option.some.inj ran
            exact ⟨fuel,⟨middle,.leave_ proof⟩,initialized,after⟩
          | break_ impossible => cases impossible
          | continue_ impossible => cases impossible
    · rintro ⟨fuel,mid,initialized,after⟩
      rcases mid with ⟨middle,flow⟩
      cases flow with
      | normal =>
        rcases after with ⟨other,result,ran,done⟩
        exact ⟨max fuel other+1,result,for_normal model pre condition step body vars middle result initialized ran,done⟩
      | leave_ proof =>
        exact ⟨fuel+1,_,for_leave model pre condition step body vars middle proof initialized,after⟩
      | break_ impossible => cases impossible
      | continue_ impossible => cases impossible


def loopBodyPost {F c n} (mode : Modality) (model : Model F) (condition : Term F n 1)
    (step : Program F ⟨c.function,false⟩ n) (body : Program F ⟨c.function,true⟩ n)
    (post : Flow c → Fml n) : Flow ⟨c.function,true⟩ → Fml n
  | .normal | .continue_ _ => .modal mode model (Program.for_ (c := c) step condition step body) post
  | .break_ _ => post .normal
  | .leave_ proof => post (.leave_ proof)

def loopConditionPost {F c n} (mode : Modality) (model : Model F) (condition : Term F n 1)
    (step : Program F ⟨c.function,false⟩ n) (body : Program F ⟨c.function,true⟩ n)
    (post : Flow c → Fml n) (values : Values 1) : Fml n :=
  if (values 0).val = 0 then post .normal
  else .modal mode model body (loopBodyPost mode model condition step body post)

def canResume {c : Control} : Flow c → Bool
  | .normal | .continue_ _ => true
  | .break_ _ | .leave_ _ => false

/-- The continuation is the ACTUAL for evaluator with step as initializer.
This executes one post-step then the next guard, never the original initializer. -/
theorem eval_loop (fuel : Nat) {F c n} (model : Model F) (condition : Term F n 1)
    (step : Program F ⟨c.function,false⟩ n) (body : Program F ⟨c.function,true⟩ n) (vars : Values n) :
    evalLoop (c := c) (fuel+1) model.environment model.words condition.code condition.words
      step.code step.words body.code body.words vars =
    (do let values ← evalExpr fuel model.environment model.words condition.code condition.words vars
        if (values 0).val = 0 then pure ⟨vars,.normal⟩
        else
          let result ← evalStmt fuel model.environment model.words body.code body.words vars
          match result.flow with
          | .normal | .continue_ _ =>
              evalStmt (fuel+1) model.environment model.words (Program.for_ (c := c) step condition step body).code
                (Program.for_ (c := c) step condition step body).words result.vars
          | .break_ _ => pure ⟨result.vars,.normal⟩
          | .leave_ proof => pure ⟨result.vars,.leave_ proof⟩) := rfl

theorem loop_zero {F c n lo} (model : Model F) (condition : Term F n 1)
    (step : Program F ⟨c.function,false⟩ n) (body : Program F ⟨c.function,true⟩ n)
    (vars : Values n) (values : Values 1)
    (tested : evalExpr lo model.environment model.words condition.code condition.words vars = some values)
    (zero : (values 0).val = 0) :
    evalLoop (c := c) (lo+1) model.environment model.words condition.code condition.words
      step.code step.words body.code body.words vars = some ⟨vars,.normal⟩ := by
  rw [eval_loop,tested]
  exact if_pos zero

theorem loop_resume {F c n lo mid hi} (model : Model F) (condition : Term F n 1)
    (step : Program F ⟨c.function,false⟩ n) (body : Program F ⟨c.function,true⟩ n)
    (vars : Values n) (values : Values 1) (afterBody : Outcome ⟨c.function,true⟩ n)
    (result : Outcome c n)
    (tested : evalExpr lo model.environment model.words condition.code condition.words vars = some values)
    (nonzero : (values 0).val ≠ 0)
    (bodyRan : evalStmt mid model.environment model.words body.code body.words vars = some afterBody)
    (resumes : canResume afterBody.flow = true)
    (continued : evalStmt hi model.environment model.words (Program.for_ (c := c) step condition step body).code
      (Program.for_ (c := c) step condition step body).words afterBody.vars = some result) :
    ∃ fuel, evalLoop fuel model.environment model.words condition.code condition.words
      step.code step.words body.code body.words vars = some result := by
  let horizon := max lo (max mid hi)
  have conditionBound : lo ≤ horizon := Nat.le_max_left _ _
  have bodyBound : mid ≤ horizon := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have resumeBound : hi ≤ horizon+1 :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (Nat.le_succ _)
  have resumeRan := evalStmt_stable resumeBound model.environment model.words
    (Program.for_ (c := c) step condition step body).code
    (Program.for_ (c := c) step condition step body).words afterBody.vars continued
  refine ⟨horizon+1,?_⟩
  rw [eval_loop,evalExpr_stable conditionBound
    model.environment model.words condition.code condition.words vars tested]
  change (if (values 0).val = 0 then _ else _) = _
  rw [if_neg nonzero,evalStmt_stable bodyBound
    model.environment model.words body.code body.words vars bodyRan]
  rcases afterBody with ⟨middle,flow⟩
  cases flow with
  | normal => exact resumeRan
  | continue_ proof => exact resumeRan
  | break_ proof => cases resumes
  | leave_ proof => cases resumes

theorem loop_break {F c n lo mid} (model : Model F) (condition : Term F n 1)
    (step : Program F ⟨c.function,false⟩ n) (body : Program F ⟨c.function,true⟩ n)
    (vars middle : Values n) (values : Values 1)
    (tested : evalExpr lo model.environment model.words condition.code condition.words vars = some values)
    (nonzero : (values 0).val ≠ 0)
    (bodyRan : evalStmt mid model.environment model.words body.code body.words vars = some ⟨middle,.break_ rfl⟩) :
    evalLoop (c := c) (max lo mid+1) model.environment model.words condition.code condition.words
      step.code step.words body.code body.words vars = some ⟨middle,.normal⟩ := by
  rw [eval_loop,evalExpr_stable (Nat.le_max_left lo mid)
    model.environment model.words condition.code condition.words vars tested]
  change (if (values 0).val = 0 then _ else _) = _
  rw [if_neg nonzero,evalStmt_stable (Nat.le_max_right lo mid)
    model.environment model.words body.code body.words vars bodyRan]
  rfl

theorem loop_leave {F c n lo mid} (model : Model F) (condition : Term F n 1)
    (step : Program F ⟨c.function,false⟩ n) (body : Program F ⟨c.function,true⟩ n)
    (vars middle : Values n) (values : Values 1) (proof : c.function = true)
    (tested : evalExpr lo model.environment model.words condition.code condition.words vars = some values)
    (nonzero : (values 0).val ≠ 0)
    (bodyRan : evalStmt mid model.environment model.words body.code body.words vars = some ⟨middle,.leave_ proof⟩) :
    evalLoop (c := c) (max lo mid+1) model.environment model.words condition.code condition.words
      step.code step.words body.code body.words vars = some ⟨middle,.leave_ proof⟩ := by
  rw [eval_loop,evalExpr_stable (Nat.le_max_left lo mid)
    model.environment model.words condition.code condition.words vars tested]
  change (if (values 0).val = 0 then _ else _) = _
  rw [if_neg nonzero,evalStmt_stable (Nat.le_max_right lo mid)
    model.environment model.words body.code body.words vars bodyRan]
  rfl


/-- One actual iteration. Continue runs the post-step; break consumes only this
loop's transfer; leave propagates. Every horizon synchronization is internal. -/
theorem modal_loop {F c n} (mode : Modality) (model : Model F) (condition : Term F n 1)
    (step : Program F ⟨c.function,false⟩ n) (body : Program F ⟨c.function,true⟩ n)
    (post : Flow c → Fml n) (vars : Values n) :
    (Fml.loopModal c mode model condition step body post).holds vars ↔
      (Fml.termModal mode model condition (loopConditionPost mode model condition step body post)).holds vars := by
  cases mode with
  | box =>
    constructor
    · intro all fuel values tested
      change (if (values 0).val = 0 then post .normal else
        Fml.modal .box model body (loopBodyPost .box model condition step body post)).holds vars
      by_cases zero : (values 0).val = 0
      · rw [if_pos zero]
        exact all (fuel+1) _ (loop_zero model condition step body vars values tested zero)
      · rw [if_neg zero]
        intro bodyFuel mid bodyRan
        rcases mid with ⟨middle,flow⟩
        cases flow with
        | normal =>
          intro resumeFuel result continued
          rcases loop_resume model condition step body vars values ⟨middle,.normal⟩ result
            tested zero bodyRan rfl continued with ⟨outer,ran⟩
          exact all outer result ran
        | continue_ proof =>
          intro resumeFuel result continued
          rcases loop_resume model condition step body vars values ⟨middle,.continue_ proof⟩ result
            tested zero bodyRan rfl continued with ⟨outer,ran⟩
          exact all outer result ran
        | break_ proof =>
          exact all (max fuel bodyFuel+1) _ (loop_break model condition step body vars middle values tested zero bodyRan)
        | leave_ proof =>
          exact all (max fuel bodyFuel+1) _ (loop_leave model condition step body vars middle values proof tested zero bodyRan)
    · intro all fuel result ran
      cases fuel with
      | zero => cases ran
      | succ fuel =>
        rw [eval_loop] at ran
        cases tested : evalExpr fuel model.environment model.words condition.code condition.words vars with
        | none => rw [tested] at ran; cases ran
        | some values =>
          rw [tested] at ran
          change (if (values 0).val = 0 then _ else _) = _ at ran
          have afterCondition := all fuel values tested
          change (if (values 0).val = 0 then post .normal else
            Fml.modal .box model body (loopBodyPost .box model condition step body post)).holds vars at afterCondition
          by_cases zero : (values 0).val = 0
          · rw [if_pos zero] at ran afterCondition
            cases Option.some.inj ran
            exact afterCondition
          · rw [if_neg zero] at ran afterCondition
            cases bodyRan : evalStmt fuel model.environment model.words body.code body.words vars with
            | none => rw [bodyRan] at ran; cases ran
            | some mid =>
              rw [bodyRan] at ran
              have afterBody := afterCondition fuel mid bodyRan
              rcases mid with ⟨middle,flow⟩
              cases flow with
              | normal => exact afterBody (fuel+1) result ran
              | continue_ proof => exact afterBody (fuel+1) result ran
              | break_ proof => cases Option.some.inj ran; exact afterBody
              | leave_ proof => cases Option.some.inj ran; exact afterBody
  | diamond =>
    constructor
    · rintro ⟨fuel,result,ran,after⟩
      cases fuel with
      | zero => cases ran
      | succ fuel =>
        rw [eval_loop] at ran
        cases tested : evalExpr fuel model.environment model.words condition.code condition.words vars with
        | none => rw [tested] at ran; cases ran
        | some values =>
          rw [tested] at ran
          change (if (values 0).val = 0 then _ else _) = _ at ran
          refine ⟨fuel,values,tested,?_⟩
          change (if (values 0).val = 0 then post .normal else
            Fml.modal .diamond model body (loopBodyPost .diamond model condition step body post)).holds vars
          by_cases zero : (values 0).val = 0
          · rw [if_pos zero] at ran ⊢
            cases Option.some.inj ran
            exact after
          · rw [if_neg zero] at ran ⊢
            cases bodyRan : evalStmt fuel model.environment model.words body.code body.words vars with
            | none => rw [bodyRan] at ran; cases ran
            | some mid =>
              rw [bodyRan] at ran
              refine ⟨fuel,mid,bodyRan,?_⟩
              rcases mid with ⟨middle,flow⟩
              cases flow with
              | normal => exact ⟨fuel+1,result,ran,after⟩
              | continue_ proof => exact ⟨fuel+1,result,ran,after⟩
              | break_ proof => cases Option.some.inj ran; exact after
              | leave_ proof => cases Option.some.inj ran; exact after
    · rintro ⟨fuel,values,tested,afterCondition⟩
      change (if (values 0).val = 0 then post .normal else
        Fml.modal .diamond model body (loopBodyPost .diamond model condition step body post)).holds vars at afterCondition
      by_cases zero : (values 0).val = 0
      · rw [if_pos zero] at afterCondition
        exact ⟨fuel+1,_,loop_zero model condition step body vars values tested zero,afterCondition⟩
      · rw [if_neg zero] at afterCondition
        rcases afterCondition with ⟨bodyFuel,mid,bodyRan,afterBody⟩
        rcases mid with ⟨middle,flow⟩
        cases flow with
        | normal =>
          rcases afterBody with ⟨resumeFuel,result,continued,after⟩
          rcases loop_resume model condition step body vars values ⟨middle,.normal⟩ result
            tested zero bodyRan rfl continued with ⟨outer,ran⟩
          exact ⟨outer,result,ran,after⟩
        | continue_ proof =>
          rcases afterBody with ⟨resumeFuel,result,continued,after⟩
          rcases loop_resume model condition step body vars values ⟨middle,.continue_ proof⟩ result
            tested zero bodyRan rfl continued with ⟨outer,ran⟩
          exact ⟨outer,result,ran,after⟩
        | break_ proof =>
          exact ⟨max fuel bodyFuel+1,_,loop_break model condition step body vars middle values tested zero bodyRan,afterBody⟩
        | leave_ proof =>
          exact ⟨max fuel bodyFuel+1,_,loop_leave model condition step body vars middle values proof tested zero bodyRan,afterBody⟩


theorem loop_completed_unique {F c n lo hi} (model : Model F) (condition : Term F n 1)
    (step : Program F ⟨c.function,false⟩ n) (body : Program F ⟨c.function,true⟩ n) (vars : Values n)
    {first second : Outcome c n}
    (one : evalLoop lo model.environment model.words condition.code condition.words
      step.code step.words body.code body.words vars = some first)
    (two : evalLoop hi model.environment model.words condition.code condition.words
      step.code step.words body.code body.words vars = some second) : first = second := by
  have left := loop_stable (Nat.le_max_left lo hi) model condition step body vars one
  have right := loop_stable (Nat.le_max_right lo hi) model condition step body vars two
  exact Option.some.inj (left.symm.trans right)

theorem loop_completed {F c n fuel} (mode : Modality) (model : Model F) (condition : Term F n 1)
    (step : Program F ⟨c.function,false⟩ n) (body : Program F ⟨c.function,true⟩ n)
    (post : Flow c → Fml n) (vars : Values n) (result : Outcome c n)
    (completed : evalLoop fuel model.environment model.words condition.code condition.words
      step.code step.words body.code body.words vars = some result) :
    (Fml.loopModal c mode model condition step body post).holds vars ↔
      (post result.flow).holds result.vars := by
  cases mode with
  | box =>
    constructor
    · intro all; exact all fuel result completed
    · intro after other actual ran
      have same := loop_completed_unique model condition step body vars completed ran
      cases same
      exact after
  | diamond =>
    constructor
    · rintro ⟨other,actual,ran,after⟩
      have same := loop_completed_unique model condition step body vars completed ran
      cases same
      exact after
    · intro after; exact ⟨fuel,result,completed,after⟩

end Solidity.Yul.Logic
