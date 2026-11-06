import Solidity.Yul.LocalBoolControl

/-! Evidence independence for the actual control interpreter, including raw
states. Different certificates for the same Source.RExpr are permitted, but
their complete result/partial state must agree. -/
namespace Solidity.Yul.LocalBoolControl

theorem base_not {env ctx expr} (proof : LocalBoolExpr.Supported env ctx expr)
    (fuel : Nat) (state : LocalState env ctx) :
    eval (.base (.not proof)) fuel state = eval (.not (.base proof)) fuel state := by
  cases fuel <;> rfl

theorem base_assign {env ctx expr} (index : Solidity.Source.Idx ctx .bool)
    (proof : LocalBoolExpr.Supported env ctx expr) (fuel : Nat) (state : LocalState env ctx) :
    eval (.base (.assign index proof)) fuel state =
      eval (.assign index (.base proof)) fuel state := by
  cases fuel <;> rfl

theorem base_independent {env ctx expr} (one : LocalBoolExpr.Supported env ctx expr)
    (two : Supported env ctx expr) (fuel : Nat) (state : LocalState env ctx) :
    eval (.base one) fuel state = eval two fuel state := by
  induction one generalizing fuel state with
  | literal value =>
      cases two with
      | base other =>
          cases LocalBoolExpr.evidence_unique (.literal value) other
          rfl
  | «local» index =>
      cases two with
      | base other =>
          cases LocalBoolExpr.evidence_unique (.local index) other
          rfl
  | not child ih =>
      cases two with
      | base other =>
          cases LocalBoolExpr.evidence_unique (.not child) other
          rfl
      | not other =>
          rw [base_not]
          cases fuel with
          | zero => rfl
          | succ fuel => rw [not_step,not_step,ih other fuel state]
  | assign index child ih =>
      cases two with
      | base other =>
          cases LocalBoolExpr.evidence_unique (.assign index child) other
          rfl
      | assign _ other =>
          rw [base_assign]
          cases fuel with
          | zero => rfl
          | succ fuel => rw [assign_step,assign_step,ih other fuel state]

theorem evidence_independent {env ctx expr} (one two : Supported env ctx expr)
    (fuel : Nat) (state : LocalState env ctx) : eval one fuel state = eval two fuel state := by
  induction one generalizing fuel state with
  | base proof => exact base_independent proof two fuel state
  | and one next ihOne ihNext =>
      cases two with
      | base impossible => cases impossible
      | and other more =>
          cases fuel with
          | zero => rfl
          | succ fuel =>
              rw [and_step,and_step,ihOne other fuel state]
              cases actual : eval other fuel state with
              | mk result after =>
                  cases result with
                  | error halt => rfl
                  | ok value =>
                      cases choice : truth value with
                      | false => simp only [choice,Bool.false_eq_true,if_false]
                      | true =>
                          simp only [choice,if_true]
                          exact ihNext more fuel after
  | or one next ihOne ihNext =>
      cases two with
      | base impossible => cases impossible
      | or other more =>
          cases fuel with
          | zero => rfl
          | succ fuel =>
              rw [or_step,or_step,ihOne other fuel state]
              cases actual : eval other fuel state with
              | mk result after =>
                  cases result with
                  | error halt => rfl
                  | ok value =>
                      cases choice : truth value with
                      | false =>
                          simp only [choice,Bool.false_eq_true,if_false]
                          exact ihNext more fuel after
                      | true => simp only [choice,if_true]
  | cond test yes no ihTest ihYes ihNo =>
      cases two with
      | base impossible => cases impossible
      | cond other one next =>
          cases fuel with
          | zero => rfl
          | succ fuel =>
              rw [cond_step,cond_step,ihTest other fuel state]
              cases actual : eval other fuel state with
              | mk result after =>
                  cases result with
                  | error halt => rfl
                  | ok value =>
                      cases choice : truth value with
                      | false =>
                          simp only [choice,Bool.false_eq_true,if_false]
                          exact ihNo next fuel after
                      | true =>
                          simp only [choice,if_true]
                          exact ihYes one fuel after
  | not child ih =>
      cases two with
      | base other => exact (base_independent other (.not child) fuel state).symm
      | not other =>
          cases fuel with
          | zero => rfl
          | succ fuel => rw [not_step,not_step,ih other fuel state]
  | assign index child ih =>
      cases two with
      | base other => exact (base_independent other (.assign index child) fuel state).symm
      | assign _ other =>
          cases fuel with
          | zero => rfl
          | succ fuel => rw [assign_step,assign_step,ih other fuel state]

end Solidity.Yul.LocalBoolControl
