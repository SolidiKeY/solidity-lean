import Solidity.Yul.LocalBoolAgreement

/-! Checked uint8 LOCAL expressions over actual Source.RExpr. The actual
Source.evalPair consumes a horizon level and uses legacy right-first versus
viaIR left-first evaluation; this consumer preserves that exact shape.
Unchecked dirty arithmetic is not silently identified with bounded Source.Val. -/
namespace Solidity.Yul.LocalU8Expr

abbrev Ty := Solidity.Source.STy.int Solidity.Source.IntTy.u8

inductive Supported (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx) :
    Solidity.Source.RExpr env ctx Ty → Type where
  | local (index : Solidity.Source.Idx ctx Ty) : Supported env ctx (.local index)
  | assign {expr} (index : Solidity.Source.Idx ctx Ty) :
      Supported env ctx expr → Supported env ctx (.assign (.local index) expr)
  | add {left right} : Supported env ctx left → Supported env ctx right →
      Supported env ctx (.binary .add left right)

def eval {env ctx expr} (proof : Supported env ctx expr) :
    Solidity.Roadmap.Pipeline → Nat → LocalState env ctx →
      (Solidity.Source.R (LocalValue env Ty) × LocalState env ctx) := by
  apply Supported.casesOn (motive := fun _ _ =>
    Solidity.Roadmap.Pipeline → Nat → LocalState env ctx →
      (Solidity.Source.R (LocalValue env Ty) × LocalState env ctx)) proof
  case «local» =>
    intro index
    exact fun _ fuel state => match fuel with
      | 0 => (.error .timeout,state)
      | _+1 => (.ok (state.1.get index),state)
  case assign =>
    intro expr index child
    exact fun pipeline fuel state => match fuel with
      | 0 => (.error .timeout,state)
      | fuel+1 =>
          let (result,next) := eval child pipeline fuel state
          match result with
          | .error halt => (.error halt,next)
          | .ok value => (.ok value,(next.1.set index value,next.2))
  case add =>
    intro left right one two
    exact fun pipeline fuel state => match fuel with
      | 0 => (.error .timeout,state)
      | 1 => (.error .timeout,state)
      | fuel+2 =>
          match pipeline with
          | .legacy =>
              let (rightResult,middle) := eval two pipeline fuel state
              match rightResult with
              | .error halt => (.error halt,middle)
              | .ok right =>
                  let (leftResult,next) := eval one pipeline fuel middle
                  (leftResult.bind (fun left => LocalOperations.u8Binary true .add left right),next)
          | .viaIR =>
              let (leftResult,middle) := eval one pipeline fuel state
              match leftResult with
              | .error halt => (.error halt,middle)
              | .ok left =>
                  let (rightResult,next) := eval two pipeline fuel middle
                  (rightResult.bind (fun right => LocalOperations.u8Binary true .add left right),next)
termination_by structural proof

theorem zero {env ctx expr} (proof : Supported env ctx expr)
    (pipeline : Solidity.Roadmap.Pipeline) (state : LocalState env ctx) :
    eval proof pipeline 0 state = (.error .timeout,state) := by cases proof <;> rfl

theorem local_read {env ctx} (index : Solidity.Source.Idx ctx Ty)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : LocalState env ctx) :
    eval (.local index) pipeline (fuel+1) state = (.ok (state.1.get index),state) := rfl

theorem assign_step {env ctx expr} (index : Solidity.Source.Idx ctx Ty)
    (proof : Supported env ctx expr) (pipeline : Solidity.Roadmap.Pipeline)
    (fuel : Nat) (state : LocalState env ctx) :
    eval (.assign index proof) pipeline (fuel+1) state =
      (let (result,next) := eval proof pipeline fuel state
       match result with
       | .error halt => (.error halt,next)
       | .ok value => (.ok value,(next.1.set index value,next.2))) := rfl

theorem add_one {env ctx left right} (one : Supported env ctx left) (two : Supported env ctx right)
    (pipeline : Solidity.Roadmap.Pipeline) (state : LocalState env ctx) :
    eval (.add one two) pipeline 1 state = (.error .timeout,state) := rfl

theorem add_legacy {env ctx left right} (one : Supported env ctx left) (two : Supported env ctx right)
    (fuel : Nat) (state : LocalState env ctx) :
    eval (.add one two) .legacy (fuel+2) state =
      (let (rightResult,middle) := eval two .legacy fuel state
       match rightResult with
       | .error halt => (.error halt,middle)
       | .ok right =>
           let (leftResult,next) := eval one .legacy fuel middle
           (leftResult.bind (fun left => LocalOperations.u8Binary true .add left right),next)) := rfl

theorem add_viaIR {env ctx left right} (one : Supported env ctx left) (two : Supported env ctx right)
    (fuel : Nat) (state : LocalState env ctx) :
    eval (.add one two) .viaIR (fuel+2) state =
      (let (leftResult,middle) := eval one .viaIR fuel state
       match leftResult with
       | .error halt => (.error halt,middle)
       | .ok left =>
           let (rightResult,next) := eval two .viaIR fuel middle
           (rightResult.bind (fun right => LocalOperations.u8Binary true .add left right),next)) := rfl

theorem world {env ctx expr} (proof : Supported env ctx expr)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : LocalState env ctx) :
    (eval proof pipeline fuel state).2.2 = state.2 := by
  induction proof generalizing pipeline fuel state with
  | «local» index => cases fuel <;> rfl
  | assign index child ih =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          have unchanged := ih pipeline fuel state
          cases actual : eval child pipeline fuel state with
          | mk result next =>
              rw [actual] at unchanged
              rw [assign_step,actual]
              cases result <;> exact unchanged
  | add one two ihOne ihTwo =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases fuel with
          | zero => rfl
          | succ fuel =>
              cases pipeline with
              | legacy =>
                  have before := ihTwo .legacy fuel state
                  cases rightRun : eval two .legacy fuel state with
                  | mk rightResult middle =>
                      rw [rightRun] at before
                      rw [add_legacy,rightRun]
                      cases rightResult with
                      | error halt => exact before
                      | ok right =>
                          dsimp only
                          have after := ihOne .legacy fuel middle
                          cases leftRun : eval one .legacy fuel middle with
                          | mk leftResult next =>
                              rw [leftRun] at after
                              exact after.trans before
              | viaIR =>
                  have before := ihOne .viaIR fuel state
                  cases leftRun : eval one .viaIR fuel state with
                  | mk leftResult middle =>
                      rw [leftRun] at before
                      rw [add_viaIR,leftRun]
                      cases leftResult with
                      | error halt => exact before
                      | ok left =>
                          dsimp only
                          have after := ihTwo .viaIR fuel middle
                          cases rightRun : eval two .viaIR fuel middle with
                          | mk rightResult next =>
                              rw [rightRun] at after
                              exact after.trans before

theorem evidence_unique {env ctx expr} (one two : Supported env ctx expr) : one = two := by
  induction one with
  | «local» index => cases two; rfl
  | assign index child ih =>
      cases two with
      | assign _ other => exact congrArg (Supported.assign index) (ih other)
  | add one next ihOne ihNext =>
      cases two with
      | add other more =>
          cases ihOne other
          cases ihNext more
          rfl

theorem evidence_independent {env ctx expr} (one two : Supported env ctx expr)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : LocalState env ctx) :
    eval one pipeline fuel state = eval two pipeline fuel state := by
  cases evidence_unique one two
  rfl

end Solidity.Yul.LocalU8Expr
