import Solidity.Yul.LocalU8Agreement

/-! Actual Source.compare over the existing checked-u8 child consumers.
Raw operands are projected explicitly by this LOCAL operation; assembly writes
remain raw. Clean-state Source agreement requires checked frames for children,
not an assumed child/simulation law. No general dirty compiler claim. -/
namespace Solidity.Yul.LocalU8Compare
open LocalU8Expr

def operation {env} (op : Solidity.Source.BinOp) (left right : LocalValue env Ty) :
    Solidity.Source.R (LocalValue env .bool) :=
  (Solidity.Source.cmpVal op (LocalOperations.u8Input left) (LocalOperations.u8Input right)).map
    (fun result => .clean (.bool result))

theorem operation_clean {env : Solidity.Source.Env} (op : Solidity.Source.BinOp)
    (left right : Solidity.Source.Val env.layout Ty) :
    operation op (.clean left) (.clean right) =
      (Solidity.Source.cmpVal op left right).map (fun result => .clean (.bool result)) := by
  unfold operation
  rw [LocalOperations.u8Input_clean_value,LocalOperations.u8Input_clean_value]

def compare {env ctx left right} (op : Solidity.Source.BinOp)
    (one : Supported env ctx left) (two : Supported env ctx right)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : LocalState env ctx) :
    Solidity.Source.R (LocalValue env .bool) × LocalState env ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | 1 => (.error .timeout,state)
  | fuel+2 => match pipeline with
    | .legacy =>
        let (rightResult,middle) := eval two pipeline fuel state
        match rightResult with
        | .error halt => (.error halt,middle)
        | .ok right =>
            let (leftResult,next) := eval one pipeline fuel middle
            (leftResult.bind (fun left => operation op left right),next)
    | .viaIR =>
        let (leftResult,middle) := eval one pipeline fuel state
        match leftResult with
        | .error halt => (.error halt,middle)
        | .ok left =>
            let (rightResult,next) := eval two pipeline fuel middle
            (rightResult.bind (fun right => operation op left right),next)

theorem compare_legacy {env ctx left right} (op : Solidity.Source.BinOp)
    (one : Supported env ctx left) (two : Supported env ctx right) (fuel : Nat)
    (state : LocalState env ctx) :
    compare op one two .legacy (fuel+2) state =
      (let (rightResult,middle) := eval two .legacy fuel state
       match rightResult with
       | .error halt => (.error halt,middle)
       | .ok right =>
           let (leftResult,next) := eval one .legacy fuel middle
           (leftResult.bind (fun left => operation op left right),next)) := rfl

theorem compare_viaIR {env ctx left right} (op : Solidity.Source.BinOp)
    (one : Supported env ctx left) (two : Supported env ctx right) (fuel : Nat)
    (state : LocalState env ctx) :
    compare op one two .viaIR (fuel+2) state =
      (let (leftResult,middle) := eval one .viaIR fuel state
       match leftResult with
       | .error halt => (.error halt,middle)
       | .ok left =>
           let (rightResult,next) := eval two .viaIR fuel middle
           (rightResult.bind (fun right => operation op left right),next)) := rfl

theorem source_compare_error {env ctx} (op : Solidity.Source.BinOp)
    (left right : Solidity.Source.RExpr env ctx Ty)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state next : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)
    (halt : Solidity.Source.Halt)
    (actual : (Solidity.Source.evalPair glob frame fuel left right).run state = (.error halt,next)) :
    (Solidity.Source.evalE glob frame (fuel+1) (.compare op left right)).run state =
      (.error halt,next) := by
  rw [Solidity.Source.evalE,Solidity.Source.Hoare.run_bind,actual]

theorem source_compare_values {env ctx} (op : Solidity.Source.BinOp)
    (left right : Solidity.Source.RExpr env ctx Ty)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (state next : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env)
    (leftValue rightValue : Solidity.Source.Val env.layout Ty)
    (actual : (Solidity.Source.evalPair glob frame fuel left right).run state =
      (.ok (.val leftValue,.val rightValue),next)) :
    (Solidity.Source.evalE glob frame (fuel+1) (.compare op left right)).run state =
      ((Solidity.Source.cmpVal op leftValue rightValue).map (fun b => .val (.bool b)),next) := by
  rw [Solidity.Source.evalE,Solidity.Source.Hoare.run_bind,actual]
  dsimp only
  change (do
    let value ← Solidity.Source.EM.lift (Solidity.Source.cmpVal op leftValue rightValue)
    pure (Solidity.Source.RVal.val (.bool value))).run next = _
  cases result : Solidity.Source.cmpVal op leftValue rightValue <;>
    simp only [Solidity.Source.EM.lift] <;> rfl

theorem step_agrees {env ctx left right} (op : Solidity.Source.BinOp) (one : Supported env ctx left) (two : Supported env ctx right)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel : Nat)
    (leftAgreement : ∀ state, eval one glob.pipeline fuel (LocalState.ofClean state) =
      cleanOutcome ((Solidity.Source.evalE glob frame fuel left).run state))
    (rightAgreement : ∀ state, eval two glob.pipeline fuel (LocalState.ofClean state) =
      cleanOutcome ((Solidity.Source.evalE glob frame fuel right).run state))
    (state : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env) :
    compare op one two glob.pipeline (fuel+2) (LocalState.ofClean state) =
      LocalBoolExpr.cleanOutcome ((Solidity.Source.evalE glob frame (fuel+2) (.compare op left right)).run state) := by
  cases pipeline : glob.pipeline with
  | legacy =>
      have first := rightAgreement state
      rw [pipeline] at first
      cases rightRun : (Solidity.Source.evalE glob frame fuel right).run state with
      | mk rightResult middle =>
          rw [rightRun] at first
          cases rightResult with
          | error halt =>
              change eval two .legacy fuel (LocalState.ofClean state) =
                (.error halt,LocalState.ofClean middle) at first
              have pairRun : (Solidity.Source.evalPair glob frame (fuel+1) left right).run state =
                  (.error halt,middle) := by
                rw [source_pair_legacy left right glob frame fuel state pipeline,rightRun]
              rw [compare_legacy,first,source_compare_error op left right glob frame (fuel+1) state middle halt pairRun]
              rfl
          | ok rightValue =>
              cases rightValue with
              | val rightValue =>
                  change eval two .legacy fuel (LocalState.ofClean state) =
                    (.ok (.clean rightValue),LocalState.ofClean middle) at first
                  have second := leftAgreement middle
                  rw [pipeline] at second
                  cases leftRun : (Solidity.Source.evalE glob frame fuel left).run middle with
                  | mk leftResult next =>
                      rw [leftRun] at second
                      cases leftResult with
                      | error halt =>
                          change eval one .legacy fuel (LocalState.ofClean middle) =
                            (.error halt,LocalState.ofClean next) at second
                          have pairRun : (Solidity.Source.evalPair glob frame (fuel+1) left right).run state =
                              (.error halt,next) := by
                            rw [source_pair_legacy left right glob frame fuel state pipeline,rightRun]
                            dsimp only
                            rw [leftRun]
                          rw [compare_legacy,first]
                          dsimp only
                          rw [second,source_compare_error op left right glob frame (fuel+1) state next halt pairRun]
                          rfl
                      | ok leftValue =>
                          cases leftValue with
                          | val leftValue =>
                              change eval one .legacy fuel (LocalState.ofClean middle) =
                                (.ok (.clean leftValue),LocalState.ofClean next) at second
                              have pairRun : (Solidity.Source.evalPair glob frame (fuel+1) left right).run state =
                                  (.ok (.val leftValue,.val rightValue),next) := by
                                rw [source_pair_legacy left right glob frame fuel state pipeline,rightRun]
                                dsimp only
                                rw [leftRun]
                              rw [compare_legacy,first]
                              dsimp only
                              rw [second,source_compare_values op left right glob frame (fuel+1) state next
                                leftValue rightValue pairRun]
                              simp only [Except.bind,operation_clean]
                              cases operation : Solidity.Source.cmpVal op leftValue rightValue <;> rfl
  | viaIR =>
      have first := leftAgreement state
      rw [pipeline] at first
      cases leftRun : (Solidity.Source.evalE glob frame fuel left).run state with
      | mk leftResult middle =>
          rw [leftRun] at first
          cases leftResult with
          | error halt =>
              change eval one .viaIR fuel (LocalState.ofClean state) =
                (.error halt,LocalState.ofClean middle) at first
              have pairRun : (Solidity.Source.evalPair glob frame (fuel+1) left right).run state =
                  (.error halt,middle) := by
                rw [source_pair_viaIR left right glob frame fuel state pipeline,leftRun]
              rw [compare_viaIR,first,source_compare_error op left right glob frame (fuel+1) state middle halt pairRun]
              rfl
          | ok leftValue =>
              cases leftValue with
              | val leftValue =>
                  change eval one .viaIR fuel (LocalState.ofClean state) =
                    (.ok (.clean leftValue),LocalState.ofClean middle) at first
                  have second := rightAgreement middle
                  rw [pipeline] at second
                  cases rightRun : (Solidity.Source.evalE glob frame fuel right).run middle with
                  | mk rightResult next =>
                      rw [rightRun] at second
                      cases rightResult with
                      | error halt =>
                          change eval two .viaIR fuel (LocalState.ofClean middle) =
                            (.error halt,LocalState.ofClean next) at second
                          have pairRun : (Solidity.Source.evalPair glob frame (fuel+1) left right).run state =
                              (.error halt,next) := by
                            rw [source_pair_viaIR left right glob frame fuel state pipeline,leftRun]
                            dsimp only
                            rw [rightRun]
                          rw [compare_viaIR,first]
                          dsimp only
                          rw [second,source_compare_error op left right glob frame (fuel+1) state next halt pairRun]
                          rfl
                      | ok rightValue =>
                          cases rightValue with
                          | val rightValue =>
                              change eval two .viaIR fuel (LocalState.ofClean middle) =
                                (.ok (.clean rightValue),LocalState.ofClean next) at second
                              have pairRun : (Solidity.Source.evalPair glob frame (fuel+1) left right).run state =
                                  (.ok (.val leftValue,.val rightValue),next) := by
                                rw [source_pair_viaIR left right glob frame fuel state pipeline,leftRun]
                                dsimp only
                                rw [rightRun]
                              rw [compare_viaIR,first]
                              dsimp only
                              rw [second,source_compare_values op left right glob frame (fuel+1) state next
                                leftValue rightValue pairRun]
                              simp only [Except.bind,operation_clean]
                              cases operation : Solidity.Source.cmpVal op leftValue rightValue <;> rfl

/-- Concrete Source equality: child agreements are discharged by the actual
existing all-tree theorem. The checked-frame premise is needed by child adds. -/
theorem source_agrees {env ctx left right} (op : Solidity.Source.BinOp)
    (one : Supported env ctx left) (two : Supported env ctx right)
    (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (checked : frame.checked = true)
    (fuel : Nat) (state : Solidity.Source.Locals env.layout ctx × Solidity.Source.St env) :
    compare op one two glob.pipeline fuel (LocalState.ofClean state) =
      LocalBoolExpr.cleanOutcome
        ((Solidity.Source.evalE glob frame fuel (.compare op left right)).run state) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases fuel with
      | zero =>
          have pairRun : (Solidity.Source.evalPair glob frame 0 left right).run state =
              (.error .timeout,state) := rfl
          rw [source_compare_error op left right glob frame 0 state state .timeout pairRun]
          rfl
      | succ fuel =>
          exact step_agrees op one two glob frame fuel
            (LocalU8Expr.source_agrees one glob frame checked fuel)
            (LocalU8Expr.source_agrees two glob frame checked fuel) state

theorem world {env ctx left right} (op : Solidity.Source.BinOp)
    (one : Supported env ctx left) (two : Supported env ctx right)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : LocalState env ctx) :
    (compare op one two pipeline fuel state).2.2 = state.2 := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases pipeline with
          | legacy =>
              have before := LocalU8Expr.world two .legacy fuel state
              cases rightRun : eval two .legacy fuel state with
              | mk result middle =>
                  rw [rightRun] at before
                  rw [compare_legacy,rightRun]
                  cases result with
                  | error halt => exact before
                  | ok right =>
                      dsimp only
                      have after := LocalU8Expr.world one .legacy fuel middle
                      cases leftRun : eval one .legacy fuel middle with
                      | mk result next =>
                          rw [leftRun] at after
                          exact after.trans before
          | viaIR =>
              have before := LocalU8Expr.world one .viaIR fuel state
              cases leftRun : eval one .viaIR fuel state with
              | mk result middle =>
                  rw [leftRun] at before
                  rw [compare_viaIR,leftRun]
                  cases result with
                  | error halt => exact before
                  | ok left =>
                      dsimp only
                      have after := LocalU8Expr.world two .viaIR fuel middle
                      cases rightRun : eval two .viaIR fuel middle with
                      | mk result next =>
                          rw [rightRun] at after
                          exact after.trans before

theorem evidence_independent {env ctx left right} (op : Solidity.Source.BinOp)
    (one other : Supported env ctx left) (two more : Supported env ctx right)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : LocalState env ctx) :
    compare op one two pipeline fuel state = compare op other more pipeline fuel state := by
  cases LocalU8Expr.evidence_unique one other
  cases LocalU8Expr.evidence_unique two more
  rfl

end Solidity.Yul.LocalU8Compare
