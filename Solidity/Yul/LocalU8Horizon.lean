import Solidity.Yul.LocalU8Expr

/-! Exact fuel stability after a non-timeout checked-u8 execution.
Timeout prefixes may retain writes and are deliberately excluded.
No Source readback, unchecked arithmetic or admission contract is changed. -/
namespace Solidity.Yul.LocalU8Horizon

theorem successor : ∀ (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx)
 (expr : Solidity.Source.RExpr env ctx Solidity.Yul.LocalU8Expr.Ty)
 (proof : Solidity.Yul.LocalU8Expr.Supported env ctx expr)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (state : Solidity.Yul.LocalState env ctx),
 (Solidity.Yul.LocalU8Expr.eval proof pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.LocalU8Expr.eval proof pipeline (fuel+1) state =
 Solidity.Yul.LocalU8Expr.eval proof pipeline fuel state := by
  intro env ctx expr proof
  induction proof with
  | «local» index =>
    intro pipeline fuel state terminal
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel => rfl
  | assign index child ih =>
    intro pipeline fuel state terminal
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel =>
      cases childRun : Solidity.Yul.LocalU8Expr.eval child pipeline fuel state with
      | mk result next =>
        cases result with
        | error halt =>
          have ready : (Solidity.Yul.LocalU8Expr.eval child pipeline fuel state).1 ≠ .error .timeout := by
            simpa only [Solidity.Yul.LocalU8Expr.assign_step,childRun] using terminal
          simp only [Solidity.Yul.LocalU8Expr.assign_step,ih pipeline fuel state ready,childRun]
        | ok value =>
          have ready : (Solidity.Yul.LocalU8Expr.eval child pipeline fuel state).1 ≠ .error .timeout := by
            rw [childRun]
            intro impossible
            cases impossible
          simp only [Solidity.Yul.LocalU8Expr.assign_step,ih pipeline fuel state ready,childRun]
  | add one two ihOne ihTwo =>
    intro pipeline fuel state terminal
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel =>
      cases fuel with
      | zero => exact False.elim (terminal rfl)
      | succ fuel =>
        cases pipeline with
        | legacy =>
          cases firstRun : Solidity.Yul.LocalU8Expr.eval two .legacy fuel state with
          | mk firstResult middle =>
            cases firstResult with
            | error halt =>
              have ready : (Solidity.Yul.LocalU8Expr.eval two .legacy fuel state).1 ≠ .error .timeout := by
                simpa only [Solidity.Yul.LocalU8Expr.add_legacy,firstRun] using terminal
              simp only [Solidity.Yul.LocalU8Expr.add_legacy,ihTwo .legacy fuel state ready,firstRun]
            | ok firstValue =>
              have ready : (Solidity.Yul.LocalU8Expr.eval two .legacy fuel state).1 ≠ .error .timeout := by
                rw [firstRun]
                intro impossible
                cases impossible
              cases secondRun : Solidity.Yul.LocalU8Expr.eval one .legacy fuel middle with
              | mk secondResult next =>
                cases secondResult with
                | error halt =>
                  have nextReady : (Solidity.Yul.LocalU8Expr.eval one .legacy fuel middle).1 ≠ .error .timeout := by
                    simpa only [Solidity.Yul.LocalU8Expr.add_legacy,firstRun,secondRun,Except.bind] using terminal
                  simp only [Solidity.Yul.LocalU8Expr.add_legacy,ihTwo .legacy fuel state ready,firstRun,
                    ihOne .legacy fuel middle nextReady,secondRun]
                | ok secondValue =>
                  have nextReady : (Solidity.Yul.LocalU8Expr.eval one .legacy fuel middle).1 ≠ .error .timeout := by
                    rw [secondRun]
                    intro impossible
                    cases impossible
                  simp only [Solidity.Yul.LocalU8Expr.add_legacy,ihTwo .legacy fuel state ready,firstRun,
                    ihOne .legacy fuel middle nextReady,secondRun]
        | viaIR =>
          cases firstRun : Solidity.Yul.LocalU8Expr.eval one .viaIR fuel state with
          | mk firstResult middle =>
            cases firstResult with
            | error halt =>
              have ready : (Solidity.Yul.LocalU8Expr.eval one .viaIR fuel state).1 ≠ .error .timeout := by
                simpa only [Solidity.Yul.LocalU8Expr.add_viaIR,firstRun] using terminal
              simp only [Solidity.Yul.LocalU8Expr.add_viaIR,ihOne .viaIR fuel state ready,firstRun]
            | ok firstValue =>
              have ready : (Solidity.Yul.LocalU8Expr.eval one .viaIR fuel state).1 ≠ .error .timeout := by
                rw [firstRun]
                intro impossible
                cases impossible
              cases secondRun : Solidity.Yul.LocalU8Expr.eval two .viaIR fuel middle with
              | mk secondResult next =>
                cases secondResult with
                | error halt =>
                  have nextReady : (Solidity.Yul.LocalU8Expr.eval two .viaIR fuel middle).1 ≠ .error .timeout := by
                    simpa only [Solidity.Yul.LocalU8Expr.add_viaIR,firstRun,secondRun,Except.bind] using terminal
                  simp only [Solidity.Yul.LocalU8Expr.add_viaIR,ihOne .viaIR fuel state ready,firstRun,
                    ihTwo .viaIR fuel middle nextReady,secondRun]
                | ok secondValue =>
                  have nextReady : (Solidity.Yul.LocalU8Expr.eval two .viaIR fuel middle).1 ≠ .error .timeout := by
                    rw [secondRun]
                    intro impossible
                    cases impossible
                  simp only [Solidity.Yul.LocalU8Expr.add_viaIR,ihOne .viaIR fuel state ready,firstRun,
                    ihTwo .viaIR fuel middle nextReady,secondRun]

theorem extension : ∀ (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx)
 (expr : Solidity.Source.RExpr env ctx Solidity.Yul.LocalU8Expr.Ty)
 (proof : Solidity.Yul.LocalU8Expr.Supported env ctx expr)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel extra : Nat)
 (state : Solidity.Yul.LocalState env ctx),
 (Solidity.Yul.LocalU8Expr.eval proof pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.LocalU8Expr.eval proof pipeline (fuel+extra) state =
 Solidity.Yul.LocalU8Expr.eval proof pipeline fuel state := by
  intro env ctx expr proof pipeline fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have stillTerminal : (Solidity.Yul.LocalU8Expr.eval proof pipeline (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (Solidity.Yul.LocalU8Horizon.successor env ctx expr proof pipeline (fuel+extra) state stillTerminal).trans ih

end Solidity.Yul.LocalU8Horizon
