import Solidity.Yul.LocalU8Horizon
import Solidity.Yul.LocalU8Compare

/-! Exact terminal fuel stability for the existing checked-u8 comparison runner.
Preserves pipeline order, raw local writes and errors. Timeout is excluded. -/
namespace Solidity.Yul.LocalU8CompareHorizon

theorem successor : ∀ (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx)
 (left right : Solidity.Source.RExpr env ctx Solidity.Yul.LocalU8Expr.Ty)
 (op : Solidity.Source.BinOp)
 (one : Solidity.Yul.LocalU8Expr.Supported env ctx left)
 (two : Solidity.Yul.LocalU8Expr.Supported env ctx right)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (state : Solidity.Yul.LocalState env ctx),
 (Solidity.Yul.LocalU8Compare.compare op one two pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.LocalU8Compare.compare op one two pipeline (fuel+1) state =
 Solidity.Yul.LocalU8Compare.compare op one two pipeline fuel state := by
  intro env ctx left right op one two pipeline fuel state terminal
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
              intro impossible
              rw [firstRun] at impossible
              have same : halt = .timeout := Except.error.inj impossible
              apply terminal
              simp only [Solidity.Yul.LocalU8Compare.compare_legacy,firstRun,same]
            simp only [Solidity.Yul.LocalU8Compare.compare_legacy,Solidity.Yul.LocalU8Horizon.successor env ctx _ two .legacy fuel state ready,firstRun]
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
                  intro impossible
                  rw [secondRun] at impossible
                  have same : halt = .timeout := Except.error.inj impossible
                  apply terminal
                  simp only [Solidity.Yul.LocalU8Compare.compare_legacy,firstRun,secondRun,Except.bind,same]
                simp only [Solidity.Yul.LocalU8Compare.compare_legacy,Solidity.Yul.LocalU8Horizon.successor env ctx _ two .legacy fuel state ready,firstRun,Solidity.Yul.LocalU8Horizon.successor env ctx _ one .legacy fuel middle nextReady,secondRun]
              | ok secondValue =>
                have nextReady : (Solidity.Yul.LocalU8Expr.eval one .legacy fuel middle).1 ≠ .error .timeout := by
                  rw [secondRun]
                  intro impossible
                  cases impossible
                simp only [Solidity.Yul.LocalU8Compare.compare_legacy,Solidity.Yul.LocalU8Horizon.successor env ctx _ two .legacy fuel state ready,firstRun,Solidity.Yul.LocalU8Horizon.successor env ctx _ one .legacy fuel middle nextReady,secondRun]
      | viaIR =>
        cases firstRun : Solidity.Yul.LocalU8Expr.eval one .viaIR fuel state with
        | mk firstResult middle =>
          cases firstResult with
          | error halt =>
            have ready : (Solidity.Yul.LocalU8Expr.eval one .viaIR fuel state).1 ≠ .error .timeout := by
              intro impossible
              rw [firstRun] at impossible
              have same : halt = .timeout := Except.error.inj impossible
              apply terminal
              simp only [Solidity.Yul.LocalU8Compare.compare_viaIR,firstRun,same]
            simp only [Solidity.Yul.LocalU8Compare.compare_viaIR,Solidity.Yul.LocalU8Horizon.successor env ctx _ one .viaIR fuel state ready,firstRun]
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
                  intro impossible
                  rw [secondRun] at impossible
                  have same : halt = .timeout := Except.error.inj impossible
                  apply terminal
                  simp only [Solidity.Yul.LocalU8Compare.compare_viaIR,firstRun,secondRun,Except.bind,same]
                simp only [Solidity.Yul.LocalU8Compare.compare_viaIR,Solidity.Yul.LocalU8Horizon.successor env ctx _ one .viaIR fuel state ready,firstRun,Solidity.Yul.LocalU8Horizon.successor env ctx _ two .viaIR fuel middle nextReady,secondRun]
              | ok secondValue =>
                have nextReady : (Solidity.Yul.LocalU8Expr.eval two .viaIR fuel middle).1 ≠ .error .timeout := by
                  rw [secondRun]
                  intro impossible
                  cases impossible
                simp only [Solidity.Yul.LocalU8Compare.compare_viaIR,Solidity.Yul.LocalU8Horizon.successor env ctx _ one .viaIR fuel state ready,firstRun,Solidity.Yul.LocalU8Horizon.successor env ctx _ two .viaIR fuel middle nextReady,secondRun]

theorem extension : ∀ (env : Solidity.Source.Env) (ctx : Solidity.Source.RCtx)
 (left right : Solidity.Source.RExpr env ctx Solidity.Yul.LocalU8Expr.Ty)
 (op : Solidity.Source.BinOp)
 (one : Solidity.Yul.LocalU8Expr.Supported env ctx left)
 (two : Solidity.Yul.LocalU8Expr.Supported env ctx right)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel extra : Nat)
 (state : Solidity.Yul.LocalState env ctx),
 (Solidity.Yul.LocalU8Compare.compare op one two pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.LocalU8Compare.compare op one two pipeline (fuel+extra) state =
 Solidity.Yul.LocalU8Compare.compare op one two pipeline fuel state := by
  intro env ctx left right op one two pipeline fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have stillTerminal : (Solidity.Yul.LocalU8Compare.compare op one two pipeline (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (Solidity.Yul.LocalU8CompareHorizon.successor env ctx left right op one two pipeline (fuel+extra) state stillTerminal).trans ih

end Solidity.Yul.LocalU8CompareHorizon
