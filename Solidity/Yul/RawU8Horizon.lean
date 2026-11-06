import Solidity.Yul.RawU8Statement
import Solidity.Yul.LocalU8Horizon

/-! Exact completed-result horizons for actual checked-u8 statement and raw-frame
execution. Timeout prefixes are excluded; pipeline stays fixed. Source transport
retains checked-frame and coherence premises, without dirty readback. -/

namespace Solidity.Yul.RawU8Horizon
theorem localExtension : ∀ (ctx : Solidity.Source.Ctx)
 (expr : Solidity.Source.RExpr ctx.env ctx.tys Solidity.Yul.LocalU8Expr.Ty)
 (proof : Solidity.Yul.LocalU8Expr.Supported ctx.env ctx.tys expr)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel extra : Nat)
 (state : Solidity.Yul.LocalState ctx.env ctx.tys),
 (Solidity.Yul.LocalU8Statement.run proof pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.LocalU8Statement.run proof pipeline (fuel+extra) state =
 Solidity.Yul.LocalU8Statement.run proof pipeline fuel state := by
  intro ctx expr proof pipeline fuel extra state terminal
  cases fuel with
  | zero => exact False.elim (terminal rfl)
  | succ fuel =>
    have childReady : (LocalU8Expr.eval proof pipeline fuel state).1 ≠ .error .timeout := by
      intro bad
      apply terminal
      simp only [LocalU8Statement.step,bad,Except.map]
    have stable := LocalU8Horizon.extension ctx.env ctx.tys expr proof pipeline fuel extra state childReady
    simp only [Nat.succ_add,LocalU8Statement.step,stable]

theorem extension : ∀ (ctx : Solidity.Source.Ctx)
 (expr : Solidity.Source.RExpr ctx.env ctx.tys Solidity.Yul.LocalU8Expr.Ty)
 (proof : Solidity.Yul.LocalU8Expr.Supported ctx.env ctx.tys expr)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel extra : Nat)
 (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawU8Statement.run proof pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawU8Statement.run proof pipeline (fuel+extra) state =
 Solidity.Yul.RawU8Statement.run proof pipeline fuel state := by
  intro ctx expr proof pipeline fuel extra state terminal
  have ready : (LocalU8Statement.run proof pipeline fuel (RawCoherent.prepare state)).1 ≠ .error .timeout := terminal
  have stable := localExtension ctx expr proof pipeline fuel extra (RawCoherent.prepare state) ready
  simp only [RawU8Statement.run,RawU8Statement.localRun,stable]

theorem successor : ∀ (ctx : Solidity.Source.Ctx)
 (expr : Solidity.Source.RExpr ctx.env ctx.tys Solidity.Yul.LocalU8Expr.Ty)
 (proof : Solidity.Yul.LocalU8Expr.Supported ctx.env ctx.tys expr)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat)
 (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawU8Statement.run proof pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawU8Statement.run proof pipeline (fuel+1) state =
 Solidity.Yul.RawU8Statement.run proof pipeline fuel state := by
  intro ctx expr proof pipeline fuel state terminal
  exact extension ctx expr proof pipeline fuel 1 state terminal

theorem sourceExtension : ∀ (ctx : Solidity.Source.Ctx)
 (expr : Solidity.Source.RExpr ctx.env ctx.tys Solidity.Yul.LocalU8Expr.Ty)
 (proof : Solidity.Yul.LocalU8Expr.Supported ctx.env ctx.tys expr)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel extra nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawCoherent.coherent state = true →
 (Solidity.Yul.RawU8Statement.run proof glob.pipeline fuel state).1 ≠ .error .timeout →
 (Solidity.Source.execS glob frame (fuel+extra) nps ph
   (Solidity.Source.RStmt.expr (R:=returns) (M:=modifier) (k:=control) expr) state.clean).run
     (Solidity.Source.L0 ctx.env,state.world) =
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.expr (R:=returns) (M:=modifier) (k:=control) expr) state.clean).run
     (Solidity.Source.L0 ctx.env,state.world) := by
  intro ctx expr proof glob frame checked fuel extra nps ph returns modifier control state same terminal
  have first := (RawU8Statement.correct ctx expr proof glob frame checked fuel nps ph returns modifier control state same).2
  have later := (RawU8Statement.correct ctx expr proof glob frame checked (fuel+extra) nps ph returns modifier control state same).2
  rw [extension ctx expr proof glob.pipeline fuel extra state terminal] at later
  exact Option.some.inj (later.symm.trans first)


end Solidity.Yul.RawU8Horizon
