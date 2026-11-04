import Solidity.Yul.RawCoherent
import Solidity.Yul.LocalBoolHorizon

/-! Completed concrete raw expression-statement horizons preserve the entire frame.
No coherence, projection or abstract adapter-stability premise is required. -/
namespace Solidity.Yul.RawStatementHorizon

theorem discardSuccessor : ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx)
 (expr : Solidity.Source.RExpr env types .bool)
 (proof : Solidity.Yul.LocalBoolControl.Supported env types expr)
 (fuel : Nat) (state : Solidity.Yul.LocalState env types),
 (Solidity.Yul.LocalExprStatement.discard (Solidity.Yul.LocalBoolControl.eval proof) fuel state).1 ≠ .error .timeout →
 Solidity.Yul.LocalExprStatement.discard (Solidity.Yul.LocalBoolControl.eval proof) (fuel+1) state =
 Solidity.Yul.LocalExprStatement.discard (Solidity.Yul.LocalBoolControl.eval proof) fuel state := by
  intro env types expr proof fuel state terminal
  cases fuel with
  | zero => exact False.elim (terminal rfl)
  | succ fuel =>
    have ready : (Solidity.Yul.LocalBoolControl.eval proof fuel state).1 ≠ .error .timeout := by
      intro bad
      apply terminal
      simp only [Solidity.Yul.LocalExprStatement.discard,bad,Except.map]
    have same := Solidity.Yul.LocalBoolHorizon.successor env types expr proof fuel state ready
    rw [Solidity.Yul.LocalExprStatement.discard_step,Solidity.Yul.LocalExprStatement.discard_step,same]

theorem rawSuccessor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier control ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawSource.Supported ctx returns modifier control stmt)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSource.execS proof fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawSource.execS proof (fuel+1) state = Solidity.Yul.RawSource.execS proof fuel state := by
  intro ctx returns modifier control stmt proof fuel state terminal
  cases proof with
  | expression body =>
    have ready : (Solidity.Yul.LocalExprStatement.discard
        (Solidity.Yul.LocalBoolControl.eval body) fuel (Solidity.Yul.RawSource.localState state)).1 ≠ .error .timeout := terminal
    have same := Solidity.Yul.RawStatementHorizon.discardSuccessor ctx.env ctx.tys _ body fuel
      (Solidity.Yul.RawSource.localState state) ready
    simp only [Solidity.Yul.RawSource.execS,Solidity.Yul.RawSource.localRun]
    rw [same]

theorem coherentSuccessor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier control ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawSource.Supported ctx returns modifier control stmt)
 (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawCoherent.execS proof fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawCoherent.execS proof (fuel+1) state = Solidity.Yul.RawCoherent.execS proof fuel state := by
  intro ctx returns modifier control stmt proof fuel state terminal
  cases proof with
  | expression body =>
    have ready : (Solidity.Yul.LocalExprStatement.discard
        (Solidity.Yul.LocalBoolControl.eval body) fuel (Solidity.Yul.RawCoherent.prepare state)).1 ≠ .error .timeout := terminal
    have same := Solidity.Yul.RawStatementHorizon.discardSuccessor ctx.env ctx.tys _ body fuel
      (Solidity.Yul.RawCoherent.prepare state) ready
    simp only [Solidity.Yul.RawCoherent.execS,Solidity.Yul.RawCoherent.localRun]
    rw [same]

theorem rawExtension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier control ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawSource.Supported ctx returns modifier control stmt)
 (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawSource.execS proof fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawSource.execS proof (fuel+extra) state = Solidity.Yul.RawSource.execS proof fuel state := by
  intro ctx returns modifier control stmt proof fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : (Solidity.Yul.RawSource.execS proof (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (Solidity.Yul.RawStatementHorizon.rawSuccessor ctx returns modifier control stmt proof (fuel+extra) state ready).trans ih

theorem coherentExtension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx)
 (stmt : Solidity.Source.RStmt ctx.env returns modifier control ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawSource.Supported ctx returns modifier control stmt)
 (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawCoherent.execS proof fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawCoherent.execS proof (fuel+extra) state = Solidity.Yul.RawCoherent.execS proof fuel state := by
  intro ctx returns modifier control stmt proof fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : (Solidity.Yul.RawCoherent.execS proof (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (Solidity.Yul.RawStatementHorizon.coherentSuccessor ctx returns modifier control stmt proof (fuel+extra) state ready).trans ih

end Solidity.Yul.RawStatementHorizon
