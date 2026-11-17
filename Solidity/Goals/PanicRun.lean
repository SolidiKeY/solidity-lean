import Solidity.Tools.Goal
import Solidity.Semantics.Panic.Run.Contracts

/-!
# The outcome contract of the panic-carrying runner (plan w3x-panic-outcomes)

A component of finish-line goal 5 (`runCarriesPanicCodes`): what the actual
runner `Panic.Run.program` / `Panic.Run.stmt` returns, for every contract,
context, state and program. No conjunct restricts the admitted programs.

This component is already proved: every conjunct is a theorem of
`Run/Contracts.lean`, `Run/Loop.lean`, `Run/Calls.lean` or `Eval.lean`, and
`run_outcomes` below assembles them by name, so the two cannot drift apart.

Not claimed: whole-program erasure of this runner to the V1 run. It is false:
self-catch binds the executed callee's code (1 for a false assertion) where
V1 binds the oracle's (e.g. 17). Only the local projections of expressions,
paths, sources and arguments are stated (`erase`, the last conjuncts).
-/

namespace Solidity.Goals

open Solidity.Semantics.Panic Solidity.Semantics.Panic.Run

@[goal Solidity.Correctness.Panic.run_outcomes "w3x-panic-outcomes"]
def panicRunOutcomes : Prop :=
  -- Sequencing and blocks: any halt stops the rest; a success continues.
  (∀ {C : Contract} {Γ Δ Ξ : Ctx} (s : Stmt C Γ Δ) (tail : Prog C Δ Ξ) (σ : State C Γ)
      (halt : Halt Raised), stmt s σ = .error halt →
    program (.cons s tail) σ = .error halt) ∧
  (∀ {C : Contract} {Γ Δ Ξ : Ctx} (s : Stmt C Γ Δ) (tail : Prog C Δ Ξ) (σ : State C Γ)
      (o : Out C σ.H Δ), stmt s σ = .ok o →
    program (.cons s tail) σ = (program tail o.st).map (fun o' => ⟨o'.st, o.ext.trans o'.ext⟩)) ∧
  (∀ {C : Contract} {Γ Δ : Ctx} (body : Prog C Γ Δ) (σ : State C Γ) (halt : Halt Raised),
    program body σ = .error halt → stmt (.block body) σ = .error halt) ∧
  -- Loops: condition and body halts propagate; the runner's loop is the engine
  -- `Loop.run`, whose result is the finite `iterN` outcome, or else `diverge`.
  (∀ {C : Contract} {Γ Δ : Ctx} (ann : LoopAnn C Γ) (c : Val C Γ .bool) (body : Prog C Γ Δ)
      (σ : State C Γ) (halt : Halt Raised), value σ c = .error halt →
    stmt (.loop ann c body) σ = .error halt) ∧
  (∀ {C : Contract} {Γ Δ : Ctx} (ann : LoopAnn C Γ) (c : Val C Γ .bool) (body : Prog C Γ Δ)
      (σ : State C Γ) (halt : Halt Raised), value σ c = .ok true →
    program body σ = .error halt → stmt (.loop ann c body) σ = .error halt) ∧
  (∀ {C : Contract} {Γ Δ : Ctx} (ann : LoopAnn C Γ) (c : Val C Γ .bool) (body : Prog C Γ Δ)
      (σ : State C Γ),
    stmt (.loop ann c body) σ = Loop.run
      (fun o : Out C σ.H Γ =>
        (program body o.st).map fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩)
      (fun o => value o.st c) ⟨σ, List.prefix_refl _⟩) ∧
  (∀ {α : Type} (body : α → EvalResult α) (c : α → EvalResult Bool) (n : Nat) (σ : α)
      (r : EvalResult α), Loop.iterN body c n σ = .inr r → Loop.run body c σ = r) ∧
  (∀ {α : Type} (body : α → EvalResult α) (c : α → EvalResult Bool) (σ : α),
    (¬ ∃ r n, Loop.iterN body c n σ = .inr r) → Loop.run body c σ = .error .diverge) ∧
  -- Internal calls, `callRec` included: the callee's halt is the call's halt.
  (∀ {C : Contract} {Γ Δ Ξ ps rs : Ctx} (name : Name) (as : Args C Γ ps) (ret : CallRet Γ rs Δ)
      (body : Prog C (rs ++ ps) Ξ) (σ : State C Γ) (a : TEnv C σ.H ps) (halt : Halt Raised),
    args σ as = .ok a → program body (ret.enterT (σ.withEnv a)).st = .error halt →
    stmt (.call name as ret body) σ = .error halt) ∧
  (∀ {C : Contract} {Γ Δ ps rs : Ctx} (name : Name) (depth : Nat) (as : Args C Γ ps)
      (ret : CallRet Γ rs Δ) (body : Unit → Prog C (rs ++ ps) (rs ++ ps)) (σ : State C Γ)
      (a : TEnv C σ.H ps) (halt : Halt Raised),
    args σ as = .ok a → program (body ()) (ret.enterT (σ.withEnv a)).st = .error halt →
    stmt (.callRec name depth as ret body) σ = .error halt) ∧
  -- Self-catch: the executed callee's intrinsic code reaches the panic handler
  -- as `codeWord code`, no oracle consulted; exhaustion and divergence escape.
  (∀ {C : Contract} {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} (ext : ExtCall C Γ) (rets : Binders ρ)
      (ok : Prog C (ρ ++ Γ) Γ₁) (err : Prog C Γ Γ₂) (binder : CodeBinder κ)
      (pnc : Prog C (κ ++ Γ) Γ₃) (other : Prog C Γ Γ₄) (as : Args C Γ ps)
      (body : Prog C (ρ ++ ps) Γf) (σ : State C Γ) (code : Code) (origin : Raised),
    (ext.addr.evalT σ).1 ≠ 0 → (ext.addr.evalT σ).1 = σ.tx.selfAddress.1 →
    call as (.rets rets.toRet) body.ext (program body) σ = .error (.intrinsic code origin) →
    stmt (.tryCall ext rets ok err binder pnc other as body true) σ =
      (program pnc (σ.withEnv
        (TEnv.append κ (binder.decodeT (H := σ.H) (codeWord code)) σ.env))).map
        (fun o => ⟨o.st.drop ((Ext.append Γ κ).trans pnc.ext), o.ext⟩)) ∧
  (∀ {C : Contract} {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} (ext : ExtCall C Γ) (rets : Binders ρ)
      (ok : Prog C (ρ ++ Γ) Γ₁) (err : Prog C Γ Γ₂) (binder : CodeBinder κ)
      (pnc : Prog C (κ ++ Γ) Γ₃) (other : Prog C Γ Γ₄) (as : Args C Γ ps)
      (body : Prog C (ρ ++ ps) Γf) (σ : State C Γ) (halt : Halt Raised),
    halt = .exhausted ∨ halt = .diverge →
    (ext.addr.evalT σ).1 ≠ 0 → (ext.addr.evalT σ).1 = σ.tx.selfAddress.1 →
    call as (.rets rets.toRet) body.ext (program body) σ = .error halt →
    stmt (.tryCall ext rets ok err binder pnc other as body true) σ = .error halt) ∧
  -- A false assertion halts with code `assert` and its producer witness.
  (∀ {C : Contract} {Γ : Ctx} (c : Val C Γ .bool) (σ : State C Γ), value σ c = .ok false →
    stmt (.assert c) σ = .error (.intrinsic .assert
      (Raised.ofOrigin (.assertion false) .assertion rfl))) ∧
  -- Failures while building revert data or catch data propagate unchanged.
  (∀ {C : Contract} {Γ : Ctx} (parts : List (RevPart C Γ)) (σ : State C Γ) (halt : Halt Raised),
    parts.mapM (revPart σ) = .error halt → stmt (.revertData parts) σ = .error halt) ∧
  (∀ {C : Contract} {Γ ρ ps Γf Γ₁ : Ctx} (ext : ExtCall C Γ) (rets : Binders ρ)
      (as : Args C Γ ps) (callee : Prog C (ρ ++ ps) Γf) (self : Bool) (kind : CatchKind)
      (x : Var) (handler : Prog C (.mem bytesR :: Γ) Γ₁) (σ : State C Γ) (halt : Halt Raised),
    catchBytes ext rets as callee.ext (program callee) self σ = .error halt →
    stmt (.catchData ext rets as callee self kind x handler) σ = .error halt) ∧
  -- The sound local V1 projections: one evaluation, its failure read as `revert`.
  (∀ {C : Contract} {Γ : Ctx} (σ : State C Γ) {p : PrimTy} (v : Val C Γ p),
    erase (value σ v) = v.evalT σ) ∧
  (∀ {C : Contract} {Γ : Ctx} (σ : State C Γ) {T : Ty} (b : SPath C Γ T),
    erase (path σ b) = b.resolveT σ) ∧
  (∀ {C : Contract} {Γ : Ctx} (σ : State C Γ) {T : Ty} (l : Loc C Γ T),
    erase (loc σ l) = l.resolveT σ) ∧
  (∀ {C : Contract} {Γ : Ctx} (σ : State C Γ) {T : Ty} (b : MPath C Γ T),
    erase (mpath σ b) = b.mvalT σ) ∧
  (∀ {C : Contract} {Γ : Ctx} (σ : State C Γ) {T : Ty} (l : MLoc C Γ T),
    erase (mloc σ l) = l.addrT σ) ∧
  (∀ {C : Contract} {Γ : Ctx} (σ : State C Γ) {T : Ty} (src : Src C Γ T),
    erase (source σ src) = src.valueT σ) ∧
  (∀ {C : Contract} {Γ : Ctx} (σ : State C Γ) {T : Ty} (src : MSrc C Γ T),
    erase (msource σ src) = src.mvalT σ) ∧
  (∀ {C : Contract} {Γ : Ctx} (σ : State C Γ) {ps : Ctx} (as : Args C Γ ps),
    erase (args σ as) = as.evalT σ)

end Solidity.Goals

namespace Solidity.Correctness.Panic

open Solidity.Semantics.Panic Solidity.Semantics.Panic.Run

theorem run_outcomes : Solidity.Goals.panicRunOutcomes :=
  ⟨program_cons_error, program_cons_ok, stmt_block_error,
   fun _ _ _ _ halt h => Loop.run_condition_error _ _ _ halt h, stmt_loop_error,
   fun _ _ _ _ => rfl, fun _ _ _ _ _ h => Loop.run_of_iterN h, fun _ _ _ h => Loop.run_diverge h,
   stmt_call_error, stmt_callRec_error, stmt_tryCall_self_panic,
   fun ext rets ok err binder pnc other as body σ halt r nz self f =>
     stmt_tryCall_self_resource ext rets ok err binder pnc other as body σ halt r nz self f,
   stmt_assert_false, revertData_error,
   fun ext rets as callee self kind _ handler σ halt f =>
     catchData_error ext rets as callee self kind handler σ halt f,
   value_erase, path_erase, loc_erase, mpath_erase, mloc_erase, source_erase, msource_erase,
   args_erase⟩

end Solidity.Correctness.Panic
