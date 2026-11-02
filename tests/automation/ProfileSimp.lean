import Solidity.Frontend.Testing
set_option sol.spec.stepPrep false
set_option sol.benchmark true
set_option sol.benchmark.tactics true
/-! Native-only probe of the original whole-leaf simp passes. New tactic names
and the runtime marker ensure this actually replaces preparation: macro rules
cannot override existing tactic elaborators such as `sol_close_eval`. -/
open Solidity Lean Elab Tactic
private def profiledSimp (stx : Syntax) : TacticM Unit := withMainContext do
  let t0 ← IO.monoNanosNow
  let r@{ctx, simprocs, dischargeWrapper, ..} ← mkSimpContext stx (eraseLocal := false)
  let t1 ← IO.monoNanosNow
  try
    let _ ← dischargeWrapper.with fun discharge? =>
      withLoopChecking r do simpLocation ctx simprocs discharge? (expandOptLocation stx[5])
    pure ()
  finally
    let t2 ← IO.monoNanosNow
    IO.eprintln ("SIMP_PARTS " ++ (Lean.Json.mkObj [
      ("contextNanos", toJson (t1-t0)), ("runNanos", toJson (t2-t1))]).compress)
elab "profile_sol_close_eval" : tactic => do
  profiledSimp (← `(tactic| simp (config := { maxSteps := 400000 }) only [close_rw_s]))
elab "profile_sol_close_facts" : tactic => do
  profiledSimp (← `(tactic| simp (config := { contextual := true, maxSteps := 400000 }) only [close_rw_s]))
elab "profile_sol_close_reads" : tactic => do
  profiledSimp (← `(tactic| simp (config := { contextual := true, maxSteps := 400000 }) only [close_rw_s, close_rw_s_last]))
macro_rules
  | `(tactic| sol_spec_prep) => `(tactic|
  (sol_benchmark "parts-active" in skip
   sol_close_unwrap
   intro σ
   profile_sol_close_eval
   all_goals try profile_sol_close_facts
   all_goals try profile_sol_close_reads
   -- the states an update lands on (`CloseS.LandedAll`), opened to binders
   all_goals (try simp only [CloseS.landedAll_def])
   all_goals try (intros; sol_close_reads_all)
   all_goals try (subst_vars; sol_close_reads_all)
   all_goals (try intros)
   all_goals (try simp only [Close.exists_unit, Close.forall_unit, Close.exists_const_type,
      Close.forall_const_type] at *)
   -- a premise `Nonempty (Landed …)` where the rest no longer reads a landed
   -- state: every premise introduced, every conjunct its own goal
   all_goals (repeat' (first | intro _ | apply And.intro))))

solc_import "SimpPreparation.ast.json" hash 0xea285672c375200c as Profile.SimpPreparation testing
solc_scoped_problems Profile.SimpPreparation decl
#solkey_test Profile.SimpPreparation only "maximum" to ".lake/profile-simp-result.json"
