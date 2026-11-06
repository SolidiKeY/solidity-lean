import Solidity.Frontend.Testing

/-! Diagnostic only: repeated native compilation of the exact selected typed
formula versus one command-local retained declaration. No search result is cached,
no observations are removed, and this probe does not replace the aggregate gate.
The fixture hash pins its compiler/source/settings provenance. -/
namespace Solidity.Tests.GetterEvaluationSharing
open Lean Elab Command Meta Solidity Solidity.Frontend

solc_import "../solc/PublicGetters.ast.json" hash 0x968ad03a36798cc3 as PublicGetters testing
solc_scoped_problems PublicGetters decl

private def probe (row : Lean.Name) : TermElabM Unit := do
  let C := mkConst ``PublicGetters
  let formula ← Symex.evaluable (mkConst row)
  if formula.hasMVar || formula.hasFVar || formula.hasLooseBVars then
    throwError "probe requires this exact closed imported formula"
  let value := mkAppN (mkConst ``Fml.callsBack) #[C, toExpr false, ctxE [], formula]
  let before ← getEnv
  let t0 ← IO.monoMsNow
  let first ← unsafe evalExpr Bool (mkConst ``Bool) value
  let t1 ← IO.monoMsNow
  let second ← unsafe evalExpr Bool (mkConst ``Bool) value
  let t2 ← IO.monoMsNow
  -- evalExpr compiles a fresh temporary declaration under withoutModifyingEnv.
  -- Check the declaration count; evalExprCore uses withoutModifyingEnv,
  -- so the temporary native helper is not retained for reuse.
  unless (← getEnv).constants.toList.length == before.constants.toList.length do
    throwError "temporary evaluation unexpectedly retained declarations"
  let helper ← mkFreshUserName (row ++ `nativeProbe)
  addAndCompile <| .defnDecl {
    name := helper, levelParams := [], type := mkConst ``Bool,
    value, hints := .opaque, safety := .safe }
  let t3 ← IO.monoMsNow
  let retainedFirst ← unsafe evalConst Bool helper
  let t4 ← IO.monoMsNow
  let retainedSecond ← unsafe evalConst Bool helper
  let t5 ← IO.monoMsNow
  unless first == second && first == retainedFirst && first == retainedSecond do
    throwError "same exact input changed its native observation"
  -- Kernel-check the retained definition against the exact original expression.
  let certificate ← mkFreshUserName (row ++ `nativeProbeEq)
  addDecl <| .thmDecl {
    name := certificate, levelParams := [],
    type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) (mkConst helper) value,
    value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) value }
  let axioms ← collectAxioms certificate
  unless axioms.all (standardAxioms.contains ·) do
    throwError "sharing equality uses nonstandard axioms"
  logInfo m!"sharing probe {row}: callbacks={first}; fresh evalExpr ms={t1-t0},{t2-t1}; retained setup ms={t3-t2}; evalConst ms={t4-t3},{t5-t4}; equality axioms={axioms}"

run_elab probe ``PublicGetters.primitives.problem
run_elab probe ``PublicGetters.arrays.problem
end Solidity.Tests.GetterEvaluationSharing
