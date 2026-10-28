import Solidity.Frontend.Import
import Solidity.Semantics.RevertMemory

/-!
# Unsigned-power panic bytes in ordinary self-call frames

Completed finite kernel executions are transported to the unbounded run.
These concrete certificates do not assert general source/compiler equivalence.
Compiler/EVM controls: `scripts/check-self-power-data.mjs`.
-/

solc_import "../../../tests/solc/SelfPowerData.legacy.ast.json" hash 0x7a70c1359061adec
  as Imported.Legacy.SelfPowerData testing
solc_import "../../../tests/solc/SelfPowerData.viaIR.ast.json" hash 0xbb1ca579b2c9db53
  as Imported.IR.SelfPowerData testing

namespace Solidity.Examples.Tactics.SelfPowerData

namespace Legacy
abbrev C : Contract := Imported.Legacy.SelfPowerData
private def initial : State C [] := { State.init C with tx := { selfAddress := ⟨7, rfl⟩ } }

private noncomputable def cutoffP := Imported.Legacy.SelfPowerData.cutoff
/-- `cutoff()` completes; divergence and resource exhaustion cannot satisfy this conclusion. -/
theorem cutoff_returns : (Prog.run initial cutoffP).toOption.isSome = true :=
  (cutoffP.runF_approx 1000 initial).returned (by decide +kernel)

private noncomputable def multiplyP := Imported.Legacy.SelfPowerData.multiply
/-- `multiply()` completes; divergence and resource exhaustion cannot satisfy this conclusion. -/
theorem multiply_returns : (Prog.run initial multiplyP).toOption.isSome = true :=
  (multiplyP.runF_approx 1000 initial).returned (by decide +kernel)

private noncomputable def declarationP := Imported.Legacy.SelfPowerData.declaration
/-- `declaration()` completes; divergence and resource exhaustion cannot satisfy this conclusion. -/
theorem declaration_returns : (Prog.run initial declarationP).toOption.isSome = true :=
  (declarationP.runF_approx 1000 initial).returned (by decide +kernel)

private noncomputable def nestedCodeP := Imported.Legacy.SelfPowerData.nestedCode
/-- `nestedCode()` completes; divergence and resource exhaustion cannot satisfy this conclusion. -/
theorem nestedCode_returns : (Prog.run initial nestedCodeP).toOption.isSome = true :=
  (nestedCodeP.runF_approx 1000 initial).returned (by
    rw [Prog.runF_eq]
    decide +kernel)

private noncomputable def internalCodeP := Imported.Legacy.SelfPowerData.internalCode
/-- `internalCode()` completes; divergence and resource exhaustion cannot satisfy this conclusion. -/
theorem internalCode_returns : (Prog.run initial internalCodeP).toOption.isSome = true :=
  (internalCodeP.runF_approx 1000 initial).returned (by decide +kernel)

private noncomputable def narrowCodeP := Imported.Legacy.SelfPowerData.narrowCode
/-- `narrowCode()` completes; divergence and resource exhaustion cannot satisfy this conclusion. -/
theorem narrowCode_returns : (Prog.run initial narrowCodeP).toOption.isSome = true :=
  (narrowCodeP.runF_approx 1000 initial).returned (by decide +kernel)

private noncomputable def fitP := Imported.Legacy.SelfPowerData.fit
/-- `fit()` completes; divergence and resource exhaustion cannot satisfy this conclusion. -/
theorem fit_returns : (Prog.run initial fitP).toOption.isSome = true :=
  (fitP.runF_approx 1000 initial).returned (by decide +kernel)

private noncomputable def shortcutsP := Imported.Legacy.SelfPowerData.shortcuts
/-- `shortcuts()` completes; divergence and resource exhaustion cannot satisfy this conclusion. -/
theorem shortcuts_returns : (Prog.run initial shortcutsP).toOption.isSome = true :=
  (shortcutsP.runF_approx 1000 initial).returned (by decide +kernel)

private noncomputable def uncheckedCodeP := Imported.Legacy.SelfPowerData.uncheckedCode
/-- `uncheckedCode()` completes; divergence and resource exhaustion cannot satisfy this conclusion. -/
theorem uncheckedCode_returns : (Prog.run initial uncheckedCodeP).toOption.isSome = true :=
  (uncheckedCodeP.runF_approx 1000 initial).returned (by decide +kernel)

private noncomputable def rawDataP := Imported.Legacy.SelfPowerData.rawData
/-- `rawData()` completes; divergence and resource exhaustion cannot satisfy this conclusion. -/
theorem rawData_returns : (Prog.run initial rawDataP).toOption.isSome = true :=
  (rawDataP.runF_approx 1000 initial).returned (by decide +kernel)

private def priorityP : Prog C [] [] := sol[C]{ priority(18); }
/-- `priority(18)` completes; divergence and resource exhaustion cannot satisfy this conclusion. -/
theorem priority_returns : (Prog.run initial priorityP).toOption.isSome = true :=
  (priorityP.runF_approx 1000 initial).returned (by decide +kernel)

private noncomputable def wrongCodeP := Imported.Legacy.SelfPowerData.wrongCode
/-- Incorrect panic expectations remain failing assertions. -/
theorem wrongCode_panics : (Prog.run initial wrongCodeP).halt? = some .panic :=
  Prog.run_halt_of_runF wrongCodeP initial 1000 (by decide) (by decide +kernel)

private noncomputable def wrongRawP := Imported.Legacy.SelfPowerData.wrongRaw
/-- Incorrect panic expectations remain failing assertions. -/
theorem wrongRaw_panics : (Prog.run initial wrongRawP).halt? = some .panic :=
  Prog.run_halt_of_runF wrongRawP initial 1000 (by decide) (by decide +kernel)

/-- Every imported body, including negative controls, is admitted. -/
example : Imported.Legacy.SelfPowerData.report.all (·.status == .elaborated) = true := by decide +kernel
private noncomputable def shortcutFailuresP := Imported.Legacy.SelfPowerData.shortcutFailures
/-- Zero/one and exponent-zero shortcuts still evaluate failing operands. -/
theorem shortcutFailures_returns : (Prog.run initial shortcutFailuresP).toOption.isSome = true :=
  (shortcutFailuresP.runF_approx 1000 initial).returned (by decide +kernel)
private def priorityWrongP : Prog C [] [] := sol[C]{ priority(1); }
/-- The opposite pipeline priority cannot satisfy the catch assertion. -/
theorem priorityWrong_panics : (Prog.run initial priorityWrongP).halt? = some .panic :=
  Prog.run_halt_of_runF priorityWrongP initial 1000 (by decide) (by decide +kernel)
private def nestedPriorityP : Prog C [] [] := sol[C]{ nestedPriorityCode(17); }
/-- Earlier operand failures precede inserted later-power guards in pipeline order. -/
theorem nestedPriority_returns : (Prog.run initial nestedPriorityP).toOption.isSome = true :=
  (nestedPriorityP.runF_approx 1000 initial).returned (by decide +kernel)
#print axioms cutoff_returns
#print axioms multiply_returns
#print axioms declaration_returns
#print axioms nestedCode_returns
#print axioms internalCode_returns
#print axioms narrowCode_returns
#print axioms fit_returns
#print axioms shortcuts_returns
#print axioms uncheckedCode_returns
#print axioms rawData_returns
#print axioms priority_returns
#print axioms wrongCode_panics
#print axioms wrongRaw_panics
#print axioms shortcutFailures_returns
#print axioms priorityWrong_panics
#print axioms nestedPriority_returns
private noncomputable def andCodeP := Imported.Legacy.SelfPowerData.andCode
/-- Selected guards run; untaken arms and earlier bounds failures keep their order. -/
theorem andCode_returns : (Prog.run initial andCodeP).toOption.isSome = true :=
  (andCodeP.runF_approx 1000 initial).returned (by decide +kernel)
#print axioms andCode_returns
private noncomputable def orCodeP := Imported.Legacy.SelfPowerData.orCode
/-- Selected guards run; untaken arms and earlier bounds failures keep their order. -/
theorem orCode_returns : (Prog.run initial orCodeP).toOption.isSome = true :=
  (orCodeP.runF_approx 1000 initial).returned (by decide +kernel)
#print axioms orCode_returns
private noncomputable def ternaryCodeP := Imported.Legacy.SelfPowerData.ternaryCode
/-- Selected guards run; untaken arms and earlier bounds failures keep their order. -/
theorem ternaryCode_returns : (Prog.run initial ternaryCodeP).toOption.isSome = true :=
  (ternaryCodeP.runF_approx 1000 initial).returned (by decide +kernel)
#print axioms ternaryCode_returns
private noncomputable def indexCodeP := Imported.Legacy.SelfPowerData.indexCode
/-- Selected guards run; untaken arms and earlier bounds failures keep their order. -/
theorem indexCode_returns : (Prog.run initial indexCodeP).toOption.isSome = true :=
  (indexCodeP.runF_approx 1000 initial).returned (by decide +kernel)
#print axioms indexCode_returns
end Legacy

namespace IR
abbrev C : Contract := Imported.IR.SelfPowerData
private def initial : State C [] := { State.init C with tx := { selfAddress := ⟨7, rfl⟩ } }

private noncomputable def cutoffP := Imported.IR.SelfPowerData.cutoff
/-- `cutoff()` completes; divergence and resource exhaustion cannot satisfy this conclusion. -/
theorem cutoff_returns : (Prog.run initial cutoffP).toOption.isSome = true :=
  (cutoffP.runF_approx 1000 initial).returned (by decide +kernel)

private noncomputable def multiplyP := Imported.IR.SelfPowerData.multiply
/-- `multiply()` completes; divergence and resource exhaustion cannot satisfy this conclusion. -/
theorem multiply_returns : (Prog.run initial multiplyP).toOption.isSome = true :=
  (multiplyP.runF_approx 1000 initial).returned (by decide +kernel)

private noncomputable def declarationP := Imported.IR.SelfPowerData.declaration
/-- `declaration()` completes; divergence and resource exhaustion cannot satisfy this conclusion. -/
theorem declaration_returns : (Prog.run initial declarationP).toOption.isSome = true :=
  (declarationP.runF_approx 1000 initial).returned (by decide +kernel)

private noncomputable def nestedCodeP := Imported.IR.SelfPowerData.nestedCode
/-- `nestedCode()` completes; divergence and resource exhaustion cannot satisfy this conclusion. -/
theorem nestedCode_returns : (Prog.run initial nestedCodeP).toOption.isSome = true :=
  (nestedCodeP.runF_approx 1000 initial).returned (by
    rw [Prog.runF_eq]
    decide +kernel)

private noncomputable def internalCodeP := Imported.IR.SelfPowerData.internalCode
/-- `internalCode()` completes; divergence and resource exhaustion cannot satisfy this conclusion. -/
theorem internalCode_returns : (Prog.run initial internalCodeP).toOption.isSome = true :=
  (internalCodeP.runF_approx 1000 initial).returned (by decide +kernel)

private noncomputable def narrowCodeP := Imported.IR.SelfPowerData.narrowCode
/-- `narrowCode()` completes; divergence and resource exhaustion cannot satisfy this conclusion. -/
theorem narrowCode_returns : (Prog.run initial narrowCodeP).toOption.isSome = true :=
  (narrowCodeP.runF_approx 1000 initial).returned (by decide +kernel)

private noncomputable def fitP := Imported.IR.SelfPowerData.fit
/-- `fit()` completes; divergence and resource exhaustion cannot satisfy this conclusion. -/
theorem fit_returns : (Prog.run initial fitP).toOption.isSome = true :=
  (fitP.runF_approx 1000 initial).returned (by decide +kernel)

private noncomputable def shortcutsP := Imported.IR.SelfPowerData.shortcuts
/-- `shortcuts()` completes; divergence and resource exhaustion cannot satisfy this conclusion. -/
theorem shortcuts_returns : (Prog.run initial shortcutsP).toOption.isSome = true :=
  (shortcutsP.runF_approx 1000 initial).returned (by decide +kernel)

private noncomputable def uncheckedCodeP := Imported.IR.SelfPowerData.uncheckedCode
/-- `uncheckedCode()` completes; divergence and resource exhaustion cannot satisfy this conclusion. -/
theorem uncheckedCode_returns : (Prog.run initial uncheckedCodeP).toOption.isSome = true :=
  (uncheckedCodeP.runF_approx 1000 initial).returned (by decide +kernel)

private noncomputable def rawDataP := Imported.IR.SelfPowerData.rawData
/-- `rawData()` completes; divergence and resource exhaustion cannot satisfy this conclusion. -/
theorem rawData_returns : (Prog.run initial rawDataP).toOption.isSome = true :=
  (rawDataP.runF_approx 1000 initial).returned (by decide +kernel)

private def priorityP : Prog C [] [] := sol[C]{ priority(1); }
/-- `priority(1)` completes; divergence and resource exhaustion cannot satisfy this conclusion. -/
theorem priority_returns : (Prog.run initial priorityP).toOption.isSome = true :=
  (priorityP.runF_approx 1000 initial).returned (by decide +kernel)

private noncomputable def wrongCodeP := Imported.IR.SelfPowerData.wrongCode
/-- Incorrect panic expectations remain failing assertions. -/
theorem wrongCode_panics : (Prog.run initial wrongCodeP).halt? = some .panic :=
  Prog.run_halt_of_runF wrongCodeP initial 1000 (by decide) (by decide +kernel)

private noncomputable def wrongRawP := Imported.IR.SelfPowerData.wrongRaw
/-- Incorrect panic expectations remain failing assertions. -/
theorem wrongRaw_panics : (Prog.run initial wrongRawP).halt? = some .panic :=
  Prog.run_halt_of_runF wrongRawP initial 1000 (by decide) (by decide +kernel)

/-- Every imported body, including negative controls, is admitted. -/
example : Imported.IR.SelfPowerData.report.all (·.status == .elaborated) = true := by decide +kernel
private noncomputable def shortcutFailuresP := Imported.IR.SelfPowerData.shortcutFailures
/-- Zero/one and exponent-zero shortcuts still evaluate failing operands. -/
theorem shortcutFailures_returns : (Prog.run initial shortcutFailuresP).toOption.isSome = true :=
  (shortcutFailuresP.runF_approx 1000 initial).returned (by decide +kernel)
private def priorityWrongP : Prog C [] [] := sol[C]{ priority(18); }
/-- The opposite pipeline priority cannot satisfy the catch assertion. -/
theorem priorityWrong_panics : (Prog.run initial priorityWrongP).halt? = some .panic :=
  Prog.run_halt_of_runF priorityWrongP initial 1000 (by decide) (by decide +kernel)
private def nestedPriorityP : Prog C [] [] := sol[C]{ nestedPriorityCode(18); }
/-- Earlier operand failures precede inserted later-power guards in pipeline order. -/
theorem nestedPriority_returns : (Prog.run initial nestedPriorityP).toOption.isSome = true :=
  (nestedPriorityP.runF_approx 1000 initial).returned (by decide +kernel)
#print axioms cutoff_returns
#print axioms multiply_returns
#print axioms declaration_returns
#print axioms nestedCode_returns
#print axioms internalCode_returns
#print axioms narrowCode_returns
#print axioms fit_returns
#print axioms shortcuts_returns
#print axioms uncheckedCode_returns
#print axioms rawData_returns
#print axioms priority_returns
#print axioms wrongCode_panics
#print axioms wrongRaw_panics
#print axioms shortcutFailures_returns
#print axioms priorityWrong_panics
#print axioms nestedPriority_returns
private noncomputable def andCodeP := Imported.IR.SelfPowerData.andCode
/-- Selected guards run; untaken arms and earlier bounds failures keep their order. -/
theorem andCode_returns : (Prog.run initial andCodeP).toOption.isSome = true :=
  (andCodeP.runF_approx 1000 initial).returned (by decide +kernel)
#print axioms andCode_returns
private noncomputable def orCodeP := Imported.IR.SelfPowerData.orCode
/-- Selected guards run; untaken arms and earlier bounds failures keep their order. -/
theorem orCode_returns : (Prog.run initial orCodeP).toOption.isSome = true :=
  (orCodeP.runF_approx 1000 initial).returned (by decide +kernel)
#print axioms orCode_returns
private noncomputable def ternaryCodeP := Imported.IR.SelfPowerData.ternaryCode
/-- Selected guards run; untaken arms and earlier bounds failures keep their order. -/
theorem ternaryCode_returns : (Prog.run initial ternaryCodeP).toOption.isSome = true :=
  (ternaryCodeP.runF_approx 1000 initial).returned (by decide +kernel)
#print axioms ternaryCode_returns
private noncomputable def indexCodeP := Imported.IR.SelfPowerData.indexCode
/-- Selected guards run; untaken arms and earlier bounds failures keep their order. -/
theorem indexCode_returns : (Prog.run initial indexCodeP).toOption.isSome = true :=
  (indexCodeP.runF_approx 1000 initial).returned (by decide +kernel)
#print axioms indexCode_returns
end IR

end Solidity.Examples.Tactics.SelfPowerData
