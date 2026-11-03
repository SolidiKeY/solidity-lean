import Solidity.Lowering.Readonly.PrimitiveCallable
import Solidity.Source.SemanticsExamples

/-! Inhabited source-call composition clients for both existing pipelines.
These discharge actual body execution/return extraction, not compiler or native
execution premises. Failure keeps its dirty source state until frame rollback. -/
namespace Solidity.Lowering.Readonly.CallableControls
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Roadmap (Pipeline)
open PrimitiveValues PrimitiveInitialization

def global (pipeline : Pipeline) : Glob EB := { GB answerOnly with pipeline := pipeline }
def dG : Decl := ⟨.function, "g", some "C", false, fn "g" .nil pUint⟩
def dPoke : Decl := ⟨.function, "poke", some "C", false, fn "poke" .nil .nil⟩
def initialReturns : Locals EB.layout [uint] := (defaults EB.layout [.uint]).onto (L0 EB)
def returned : Locals EB.layout [uint] := .cons (.int 12 (by decide)) .nil
def outputs : RVals EB.layout [uint] := .cons (.val (.int 12 (by decide))) .nil

def bodyFinal (pipeline : Pipeline) : St EB :=
  ((runMods (global pipeline) FC 20 gBody gBody.mods initialReturns).run (L0 EB, sB)).2.2

theorem body_execution (pipeline : Pipeline) :
    (runMods (global pipeline) FC 20 gBody gBody.mods initialReturns).run (L0 EB, sB) =
      (.ok returned, (L0 EB, bodyFinal pipeline)) := by cases pipeline <;> rfl

/-- Actual source call success through the composition theorem, with the
primitive return initialization premise discharged by production code. -/
theorem call_success (pipeline : Pipeline) :
    (callInternal (global pipeline) FC 21 dG (Vals.nil : Vals EB.layout []) [uint]).run (L0 EB, sB) =
      (.ok (mkRet [uint] outputs), (L0 EB, bodyFinal pipeline)) := by
  apply PrimitiveCallable.complete (global pipeline) FC 19 dG .nil [.uint] gBody
    (by rfl) rfl returned outputs sB (bodyFinal pipeline)
  · exact body_execution pipeline
  · rfl

theorem success_writes (pipeline : Pipeline) :
    readX (bodyFinal pipeline) = some 5 ∧ readT (bodyFinal pipeline) = some 7 := by
  cases pipeline <;> exact ⟨rfl, rfl⟩

def failureFinal (pipeline : Pipeline) : St EB :=
  ((runMods (global pipeline) FC 20 pokeBody pokeBody.mods (L0 EB)).run (L0 EB, sB)).2.2

theorem body_revert (pipeline : Pipeline) :
    (runMods (global pipeline) FC 20 pokeBody pokeBody.mods (L0 EB)).run (L0 EB, sB) =
      (.error (.revert []), (L0 EB, failureFinal pipeline)) := by cases pipeline <;> rfl

theorem call_revert (pipeline : Pipeline) :
    (callInternal (global pipeline) FC 21 dPoke (Vals.nil : Vals EB.layout []) []).run (L0 EB, sB) =
      (.error (.revert []), (L0 EB, failureFinal pipeline)) := by
  apply PrimitiveCallable.body_failure (global pipeline) FC 19 dPoke .nil [] pokeBody
    (by rfl) rfl sB (failureFinal pipeline) (.revert [])
  exact body_revert pipeline

/-- callInternal does not invent the enclosing rollback: that remains the
actual enterInstance/parent frame's job. -/
theorem revert_keeps_dirty_until_frame (pipeline : Pipeline) :
    readX (failureFinal pipeline) = some 1 ∧ readT (failureFinal pipeline) = some 2 := by
  cases pipeline <;> exact ⟨rfl, rfl⟩

theorem wrong_call_frame (pipeline : Pipeline) :
    (callInternal (global pipeline) FC 21 dG (Vals.nil : Vals EB.layout []) []).run (L0 EB, sB) =
      (.error (.stuck "call frame"), (L0 EB, sB)) := by
  apply PrimitiveCallable.wrong_frame (global pipeline) FC 19 dG .nil [] gBody (by rfl) _ sB
  simp only [gBody, List.reverseAux]
  intro impossible
  cases impossible

end Solidity.Lowering.Readonly.CallableControls
