import SolidityBridge.ExternalEvm.Assembly.Termination
import SolidityBridge.ExternalEvm.Assembly.PureFetched
import SolidityBridge.ExternalEvm.Assembly.LinkedChecks

namespace Solidity.Evm.External.Assembly.TerminationChecks
open EvmYul EvmYul.EVM

def program := LinkedChecks.loopProgram

def layout : ExitLayout program :=
  (checkExit program).get (by decide +kernel)

theorem extracted {α ε : Type} (result : Except ε α) (h : result.toOption.isSome) :
    result = .ok (result.toOption.get h) := by
  cases result with
  | error e => cases h
  | ok value => rfl

def reference := StackLoop.initial [.ofNat 1, .ofNat 2, .ofNat 0, .ofNat 9]
def sourceInput := {Machine.init with stack := [w[1], w[2], w[0], w[9]]}
def sourceOutput := {Machine.init with stack := [w[9]]}

def fetched : EVM.State := (fetchedSteps 21 reference).toOption.get (by decide +kernel)
theorem fetchedRun : fetchedSteps 21 reference = .ok fetched := extracted _ _
def charged : EVM.State :=
  (driverSteps 21 24 program.validJumps LinkedChecks.input).toOption.get (by decide +kernel)
theorem chargedRun : driverSteps 21 24 program.validJumps LinkedChecks.input = .ok charged := extracted _ _
def gates : TerminalGates program.validJumps charged :=
  (checkTerminalGates program.validJumps charged).get (by decide +kernel)

-- Keep checked endpoints abstract during elaboration. Their equations above
-- remain kernel checked; no state is repeatedly normalized through 21 steps.
attribute [irreducible] fetched charged

theorem fetchedBoundary : Boundary program.checked.image program.frame StackLoop.code.length sourceOutput fetched := by
  have observed : (fetchedSteps 21 reference).toOption.map (fun t => (t.pc.toNat, words t.stack)) =
      some (72, [w[9]]) := by decide +kernel
  rw [fetchedRun] at observed
  change some (fetched.pc.toNat, words fetched.stack) = some (72, [w[9]]) at observed
  have result : (fetched.pc.toNat, words fetched.stack) = (72, [w[9]]) := Option.some.inj observed
  have pure : PureFetched 21 reference :=
    ((checkPureFetched 21 reference).get (by decide +kernel)).down
  have frame := pure.frame fetchedRun
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩
  · have ha : address StackLoop.code 0 ⟨1, by decide⟩ = some 72 := rfl
    have pc : fetched.pc.toNat = 72 := congrArg (fun p : Nat × List Word => p.1) result
    exact ha.trans (congrArg (fun n : Nat => some n) pc).symm
  · exact (congrArg (fun p : Nat × List Word => p.2) result).symm
  · calc fetched.toState = reference.toState := frame.1
         _ = program.frame.toState := rfl
  · calc fetched.memory = reference.memory := frame.2
         _ = program.frame.memory := rfl

theorem sourceRun : run StackLoop.code sourceInput = .ok sourceOutput 0 := by
  have h : (Instr.loop [] []).step sourceInput = .ok sourceOutput 0 := loopRun_of_iterN (n := 3) rfl
  change ((Instr.loop [] []).step _).bind _ = _
  rw [h]
  rfl

theorem entry : Boundary program.checked.image program.frame 0 sourceInput reference := by
  exact ⟨by decide, rfl, rfl, rfl, rfl⟩

/-- This inhabited compiler-facing instance derives the count existential
from the automatic recursive certificate and actual source run. -/
example := program.success_simulation layout sourceInput sourceOutput reference entry sourceRun

/-- Actual success is obtained through the shared generic proof path and
executable prefix/terminal certificates, not by evaluating X. -/
theorem compiledSuccess : ∃ out,
    X 24 program.validJumps LinkedChecks.input = .ok (.success out .empty) ∧
      SuccessBoundary layout sourceOutput out := by
  obtain ⟨terminal, counted, boundary, finish⟩ := layout.success_of_fetched 21 0 sourceOutput
    reference fetched LinkedChecks.input fetchedRun fetchedBoundary rfl LinkedChecks.ready
  have he : terminal = charged := Except.ok.inj (counted.symm.trans chargedRun)
  subst terminal
  exact finish gates

#guard (checkTerminalGates program.validJumps {charged with gasAvailable := .ofNat 0}).isNone
#guard (checkReady 21 22 program.validJumps LinkedChecks.input).isSome
#guard (checkReady 21 21 program.validJumps LinkedChecks.input).isNone
-- Prefix readiness alone does not manufacture the two missing terminal steps.
#guard (match X 22 program.validJumps LinkedChecks.input with | .error .OutOfFuel => true | _ => false)

end Solidity.Evm.External.Assembly.TerminationChecks
