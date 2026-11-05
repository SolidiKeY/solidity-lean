import Solidity.Yul.RawCheckedControlSequence
import Solidity.Yul.RawLoopBodyHorizon
import Solidity.Yul.RawU8Horizon

/-! Concrete control-sequence/block horizons preserve exact flows and whole raw frames.
Only a normal head executes the tail; break/continue/error short-circuit unchanged. -/
namespace Solidity.Yul.RawCheckedControlSequenceHorizon

theorem successor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawCheckedControlSequence.Supported ctx returns modifier u items)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawCheckedControlSequence.run proof pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawCheckedControlSequence.run proof pipeline (fuel+1) state = Solidity.Yul.RawCheckedControlSequence.run proof pipeline fuel state := by
  intro ctx returns modifier u items proof pipeline
  induction proof with
  | nil =>
    intro fuel state terminal
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel => rfl
  | cons head tail ih =>
    intro fuel state terminal
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel =>
      have ready : (Solidity.Yul.RawLoopBody.run head fuel state).1 ≠ .error .timeout := by
        intro bad
        apply terminal
        rw [Solidity.Yul.RawCheckedControlSequence.run_cons]
        dsimp only
        rw [bad]
      have same := Solidity.Yul.RawLoopBodyHorizon.successor ctx returns modifier u _ head fuel state ready
      rw [Solidity.Yul.RawCheckedControlSequence.run_cons,Solidity.Yul.RawCheckedControlSequence.run_cons,same]
      cases actual : Solidity.Yul.RawLoopBody.run head fuel state with
      | mk result next =>
        cases result with
        | error halt => rfl
        | ok flow =>
          cases flow with
          | normal =>
            apply ih fuel next
            rw [Solidity.Yul.RawCheckedControlSequence.run_cons,actual] at terminal
            exact terminal
          | break_ h => rfl
          | continue_ h => rfl
          | leave_ impossible => cases impossible
  | uint8 head tail ih =>
    intro fuel state terminal
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel =>
      have ready : (RawU8Statement.run head pipeline fuel state).1 ≠ .error .timeout := by
        intro bad
        apply terminal
        rw [RawCheckedControlSequence.run_uint8]
        dsimp only
        rw [bad]
      have same := RawU8Horizon.successor ctx _ head pipeline fuel state ready
      rw [RawCheckedControlSequence.run_uint8,RawCheckedControlSequence.run_uint8,same]
      cases actual : RawU8Statement.run head pipeline fuel state with
      | mk result next =>
        cases result with
        | error halt => rfl
        | ok value =>
          apply ih fuel next
          rw [RawCheckedControlSequence.run_uint8,actual] at terminal
          exact terminal


theorem blockSuccessor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawCheckedControlSequence.Supported ctx returns modifier u items)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawCheckedControlSequence.block proof pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawCheckedControlSequence.block proof pipeline (fuel+1) state = Solidity.Yul.RawCheckedControlSequence.block proof pipeline fuel state := by
  intro ctx returns modifier u items proof pipeline fuel state terminal
  cases fuel with
  | zero => exact False.elim (terminal rfl)
  | succ fuel =>
    exact Solidity.Yul.RawCheckedControlSequenceHorizon.successor ctx returns modifier u items proof pipeline fuel state terminal

theorem extension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawCheckedControlSequence.Supported ctx returns modifier u items)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawCheckedControlSequence.run proof pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawCheckedControlSequence.run proof pipeline (fuel+extra) state = Solidity.Yul.RawCheckedControlSequence.run proof pipeline fuel state := by
  intro ctx returns modifier u items proof pipeline fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : (Solidity.Yul.RawCheckedControlSequence.run proof pipeline (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (Solidity.Yul.RawCheckedControlSequenceHorizon.successor ctx returns modifier u items proof pipeline (fuel+extra) state ready).trans ih

theorem blockExtension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier u : Bool)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawCheckedControlSequence.Supported ctx returns modifier u items)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawCheckedControlSequence.block proof pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawCheckedControlSequence.block proof pipeline (fuel+extra) state = Solidity.Yul.RawCheckedControlSequence.block proof pipeline fuel state := by
  intro ctx returns modifier u items proof pipeline fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : (Solidity.Yul.RawCheckedControlSequence.block proof pipeline (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (Solidity.Yul.RawCheckedControlSequenceHorizon.blockSuccessor ctx returns modifier u items proof pipeline (fuel+extra) state ready).trans ih

theorem sourceItemsExtension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawCheckedControlSequence.Supported ctx returns modifier u items)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel extra nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 (Solidity.Yul.RawCheckedControlSequence.run proof glob.pipeline fuel state).1 ≠ .error .timeout →
 (Solidity.Source.execItems glob frame (fuel+extra) nps ph items state.clean).run (Solidity.Source.L0 ctx.env,state.world) =
 (Solidity.Source.execItems glob frame fuel nps ph items state.clean).run (Solidity.Source.L0 ctx.env,state.world) := by
  intro ctx returns modifier u items proof glob frame checked fuel extra nps ph state same terminal
  have first := RawCheckedControlSequence.correct ctx returns modifier u items proof glob frame checked fuel nps ph state same
  have later := RawCheckedControlSequence.correct ctx returns modifier u items proof glob frame checked (fuel+extra) nps ph state same
  rw [extension ctx returns modifier u items proof glob.pipeline fuel extra state terminal] at later
  exact later.2.trans first.2.symm

theorem sourceBlockExtension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (items : Solidity.Source.RItems ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawCheckedControlSequence.Supported ctx returns modifier u items)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel extra nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 (Solidity.Yul.RawCheckedControlSequence.block proof glob.pipeline fuel state).1 ≠ .error .timeout →
 (Solidity.Source.execS glob frame (fuel+extra) nps ph (Solidity.Source.RStmt.block items) state.clean).run (Solidity.Source.L0 ctx.env,state.world) =
 (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.block items) state.clean).run (Solidity.Source.L0 ctx.env,state.world) := by
  intro ctx returns modifier u items proof glob frame checked fuel extra nps ph state same terminal
  have first := RawCheckedControlSequence.block_correct proof glob frame checked fuel nps ph state same
  have later := RawCheckedControlSequence.block_correct proof glob frame checked (fuel+extra) nps ph state same
  rw [blockExtension ctx returns modifier u items proof glob.pipeline fuel extra state terminal] at later
  exact later.2.trans first.2.symm

end Solidity.Yul.RawCheckedControlSequenceHorizon
