import Solidity.Yul.RawCheckedSequence
import Solidity.Yul.RawStatementHorizon
import Solidity.Yul.RawU8Horizon

/-! Exact mixed-sequence/block stability after non-timeout completion.
Pipeline and original frame stay fixed. Actual Source transport retains
checked-frame and coherence premises; timeout prefixes remain observable. -/

namespace Solidity.Yul.RawCheckedSequenceHorizon
theorem successor : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx)
 (items : Solidity.Source.RItems ctx.env returns modifier control ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawCheckedSequence.Supported ctx returns modifier control items)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawCheckedSequence.run proof pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawCheckedSequence.run proof pipeline (fuel+1) state =
 Solidity.Yul.RawCheckedSequence.run proof pipeline fuel state := by
  intro ctx returns modifier control items proof pipeline fuel state terminal
  induction proof generalizing pipeline fuel state with
  | nil =>
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel => rfl
  | @boolean stmt rest head tail ih =>
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel =>
      cases first : RawCoherent.execS head fuel state with
      | mk result next =>
        cases result with
        | error halt =>
          have ready : (RawCoherent.execS head fuel state).1 ≠ .error .timeout := by
            simpa only [RawCheckedSequence.run_boolean,first] using terminal
          have stable := RawStatementHorizon.coherentSuccessor ctx returns modifier control stmt head fuel state ready
          simp only [RawCheckedSequence.run_boolean,stable,first]
        | ok value =>
          have ready : (RawCoherent.execS head fuel state).1 ≠ .error .timeout := by
            rw [first]
            intro bad
            cases bad
          have stable := RawStatementHorizon.coherentSuccessor ctx returns modifier control stmt head fuel state ready
          have tailReady : (RawCheckedSequence.run tail pipeline fuel next).1 ≠ .error .timeout := by
            simpa only [RawCheckedSequence.run_boolean,first] using terminal
          have tailStable := ih pipeline fuel next tailReady
          simp only [RawCheckedSequence.run_boolean,stable,first,tailStable]
  | @uint8 expr rest head tail ih =>
    cases fuel with
    | zero => exact False.elim (terminal rfl)
    | succ fuel =>
      cases first : RawU8Statement.run head pipeline fuel state with
      | mk result next =>
        cases result with
        | error halt =>
          have ready : (RawU8Statement.run head pipeline fuel state).1 ≠ .error .timeout := by
            simpa only [RawCheckedSequence.run_uint8,first] using terminal
          have stable := RawU8Horizon.successor ctx expr head pipeline fuel state ready
          simp only [RawCheckedSequence.run_uint8,stable,first]
        | ok value =>
          have ready : (RawU8Statement.run head pipeline fuel state).1 ≠ .error .timeout := by
            rw [first]
            intro bad
            cases bad
          have stable := RawU8Horizon.successor ctx expr head pipeline fuel state ready
          have tailReady : (RawCheckedSequence.run tail pipeline fuel next).1 ≠ .error .timeout := by
            simpa only [RawCheckedSequence.run_uint8,first] using terminal
          have tailStable := ih pipeline fuel next tailReady
          simp only [RawCheckedSequence.run_uint8,stable,first,tailStable]

theorem extension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx)
 (items : Solidity.Source.RItems ctx.env returns modifier control ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawCheckedSequence.Supported ctx returns modifier control items)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawCheckedSequence.run proof pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawCheckedSequence.run proof pipeline (fuel+extra) state =
 Solidity.Yul.RawCheckedSequence.run proof pipeline fuel state := by
  intro ctx returns modifier control items proof pipeline fuel extra state terminal
  induction extra with
  | zero => rfl
  | succ extra ih =>
    have ready : (RawCheckedSequence.run proof pipeline (fuel+extra) state).1 ≠ .error .timeout := by
      rw [ih]
      exact terminal
    exact (successor ctx returns modifier control items proof pipeline (fuel+extra) state ready).trans ih

theorem blockExtension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx)
 (items : Solidity.Source.RItems ctx.env returns modifier control ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawCheckedSequence.Supported ctx returns modifier control items)
 (pipeline : Solidity.Roadmap.Pipeline) (fuel extra : Nat) (state : Solidity.Yul.RawFrame.State ctx),
 (Solidity.Yul.RawCheckedSequence.block proof pipeline fuel state).1 ≠ .error .timeout →
 Solidity.Yul.RawCheckedSequence.block proof pipeline (fuel+extra) state =
 Solidity.Yul.RawCheckedSequence.block proof pipeline fuel state := by
  intro ctx returns modifier control items proof pipeline fuel extra state terminal
  cases fuel with
  | zero => exact False.elim (terminal rfl)
  | succ fuel =>
    have ready : (RawCheckedSequence.run proof pipeline fuel state).1 ≠ .error .timeout := terminal
    have stable := extension ctx returns modifier control items proof pipeline fuel extra state ready
    simp only [Nat.succ_add,RawCheckedSequence.block,stable]

theorem sourceItemsExtension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx)
 (items : Solidity.Source.RItems ctx.env returns modifier control ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawCheckedSequence.Supported ctx returns modifier control items)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel extra nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 (Solidity.Yul.RawCheckedSequence.run proof glob.pipeline fuel state).1 ≠ .error .timeout →
 (Solidity.Source.execItems glob frame (fuel+extra) nps ph items state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 (Solidity.Source.execItems glob frame fuel nps ph items state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) := by
  intro ctx returns modifier control items proof glob frame checked fuel extra nps ph state same terminal
  have first := RawCheckedSequence.correct ctx returns modifier control items proof glob frame checked fuel nps ph state same
  have later := RawCheckedSequence.correct ctx returns modifier control items proof glob frame checked (fuel+extra) nps ph state same
  rw [extension ctx returns modifier control items proof glob.pipeline fuel extra state terminal] at later
  exact later.2.trans first.2.symm

theorem sourceBlockExtension : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
 (modifier : Bool) (control : Solidity.Source.SCtx)
 (items : Solidity.Source.RItems ctx.env returns modifier control ctx.tys ctx.tys)
 (proof : Solidity.Yul.RawCheckedSequence.Supported ctx returns modifier control items)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel extra nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 (Solidity.Yul.RawCheckedSequence.block proof glob.pipeline fuel state).1 ≠ .error .timeout →
 (Solidity.Source.execS glob frame (fuel+extra) nps ph (Solidity.Source.RStmt.block items) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.block items) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) := by
  intro ctx returns modifier control items proof glob frame checked fuel extra nps ph state same terminal
  have first := RawCheckedSequence.block_correct ctx returns modifier control items proof glob frame checked fuel nps ph state same
  have later := RawCheckedSequence.block_correct ctx returns modifier control items proof glob frame checked (fuel+extra) nps ph state same
  rw [blockExtension ctx returns modifier control items proof glob.pipeline fuel extra state terminal] at later
  exact later.2.trans first.2.symm


end Solidity.Yul.RawCheckedSequenceHorizon
