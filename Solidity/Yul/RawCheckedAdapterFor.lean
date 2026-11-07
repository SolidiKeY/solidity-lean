import Solidity.Yul.RawCheckedAdapterLoop
import Solidity.Yul.RawSourceAdapterFor

/-! Checked Source for composition with same-context initializer, present
condition and no post. Initializer control/error behavior and exact frames
follow existing Source evaluation; this is not general for admission. -/
namespace Solidity.Yul.RawCheckedAdapterFor

def run {ctx returns modifier u initial condition body}
    (initializer : RawCheckedAdapter.Adapter ctx returns modifier u initial)
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (inside : RawCheckedAdapter.Adapter ctx returns modifier u body)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R Unit × RawFrame.State ctx :=
  match fuel with
  | 0 => (.error .timeout,state)
  | n+1 =>
    let first := initializer.run pipeline n state
    match first.1 with
    | .error halt => (.error halt,first.2)
    | .ok flow => match flow with
      | .normal => RawCheckedAdapterLoop.run test inside pipeline n first.2
      | .break_ _ | .continue_ _ => (.error (.stuck "for initializer"),first.2)
      | .leave_ impossible => nomatch impossible

end Solidity.Yul.RawCheckedAdapterFor

namespace Solidity.Yul.RawCheckedAdapterFor
theorem correct : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier l u : Bool)
 (initial body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (initializer : Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u initial)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (inside : Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u body)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent
   (Solidity.Yul.RawCheckedAdapterFor.run initializer test inside glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.forLoop (l := l) initial (.some condition) .none body) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawSequence.represented
   (Solidity.Yul.RawCheckedAdapterFor.run initializer test inside glob.pipeline fuel state) := by
  intro ctx returns modifier l u initial body condition initializer test inside glob frame checked fuel nps ph state same
  cases fuel with
  | zero => exact ⟨same,rfl⟩
  | succ fuel =>
    have first := initializer.correct glob frame checked fuel nps ph state same
    have second := RawCheckedAdapterLoop.correct ctx returns modifier true u condition test body inside
      glob frame checked fuel nps ph (initializer.run glob.pipeline fuel state).2 first.1
    have iteration :
        (Solidity.Source.forIter glob frame fuel nps ph (.some condition) .none body
          (initializer.run glob.pipeline fuel state).2.clean).run
          (Solidity.Source.L0 ctx.env,(initializer.run glob.pipeline fuel state).2.world) =
        RawSequence.represented (RawCheckedAdapterLoop.run test inside glob.pipeline fuel
          (initializer.run glob.pipeline fuel state).2) := by
      simpa only [RawSourceForIter.source_while] using second.2
    have actual := RawSourceAdapterFor.source_step (l := l) condition glob frame fuel nps ph state
      (initializer.run glob.pipeline fuel state)
      (RawCheckedAdapterLoop.run test inside glob.pipeline fuel (initializer.run glob.pipeline fuel state).2)
      first.2 iteration
    cases tag : (initializer.run glob.pipeline fuel state).1 with
    | error halt =>
      simp only [run,tag] at actual ⊢
      exact ⟨first.1,actual⟩
    | ok flow =>
      cases flow with
      | normal =>
        simp only [run,tag] at actual ⊢
        exact ⟨second.1,actual⟩
      | break_ h | continue_ h =>
        simp only [run,tag] at actual ⊢
        exact ⟨first.1,actual⟩
      | leave_ h => cases h

theorem lift_correct : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (initial body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys)
 (condition : Solidity.Source.RExpr ctx.env ctx.tys .bool)
 (initializer : Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u initial)
 (test : Solidity.Yul.LocalBoolControl.Supported ctx.env ctx.tys condition)
 (inside : Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u body)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent
   (Solidity.Yul.RawCheckedAdapterFor.run initializer test inside glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.forLoop (l := true) initial (.some condition) .none body) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawLoopBody.represented
   ((Solidity.Yul.RawCheckedAdapterFor.run initializer test inside glob.pipeline fuel state).1.map
      (fun _ => (Solidity.Yul.Closed.Flow.normal : Solidity.Yul.RawLoopBody.Flow)),
    (Solidity.Yul.RawCheckedAdapterFor.run initializer test inside glob.pipeline fuel state).2) := by
  intro ctx returns modifier u initial body condition initializer test inside glob frame checked fuel nps ph state same
  rw [RawLoopBody.plain_represented]
  exact correct ctx returns modifier true u initial body condition initializer test inside glob frame checked fuel nps ph state same

def adapter {ctx returns modifier u initial condition body}
    (initializer : RawCheckedAdapter.Adapter ctx returns modifier u initial)
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (inside : RawCheckedAdapter.Adapter ctx returns modifier u body) :
    RawCheckedAdapter.Adapter ctx returns modifier u
      (Solidity.Source.RStmt.forLoop (l := true) initial (.some condition) .none body) where
  run pipeline fuel state :=
    let actual := run initializer test inside pipeline fuel state
    (actual.1.map (fun _ => .normal),actual.2)
  correct := lift_correct ctx returns modifier u initial body condition initializer test inside

end Solidity.Yul.RawCheckedAdapterFor
