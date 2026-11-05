import Solidity.Yul.RawU8For
import Solidity.Yul.RawCheckedGrowingAbsent

/-! Concrete uint8-initialized loops with neither guard nor post. The existing
literal-true no-post producer and Source omission transport are composed;
actual body certificates and checked/coherent Source premises remain explicit. -/
namespace Solidity.Yul.RawU8ForAbsent
def run {ctx returns modifier u name initializer body}
    (initial : LocalU8Expr.Supported ctx.env ctx.tys initializer)
    (inside : RawCheckedAdapter.Adapter (ctx.push name LocalU8Expr.Ty) returns modifier u body)
    (pipeline : Solidity.Roadmap.Pipeline) (fuel : Nat) (state : RawFrame.State ctx) :
    Solidity.Source.R Unit × RawFrame.State ctx :=
  RawU8For.run initial (LocalBoolControl.Supported.base (.literal true)) inside pipeline fuel state

def adapter (ctx : Solidity.Source.Ctx) (name : String)
    (returns : List Solidity.Source.STy) (modifier u : Bool)
    (initializer : Solidity.Source.RExpr ctx.env ctx.tys LocalU8Expr.Ty)
    (initial : LocalU8Expr.Supported ctx.env ctx.tys initializer)
    (body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩
      (ctx.push name LocalU8Expr.Ty).tys (ctx.push name LocalU8Expr.Ty).tys)
    (inside : RawCheckedAdapter.Adapter (ctx.push name LocalU8Expr.Ty) returns modifier u body) :
    RawCheckedAdapter.Adapter ctx returns modifier u
      (.forLoop (l := true) (.declInit (τ := LocalU8Expr.Ty) initializer (by rfl)) .none .none body) :=
  RawCheckedGrowingAbsent.adapter
    (RawU8For.adapter ctx name returns modifier u initializer initial (.bool true) body
      (LocalBoolControl.Supported.base (.literal true)) inside)
end Solidity.Yul.RawU8ForAbsent

namespace Solidity.Yul.RawU8ForAbsent
theorem correct : ∀ (ctx : Solidity.Source.Ctx) (name : String)
 (returns : List Solidity.Source.STy) (modifier u : Bool)
 (initializer : Solidity.Source.RExpr ctx.env ctx.tys Solidity.Yul.LocalU8Expr.Ty)
 (initial : Solidity.Yul.LocalU8Expr.Supported ctx.env ctx.tys initializer)
 (body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩
   (ctx.push name Solidity.Yul.LocalU8Expr.Ty).tys (ctx.push name Solidity.Yul.LocalU8Expr.Ty).tys)
 (inside : Solidity.Yul.RawCheckedAdapter.Adapter (ctx.push name Solidity.Yul.LocalU8Expr.Ty) returns modifier u body)
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent
   (Solidity.Yul.RawU8ForAbsent.run initial inside glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (.forLoop (l := true)
     (.declInit (τ := Solidity.Yul.LocalU8Expr.Ty) initializer (by rfl)) .none .none body)
   state.clean).run (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawSequence.represented
   (Solidity.Yul.RawU8ForAbsent.run initial inside glob.pipeline fuel state) := by
  intro ctx name returns modifier u initializer initial body inside glob frame checked fuel nps ph state same
  have actual := (adapter ctx name returns modifier u initializer initial body inside).correct
    glob frame checked fuel nps ph state same
  have runner : (adapter ctx name returns modifier u initializer initial body inside).run
      glob.pipeline fuel state =
      ((run initial inside glob.pipeline fuel state).1.map
        (fun _ => (Closed.Flow.normal : RawLoopBody.Flow)),
       (run initial inside glob.pipeline fuel state).2) := rfl
  rw [runner] at actual
  simpa only [RawLoopBody.plain_represented] using actual
end Solidity.Yul.RawU8ForAbsent
