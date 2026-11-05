import Solidity.Yul.RawCheckedControlIfElse

/-! Executable checked Source contracts indexed by existing intrinsic syntax.
The pipeline and checked-frame premise are explicit. Factories below provide
concrete proof fields from existing implementations; arbitrary syntax has no instance.
RawSourceAdapter.Adapter remains unchanged and supplies a stronger law without a checked-frame premise. -/
namespace Solidity.Yul.RawCheckedAdapter

structure Adapter (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy)
    (modifier u : Bool)
    (stmt : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys) where
  run : Solidity.Roadmap.Pipeline → Nat → RawFrame.State ctx →
    Solidity.Source.R RawLoopBody.Flow × RawFrame.State ctx
  correct : ∀ (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr),
    frame.checked = true →
    ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
    (state : RawFrame.State ctx), RawCoherent.coherent state = true →
      RawCoherent.coherent (run glob.pipeline fuel state).2 = true ∧
        (Solidity.Source.execS glob frame fuel nps ph stmt state.clean).run
          (Solidity.Source.L0 ctx.env,state.world) =
            RawLoopBody.represented (run glob.pipeline fuel state)

/-- Reuse an existing unconditional producer, ignoring the additional premise. -/
def fromAdapter {ctx returns modifier u stmt}
    (source : RawSourceAdapter.Adapter ctx returns modifier u stmt) :
    Adapter ctx returns modifier u stmt where
  run _pipeline := source.run
  correct glob frame _checked := source.correct glob frame

/-- A concrete mixed checked-word block, including break/continue propagation. -/
def block {ctx returns modifier u items}
    (proof : RawCheckedControlSequence.Supported ctx returns modifier u items) :
    Adapter ctx returns modifier u (.block items) where
  run := RawCheckedControlSequence.block proof
  correct glob frame checked fuel nps ph state same :=
    RawCheckedControlSequence.block_correct proof glob frame checked fuel nps ph state same

/-- Actual conditional producer over the supplied intrinsic mixed-block certificates. -/
def conditional {ctx returns modifier u condition yes no}
    (test : LocalBoolControl.Supported ctx.env ctx.tys condition)
    (one : RawCheckedControlSequence.Supported ctx returns modifier u yes)
    (two : RawCheckedControlSequence.Supported ctx returns modifier u no) :
    Adapter ctx returns modifier u (.ifElse condition (.block yes) (.block no)) where
  run := RawCheckedControlIfElse.run test one two
  correct := RawCheckedControlIfElse.correct ctx returns modifier u condition test yes no one two

end Solidity.Yul.RawCheckedAdapter
