import Solidity.Yul.RawCheckedAdapterAbsent
/-! Omitted-guard transport for actual checked producers with context-growing
initializers. Runtime, frames and premises remain unchanged. A concrete
literal-true producer is required; this is not general loop admission. -/
namespace Solidity.Yul.RawCheckedGrowingAbsent
theorem correct : ∀ (ctx : Solidity.Source.Ctx) (returns : List Solidity.Source.STy) (modifier u : Bool)
 (middle after : Solidity.Source.RCtx)
 (initial : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys middle)
 (body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ middle after)
 (post : Solidity.Source.ROptExpr ctx.env middle)
 (producer : Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u
   (.forLoop (l := true) initial (.some (.bool true)) post body))
 (glob : Solidity.Source.Glob ctx.env) (frame : Solidity.Source.Fr), frame.checked = true →
 ∀ (fuel nps : Nat) (ph : Option (Solidity.Source.Ph ctx.env))
 (state : Solidity.Yul.RawFrame.State ctx), Solidity.Yul.RawCoherent.coherent state = true →
 Solidity.Yul.RawCoherent.coherent (producer.run glob.pipeline fuel state).2 = true ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (.forLoop (l := true) initial .none post body) state.clean).run
   (Solidity.Source.L0 ctx.env,state.world) =
 Solidity.Yul.RawLoopBody.represented (producer.run glob.pipeline fuel state) := by
  intro ctx returns modifier u middle after initial body post producer glob frame checked fuel nps ph state same
  simpa only [RawSourceForPost.Absent.source_initialized] using
    producer.correct glob frame checked fuel nps ph state same

def adapter {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier u : Bool}
    {middle after : Solidity.Source.RCtx}
    {initial : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys middle}
    {body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ middle after}
    {post : Solidity.Source.ROptExpr ctx.env middle}
    (producer : RawCheckedAdapter.Adapter ctx returns modifier u
      (.forLoop (l := true) initial (.some (.bool true)) post body)) :
    RawCheckedAdapter.Adapter ctx returns modifier u
      (.forLoop (l := true) initial .none post body) where
  run := producer.run
  correct := correct ctx returns modifier u middle after initial body post producer
end Solidity.Yul.RawCheckedGrowingAbsent
