import Solidity.Yul.RawCheckedAdapter
import Solidity.Yul.RawSourceForPost

/-! Omitted-condition transport for an existing checked Source for producer.
The runtime is retained verbatim; only the Source syntax index changes.
This requires a concrete literal-true producer and does not supply general
for admission or a producer for an arbitrary post expression. -/
namespace Solidity.Yul.RawCheckedAdapterAbsent

/-- Transport a real producer without changing runtime, frames or premises. -/
def adapter : ∀ {ctx : Solidity.Source.Ctx} {returns : List Solidity.Source.STy} {modifier u : Bool}
 {initial body : Solidity.Source.RStmt ctx.env returns modifier ⟨true,u⟩ ctx.tys ctx.tys}
 {post : Solidity.Source.ROptExpr ctx.env ctx.tys},
 Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u
   (.forLoop (l := true) initial (.some (.bool true)) post body) →
 Solidity.Yul.RawCheckedAdapter.Adapter ctx returns modifier u
   (.forLoop (l := true) initial .none post body) := by
  intro ctx returns modifier u initial body post producer
  exact {
    run := producer.run
    correct := fun glob frame checked fuel nps ph state same => by
      simpa only [RawSourceForPost.Absent.source_initialized] using
        producer.correct glob frame checked fuel nps ph state same
  }

end Solidity.Yul.RawCheckedAdapterAbsent
