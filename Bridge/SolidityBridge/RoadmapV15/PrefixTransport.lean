import Solidity.Roadmap.Contracts

/-!
Observation transport for the existing G01 resource-indexed prefixes.
These lemmas construct no execution and discharge no simulation premise.
-/
namespace SolidityBridge.RoadmapV15
open Solidity.Roadmap

def mapPrefix {E O E' O' : Type} (event : E → E') (outcome : O → O')
    (p : Prefix E O) : Prefix E' O' :=
  ⟨p.events.map event, p.final.map outcome⟩

theorem mapPrefix_le {E O E' O' : Type} (event : E → E') (outcome : O → O')
    {p q : Prefix E O} (h : p.Le q) :
    (mapPrefix event outcome p).Le (mapPrefix event outcome q) := by
  refine ⟨h.1.map event, ?_⟩
  rcases h.2 with hn | he
  · exact .inl (by simp only [mapPrefix, hn, Option.map_none])
  · exact .inr (congrArg (mapPrefix event outcome) he)

theorem mapPrefix_final_none {E O E' O' : Type} (event : E → E') (outcome : O → O')
    (p : Prefix E O) : (mapPrefix event outcome p).final = none ↔ p.final = none := by
  cases p with
  | mk events final =>
    cases final <;> simp only [mapPrefix, Option.map_none, Option.map_some,
      Option.some_ne_none]

theorem mapPrefix_consistent {R E O E' O' : Type} [LE R]
    (event : E → E') (outcome : O → O') (p : Prefixes R E O)
    (h : Prefixes.Consistent p) :
    Prefixes.Consistent (fun r => mapPrefix event outcome (p r)) :=
  fun r r' hr => mapPrefix_le event outcome (h r r' hr)

/-- The same admissible resource bounds have no completed outcome after
observation transport, even when the observation map is not injective. -/
theorem mapPrefix_diverges_iff {R E O E' O' : Type} (A : R → Prop)
    (event : E → E') (outcome : O → O') (p : Prefixes R E O) :
    Prefixes.Diverges A (fun r => mapPrefix event outcome (p r)) ↔
      Prefixes.Diverges A p := by
  constructor
  · intro h r hr
    exact (mapPrefix_final_none event outcome (p r)).mp (h r hr)
  · intro h r hr
    exact (mapPrefix_final_none event outcome (p r)).mpr (h r hr)

/-- A completed prefix remains completed with exactly its mapped outcome. -/
theorem mapPrefix_completes {R E O E' O' : Type}
    (event : E → E') (outcome : O → O') (p : Prefixes R E O) (o : O)
    (h : Prefixes.Completes p o) :
    Prefixes.Completes (fun r => mapPrefix event outcome (p r)) (outcome o) := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, by simp only [mapPrefix, hr, Option.map_some]⟩

end SolidityBridge.RoadmapV15
