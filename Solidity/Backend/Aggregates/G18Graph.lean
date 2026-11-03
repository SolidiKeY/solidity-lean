import Solidity.Lowering.V07.DeclarationGraph
import Solidity.Backend.Aggregates.G18Storage

/-! Actual V07 declaration-graph consumer. Ordered shape correspondence yields
actual source field typing, not value/heap/storage execution preservation. -/
namespace Solidity.Backend.Aggregates
open Lowering.V07

/-- Lookup at the SAME index preserves the name and the complete graph-type
relation. No inverse/injectivity claim for collapsed primitive descriptors. -/
theorem fields_lookup {D : Source.Layout} {n : Nat} {names : Fin n → Source.DeclName}
    {xs : List (String × Source.STy)} {ys : List (Name × TypeGraph.Ty n)}
    (h : GraphFieldsRel D names xs ys) (i : Nat) (t : Name × TypeGraph.Ty n)
    (ht : ys[i]? = some t) :
    ∃ s, xs[i]? = some s ∧ s.1 = t.1 ∧ GraphTypeRel D names s.2 t.2 := by
  induction h generalizing i with
  | nil => simp only [List.getElem?_nil] at ht; cases ht
  | @cons s u ss us hn hu hrest ih =>
    cases i with
    | zero =>
      have he : u = t := Option.some.inj ht
      subst t
      exact ⟨s, rfl, hn, hu⟩
    | succ i =>
      obtain ⟨z, hz, hname, htype⟩ := ih i ht
      exact ⟨z, hz, hname, htype⟩

/-- Consume the published certificate rather than a separately supplied desired
field correspondence. Location remains explicit, including memory versus storage. -/
theorem graph_field_type {E : Source.Env} {loc : Source.DataLoc} {n : Nat}
    {G : TypeGraph.Schema n} (c : DeclarationGraph E loc G) (node : Fin n)
    (i : Nat) (field : Name) (T : TypeGraph.Ty n)
    (ht : (G.fields node)[i]? = some (field, T)) :
    ∃ τ, E.fieldTy? (c.sourceName node) loc i = some τ ∧
      (c.sourceFields node)[i]? = some (field, τ) ∧
      GraphTypeRel E.layout c.sourceName τ T := by
  obtain ⟨⟨name, τ⟩, hs, hn, hr⟩ := fields_lookup (c.fields_relate node) i (field, T) ht
  change name = field at hn
  subst name
  refine ⟨τ, ?_, hs, hr⟩
  simp only [Source.Env.fieldTy?, c.fields_resolve, Option.bind_some, hs, Option.map_some]

/-- Actual storage path typing after selecting the certified struct field.
The starting path's admission remains explicit: a struct graph is not a
state-variable/root certificate. No storage read/write simulation is assumed. -/
theorem graph_storage_path {E : Source.Env} {n : Nat} {G : TypeGraph.Schema n}
    (c : DeclarationGraph E .storage G) (node : Fin n) (p : Source.SPath)
    (hp : E.pathTy p = some (.struct .storage (c.sourceName node)))
    (i : Nat) (field : Name) (T : TypeGraph.Ty n)
    (ht : (G.fields node)[i]? = some (field, T)) :
    ∃ τ, E.pathTy {p with steps := p.steps ++ [.field i]} = some τ ∧
      GraphTypeRel E.layout c.sourceName τ T := by
  obtain ⟨τ, hτ, _, hr⟩ := graph_field_type c node i field T ht
  exact ⟨τ, (struct_path E p .storage (c.sourceName node) hp i).trans hτ, hr⟩

/-- The actual MEMORY-layout list selects the corresponding source type.
There is deliberately no storage-certificate substitution for memory_layout. -/
theorem graph_memory_field {E : Source.Env} {n : Nat} {G : TypeGraph.Schema n}
    (c : DeclarationGraph E .memory G) (node : Fin n) (i : Nat)
    (field : Name) (T : TypeGraph.Ty n) (ht : (G.fields node)[i]? = some (field, T)) :
    ∃ τ, (E.layout.fields (c.sourceName node))[i]? = some τ ∧
      GraphTypeRel E.layout c.sourceName τ T := by
  obtain ⟨τ, _, hs, hr⟩ := graph_field_type c node i field T ht
  refine ⟨τ, ?_, hr⟩
  rw [c.memory_layout]
  simp only [List.getElem?_map, hs, Option.map_some]

#print axioms fields_lookup
#print axioms graph_field_type
#print axioms graph_storage_path
#print axioms graph_memory_field
end Solidity.Backend.Aggregates
