import Solidity.Correctness.Lowering.Total.Versions.CalleeBinding.Resolved
import Solidity.Correctness.Lowering.Total.Decode.Callee.Units

/-!
# Binding translated function entries to their elaborated bodies

The function index is relative to the original ordered model function list.
The unit builder preserves the supplied Source declaration prefix, and selection
skips exactly that prefix and the enclosing contract declaration. Successful
binding therefore identifies the translated model entry, rather than an
arbitrary declaration at an independently supplied absolute index.

The prefix is still supplied syntax. Complete model-contract reconstruction,
request/callee identity, alias resolution and execution agreement remain open.
-/
namespace Solidity.Correctness.Lowering.Total.Version.CalleeBinding

/-- Assemble the function list and bind one entry's actual Source body.
The whole unit must elaborate, and the selected declaration must have a frame
and complete elaborated body. Unsupported entries fail unit construction. -/
def fromFunctions (T : Decode.Tables) (R : CallSpellExt.Registry)
    (settings : Source.Settings) (scope : String)
    (leadingParts : Source.Syn (.list (.part false)))
    (fs : List (Name × FunDecl)) (index : Nat) : Option Output := do
  let u ← Decode.Callee.withFunctions T R scope leadingParts fs
  fromResolutionAt (Source.resolveUnit settings u)
    (1 + (leadingParts.collect (some scope)).length + index)

/-- The selected body belongs to the exact translation of the original function
entry at `index`, including its retained source identity. The existing resolution
binding certificate supplies its actual frame and complete body; this theorem
does not identify a model alias with that source identity or prove coverage. -/
theorem fromFunctions_bound {T : Decode.Tables} {R : CallSpellExt.Registry}
    {settings : Source.Settings} {scope : String}
    {leadingParts : Source.Syn (.list (.part false))}
    {fs : List (Name × FunDecl)} {index : Nat} {entry : Name × FunDecl} {s : Output}
    (h : fromFunctions T R settings scope leadingParts fs index = some s)
    (hi : fs[index]? = some entry) :
    ∃ u, Decode.Callee.withFunctions T R scope leadingParts fs = some u ∧
      s.source.res = Source.resolveUnit settings u ∧
      Decode.Callee.fromMetadata T R scope entry.2 = some s.declaration ∧
      s.declaration ∈ s.source.res.env.decls ∧
      fromResolution (Source.resolveUnit settings u) s.declaration = some s := by
  simp only [fromFunctions, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨u, hu, hs⟩ := h
  obtain ⟨hd, hm, hb⟩ := fromResolutionAt_member hs
  obtain ⟨_, hr, _⟩ := fromResolution_bound hb
  change u.decls[1 + (leadingParts.collect (some scope)).length + index]? =
    some s.declaration at hd
  have ht := congrArg (fun ds => ds[index]?) (Decode.Callee.withFunctions_tail hu)
  simp only [List.getElem?_map, List.getElem?_drop, hd, hi, Option.map_some] at ht
  exact ⟨u, hu, hr, (Option.some.inj ht).symm, hm, hb⟩

end Solidity.Correctness.Lowering.Total.Version.CalleeBinding
