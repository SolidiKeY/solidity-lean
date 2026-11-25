import Solidity.Correctness.Lowering.Total.Decode.Callee.Metadata

/-!
# Ordered assembly of ordinary function declarations

Every original function entry is translated, in order, using its retained
source metadata. Model aliases label the input entries; they do not replace
source names. A failed entry fails the whole list. This is a component for unit
construction, not full contract reconstruction or universal callee coverage.
-/
namespace Solidity.Correctness.Lowering.Total.Decode.Callee

/-- Extract an ordinary contract function's syntax without a dependent cast. -/
def ordinaryNode (d : Source.Decl) : Option (Source.Syn (.part false)) :=
  match d.kind, d.top, d.node with
  | .function, false, node => some node
  | _, _, _ => none

/-- Assemble every function entry. Unsupported declarations are never filtered. -/
def functionParts (T : Tables) (R : CallSpellExt.Registry) (scope : String) :
    List (Name × FunDecl) → Option (Source.Syn (.list (.part false)))
  | [] => some .nil
  | (_, f) :: fs => do
      let d ← fromMetadata T R scope f
      let node ← ordinaryNode d
      pure (.cons node (← functionParts T R scope fs))

private theorem node_collect {T : Tables} {R : CallSpellExt.Registry} {scope : String}
    {f : FunDecl} {d : Source.Decl} {node : Source.Syn (.part false)}
    (hd : fromMetadata T R scope f = some d) (hn : ordinaryNode d = some node) :
    node.collect (some scope) = [d] := by
  obtain ⟨source, vis, _, _, hf, _⟩ := fromMetadata_header hd
  obtain ⟨_, _, _, _, _, _, _, _, he, _⟩ :=
    functionDecl_faithful T R scope source.name (some vis)
      (sourceMutability source.mutability) f d hf { decls := [] }
  subst d
  simp only [ordinaryNode, Option.some.injEq] at hn
  subst node
  rw [Source.Syn.collect]
  rfl

/-- Exact ordered correspondence of the real Source declaration table with
translation of every original entry. The equality preserves all positions and
forbids silently dropping failed entries; it is not execution faithfulness. -/
theorem functionParts_faithful (T : Tables) (R : CallSpellExt.Registry) (scope : String) :
    ∀ fs parts, functionParts T R scope fs = some parts →
      (parts.collect (some scope)).map some =
        fs.map (fun f => fromMetadata T R scope f.2) := by
  intro fs
  induction fs with
  | nil =>
      intro parts h
      cases h
      rfl
  | cons f fs ih =>
      intro parts h
      simp only [functionParts, Option.bind_eq_bind, Option.pure_def,
        Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨d, hd, node, hn, rest, hr, rfl⟩ := h
      rw [Source.Syn.collect, node_collect hd hn]
      simp only [List.singleton_append, List.map_cons, hd, ih rest hr]

/-- The collected declaration count equals the number of original entries. -/
theorem functionParts_length {T : Tables} {R : CallSpellExt.Registry} {scope : String}
    {fs : List (Name × FunDecl)} {parts : Source.Syn (.list (.part false))}
    (h : functionParts T R scope fs = some parts) :
    (parts.collect (some scope)).length = fs.length := by
  have hl := congrArg List.length (functionParts_faithful T R scope fs parts h)
  simpa only [List.length_map] using hl

end Solidity.Correctness.Lowering.Total.Decode.Callee
