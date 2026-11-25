import Solidity.Correctness.Lowering.Total.Decode.Callee.Declarations

/-!
# Contract units with an explicit declaration prefix and translated functions

The prefix is supplied Source syntax, not a guessed translation of the model's
state, modifiers or other metadata. It is preserved exactly before all function
entries. This compositional unit builder does not establish complete model
contract reconstruction, source-name consistency or execution agreement.
-/
namespace Solidity.Correctness.Lowering.Total.Decode.Callee

/-- Concatenate contract parts without rebuilding or filtering either side. -/
def appendParts : Source.Syn (.list (.part false)) →
    Source.Syn (.list (.part false)) → Source.Syn (.list (.part false))
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (appendParts xs ys)

private theorem collect_appendParts (scope : Option String) :
    ∀ (xs ys : Source.Syn (.list (.part false))),
      (appendParts xs ys).collect scope = xs.collect scope ++ ys.collect scope
  | .nil, _ => by simp only [appendParts, Source.Syn.collect, List.nil_append]
  | .cons x xs, ys => by
      simp only [appendParts, Source.Syn.collect, collect_appendParts scope xs ys, List.append_assoc]

/-- Preserve the supplied prefix and assemble all original function entries in
one contract unit. An unsupported function fails the entire construction. -/
def withFunctions (T : Tables) (R : CallSpellExt.Registry) (scope : String)
    (leadingParts : Source.Syn (.list (.part false))) (fs : List (Name × FunDecl)) :
    Option (Source.Syn .unit) := do
  let functions ← functionParts T R scope fs
  pure (.unit (.cons (.contract false scope .none .nil (appendParts leadingParts functions)) .nil))

/-- Successful construction retains the exact prefix and the full translated
function list. The collected table consists of the contract declaration,
followed by the prefix declarations, followed by the function declarations. -/
theorem withFunctions_declarations {T : Tables} {R : CallSpellExt.Registry}
    {scope : String} {leadingParts : Source.Syn (.list (.part false))}
    {fs : List (Name × FunDecl)} {u : Source.Syn .unit}
    (h : withFunctions T R scope leadingParts fs = some u) :
    ∃ functions, functionParts T R scope fs = some functions ∧
      u = .unit (.cons (.contract false scope .none .nil (appendParts leadingParts functions)) .nil) ∧
      u.decls = ⟨.contract, scope, none, true,
        .contract false scope .none .nil (appendParts leadingParts functions)⟩ ::
        (leadingParts.collect (some scope) ++ functions.collect (some scope)) := by
  simp only [withFunctions, Option.bind_eq_bind, Option.pure_def,
    Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨functions, hf, rfl⟩ := h
  refine ⟨functions, hf, rfl, ?_⟩
  simp only [Source.Syn.decls, Source.Syn.collect, collect_appendParts, List.append_nil]

/-- Dropping only the contract and supplied prefix exposes the exact ordered
translations of the original function entries, with no missing or extra entry. -/
theorem withFunctions_tail {T : Tables} {R : CallSpellExt.Registry}
    {scope : String} {leadingParts : Source.Syn (.list (.part false))}
    {fs : List (Name × FunDecl)} {u : Source.Syn .unit}
    (h : withFunctions T R scope leadingParts fs = some u) :
    (u.decls.drop (1 + (leadingParts.collect (some scope)).length)).map some =
      fs.map (fun f => fromMetadata T R scope f.2) := by
  obtain ⟨functions, hf, _, hd⟩ := withFunctions_declarations h
  rw [hd]
  simp only [Nat.add_comm 1, List.drop_succ_cons, List.drop_left]
  exact functionParts_faithful T R scope fs functions hf

end Solidity.Correctness.Lowering.Total.Decode.Callee
