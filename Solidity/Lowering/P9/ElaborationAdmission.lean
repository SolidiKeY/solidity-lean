import Solidity.Source.Elaborate

/-! General elaborator/body-certificate transport for call admission.
No parser completeness, global wellformed→accepted theorem or execution proof. -/
namespace Solidity.Lowering.P9

/-- Recover the real algorithm's admission flag, not a desired simulation. -/
theorem elaborates_of_success (r : Source.Resolution)
    (h : (Source.elaborate r).isSome = true) : Source.elaborates r.env = true := by
  unfold Source.elaborate at h
  cases hf : Source.elaborates r.env with
  | false => simp only [hf, Bool.false_eq_true, ↓reduceIte, Option.isSome_none] at h
  | true => rfl

/-- Every syntactically body-bearing environment declaration receives its
actual typed body. Abstract declarations are not asserted to possess bodies. -/
theorem accepted_body (r : Source.Resolution)
    (h : (Source.elaborate r).isSome = true) (d : Source.Decl)
    (hd : d ∈ r.env.decls) (hb : d.hasBody = true) :
    ∃ b : Source.RBody r.env, (Source.progOf r.env).body d = some b ∧
      Source.RBody.Derived r.env d b := by
  have hf := elaborates_of_success r h
  unfold Source.elaborates at hf
  simp only [Bool.and_eq_true, List.all_eq_true] at hf
  have allBodies := hf.1.1
  have hi := allBodies d hd
  rw [hb] at hi
  change (Source.elabBody r.env d).isSome = true at hi
  cases he : Source.elabBody r.env d with
  | none => rw [he] at hi; cases hi
  | some result =>
    exact ⟨result.val, by change (Source.elabBody r.env d).map Subtype.val = some result.val; rw [he]; rfl, result.property⟩

/-- The existing published Resolves' relation supplies environment/unit
coherence (and currently an empty link-map premise). Nothing is erased. -/
theorem resolved_accepted_body {s : Source.Settings} {u : Source.Syn .unit}
    {r : Source.Resolution} (hr : Source.Resolves' s u r)
    (ha : (Source.elaborate r).isSome = true) (d : Source.Decl)
    (hd : d ∈ u.decls) (hb : d.hasBody = true) :
    ∃ b : Source.RBody r.env, (Source.progOf r.env).body d = some b ∧
      Source.RBody.Derived r.env d b := by
  apply accepted_body r ha d _ hb
  rw [hr.2]
  exact hd

/-- Exact program identity is retained dependently across the actual output. -/
theorem elaborate_program {r : Source.Resolution} {el : Source.Elaborated}
    (h : Source.elaborate r = some el) :
    el.res = r ∧ HEq el.prog (Source.progOf r.env) := by
  unfold Source.elaborate at h
  split at h
  · cases Option.some.inj h
    exact ⟨rfl, HEq.rfl⟩
  · cases h

#print axioms accepted_body
#print axioms resolved_accepted_body
#print axioms elaborate_program
end Solidity.Lowering.P9
