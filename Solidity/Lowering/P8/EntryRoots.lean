import Solidity.Lowering.P8.DispatchCoverage
import Solidity.Frontend.Admission.ProgramRoots

/-! Roots selected by the actual external source entry routines. No caller-
provided roster premise is used. This is finite entry/body coverage, not
receiver reachability, complete G15 extraction, profile or SourceSpec adequacy. -/
namespace Solidity.Lowering.P8.EntryRoots
open Source Frontend.Admission

/-- An actual selector hit names an environment declaration and a present
body after virtual dispatch. The published dispatch theorem is reused.
This is a selector fact, not proof of dispatch execution: nonempty input,
payment, calldata decoding and other execution checks are not discharged. -/
theorem function_entry : ∀ {E : Env} (G : Glob E) (F : Fr) (input : Roadmap.Bytes) (d : Decl),
    G.pickFn F input = some d → d ∈ E.decls ∧
      ∃ b, G.prog.body (G.dispatchFn F.contract d) = some b ∧
        G.dispatchFn F.contract d ∈ E.decls := by
  intro E G F input d h
  unfold Solidity.Source.Glob.pickFn at h
  have hd : d ∈ E.exposed F.contract := List.mem_of_find?_eq_some h
  obtain ⟨s, _, hs⟩ := List.mem_flatMap.mp hd
  have hm : d ∈ E.decls := (List.mem_filter.mp hs).1
  have hp := List.find?_some h
  simp only [Bool.and_eq_true] at hp
  have hb : (G.prog.body (G.dispatchFn F.contract d)).isSome = true := hp.1
  cases he : G.prog.body (G.dispatchFn F.contract d) with
  | none => rw [he] at hb; cases hb
  | some b => exact ⟨hm, b, rfl, Solidity.Lowering.P9.WholeProgram.dispatch_mem G F.contract d E.decls rfl hm⟩

/-- The receive/fallback lookup preserves the actual declaration and kind,
including inherited selection. Body presence is deliberately not invented. -/
theorem special_entry : ∀ (E : Env) (c : String) (k : DeclKind) (d : Decl),
    E.special c k = some d → d ∈ E.decls ∧ d.kind = k := by
  intro E c k d h
  unfold Solidity.Source.Env.special at h
  obtain ⟨s, _, hs⟩ := List.exists_of_findSome?_eq_some h
  have hm : d ∈ E.decls := List.mem_of_find?_eq_some hs
  have hp := List.find?_some hs
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨hm, hp.2⟩

/-- Routine transport into the independent carried-field root relation.
No inhabitant is supplied; no hypothetical environment membership is assumed. -/
abbrev SelectedEntryRootCoverage : Prop :=
  ∀ {E : Env} (G : Glob E) (F : Fr) (input : Roadmap.Bytes) (d : Decl),
    G.pickFn F input = some d → ∃ b,
      G.prog.body (G.dispatchFn F.contract d) = some b ∧
      (ProgramRoot.body (P := G.prog) (G.dispatchFn F.contract d) b).Occurs ∧
      ∀ site ∈ bodyObservations b, site ∈ programObservations G.prog

/-- Routine special-entry body transport. The actual lookup does not test
body presence, so the successful source body lookup remains explicit. -/
abbrev SpecialEntryBodyCoverage : Prop :=
  ∀ {E : Env} (G : Glob E) (c : String) (k : DeclKind) (d : Decl) (b : RBody E),
    E.special c k = some d → G.prog.body d = some b →
      (ProgramRoot.body (P := G.prog) d b).Occurs ∧
      ∀ site ∈ bodyObservations b, site ∈ programObservations G.prog

/-- info: 'Solidity.Lowering.P8.EntryRoots.function_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms function_entry
/-- info: 'Solidity.Lowering.P8.EntryRoots.special_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms special_entry
end Solidity.Lowering.P8.EntryRoots
