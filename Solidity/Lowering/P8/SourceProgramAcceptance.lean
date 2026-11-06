import Solidity.Lowering.P8.SourcePrograms

/-! Exact acceptance projection of the actual Source algorithms. Only the
success bit is projected: actual program values, names and graph judgments
remain those of SourcePrograms. No profile/semantic completeness is claimed. -/
namespace Solidity.Lowering.P8.SourceProgramAcceptance
open Source Roadmap.Frontend SourcePrograms

theorem elaborate_acceptance : ∀ r : Resolution,
    (elaborate r).isSome = elaborates r.env := by
  intro r
  cases hb : Solidity.Source.elaborates r.env <;>
    simp only [Solidity.Source.elaborate, hb, Bool.false_eq_true, ↓reduceIte, Option.isSome_none, Option.isSome_some]

abbrev UnitsAcceptance : Prop := ∀ us : List (String × Resolution),
  (elaborateUnits us).isSome = us.all (fun u => elaborates u.2.env)

theorem units_acceptance : UnitsAcceptance := by
  intro us
  induction us with
  | nil => rfl
  | cons u us ih =>
    rw [Solidity.Lowering.P8.SourcePrograms.elaborateUnits]
    cases he : Solidity.Source.elaborate u.2 with
    | none =>
      have hf : Solidity.Source.elaborates u.2.env = false := by
        have h := Solidity.Lowering.P8.SourceProgramAcceptance.elaborate_acceptance u.2
        rw [he] at h
        exact h.symm
      simp only [bind, Option.bind, List.all_cons, hf, Bool.false_and, Option.isSome_none]
    | some el =>
      have hf : Solidity.Source.elaborates u.2.env = true := by
        have h := Solidity.Lowering.P8.SourceProgramAcceptance.elaborate_acceptance u.2
        rw [he] at h
        exact h.symm
      cases ht : Solidity.Lowering.P8.SourcePrograms.elaborateUnits us with
      | none =>
        have hh : us.all (fun u => Solidity.Source.elaborates u.2.env) = false := by
          rw [ht] at ih
          exact ih.symm
        simp only [bind, Option.bind, List.all_cons, hf, hh, Bool.true_and, Option.isSome_none]
      | some es =>
        have hh : us.all (fun u => Solidity.Source.elaborates u.2.env) = true := by
          rw [ht] at ih
          exact ih.symm
        simp only [bind, pure, Option.bind, List.all_cons, hf, hh, Bool.and_self, Option.isSome_some]

/-- Exact component-guard and actual elaborator acceptance proposition. -/
abbrev AdmitAcceptance : Prop := ∀ (i : Input) (p : CheckedSyntax.Parsed)
  (r : SourceResolutions.Packet) (cert : CheckedSyntax.Cert),
  (SourcePrograms.accept i p r cert).isSome =
    (SourceMetadata.checkInput i p r cert && r.units.all (fun u => elaborates u.2.env))

theorem acceptance_projection : AdmitAcceptance := by
  intro i p r cert
  unfold Solidity.Lowering.P8.SourcePrograms.accept
  cases h : Solidity.Lowering.P8.SourceMetadata.checkInput i p r cert <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Option.isSome_none,
      Solidity.Lowering.P8.SourceProgramAcceptance.units_acceptance, Bool.false_and, Bool.true_and]

/-- info: 'Solidity.Lowering.P8.SourceProgramAcceptance.acceptance_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms acceptance_projection
/-- info: 'Solidity.Lowering.P8.SourceProgramAcceptance.elaborate_acceptance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms elaborate_acceptance
/-- info: 'Solidity.Lowering.P8.SourceProgramAcceptance.units_acceptance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms units_acceptance
end Solidity.Lowering.P8.SourceProgramAcceptance
