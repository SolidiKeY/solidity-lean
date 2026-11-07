import Solidity.Roadmap.G49Final.FoldedPublic
import Lean

/-! Synthetic prefix controls for the pass algebra, not substitute source or
EVM semantics. They retain ordered events, exact revert data, nontrivial bounds
and environment maps, and exercise reverse execution without Forward. -/
namespace Solidity.Roadmap.G49Final.H64Controls

private def observed : Prefix Event Outcome :=
  ⟨[.answer (.revert [1, 2]) none, .reentered (.success [42])], some (.revert [1, 2])⟩

private abbrev fixture (environment forward guard : Nat) : Behaviour where
  Env := Nat
  Res := Nat
  resLE := inferInstance
  Allowed e := e = environment
  Admissible _ := True
  Forward _ r := forward ≤ r
  Guard _ r := guard ≤ r
  observe _ _ := observed
  consistent := fun _ _ _ _ => Prefix.Le.refl _

private def shift (a b forward guard delta : Nat) :
    PassCorrect (fixture a forward guard) (fixture b (forward + delta) (guard + delta)) where
  envAbs _ := a
  envSound := fun _ _ => rfl
  envOnto := fun _ h => ⟨b, rfl, h.symm⟩
  need _ r := r + delta
  need_ok := by
    intro e r _ ready
    have hf : forward ≤ r := ready.2.1
    have hg : guard ≤ r := ready.2.2
    exact ⟨⟨trivial, by dsimp [fixture]; omega, by dsimp [fixture]; omega⟩, Prefix.Le.refl _⟩
  back := by
    intro e r _ _ hg
    have bound : guard + delta ≤ r := hg
    exact ⟨r - delta, trivial, by dsimp [fixture]; omega, Prefix.Le.refl _⟩

private def stages : PassList (fixture 7 10 2) (fixture 9 15 7) :=
  .cons (shift 7 8 10 2 2) (.cons (shift 8 9 12 4 3) (.nil _))

/-- One Ready proof drives two nonidentity resource transforms and env maps. -/
theorem forward_revert_with_full_events :
    (fixture 9 15 7).Ready 9 (stages.fold.need 9 10) ∧
    stages.fold.need 9 10 = 15 ∧
    (fixture 7 10 2).observe (stages.fold.envAbs 9) 10 =
      (fixture 9 15 7).observe 9 15 := by
  have source : (fixture 7 10 2).Ready (stages.fold.envAbs 9) 10 :=
    ⟨trivial, by decide, by decide⟩
  have result := public_end_to_end stages 9 rfl 10 source
  exact ⟨result.1.1, rfl, (result.1.2.final_eq rfl).symm⟩

/-- Reverse correspondence still applies below the target Forward threshold. -/
theorem reverse_without_forward :
    ¬ (fixture 9 15 7).Forward 9 7 ∧
    ∃ rs, (fixture 7 10 2).Admissible rs ∧
      (fixture 7 10 2).Guard (stages.fold.envAbs 9) rs ∧
      ((fixture 9 15 7).observe 9 7).Le
        ((fixture 7 10 2).observe (stages.fold.envAbs 9) rs) :=
  ⟨by decide, stages.fold.back 9 7 rfl trivial (by decide)⟩

/-- Source Forward itself is not added to the reverse interface. -/
theorem reverse_source_not_forward :
    ¬ (fixture 7 10 2).Forward 7 2 ∧
    ∃ rs, (fixture 7 10 2).Admissible rs ∧ (fixture 7 10 2).Guard 7 rs ∧
      ((fixture 7 10 2).observe 7 2).Le ((fixture 7 10 2).observe 7 rs) :=
  ⟨by decide, (PassCorrect.refl (fixture 7 10 2)).back 7 2 rfl trivial (by decide)⟩

/-- Failure payload/order and composed resources may not be relabelled. -/
theorem wrong_observations_rejected :
    observed.final ≠ some (.revert [2, 1]) ∧
    observed.events ≠ [.reentered (.success [42]), .answer (.revert [1, 2]) none] ∧
    stages.fold.need 9 10 ≠ 14 := by decide

private def complete : Unit → Prefix Event Outcome := fun _ => ⟨[], some (.success [1])⟩
private def pending : Unit → Prefix Event Outcome := fun _ => ⟨[], none⟩

/-- A kernel-checked obstruction to treating bare RefinesUnder as the common
transitive pass relation: its middle Forward condition can become false. -/
theorem bare_refinement_not_transitive :
    RefinesUnder (fun _ : Unit => True) (fun _ : Unit => True)
      (fun _ => True) (fun _ => True) (fun _ => True) complete complete ∧
    RefinesUnder (fun _ : Unit => True) (fun _ : Unit => True)
      (fun _ => False) (fun _ => True) (fun _ => True) complete pending ∧
    ¬ RefinesUnder (fun _ : Unit => True) (fun _ : Unit => True)
      (fun _ => True) (fun _ => True) (fun _ => True) complete pending := by
  refine ⟨⟨fun _ _ _ _ => ⟨(), trivial, Prefix.Le.refl _⟩,
      fun _ _ _ => ⟨(), trivial, Prefix.Le.refl _⟩⟩, ?_, ?_⟩
  · exact ⟨fun _ _ hf _ => False.elim hf,
      fun _ _ _ => ⟨(), trivial, List.prefix_refl _, Or.inl rfl⟩⟩
  · intro assumed
    obtain ⟨_, _, below⟩ := assumed.1 () trivial trivial trivial
    have equal := below.final_eq (o := .success [1]) rfl
    have impossible := congrArg Prefix.final equal
    cases impossible

end Solidity.Roadmap.G49Final.H64Controls

#print axioms Solidity.Roadmap.G49Final.PassCorrect.trans
#print axioms Solidity.Roadmap.G49Final.PassList.fold
#print axioms Solidity.Roadmap.G49Final.public_end_to_end
#print axioms Solidity.Roadmap.G49Final.source_from_admitted
#print axioms Solidity.Roadmap.G49Final.source_ready
#print axioms Solidity.Roadmap.G49Final.g49_g50_of_fold
#print axioms Solidity.Roadmap.G49Final.H64Controls.forward_revert_with_full_events
#print axioms Solidity.Roadmap.G49Final.H64Controls.reverse_without_forward
#print axioms Solidity.Roadmap.G49Final.H64Controls.reverse_source_not_forward
#print axioms Solidity.Roadmap.G49Final.H64Controls.wrong_observations_rejected
#print axioms Solidity.Roadmap.G49Final.H64Controls.bare_refinement_not_transitive

#print axioms Solidity.Roadmap.G49Final.cert_adapter
#print axioms Solidity.Roadmap.G49Final.lowering_adapter
#print axioms Solidity.Roadmap.G49Final.compilation_adapter
#print axioms Solidity.Roadmap.G49Final.execution_adapter
#print axioms Solidity.Roadmap.G49Final.p8b_adapter

/- The full typed inventory is emitted to the external checked-run log. -/
open Lean Elab Command in
run_cmd do
  let names := #[`Solidity.Roadmap.G49Final.PassCorrect.trans,
    `Solidity.Roadmap.G49Final.PassList.fold,
    `Solidity.Roadmap.G49Final.public_end_to_end,
    `Solidity.Roadmap.G49Final.cert_adapter,
    `Solidity.Roadmap.G49Final.lowering_adapter,
    `Solidity.Roadmap.G49Final.compilation_adapter,
    `Solidity.Roadmap.G49Final.execution_adapter,
    `Solidity.Roadmap.G49Final.p8b_adapter,
    `Solidity.Roadmap.G49Final.source_from_admitted,
    `Solidity.Roadmap.G49Final.source_ready,
    `Solidity.Roadmap.G49Final.pipeline,
    `Solidity.Roadmap.G49Final.pipeline_env,
    `Solidity.Roadmap.G49Final.PublicObligations.mk,
    `Solidity.Roadmap.G49Final.g49_g50_of_fold]
  let mut declarations : Array Json := #[]
  for name in names do
    let info ← getConstInfo name
    let ty ← liftTermElabM do return (← Meta.ppExpr info.type).pretty
    let binders ← liftTermElabM do
      Meta.forallBoundedTelescope info.type (some info.type.getNumHeadForalls) fun xs _ => do
        let mut rows : Array Json := #[]
        let mut raw := info.type
        for x in xs do
          let decl ← x.fvarId!.getDecl
          let domain := raw.consumeMData.bindingDomain!
          raw := raw.consumeMData.bindingBody!
          rows := rows.push (Json.mkObj [
            ("index", toJson rows.size), ("name", toJson decl.userName.toString),
            ("type", toJson (← Meta.ppExpr decl.type).pretty),
            ("isProp", toJson (← Meta.isProp decl.type)),
            ("closedExpr", toJson (reprStr domain)),
            ("constants", toJson (decl.type.getUsedConstants.toList.map Name.toString))])
        return rows
    let axioms ← collectAxioms name
    declarations := declarations.push (Json.mkObj [
      ("name", toJson name.toString), ("type", toJson ty), ("binders", .arr binders),
      ("dependencies", toJson (info.getUsedConstantsAsSet.toList.map Name.toString)),
      ("axioms", toJson (axioms.toList.map Name.toString))])
  logInfo m!"H64-INVENTORY {(Json.mkObj [("declarations", .arr declarations)]).compress}"
