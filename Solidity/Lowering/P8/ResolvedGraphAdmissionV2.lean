import Solidity.Lowering.P8.SourceAstResolvedGraphs
import Solidity.Lowering.P8.DeclarationGraphAdmissionV2

/-! Computed whole-resolution metadata to the existing H24 v2 environment contract.
Regression purpose: require every location view at one unchanged environment,
without treating component failure as Source rejection or claiming program
admission. The optional lifted proof is the existing contract, not a new AST,
program, SourceSpec or origin. Frozen v1 and existing v2 APIs stay unchanged. -/
namespace Solidity.Lowering.P8.ResolvedGraphAdmissionV2
open Lean Solidity.Source

/-- Exactly the three computed location successes, not a profile or semantic oracle. -/
def Ready (origin : Name) (resolved : Resolution) : Prop :=
  (V07.LocationGraphProducer.produce origin resolved.env .storage).isSome = true ∧
  (V07.LocationGraphProducer.produce origin resolved.env .memory).isSome = true ∧
  (V07.LocationGraphProducer.produce origin resolved.env .calldata).isSome = true

instance (origin : Name) (resolved : Resolution) : Decidable (Ready origin resolved) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem ready_iff_all (origin : Name) (resolved : Resolution) :
    Ready origin resolved ↔ ∀ loc,
      (V07.LocationGraphProducer.produce origin resolved.env loc).isSome = true := by
  constructor
  · intro ready loc
    cases loc with
    | storage => exact ready.1
    | memory => exact ready.2.1
    | calldata => exact ready.2.2
  · intro all
    exact ⟨all .storage, all .memory, all .calldata⟩

/-- Only actual computed successes supply the graph fields; local v2 refusal is derived. -/
def certifyEnv (origin : Name) (resolved : Resolution) :
    Option (PLift (DeclarationGraphAdmissionV2.EnvAdmission resolved.env)) :=
  if ready : Ready origin resolved then
    some ⟨DeclarationGraphAdmissionV2.of_graphs resolved.env (fun loc =>
      V07.GraphAdmissionAssembly.graph_of_produce origin resolved.env loc
        ((ready_iff_all origin resolved).mp ready loc))⟩
  else none

theorem certifyEnv_success_iff (origin : Name) (resolved : Resolution) :
    (certifyEnv origin resolved).isSome = true ↔ Ready origin resolved := by
  unfold certifyEnv
  by_cases ready : Ready origin resolved
  · rw [dif_pos ready]
    exact ⟨fun _ => ready, fun _ => rfl⟩
  · rw [dif_neg ready]
    constructor
    · intro bad
      cases bad
    · intro admitted
      exact False.elim (ready admitted)

abbrev Result := (resolved : Resolution) ×
  Option (PLift (DeclarationGraphAdmissionV2.EnvAdmission resolved.env))

def assemble (origin : Name) (resolved : Resolution) : Result :=
  ⟨resolved, certifyEnv origin resolved⟩

/-- Preserve conversion errors and the complete candidate even when certification is None. -/
def certify (origin : Name) (fuel : Nat) (settings : Settings) (node : Json) :
    Except String Result :=
  (SourceAstResolvedGraphs.produce origin fuel settings node .storage).map
    (fun result => assemble origin result.1)

theorem output_resolution (origin : Name) (fuel : Nat) (settings : Settings)
    (node : Json) (result : Result) (returned : certify origin fuel settings node = .ok result) :
    ∃ unit, SourceAstUnit.unit fuel node = .ok unit ∧ result.1 = Source.resolveUnit settings unit := by
  cases computed : SourceAstResolvedGraphs.produce origin fuel settings node .storage with
  | error message =>
    rw [certify, computed] at returned
    cases returned
  | ok output =>
    rw [certify, computed] at returned
    cases returned
    exact SourceAstResolvedGraphs.output_resolution origin fuel settings node .storage output computed

/-- Joint provenance, original resolution relation and the existing v2 environment contract.
This is no whole-program v2 typing or actual Source admission theorem. -/
theorem certified_output (origin : Name) (fuel : Nat) (settings : Settings)
    (node : Json) (result : Result) (returned : certify origin fuel settings node = .ok result)
    (success : result.2.isSome = true) (links : settings.links = []) :
    ∃ unit, SourceAstUnit.unit fuel node = .ok unit ∧
      result.1 = Source.resolveUnit settings unit ∧ Source.Resolves' settings unit result.1 ∧
      DeclarationGraphAdmissionV2.EnvAdmission unit.env := by
  obtain ⟨unit, converted, same⟩ := output_resolution origin fuel settings node result returned
  have admitted : DeclarationGraphAdmissionV2.EnvAdmission result.1.env := by
    cases present : result.2 with
    | none => rw [present] at success; cases success
    | some proof => exact proof.down
  rw [same] at admitted
  exact ⟨unit, converted, same, ⟨links, same⟩, admitted⟩

/-- info: 'Solidity.Lowering.P8.ResolvedGraphAdmissionV2.ready_iff_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ready_iff_all
/-- info: 'Solidity.Lowering.P8.ResolvedGraphAdmissionV2.certifyEnv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certifyEnv
/-- info: 'Solidity.Lowering.P8.ResolvedGraphAdmissionV2.certifyEnv_success_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certifyEnv_success_iff
/-- info: 'Solidity.Lowering.P8.ResolvedGraphAdmissionV2.output_resolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms output_resolution
/-- info: 'Solidity.Lowering.P8.ResolvedGraphAdmissionV2.certified_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certified_output
end Solidity.Lowering.P8.ResolvedGraphAdmissionV2
