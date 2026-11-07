import Solidity.Yul.Compilation.Allocation
import Lean

/-! Complete simultaneous witnesses for all nine ordinary Allocation statements,
and H69 certificates for its three allocation-separation statements. Positive
fixtures use inhabited Fin 1 indices, including coupled equality and ordering
premises. This audits arithmetic interfaces, not runtime memory contents.
-/
namespace H62.AuditYul.AllocationWitnesses
open Solidity.Yul.Compilation

theorem bounds_joint : ∃ (n : Nat) (_s : Slots n) (_i : Fin n), True :=
  ⟨1, ⟨0⟩, ⟨0, by decide⟩, trivial⟩

theorem injective_joint : ∃ (n : Nat) (s : Slots n) (i j : Fin n)
    (_h : s.at i = s.at j), True :=
  ⟨1, ⟨0⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, rfl, trivial⟩

theorem extend_joint : ∃ (n : Nat) (_s : Slots n) (_k : Nat) (_i : Fin n), True :=
  ⟨1, ⟨0⟩, 1, ⟨0, by decide⟩, trivial⟩

theorem relocate_joint : ∃ (n : Nat) (_s : Slots n) (_delta : Nat) (_i : Fin n), True :=
  ⟨1, ⟨0⟩, 1, ⟨0, by decide⟩, trivial⟩

theorem local_bound_joint : ∃ (a r l : Nat) (_f : Frame a r l) (_i : Fin l), True :=
  ⟨1, 1, 1, ⟨0⟩, ⟨0, by decide⟩, trivial⟩

theorem caller_joint : ∃ (a r l n : Nat) (s : Slots n) (_i : Fin n)
    (f : Frame a r l) (_h : s.base + n ≤ f.base) (_j : Fin l), True :=
  ⟨1, 1, 1, 1, ⟨0⟩, ⟨0, by decide⟩, ⟨1⟩, by decide, ⟨0, by decide⟩, trivial⟩

theorem height_joint : ∃ (_tail _a _b : Nat), True := ⟨1, 1, 1, trivial⟩

theorem label_injective_joint : ∃ (n : Nat) (base : Nat) (i j : Fin n)
    (_h : label base i = label base j), True :=
  ⟨1, 0, ⟨0, by decide⟩, ⟨0, by decide⟩, rfl, trivial⟩

theorem label_relocate_joint : ∃ (n _base _delta : Nat) (_i : Fin n), True :=
  ⟨1, 0, 1, ⟨0, by decide⟩, trivial⟩

/-- Argument and result intervals cannot overlap at well-typed indices. -/
theorem arg_result_disjoint {a r l : Nat} (f : Frame a r l)
    (i : Fin a) (j : Fin r) : f.arg i ≠ f.result j :=
  Frame.arg_result_disjoint f i j

/-- Result and local intervals cannot overlap at well-typed indices. -/
theorem result_local_disjoint {a r l : Nat} (f : Frame a r l)
    (i : Fin r) (j : Fin l) : f.result i ≠ f.local j :=
  Frame.result_local_disjoint f i j

/-- Argument and local intervals cannot overlap at well-typed indices. -/
theorem arg_local_disjoint {a r l : Nat} (f : Frame a r l)
    (i : Fin a) (j : Fin l) : f.arg i ≠ f.local j :=
  Frame.arg_local_disjoint f i j

open Lean Meta Elab Command in
run_cmd do
  let ordinary : Array (Name × Name) := #[
    (`Slots.bounds, `bounds_joint), (`Slots.injective, `injective_joint),
    (`Slots.extend_at, `extend_joint), (`Slots.relocate, `relocate_joint),
    (`Frame.local_bound, `local_bound_joint), (`Frame.caller_below_locals, `caller_joint),
    (`returnHeight_compose, `height_joint), (`label_injective, `label_injective_joint),
    (`label_relocate, `label_relocate_joint)]
  for (sourceSuffix, proofSuffix) in ordinary do
    let sourceName := `Solidity.Yul.Compilation ++ sourceSuffix
    let proofName := `H62.AuditYul.AllocationWitnesses ++ proofSuffix
    let source ← getConstInfo sourceName
    let audit ← getConstInfo proofName
    unless source.levelParams == audit.levelParams do
      throwError "allocation witness universes changed: {sourceName}"
    liftTermElabM do
      let expected ← forallTelescopeReducing source.type fun xs _ => do
        let mut result := mkConst ``True
        for x in xs.reverse do
          result ← mkAppM ``Exists #[← mkLambdaFVars #[x] result]
        pure result
      unless ← isDefEq audit.type expected do
        throwError "allocation witness omitted or changed a premise: {sourceName}"
    let axioms ← liftTermElabM (collectAxioms proofName)
    unless axioms.all (fun n => [``propext, ``Classical.choice, ``Quot.sound].contains n) do
      throwError "unapproved allocation witness axioms: {proofName}"
    logInfo m!"ALLOCATION_JOINT_PASS: {sourceName}"
  for suffix in #[`arg_result_disjoint, `result_local_disjoint, `arg_local_disjoint] do
    let sourceName := `Solidity.Yul.Compilation.Frame ++ suffix
    let proofName := `H62.AuditYul.AllocationWitnesses ++ suffix
    let source ← getConstInfo sourceName
    let audit ← getConstInfo proofName
    unless source.type == audit.type && source.levelParams == audit.levelParams do
      throwError "allocation separation statement changed: {sourceName}"
    let axioms ← liftTermElabM (collectAxioms proofName)
    unless axioms.all (fun n => [``propext, ``Classical.choice, ``Quot.sound].contains n) do
      throwError "unapproved separation axioms: {proofName}"
    logInfo m!"ALLOCATION_REFUTATION_PASS: {sourceName}"

#print axioms injective_joint
#print axioms caller_joint
#print axioms arg_result_disjoint
end H62.AuditYul.AllocationWitnesses
