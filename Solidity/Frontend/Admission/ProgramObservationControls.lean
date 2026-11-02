import Solidity.Frontend.Admission.ProgramObservations

/-! Actual typed Program-field scanning controls. These are not witnesses of
Elaborated, SourceSpec, imported solc programs or external execution. -/
namespace Solidity.Frontend.Admission.ProgramControls
open Solidity.Source

def constantDecl : Decl :=
  ⟨.constant, "seed", none, true, .constant (.elem (.int false 256 (by decide +kernel))) "seed" (.lit (.num (.dec 0 0 0)))⟩
def env : Env := ⟨[constantDecl]⟩
def time : RExpr env [] (.int IntTy.u256) := .magic .block "timestamp" rfl
def sender : RExpr env [] (.address false) := .magic .msg "sender" rfl

def args : RConvArgs env [] [.int IntTy.u256] := .cons time (by decide +kernel) .nil

def body : RBody env := {
  ps := [], rs := [], inModifier := false, locals := [], out := []
  items := .stmt (.expr sender) .nil
  mods := [⟨constantDecl, [.int IntTy.u256], args⟩] }
def init : RInit env := ⟨constantDecl, .int IntTy.u256, rfl, time⟩
def base : RBaseArg env [] := ⟨"Base", [.int IntTy.u256], args⟩
def program : Program env := {
  body := fun _ => some body
  consts := fun _ => some init
  inits := fun _ => [init]
  ctor := fun _ => some body
  ctorLocals := fun _ => []
  baseArgs := fun _ => [base]
  contracts := ["C"] }

/-- Body, modifier argument, constant, constructor body/modifier, initializer,
and base arguments all survive, with repetitions and structural order intact. -/
theorem all_containers : programObservations program =
    [.magic .msg "sender", .magic .block "timestamp", .magic .block "timestamp",
     .magic .msg "sender", .magic .block "timestamp", .magic .block "timestamp",
     .magic .block "timestamp"] := rfl

theorem all_containers_admitted :
    (programObservations program).all ObservationSite.allowed = true := by decide +kernel

theorem populated_constructor_site :
    ProgramSite program (.magic .msg "sender") :=
  .inr ⟨"C", List.mem_cons_self, .inl ⟨body, rfl, List.mem_append_left _ List.mem_cons_self⟩⟩

theorem modifier_targets_retained : programModifierTargets program =
    [constantDecl, constantDecl] := rfl

theorem base_targets_retained : programBaseTargets program = ["Base"] := rfl

/-- An incorrect smaller collection is refuted, not accepted as coverage. -/
theorem body_only_refuted : programObservations program ≠ bodyObservations body := by
  intro h
  have hl := congrArg List.length h
  change 7 = 2 at hl
  cases hl

/-- Roster omission remains visible; no theorem silently assumes arbitrary
Program lookups outside the actual finite roster are covered. -/
def omitted : Program env := { program with contracts := [] }
theorem missing_contract_changes_scan :
    programObservations omitted ≠ programObservations program := by
  intro h
  have hl := congrArg List.length h
  change 3 = 7 at hl
  cases hl

/-- A source-declaration lookup alone is not a nonempty body certificate. -/
def missingBody : Program env := { program with body := fun _ => none }
theorem missing_body_visible :
    programObservations missingBody ≠ programObservations program := by
  intro h
  have hl := congrArg List.length h
  change 5 = 7 at hl
  cases hl

#print axioms all_containers
#print axioms all_containers_admitted
#print axioms body_only_refuted
#print axioms missing_contract_changes_scan
#print axioms Solidity.Frontend.Admission.program_observation_iff
#print axioms Solidity.Frontend.Admission.elaborated_constructor_in_declarations
end Solidity.Frontend.Admission.ProgramControls
