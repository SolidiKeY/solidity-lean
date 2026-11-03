import Solidity.Frontend.Admission.ProgramObservations

/-! Actual typed Program-field scanning controls. These are not witnesses of
Elaborated, SourceSpec, imported solc programs or external execution. -/
namespace Solidity.Frontend.Admission.ProgramControls
open Solidity.Source

def constantDecl : Decl :=
  ⟨.constant, "seed", none, true, .constant (.elem (.int false 256 (by decide +kernel))) "seed" (.lit (.num (.dec 0 0 0)))⟩
def functionDecl : Decl :=
  ⟨.function, "run", some "C", false,
    .function (.ident "run") .nil none none
      (.cons (.modInv ⟨"guard", []⟩
        (.some (.positional (.cons (.member (.ident "block") "timestamp") .nil)))) .nil)
      false none .nil
      (.some (.block (.cons (.stmtItem (.simpleStmt
        (.exprStmt (.member (.ident "msg") "sender")))) .nil)))⟩
def modifierDecl : Decl :=
  ⟨.modifier, "guard", some "C", false,
    .modifier "guard" (.some (.cons
      (.param (.elem (.int false 256 (by decide +kernel))) none (some "stamp")) .nil)) false none (.some (.block (.cons (.stmtItem (.simpleStmt (.exprStmt (.ident "_")))) .nil)))⟩
def env : Env := ⟨[functionDecl, constantDecl, modifierDecl]⟩
def time : RExpr env [] (.int IntTy.u256) := .magic .block "timestamp" rfl
def sender : RExpr env [] (.address false) := .magic .msg "sender" rfl

def args : RConvArgs env [] [.int IntTy.u256] := .cons time (by decide +kernel) .nil

def body : RBody env := {
  ps := [], rs := [], inModifier := false, locals := [], out := []
  items := .stmt (.expr sender) .nil
  mods := [⟨modifierDecl, [.int IntTy.u256], args⟩] }
def modifierBody : RBody env := {
  ps := [.int IntTy.u256], rs := [], inModifier := true,
  locals := [.int IntTy.u256], out := [.int IntTy.u256]
  items := .stmt (.placeholder rfl) .nil
  mods := [] }
def init : RInit env := ⟨constantDecl, .int IntTy.u256, rfl, time⟩
def base : RBaseArg env [] := ⟨"Base", [.int IntTy.u256], args⟩
def program : Program env := {
  body := fun d => if d.name == "run" then some body else
    if d.name == "guard" then some modifierBody else none
  consts := fun d => if d.name == "seed" then some init else none
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
    [modifierDecl, modifierDecl] := rfl

theorem modifier_target_kind : modifierDecl.kind = .modifier := rfl

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

/-- Parameters derived from the actual declarations match the carried frames. -/
theorem modifier_frame_parameters :
    (modifierDecl.frame? env).map Frame.ps = some modifierBody.ps := rfl

theorem function_frame_parameters :
    (functionDecl.frame? env).map Frame.ps = some body.ps := rfl

theorem invocation_parameter_types : body.mods.map (·.ps) = [modifierBody.ps] := rfl

theorem host_is_function : functionDecl.kind = .function := rfl

/-- info: 'Solidity.Frontend.Admission.ProgramControls.modifier_frame_parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms modifier_frame_parameters
/-- info: 'Solidity.Frontend.Admission.ProgramControls.function_frame_parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms function_frame_parameters
/-- info: 'Solidity.Frontend.Admission.ProgramControls.invocation_parameter_types' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms invocation_parameter_types
/-- info: 'Solidity.Frontend.Admission.ProgramControls.host_is_function' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms host_is_function
/-- info: 'Solidity.Frontend.Admission.ProgramControls.all_containers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms all_containers
/-- info: 'Solidity.Frontend.Admission.ProgramControls.all_containers_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms all_containers_admitted
/-- info: 'Solidity.Frontend.Admission.ProgramControls.body_only_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms body_only_refuted
/-- info: 'Solidity.Frontend.Admission.ProgramControls.missing_contract_changes_scan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms missing_contract_changes_scan
/-- info: 'Solidity.Frontend.Admission.program_observation_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Frontend.Admission.program_observation_iff
/-- info: 'Solidity.Frontend.Admission.elaborated_constructor_in_declarations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Frontend.Admission.elaborated_constructor_in_declarations
end Solidity.Frontend.Admission.ProgramControls
