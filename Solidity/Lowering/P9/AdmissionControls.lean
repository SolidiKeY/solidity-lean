import Solidity.Lowering.P9.ElaborationAdmission
import Solidity.Lowering.P9.CallControls
import Solidity.Source.Semantics

/-! Admission, necessary-body and inhabited execution
controls. The explicit fixed model witnesses source-only nonvacuity, not pinned EVM. -/
namespace Solidity.Lowering.P9.AdmissionControls
open Solidity.Lowering.P9

theorem truth_accepted : (Source.elaborate resolution).isSome = true := by
  obtain ⟨el, he, _, _⟩ := actual_elaboration
  rw [he]
  rfl

theorem truth_typed_body : ∃ b : Source.RBody resolution.env,
    (Source.progOf resolution.env).body declaration = some b ∧
    Source.RBody.Derived resolution.env declaration b :=
  accepted_body resolution truth_accepted declaration declaration_present rfl

/-- The inherited source execution proof is parametric in all fixed EVM inputs. -/
theorem source_only_witness (fixed : Roadmap.Fixed) :
    (Source.evalE (glob fixed) caller 11 protectedCall).run
      (.cons (.bool false) .nil, Source.St.init resolution.env) =
      (.ok (.val (.bool true)), (.cons (.bool false) .nil, Source.St.init resolution.env)) :=
  protected_success fixed (Source.St.init resolution.env)

/-- A concrete fixed model for inhabited source controls; no hashing occurs here. -/
def observationFixed : Roadmap.Fixed where
  evm := {
    keccak := fun _ => 0
    keccak_lt := fun _ => by decide
    precompile := fun _ _ => none
    precompileGas := fun _ _ => 0 }
  ledger := fun bal _ a => bal a
  regionLen := 1
  rootSlots := 1

example :
    (Source.evalE (glob observationFixed) caller 11 protectedCall).run
      (.cons (.bool false) .nil, Source.St.init resolution.env) =
      (.ok (.val (.bool true)), (.cons (.bool false) .nil, Source.St.init resolution.env)) :=
  source_only_witness observationFixed

def abstractFunction : Source.Syn (.part false) :=
  .function (.ident "declared") .nil (some .external) none .nil false none
    (.cons (.param (.elem .bool) none none) .nil) .none

def interfaceUnit : Source.Syn .unit :=
  .unit (.cons (.interface "P9Interface" .nil (.cons abstractFunction .nil)) .nil)
def interfaceResolution := Source.resolveUnit {pipeline := .legacy} interfaceUnit
def abstractDecl : Source.Decl := ⟨.function, "declared", some "P9Interface", false, abstractFunction⟩

theorem interface_accepted : (Source.elaborate interfaceResolution).isSome = true := by rfl
theorem interface_profile : Source.InProfileSyntax interfaceResolution := rfl
theorem abstract_present : abstractDecl ∈ interfaceResolution.env.decls :=
  List.mem_cons_of_mem _ List.mem_cons_self

theorem abstract_has_no_body : abstractDecl.hasBody = false := rfl
theorem actual_missing_body : (Source.progOf interfaceResolution.env).body abstractDecl = none := rfl

/-- Accepted interface declarations do not gain invented bodies. The source
hasBody premise of accepted_body cannot be omitted. -/
theorem body_premise_necessary :
    (Source.elaborate interfaceResolution).isSome = true ∧
      abstractDecl ∈ interfaceResolution.env.decls ∧ abstractDecl.hasBody = false ∧
      (Source.progOf interfaceResolution.env).body abstractDecl = none :=
  ⟨interface_accepted, abstract_present, abstract_has_no_body, actual_missing_body⟩

def badFunction : Source.Syn (.part false) :=
  .function (.ident "bad") .nil (some .internal) none .nil false none
    (.cons (.param (.elem (.int false 8 (by decide))) none none) .nil)
    (.some (.block (.cons (.stmtItem (.returnStmt (.some (.lit (.bool true))))) .nil)))
def badUnit : Source.Syn .unit :=
  .unit (.cons (.contract false "P9Bad" .none .nil (.cons badFunction .nil)) .nil)
def badResolution := Source.resolveUnit {pipeline := .legacy} badUnit

theorem wrong_return_type_rejected : Source.elaborate badResolution = none := rfl

#print axioms truth_typed_body
#print axioms source_only_witness
#print axioms body_premise_necessary
#print axioms wrong_return_type_rejected
end Solidity.Lowering.P9.AdmissionControls
