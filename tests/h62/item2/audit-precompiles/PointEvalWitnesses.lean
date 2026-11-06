import Lean.Elab.Command
import Solidity.Precompiles.PointEval

/-! Guards against a PointEval census assuming a successful cryptographic input
or counting separately inhabited decoder/check premises as a joint witness.
Malformed nonempty inputs and an inhabited abstract bind/check instance retain
the original laws. The successful pointEval_result premise remains open here;
these proofs do not establish native crypto equality or compiler success. -/
namespace H62.AuditPrecompiles.Successor.PointEval
open Solidity.Precompiles Solidity.Roadmap.Evm
open Solidity.Precompiles.PointEval

theorem bind_failure_data : ∃ (α β : Type) (o : Option α) (f : α → Bool) (v : β),
    (o >>= fun i => if f i = true then some v else none) = none ↔
      o = none ∨ ∃ i, o = some i ∧ f i = false :=
  ⟨Unit, Unit, some (), (fun _ => true), (), bind_check_eq_none _ _ _⟩

theorem bind_success_joint : ∃ (α β : Type) (o : Option α) (f : α → Bool) (v w : β),
    (o >>= fun i => if f i = true then some v else none) = some w ∧ w = v := by
  have h : ((some () : Option Unit) >>= fun _ =>
      if true = true then some () else none) = some () := rfl
  exact ⟨Unit, Unit, some (), (fun _ => true), (), (), h, bind_check_eq_some h⟩

theorem failure_data : ∃ d : Bytes,
    pointEval d = none ↔ decode d = none ∨ ∃ i, decode d = some i ∧ verifies i = false :=
  ⟨[1], pointEval_eq_none_iff [1]⟩

theorem decode_length_joint : ∃ d : Bytes, d.length ≠ 192 ∧ decode d = none := by
  have h : ([1] : Bytes).length ≠ 192 := by decide
  exact ⟨[1], h, decode_length h⟩

theorem pointEval_length_joint : ∃ d : Bytes, d.length ≠ 192 ∧ pointEval d = none := by
  have h : ([1] : Bytes).length ≠ 192 := by decide
  exact ⟨[1], h, pointEval_length h⟩

/-- info: 'H62.AuditPrecompiles.Successor.PointEval.bind_failure_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bind_failure_data
/-- info: 'H62.AuditPrecompiles.Successor.PointEval.bind_success_joint' depends on axioms: [propext] -/
#guard_msgs in
#print axioms bind_success_joint
/-- info: 'H62.AuditPrecompiles.Successor.PointEval.failure_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms failure_data
/-- info: 'H62.AuditPrecompiles.Successor.PointEval.decode_length_joint' depends on axioms: [propext] -/
#guard_msgs in
#print axioms decode_length_joint
/-- info: 'H62.AuditPrecompiles.Successor.PointEval.pointEval_length_joint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pointEval_length_joint
run_cmd Lean.logInfo "CORE_APPLICABILITY_PASS module=PointEval original=5 guards=5"
end H62.AuditPrecompiles.Successor.PointEval
