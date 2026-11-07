import Solidity.Backend.Scalar.Checked
import Solidity.Backend.Scalar.Heights

/-!
Success and distinguishing failure/resource controls against the actual
frozen certificate interfaces and local evaluators, checked with Lean 4.24.0.

These are gasless Osaka slices. GAS/BASEFEE/CLZ refusal below does not prove gas
adequacy or execution on another fork. Neither evaluator has a gas/fork input;
fetched EVM execution, gas, fork agreement, and generic source compilation
remain separate obligations. These controls cannot discharge those boundaries.
-/
namespace Solidity.Backend.Scalar.H62Audit

/-- Success for every supported Boolean input and every untouched tail, for
any implementation satisfying the frozen public unary certificate. -/
theorem boolean_not_total (c : UnaryCertificate .not .bool rfl)
    (b : Bool) (tail : Stack) :
    run c.code (encodeValue .bool b :: tail) =
      some (encodeValue .bool (!b) :: tail) := by
  cases b <;> exact c.correct _ tail

theorem boolean_and_total (c : BinaryCertificate .and .bool rfl)
    (a b : Bool) (tail : Stack) :
    run c.code (encodeValue .bool a :: encodeValue .bool b :: tail) =
      some (encodeValue .bool (a && b) :: tail) := by
  cases a <;> cases b <;> exact c.correct _ _ tail

/-- A reject-all implementation cannot inhabit this existing public contract. -/
theorem reject_all_cannot_certify_not :
    ¬ ∃ c : UnaryCertificate .not .bool rfl, ∀ st : Stack, run c.code st = none := by
  rintro ⟨c, reject⟩
  have success := boolean_not_total c true []
  rw [reject] at success
  cases success

private def zero : PrimTy.uint.Denote := ⟨0, by decide⟩

/-- A supported arithmetic input must select success, including for arbitrary
alternative implementations of the actual frozen checked certificate. -/
theorem checked_add_zero_total (c : CheckedCertificate .add .uint rfl) (tail : Stack) :
    guarded c.test c.body overflowFailure
      (encodeValue .uint zero :: encodeValue .uint zero :: tail) =
      some (.ok (encodeValue .uint zero :: tail)) := by
  exact c.correct zero zero tail

/-- Always reverting fails the checked public contract on a supported input. -/
theorem always_revert_cannot_certify_add :
    ¬ ∃ c : CheckedCertificate .add .uint rfl, ∀ st : Stack,
      guarded c.test c.body overflowFailure st = some (.error overflowFailure) := by
  rintro ⟨c, revert⟩
  have success := checked_add_zero_total c []
  rw [revert] at success
  cases success

/-- The same raw EVM division body returns zero; the source-level component
must instead observe the original panic payload on its guarded failure branch. -/
theorem division_failure_observable :
    run [.op .DIV] [7, 0, 99] = some [0, 99] ∧
    guarded (zeroTest ⟨1, by decide⟩) [.op .DIV] divisionFailure [7, 0, 99] =
      some (.error divisionFailure) ∧
    guarded (zeroTest ⟨1, by decide⟩) [.op .DIV] divisionFailure [7, 2, 99] =
      some (.ok [3, 99]) := ⟨rfl, rfl, rfl⟩

theorem panic_classes_distinct : divisionFailure ≠ overflowFailure := by decide +kernel

/-- Real stack-bound observation rejects a push at the physical limit. -/
theorem physical_capacity_boundary :
    stackBound [.op (.DUP ⟨0, by decide⟩)] 1023 = true ∧
    stackBound [.op (.DUP ⟨0, by decide⟩)] 1024 = false := by decide +kernel

/-- The local relation cannot be used to claim GAS or fork-environment
observations. CLZ is in the Osaka opcode type but outside this numeric slice. -/
theorem gas_and_fork_boundary :
    run [.op .GAS] [7] = none ∧
    run [.op .BASEFEE] [7] = none ∧
    run [.op .CLZ] [7] = none := ⟨rfl, rfl, rfl⟩

end Solidity.Backend.Scalar.H62Audit
