import Solidity.Semantics.Run

/-!
# Code-carrying panic results beside the frozen typed run

V1 `THalt`, `TRes` and the logical typed-run specification are unchanged.
The loop implementation entries have separate exact logical-name links; their
generated execution helpers remain a distinct trust obligation. V2 retains
which V1 halt an intrinsic failure used: arithmetic/index/pop failures
forget to `revert`, whereas an explicit V2 source assertion forgets to
`panic`. Existing encoded payloads are observations of bytes, not certified
intrinsic origins. An unclassified V1 panic has no guessed code.

The gap guarded here is loss of panic provenance: a result-only translation
cannot distinguish source assertions from generated arithmetic/enum guards.
The V2 operation constructors are reserved for their actual site evaluators;
`lift` deliberately does not classify an arbitrary V1 assertion as 0x01.
Outside source producers must adopt the V2 interface with their origin
association; erasure alone does not establish source/compiler fidelity.
-/

namespace Solidity.PanicV2

/-- The solc panic-code vocabulary, including codes whose intrinsic producer
is not modeled by V1. Having a code is not an emission/coverage theorem. -/
inductive Code where
  | generic | assertion | arithmetic | zeroDivisor | enumConversion
  | storageEncoding | emptyPop | bounds | allocation | uninitializedFunction
  deriving DecidableEq, Repr

/-- Numeric `Panic(uint256)` code (solc 0.8.38). -/
def Code.toNat : Code → Nat
  | .generic => 0x00
  | .assertion => 0x01
  | .arithmetic => 0x11
  | .zeroDivisor => 0x12
  | .enumConversion => 0x21
  | .storageEncoding => 0x22
  | .emptyPop => 0x31
  | .bounds => 0x32
  | .allocation => 0x41
  | .uninitializedFunction => 0x51

/-- Only the modeled operation failures that V1 reads as a bare revert. -/
inductive OperationFailure where
  | arithmetic | zeroDivisor | emptyPop | bounds
  deriving DecidableEq, Repr

/-- A modeled operation failure's code. -/
def OperationFailure.code : OperationFailure → Code
  | .arithmetic => .arithmetic
  | .zeroDivisor => .zeroDivisor
  | .emptyPop => .emptyPop
  | .bounds => .bounds

/-- Explicit origin in V2 assertion syntax. It is not reconstructed from
V1 erasure; adoption by a source producer still needs its association proof. -/
inductive AssertionOrigin where
  | source | arithmeticGuard | enumGuard
  deriving DecidableEq, Repr

/-- Generated guards and source assertions keep different panic codes. -/
def AssertionOrigin.code : AssertionOrigin → Code
  | .source => .assertion
  | .arithmeticGuard => .arithmetic
  | .enumGuard => .enumConversion

/-- A V2 halt retains its exact V1 reading. The assertion origin belongs to explicit
V2 syntax; it is never inferred from a V1 `.panic`.
No operation constructor turns V1 success/exhaustion into a panic. -/
inductive Halt where
  | legacy (halt : THalt)
  | assertion (origin : AssertionOrigin)
  | operation (failure : OperationFailure)
  deriving DecidableEq, Repr

/-- Forget only the new diagnostic information. -/
def Halt.erase : Halt → THalt
  | .legacy halt => halt
  | .assertion _ => .panic
  | .operation _ => .revert

/-- Byte-observed and intrinsic codes have distinct origins. Arbitrary
external `Panic` payloads cannot certify intrinsic source provenance. -/
inductive Observation where
  | intrinsic (code : Code)
  | payload (code : Semantics.Word)

/-- Numeric code of either observation; its origin remains available. -/
def Observation.toNat : Observation → Nat
  | .intrinsic code => code.toNat
  | .payload code => code.1.toNat

/-- A bare V1 panic stays unclassified; encoded panic bytes retain their
observed code, including nonstandard oracle-supplied values. -/
def Halt.observation? : Halt → Option Observation
  | .legacy (.revertWith data) => (Semantics.decodePanic data).map Observation.payload
  | .legacy _ => none
  | .assertion origin => some (.intrinsic origin.code)
  | .operation failure => some (.intrinsic failure.code)

/-- Observe a code without discarding the separately available origin. -/
def Halt.panicCode? (halt : Halt) : Option Nat :=
  halt.observation?.map Observation.toNat

/-- V2 results preserve the full typed successful value, not just a halt tag. -/
abbrev Result (α : Type) := Except Halt α

/-- Exact projection of values and halts into the frozen V1 result type. -/
def erase {α : Type} : Result α → TRes α
  | .ok a => .ok a
  | .error halt => .error halt.erase

/-- Lift unknown V1 outcomes without manufacturing an intrinsic cause. -/
def lift {α : Type} : TRes α → Result α
  | .ok a => .ok a
  | .error halt => .error (.legacy halt)

/-- A typed option's unclassified failure is still exactly V1's revert. -/
def ofOpt {α : Type} : Option α → Result α
  | some a => .ok a
  | none => .error (.legacy .revert)

/-- A site-classified failure, only on the actual failed option branch. -/
def checked {α : Type} (failure : OperationFailure) : Option α → Result α
  | some a => .ok a
  | none => .error (.operation failure)

@[simp] theorem erase_lift {α : Type} (result : TRes α) :
    erase (lift result) = result := by
  cases result <;> rfl

@[simp] theorem erase_ofOpt {α : Type} (value : Option α) :
    erase (ofOpt value) = TRes.ofOpt value := by
  cases value <;> rfl

@[simp] theorem erase_checked {α : Type} (failure : OperationFailure) (value : Option α) :
    erase (checked failure value) = TRes.ofOpt value := by
  cases value <;> rfl

@[simp] theorem erase_bind {α β : Type} (result : Result α) (next : α → Result β) :
    erase (result >>= next) = (erase result >>= fun a => erase (next a)) := by
  cases result <;> rfl

@[simp] theorem erase_map {α β : Type} (result : Result α) (f : α → β) :
    erase (result.map f) = (erase result).map f := by
  cases result <;> rfl

/-- Compose exact projections using proved sub-evaluator equations. This
is a congruence lemma, not an assumed simulation field on an evaluator. -/
theorem erase_bind_congr {α β : Type} {result : Result α} {legacy : TRes α}
    {next : α → Result β} {oldNext : α → TRes β}
    (first : erase result = legacy) (rest : ∀ a, erase (next a) = oldNext a) :
    erase (result >>= next) = (legacy >>= oldNext) := by
  rw [erase_bind, first]
  exact congrArg (fun k => legacy >>= k) (funext rest)

/-- Gap control: an unclassified V1 panic must not silently default to 1. -/
theorem legacy_panic_unclassified : (Halt.legacy .panic).panicCode? = none := rfl

/-- Gap control: operation diagnostics retain V1 revert rather than panic. -/
theorem operation_erases_revert (failure : OperationFailure) :
    (Halt.operation failure).erase = .revert := rfl

/-- A result-level projection is exact even for arbitrary unknown V1 halts. -/
theorem lift_error_erase {α : Type} (halt : THalt) :
    erase (lift (.error halt : TRes α)) = .error halt := rfl

/-- info: 'Solidity.PanicV2.erase_lift' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms erase_lift

/-- info: 'Solidity.PanicV2.erase_ofOpt' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms erase_ofOpt

/-- info: 'Solidity.PanicV2.erase_checked' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms erase_checked

/-- info: 'Solidity.PanicV2.erase_bind' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms erase_bind

/-- info: 'Solidity.PanicV2.erase_map' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms erase_map

/-- info: 'Solidity.PanicV2.legacy_panic_unclassified' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms legacy_panic_unclassified

/-- info: 'Solidity.PanicV2.operation_erases_revert' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms operation_erases_revert

/-- info: 'Solidity.PanicV2.lift_error_erase' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms lift_error_erase

/-- info: 'Solidity.PanicV2.erase_bind_congr' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms erase_bind_congr

end Solidity.PanicV2
