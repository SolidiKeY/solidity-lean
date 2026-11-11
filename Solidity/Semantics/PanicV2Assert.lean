import Solidity.Semantics.PanicV2Eval

/-!
# Explicit assertion provenance in V2

The gap guarded is source-assert 0x01 versus generated overflow/enum guards
0x11/0x21, all erased to the same V1 assertion. `Assertion` is explicit V2
syntax, not a result-only classifier of V1 programs. Its producer origin
must be associated by an adopting source/lowering owner; erasure alone is
not such a source/compiler theorem. Existing V1 assertions lifted without
an origin deliberately retain an unknown code.

This first site family proves both the exact full-result projection and
its false/success/condition-failure cases. The condition uses the structural V2 expression evaluator, whose exact
projection is proved independently. Its site classifiers are refined by family.
-/

namespace Solidity.PanicV2

variable {C : Contract} {Γ : Ctx}

/-- A typed V2 step over exactly the existing states and heap extensions. -/
abbrev Step (C : Contract) (Γ Δ : Ctx) :=
  (σ : State C Γ) → Result (Out C σ.H Δ)

/-- Explicitly originated assertion, retaining its typed condition. -/
structure Assertion (C : Contract) (Γ : Ctx) where
  origin : AssertionOrigin
  condition : Val C Γ .bool

/-- The original V1 statement, without changing its body or constructor. -/
def Assertion.erase (a : Assertion C Γ) : Stmt C Γ Γ := .assert a.condition

/-- Evaluate the condition once, then tag only this assertion's failure.
A failed condition is forwarded rather than relabelled as assertion failure. -/
def Assertion.run (a : Assertion C Γ) : Step C Γ Γ := fun σ => do
  let value ← Eval.value σ a.condition
  if boolT value then .ok ⟨σ, List.prefix_refl _⟩
  else .error (.assertion a.origin)

/-- Exact erasure includes the entire successful state/heap extension and
all condition failures, not just the final halt tag. -/
theorem Assertion.run_erase (a : Assertion C Γ) (σ : State C Γ) :
    PanicV2.erase (a.run σ) = TRun.assert a.condition σ := by
  exact erase_bind_congr (Eval.value_erase σ a.condition) fun value => by
    cases value <;> rfl

/-- Link the V2 operation to the actual frozen statement interpreter. -/
theorem Assertion.run_erase_stmt (a : Assertion C Γ) (σ : State C Γ) :
    PanicV2.erase (a.run σ) = a.erase.run σ :=
  a.run_erase σ

/-- One general assertion-family lemma: a false, successfully evaluated
condition carries the explicit V2 origin's code and V1 panic reading. -/
theorem Assertion.run_false (a : Assertion C Γ) (σ : State C Γ)
    (condition : a.condition.evalT σ = .ok false) :
    a.run σ = .error (.assertion a.origin) := by
  unfold Assertion.run
  rw [Eval.value_of_ok σ a.condition _ condition]
  rfl

/-- Successful assertions leave the complete original state unchanged. -/
theorem Assertion.run_true (a : Assertion C Γ) (σ : State C Γ)
    (condition : a.condition.evalT σ = .ok true) :
    a.run σ = .ok ⟨σ, List.prefix_refl _⟩ := by
  unfold Assertion.run
  rw [Eval.value_of_ok σ a.condition _ condition]
  rfl

/-- Gap control: an earlier condition failure is never changed to 0x01. -/
theorem Assertion.condition_failure (a : Assertion C Γ) (σ : State C Γ)
    (halt : Halt) (condition : Eval.value σ a.condition = .error halt) :
    a.run σ = .error halt := by
  unfold Assertion.run
  rw [condition]
  rfl

/-- Even a classified condition failure retains its original V1 reading. -/
theorem Assertion.condition_failure_erase (a : Assertion C Γ) (σ : State C Γ)
    (halt : THalt) (condition : a.condition.evalT σ = .error halt) :
    PanicV2.erase (a.run σ) = .error halt := by
  rw [Assertion.run_erase]
  unfold TRun.assert
  rw [condition]
  rfl

/-- A V2 source assertion failing at its own site reports Panic(0x01).
This does not classify generated V1 assertions without provenance. -/
theorem Assertion.source_code (c : Val C Γ .bool) (σ : State C Γ)
    (condition : c.evalT σ = .ok false) :
    (Assertion.run ⟨.source, c⟩ σ) = .error (.assertion .source) ∧
      (Halt.assertion .source).panicCode? = some 0x01 := by
  exact ⟨Assertion.run_false ⟨.source, c⟩ σ condition, rfl⟩

/-- Generated assertion origins retain their own codes while erasing to the
same V1 panic. This is a V2 syntax theorem, not a producer-association proof. -/
theorem Assertion.guard_codes :
    (Halt.assertion .arithmeticGuard).panicCode? = some 0x11 ∧
    (Halt.assertion .enumGuard).panicCode? = some 0x21 ∧
    (Halt.assertion .arithmeticGuard).erase = .panic ∧
    (Halt.assertion .enumGuard).erase = .panic := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- info: 'Solidity.PanicV2.Assertion.run_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Assertion.run_erase
/-- info: 'Solidity.PanicV2.Assertion.run_erase_stmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Assertion.run_erase_stmt
/-- info: 'Solidity.PanicV2.Assertion.run_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Assertion.run_false
/-- info: 'Solidity.PanicV2.Assertion.run_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Assertion.run_true
/-- info: 'Solidity.PanicV2.Assertion.condition_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Assertion.condition_failure
/-- info: 'Solidity.PanicV2.Assertion.condition_failure_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Assertion.condition_failure_erase
/-- info: 'Solidity.PanicV2.Assertion.source_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Assertion.source_code
/-- info: 'Solidity.PanicV2.Assertion.guard_codes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Assertion.guard_codes

end Solidity.PanicV2
