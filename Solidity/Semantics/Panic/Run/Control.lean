import Solidity.Semantics.Panic.Run.Calls

namespace Solidity.Semantics.Panic

variable {C : Contract} {Γ : Ctx}

namespace Run

def ite {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (h₁ : Ext Γ Γ₁) (thn : Step C Γ Γ₁)
    (h₂ : Ext Γ Γ₂) (els : Step C Γ Γ₂) : Step C Γ Γ := fun σ => do
  let v ← value σ c
  if boolT v then (thn σ).map fun o => ⟨o.st.drop h₁, o.ext⟩
  else (els σ).map fun o => ⟨o.st.drop h₂, o.ext⟩

def require (c : Val C Γ .bool) : Step C Γ Γ := fun σ => do
  let v ← value σ c
  if boolT v then pure ⟨σ, List.prefix_refl _⟩ else .error .revert

def assert (c : Val C Γ .bool) : Step C Γ Γ := fun σ => do
  let v ← value σ c
  let _ ← evalProducer (.assertion (boolT v))
  pure ⟨σ, List.prefix_refl _⟩

def loop {Γ₁ : Ctx} (c : Val C Γ .bool) (h : Ext Γ Γ₁) (body : Step C Γ Γ₁) : Step C Γ Γ :=
  fun σ => Loop.run
    (fun o : Out C σ.H Γ => (body o.st).map fun o' => ⟨o'.st.drop h, o.ext.trans o'.ext⟩)
    (fun o => value o.st c) ⟨σ, List.prefix_refl _⟩

/-- A block: its locals popped. -/
def block {Γ₁ : Ctx} (h : Ext Γ Γ₁) (body : Step C Γ Γ₁) : Step C Γ Γ := fun σ =>
  (body σ).map fun o => ⟨o.st.drop h, o.ext⟩

/-- A sequence: the first statement, then the rest. -/
def seq {Γ₁ Γ₂ : Ctx} (s : Step C Γ Γ₁) (P : Step C Γ₁ Γ₂) : Step C Γ Γ₂ := fun σ =>
  match s σ with
  | .ok o => (P o.st).map fun o' => ⟨o'.st, o.ext.trans o'.ext⟩
  | .error e => .error e

/-- The empty sequence. -/
def nil : Step C Γ Γ := fun σ => .ok ⟨σ, List.prefix_refl _⟩

/-- Sequence failure is independent of the continuation and preserves its origin. -/
theorem seq_error {Δ Ξ : Ctx} (first : Step C Γ Δ) (next : Step C Δ Ξ)
    (σ : State C Γ) (halt : Halt Raised) (h : first σ = .error halt) :
    seq first next σ = .error halt := by
  simp only [seq, h]

/-- Assertion code 1 is produced by the actual false assertion, with its witness. -/
theorem assert_false (c : Val C Γ .bool) (σ : State C Γ)
    (h : value σ c = .ok false) :
    assert c σ = .error (.intrinsic .assert
      (Raised.ofOrigin (.assertion false) .assertion rfl)) := by
  simp only [assert, h]
  rfl

/-- An expression's failure is propagated before the assertion guard is evaluated. -/
theorem assert_eval_error (c : Val C Γ .bool) (σ : State C Γ) (halt : Halt Raised)
    (h : value σ c = .error halt) : assert c σ = .error halt := by
  simp only [assert, h]
  rfl

/-- The producer's code and retained failed site agree, not just their V1 erasure. -/
theorem producer_actual_code {α : Type} (producer : Solidity.Panic.Producer α)
    (code : Code) (origin : Raised)
    (h : evalProducer producer = .error (.intrinsic code origin)) :
    code = siteCode origin.site := by
  unfold evalProducer at h
  split at h
  · cases h
  · cases h
  · cases h
    rw [Raised.ofOrigin_site]

/-- A caught assertion uses code 1 even if an external oracle advertises code 17. -/
theorem catch_assert_false {α : Type} (c : Val C Γ .bool) (σ : State C Γ)
    (h : value σ c = .ok false) (ok : Out C σ.H Γ → EvalResult α)
    (err : Unit → EvalResult α) (pnc : Semantics.Word → EvalResult α)
    (other : Unit → EvalResult α) :
    (match assert c σ with
      | .ok out => ok out
      | .error halt => catchHalt halt err pnc other) = pnc (codeWord .assert) := by
  rw [assert_false c σ h]
  rfl

/- Runtime regression: neither unselected handler's infinite loop is evaluated. -/
#guard (match catchHalt
    (.intrinsic .assert (Raised.ofOrigin (.assertion false) .assertion rfl))
    (fun _ => Loop.run (fun n : Nat => .ok n) (fun _ => .ok true) 0)
    (fun c => .ok c.val.toNat)
    (fun _ => Loop.run (fun n : Nat => .ok n) (fun _ => .ok true) 0) with
  | .ok n => n == 1
  | .error _ => false)

end Run
end Solidity.Semantics.Panic
