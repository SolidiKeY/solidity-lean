import Solidity.Calculus.CallFunctionPlan

/-! # Checked-plan acceptance, refusal and semantic controls
Concrete producer results, not only generic laws for hypothetical plans.
-/
namespace Solidity.Examples.Tactics.CallFunctionPlan
open Solidity.CallFunctionPlan Solidity.CallFunctionTable
private abbrev C := StandardExample
private abbrev Γ : Ctx := [.val .uint, .val .uint]
private def name : Var := .fresh "same" 0
private def affine {Δ : Ctx} (x : Val C Δ .uint) : Val C Δ .uint :=
  .binop .add rfl rfl (.binop .mul rfl rfl x (.simple (.lit 3 rfl))) (.simple (.lit 1 rfl))
private def base : Tm C (.val .uint :: Γ) (.val .uint) :=
  (affine (.simple (.local .here))).lower
private def nested (n : Nat) (v : Val C Γ .uint) : Val C Γ .uint :=
  match n with
  | 0 => v
  | n+1 => affine (nested n v)
private def oldTerm (k : Nat) : Tm C Γ (.val .uint) :=
  (nested (2^k) (.simple (.local (.there .here)))).lower
private def original (n : Nat) : State C Γ :=
  (({ State.init C with selfBalance := uintOfNat 5 }).push
    (t := .val .uint) (uintOfNat n)).push (t := .val .uint) (uintOfNat 99)
private def post (n : Nat) : Fml C Γ := .eq (.pvV .here) (.app0 (.lit (uintOfNat n)))

/-- Actual concrete checker accepts several distinct doubling levels. -/
theorem accepts :
    (checked? base 0 (.there .here) (oldTerm 0)).isSome = true ∧
    (checked? base 1 (.there .here) (oldTerm 1)).isSome = true ∧
    (checked? base 2 (.there .here) (oldTerm 2)).isSome = true ∧
    (checked? base 3 (.there .here) (oldTerm 3)).isSome = true ∧
    (checked? base 4 (.there .here) (oldTerm 4)).isSome = true := by
  decide +kernel

/-- Concrete accepted data carries its actual expansion proof. -/
theorem inhabited : ∃ plan : Plan (oldTerm 1),
    checked? base 1 (.there .here) (oldTerm 1) = some plan :=
  Option.isSome_iff_exists.mp accepts.2.1

/-- Every plan for this actual old term proves the returning observation,
through exact capture/restoration rather than a hypothetical future interface. -/
theorem returning (plan : Plan (oldTerm 1)) (m : Modality) :
    holds (original 2) (plan.leaf m name name name .here (post 22)) := by
  apply (plan.holds m name name name .here (post 22) (original 2)).mpr
  apply CallResultCapture.sound name .here (oldTerm 1) (post 22) (original 2)
  apply (CallResultRestore.holds_leaf_of_eval m name .refl .here (oldTerm 1) (post 22)
    (original 2) (uintOfNat 22) rfl).mpr
  rfl

/-- A real checked result and a real successful emitted leaf coexist. -/
theorem checkedReturning (m : Modality) : ∃ plan : Plan (oldTerm 1),
    checked? base 1 (.there .here) (oldTerm 1) = some plan ∧
    holds (original 2) (plan.leaf m name name name .here (post 22)) := by
  obtain ⟨plan, hp⟩ := inhabited
  exact ⟨plan, hp, returning plan m⟩

/-- A wrong observable is false in the same actual state for every accepted plan. -/
theorem wrongResult (plan : Plan (oldTerm 1)) (m : Modality) :
    ¬ holds (original 2) (plan.leaf m name name name .here (post 23)) := by
  intro hh
  have hu : holds (original 2) (.upd m (Upd.nil.snoc (.local .here (.val (oldTerm 1)))) (post 23)) :=
    (plan.holds m name name name .here (post 23) (original 2)).mp hh
  have hc : holds (original 2) (CallResultRestore.leaf m name .refl .here (oldTerm 1) (post 23)) :=
    CallResultCapture.complete name .here (oldTerm 1) (post 23) (original 2) hu
  have hp : holds ((original 2).setLocal .here (uintOfNat 22)) (post 23) :=
    (CallResultRestore.holds_leaf_of_eval m name .refl .here (oldTerm 1) (post 23)
      (original 2) (uintOfNat 22) rfl).mp hc
  have he : (some (uintOfNat 22) : Option Key) = some (uintOfNat 23) := hp
  have bad : (22 : Int) = 23 := congrArg Subtype.val (Option.some.inj he)
  omega

/-- The returned level and base come from actual checker output. -/
theorem checkedMetadata : (checked? base 2 (.there .here) (oldTerm 2)).map
    (fun plan => (plan.level, plan.base.size, plan.input.toNat)) = some (2,5,1) := rfl

/-- Wrong level or argument position cannot certify this actual old term. -/
theorem mismatchedShape :
    (checked? base 2 (.there .here) (oldTerm 1)).isSome = false ∧
    (checked? base 1 .here (oldTerm 1)).isSome = false := ⟨rfl, rfl⟩

private def changed : Tm C (.val .uint :: Γ) (.val .uint) :=
  (Val.binop .add rfl rfl
    (.binop .mul rfl rfl (.simple (.local .here)) (.simple (.lit 3 rfl)))
    (.simple (.lit 2 rfl))).lower
private def reversed : Tm C (.val .uint :: Γ) (.val .uint) :=
  (Val.binop .mul rfl rfl
    (.binop .add rfl rfl (.simple (.local .here)) (.simple (.lit 1 rfl)))
    (.simple (.lit 3 rfl))).lower

/-- Changed arithmetic or reversed dependent operations are rejected. -/
theorem changedOrReversed :
    (checked? changed 1 (.there .here) (oldTerm 1)).isSome = false ∧
    (checked? reversed 1 (.there .here) (oldTerm 1)).isSome = false := ⟨rfl, rfl⟩

private def constant : Tm C (.val .uint :: Γ) (.val .uint) := .app0 (.lit (uintOfNat 7))

/-- Even a syntactically matching constant refuses without its strict-read fact. -/
theorem refusesNonstrict :
    (checked? constant 0 (.there .here) (.app0 (.lit (uintOfNat 7)))).isSome = false := rfl

private def pushRead : Tm C (.val .uint :: Γ) (.val .uint) :=
  .app2 .find (.app2 .pushSlot (.app0 .storage) (.app0 (.root "values" rfl)))
    (.app2 (.at (.arr .dyn)) (.app0 (.root "values" rfl)) (.pvV .here))

/-- Push-bearing terms retain the ordinary route: no exhaustion assumption is added. -/
theorem refusesPush : pushRead.pushFree = false ∧
    (checked? pushRead 0 (.there .here) (oldTerm 0)).isSome = false := ⟨rfl, rfl⟩

/-- The retained-intermediate guard refuses just below the actual size and
accepts at it, rather than silently ignoring its configured bound. -/
theorem intermediateLimit :
    (boundedExpansion? 8 base (.there .here) 2).isSome = false ∧
    (boundedExpansion? 9 base (.there .here) 2).map Tm.size = some 9 := ⟨rfl, rfl⟩

/-- A proposed huge level is rejected before computing that power or expansion. -/
theorem excessiveLevel :
    (checked? base 1000 (.there .here) (oldTerm 1)).isSome = false := rfl

private abbrev WΓ : Ctx := [.old, .val .uint]
private def snapshotRead : Tm C (.val .uint :: WΓ) (.val .uint) :=
  .app2 (.binop .add rfl) (.pvV .here)
    (.app2 .find (.pvS (.there .here)) (.app0 (.root "total" rfl)))

/-- Value-only refusal is independent of the passing no-push/strict flags. -/
theorem refusesNonValueOnly : snapshotRead.pushFree = true ∧
    snapshotRead.strictReads 0 = true ∧ snapshotRead.valOnly = false ∧
    (checked? snapshotRead 0 (.there .here : Idx WΓ (.val .uint))
      (.app0 (.lit (uintOfNat 7)))).isSome = false := ⟨rfl, rfl, rfl, rfl⟩

end Solidity.Examples.Tactics.CallFunctionPlan
