import Solidity.Yul.World.Frames

/-!
# EIP-6780 lifecycle preparation over typed source accounts

Only an account created in this transaction can be scheduled for deletion;
code/storage survive until transaction finalization. The existing typed transfer
implements the distinct, known beneficiary case. Environment credit and world
adequacy are external prerequisites, not assumed by these laws.
-/
namespace Solidity.Yul.World
open Solidity.Roadmap (Address Word Bytes)
open Solidity.Source
variable {D : Layout} {L T : Address → SPath → STy}

/-- Transaction-local lifecycle metadata, separate from existing owner state. -/
structure Lifecycle (D : Layout) (L T : Address → SPath → STy) where
  execution : ExecState D L T
  created : Address → Bool
  doomed : Address → Bool

/-- Only call after a successful creation; rollback must restore the entry
snapshot of this metadata along with the journal. -/
def Lifecycle.recordCreation (s : Lifecycle D L T) (a : Address) : Lifecycle D L T :=
  { s with created := fun b => if b = a then true else s.created b }

/-- Static SELFDESTRUCT is exceptional. Otherwise schedule deletion only for
same-transaction creations; this step itself cannot erase code or storage. -/
def Lifecycle.schedule (s : Lifecycle D L T) (static : Bool) (a : Address) :
    Option (Lifecycle D L T) :=
  if static then none else some { s with doomed := fun b => if b = a then (s.doomed b || s.created b) else s.doomed b }

theorem schedule_static (s : Lifecycle D L T) (a : Address) :
    s.schedule true a = none := rfl

theorem schedule_world (s t : Lifecycle D L T) (static : Bool) (a : Address)
    (h : s.schedule static a = some t) : t.execution = s.execution := by
  unfold Lifecycle.schedule at h
  split at h
  next => contradiction
  next => cases h; rfl

/-- EIP-6780's self-beneficiary exception: pre-existing accounts keep their
balance; same-transaction creations burn it. Deletion is still deferred. -/
def selfBeneficiary (s : ExecState D L T) (created : Bool) (a : Address) : ExecState D L T :=
  if created then s.apply (.account a (fun old => { old with balance := ⟨0, by decide⟩ })) else s

theorem selfBeneficiary_old (s : ExecState D L T) (a : Address) :
    selfBeneficiary s false a = s := rfl

/-- Known distinct beneficiaries reuse the existing transfer, with its real
funding/overflow conditions. This is not a foreign-account credit adapter. -/
def destructTransfer (s : ExecState D L T) (created : Bool) (a beneficiary : Address) :
    Option (ExecState D L T) :=
  if a = beneficiary then some (selfBeneficiary s created a)
  else s.transfer a beneficiary (s.world.accounts a).balance

/-- Finalization erases only the accounts both created and scheduled in this
transaction, then clears transient storage, journal and lifecycle flags. -/
def Lifecycle.finish (s : Lifecycle D L T) : Lifecycle D L T :=
  ⟨⟨⟨fun a => if s.created a && s.doomed a then Account.empty (L a)
      else s.execution.world.accounts a⟩, Transient.empty, []⟩,
    fun _ => false, fun _ => false⟩

theorem finish_old (s : Lifecycle D L T) (a : Address) (h : s.created a = false) :
    s.finish.execution.world.accounts a = s.execution.world.accounts a := by
  simp only [Lifecycle.finish, h, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

theorem finish_created_doomed (s : Lifecycle D L T) (a : Address)
    (hc : s.created a = true) (hd : s.doomed a = true) :
    s.finish.execution.world.accounts a = Account.empty (L a) := by
  simp only [Lifecycle.finish, hc, hd, Bool.true_and, ↓reduceIte]

theorem finish_transient (s : Lifecycle D L T) (a : Address) (p : SPath) :
    (s.finish.execution.transient.cells a).read p = Val.default D (T a p) := rfl

theorem finish_flags (s : Lifecycle D L T) (a : Address) :
    s.finish.created a = false ∧ s.finish.doomed a = false := ⟨rfl, rfl⟩

/-- A reverted frame restores entry lifecycle metadata; any journaled effects,
including a self-beneficiary balance burn, are undone by the existing journal. -/
def Lifecycle.revert (entry : Lifecycle D L T) (ops : List (Op D L T))
    (a c : Address) (v : Word) (input : Bytes) (static : Bool) : Lifecycle D L T :=
  { entry with execution := (entry.execution.enter a c v input static).rollback (entry.execution.run ops) }

theorem lifecycle_revert (entry : Lifecycle D L T) (ops : List (Op D L T))
    (a c : Address) (v : Word) (input : Bytes) (static : Bool) :
    entry.revert ops a c v input static = entry := by
  simp only [Lifecycle.revert, rollback_run]

/-! ## Exact metadata and transaction-boundary laws -/

theorem recordCreation_same (s : Lifecycle D L T) (a : Address) :
    (s.recordCreation a).created a = true := by
  simp only [Lifecycle.recordCreation, ↓reduceIte]

theorem recordCreation_other (s : Lifecycle D L T) (a b : Address) (h : b ≠ a) :
    (s.recordCreation a).created b = s.created b := by
  simp only [Lifecycle.recordCreation, h, ↓reduceIte]

theorem recordCreation_preserves (s : Lifecycle D L T) (a : Address) :
    (s.recordCreation a).execution = s.execution ∧
    (s.recordCreation a).doomed = s.doomed := ⟨rfl, rfl⟩

theorem schedule_none_iff (s : Lifecycle D L T) (static : Bool) (a : Address) :
    s.schedule static a = none ↔ static = true := by
  cases static <;> simp only [Lifecycle.schedule, Bool.false_eq_true, ↓reduceIte,
    reduceCtorEq]

/-- Successful scheduling determines the exact pointwise metadata; no
well-formedness or reachability of arbitrary supplied flags is inferred. -/
theorem schedule_exact (s t : Lifecycle D L T) (static : Bool) (a : Address)
    (h : s.schedule static a = some t) :
    static = false ∧ t.execution = s.execution ∧ t.created = s.created ∧
    t.doomed a = (s.doomed a || s.created a) ∧
    (∀ b, b ≠ a → t.doomed b = s.doomed b) := by
  cases static with
  | true => cases h
  | false =>
    cases h
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · simp only [↓reduceIte]
    · intro b hb
      simp only [hb, ↓reduceIte]

theorem finish_not_both (s : Lifecycle D L T) (a : Address)
    (h : (s.created a && s.doomed a) = false) :
    s.finish.execution.world.accounts a = s.execution.world.accounts a := by
  simp only [Lifecycle.finish, h, Bool.false_eq_true, ↓reduceIte]

theorem finish_not_doomed (s : Lifecycle D L T) (a : Address) (h : s.doomed a = false) :
    s.finish.execution.world.accounts a = s.execution.world.accounts a := by
  apply finish_not_both
  simp only [h, Bool.and_false]

theorem finish_journal (s : Lifecycle D L T) : s.finish.execution.journal = [] := rfl

theorem finish_idempotent (s : Lifecycle D L T) : s.finish.finish = s.finish := rfl

/-- Prior-transaction creations cannot be scheduled for deletion in a new
transaction unless a new successful creation records them again. -/
theorem schedule_after_finish (s t : Lifecycle D L T) (a : Address)
    (h : s.finish.schedule false a = some t) :
    t.execution = s.finish.execution ∧ t.created = (fun _ => false) ∧
    t.doomed = (fun _ => false) := by
  cases h
  refine ⟨rfl, rfl, ?_⟩
  funext b
  by_cases hb : b = a <;> simp only [hb, ↓reduceIte, Lifecycle.finish, Bool.false_or]

/-! ## Actual balance-changing outputs and journal rollback -/

/-- The actual burn is one ordinary account operation (old accounts do none). -/
theorem selfBeneficiary_run (s : ExecState D L T) (created : Bool) (a : Address) :
    selfBeneficiary s created a = s.run
      (if created then [.account a (fun old => { old with balance := ⟨0, by decide⟩ })] else []) := by
  cases created <;> rfl

theorem selfBeneficiary_fresh_account (s : ExecState D L T) (a : Address) :
    (selfBeneficiary s true a).world.accounts a =
      { s.world.accounts a with balance := ⟨0, by decide⟩ } := by
  exact World.set_get _ _ _

theorem selfBeneficiary_other (s : ExecState D L T) (created : Bool) (a b : Address)
    (h : b ≠ a) :
    (selfBeneficiary s created a).world.accounts b = s.world.accounts b := by
  cases created with
  | false => rfl
  | true => exact World.set_other _ h _

/-- The frame's mark is the actual entry journal length, without assuming an
empty caller journal. Its context value need not equal the burned balance. -/
theorem rollback_selfBeneficiary (s : ExecState D L T) (created : Bool) (target a c : Address)
    (v : Word) (input : Bytes) (static : Bool) :
    (s.enter a c v input static).rollback (selfBeneficiary s created target) = s := by
  rw [selfBeneficiary_run]
  exact rollback_run _ _ _ _ _ _ _

/-- A successful actual known transfer, not an arbitrary operation/outcome
assumption, is undone at its actual frame-entry mark. -/
theorem rollback_destructTransfer (s out : ExecState D L T) (created : Bool)
    (src dst : Address) (h : destructTransfer s created src dst = some out)
    (a c : Address) (v : Word) (input : Bytes) (static : Bool) :
    (s.enter a c v input static).rollback out = s := by
  by_cases heq : src = dst
  · simp only [destructTransfer, heq, ↓reduceIte, Option.some.injEq] at h
    subst out
    exact rollback_selfBeneficiary _ _ _ _ _ _ _ _
  · simp only [destructTransfer, heq, ↓reduceIte] at h
    exact rollback_transfer s out heq _ h a c input static

/-- Successful outputs are concretely journaled by the existing owner
implementation. This existential is proved, never an adequacy premise. -/
theorem destructTransfer_run (s out : ExecState D L T) (created : Bool) (src dst : Address)
    (h : destructTransfer s created src dst = some out) :
    ∃ ops : List (Op D L T), out = s.run ops := by
  by_cases heq : src = dst
  · simp only [destructTransfer, heq, ↓reduceIte, Option.some.injEq] at h
    subst out
    exact ⟨_, selfBeneficiary_run s created dst⟩
  · simp only [destructTransfer, ExecState.transfer, heq, ↓reduceIte] at h
    split at h
    · next hc =>
        cases h
        exact ⟨[.account src (fun x => x.withBalance
          ⟨(s.world.accounts src).balance.val - (s.world.accounts src).balance.val, by omega⟩),
          .account dst (fun x => x.withBalance
            ⟨(s.world.accounts dst).balance.val + (s.world.accounts src).balance.val, hc.2⟩)], rfl⟩
    · cases h

theorem destructTransfer_other (s out : ExecState D L T) (created : Bool)
    (src dst b : Address) (h : destructTransfer s created src dst = some out)
    (hs : b ≠ src) (hd : b ≠ dst) :
    out.world.accounts b = s.world.accounts b := by
  by_cases heq : src = dst
  · simp only [destructTransfer, heq, ↓reduceIte, Option.some.injEq] at h
    subst out
    exact selfBeneficiary_other s created dst b hd
  · simp only [destructTransfer, ExecState.transfer, heq, ↓reduceIte] at h
    split at h
    · cases h
      simp only [ExecState.apply, World.set_other _ hd, World.set_other _ hs]
    · cases h

/-- A successful child with its actual balance-changing output remains
rollbackable by the enclosing frame, before or after further caller writes. -/
theorem destructTransfer_outer_revert (entry out : ExecState D L T)
    (prior later : List (Op D L T)) (created : Bool) (src dst : Address)
    (h : destructTransfer (entry.run prior) created src dst = some out)
    (a c : Address) (v : Word) (input : Bytes) (static : Bool) :
    (entry.enter a c v input static).rollback
      (((entry.run prior).enter a c v input static).commit out |>.run later) = entry := by
  obtain ⟨ops, hout⟩ := destructTransfer_run _ _ _ _ _ h
  rw [hout]
  exact rollback_outer_after_commit entry prior ops later a c v input static

/-- An inner revert restores the actual nonempty caller prefix; an enclosing
revert then restores the earlier entry. The operation list is only the caller
prefix, not a substitute for proving the actual transfer output reversible. -/
theorem destructTransfer_prefix_revert (entry out : ExecState D L T)
    (prior : List (Op D L T)) (created : Bool) (src dst : Address)
    (h : destructTransfer (entry.run prior) created src dst = some out)
    (a c : Address) (v : Word) (input : Bytes) (static : Bool) :
    ((entry.run prior).enter a c v input static).rollback out = entry.run prior ∧
    (entry.enter a c v input static).rollback
      (((entry.run prior).enter a c v input static).rollback out) = entry := by
  have inner : ((entry.run prior).enter a c v input static).rollback out = entry.run prior :=
    rollback_destructTransfer _ _ _ _ _ h _ _ _ _ _
  refine ⟨inner, ?_⟩
  rw [inner]
  exact rollback_run _ _ _ _ _ _ _

theorem selfBeneficiary_outer_revert (entry : ExecState D L T)
    (prior later : List (Op D L T)) (created : Bool) (target a c : Address)
    (v : Word) (input : Bytes) (static : Bool) :
    (entry.enter a c v input static).rollback
      (((entry.run prior).enter a c v input static).commit
        (selfBeneficiary (entry.run prior) created target) |>.run later) = entry := by
  rw [selfBeneficiary_run]
  exact rollback_outer_after_commit _ _ _ _ _ _ _ _ _

end Solidity.Yul.World
