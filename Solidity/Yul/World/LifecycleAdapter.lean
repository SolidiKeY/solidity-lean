import Solidity.Yul.World.Lifecycle

/-! # Known-account SELFDESTRUCT effect composition
This composes the actual existing typed transfer and lifecycle functions. It is
not environment beneficiary credit, frame/source admission or reachability of
arbitrary supplied metadata. Successful SELFDESTRUCT terminates its frame.
-/
namespace Solidity.Yul.World
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
variable {D : Layout} {L T : Address → SPath → STy}

/-- Known typed-account destruction; static rejection and real transfer failure
are retained as missing normal transitions, not callee revert outcomes. -/
def Lifecycle.destructKnown (s : Lifecycle D L T) (static : Bool) (source beneficiary : Address) :
    Option (Lifecycle D L T) :=
  if static then none else do
    let execution ← destructTransfer s.execution (s.created source) source beneficiary
    ({ s with execution := execution }).schedule false source

/-- A successful destruction ends the callee with empty return bytes. -/
def Lifecycle.destructTerminate (s : Lifecycle D L T) (static : Bool) (source beneficiary : Address) :
    Option (Lifecycle D L T × Outcome) :=
  (s.destructKnown static source beneficiary).map (fun after => (after, .success []))

theorem destructKnown_static (s : Lifecycle D L T) (source beneficiary : Address) :
    s.destructKnown true source beneficiary = none := rfl

theorem destructKnown_exact (s : Lifecycle D L T) (execution : ExecState D L T)
    (source beneficiary : Address)
    (h : destructTransfer s.execution (s.created source) source beneficiary = some execution) :
    s.destructKnown false source beneficiary =
      ({ s with execution := execution }).schedule false source := by
  simp only [Lifecycle.destructKnown, Bool.false_eq_true, ↓reduceIte, h, bind, Option.bind_some]

/-- The execution and metadata are derived from the actual successful output,
not supplied as an unproved world-adequacy wrapper. -/
theorem destructKnown_success (s after : Lifecycle D L T) (static : Bool) (source beneficiary : Address)
    (h : s.destructKnown static source beneficiary = some after) :
    static = false ∧
    destructTransfer s.execution (s.created source) source beneficiary = some after.execution ∧
    after.created = s.created ∧ after.doomed source = (s.doomed source || s.created source) ∧
    (∀ other, other ≠ source → after.doomed other = s.doomed other) := by
  cases static with
  | true => cases h
  | false =>
    cases ht : destructTransfer s.execution (s.created source) source beneficiary with
    | none =>
      simp only [Lifecycle.destructKnown, Bool.false_eq_true, ↓reduceIte, ht, bind, Option.bind_none] at h
      cases h
    | some execution =>
      rw [destructKnown_exact s execution source beneficiary ht] at h
      have hs := schedule_exact { s with execution := execution } after false source h
      refine ⟨rfl, ?_, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩
      rw [hs.2.1]

/-- Journal rollback consumes the actual post-destruction state, including
its nonzero burn/transfer. Earlier caller entries are never assumed empty. -/
theorem destructKnown_rollback (s after : Lifecycle D L T) (static : Bool) (source beneficiary : Address)
    (h : s.destructKnown static source beneficiary = some after)
    (a c : Address) (value : Word) (input : Bytes) (frameStatic : Bool) :
    (s.execution.enter a c value input frameStatic).rollback after.execution = s.execution :=
  rollback_destructTransfer _ _ _ _ _ (destructKnown_success _ _ _ _ _ h).2.1 _ _ _ _ _

/-- Metadata snapshots are transaction/frame local. Only metadata is restored
by the snapshot definition; the actual returned execution is journal-rolled. -/
def Lifecycle.rollbackDestruction (entry after : Lifecycle D L T)
    (a c : Address) (value : Word) (input : Bytes) (static : Bool) : Lifecycle D L T :=
  { entry with execution := (entry.execution.enter a c value input static).rollback after.execution }

theorem destructKnown_rollback_all (s after : Lifecycle D L T) (static : Bool) (source beneficiary : Address)
    (h : s.destructKnown static source beneficiary = some after)
    (a c : Address) (value : Word) (input : Bytes) (frameStatic : Bool) :
    s.rollbackDestruction after a c value input frameStatic = s := by
  simp only [Lifecycle.rollbackDestruction, destructKnown_rollback _ _ _ _ _ h]

/-- Only accounts actually created and scheduled in this transaction disappear. -/
theorem destructKnown_fresh_finish (s after : Lifecycle D L T) (static : Bool) (source beneficiary : Address)
    (h : s.destructKnown static source beneficiary = some after) (created : s.created source = true) :
    after.finish.execution.world.accounts source = Account.empty (L source) := by
  have hs := destructKnown_success _ _ _ _ _ h
  apply finish_created_doomed
  · rw [hs.2.2.1]
    exact created
  · rw [hs.2.2.2.1, created, Bool.or_true]

theorem destructKnown_old_finish (s after : Lifecycle D L T) (static : Bool) (source beneficiary : Address)
    (h : s.destructKnown static source beneficiary = some after) (created : s.created source = false) :
    after.finish.execution.world.accounts source = after.execution.world.accounts source := by
  apply finish_old
  rw [(destructKnown_success _ _ _ _ _ h).2.2.1]
  exact created

/-- Full records at addresses outside both endpoints survive the actual step. -/
theorem destructKnown_other (s after : Lifecycle D L T) (static : Bool) (source beneficiary other : Address)
    (h : s.destructKnown static source beneficiary = some after)
    (hs : other ≠ source) (hb : other ≠ beneficiary) :
    after.execution.world.accounts other = s.execution.world.accounts other :=
  destructTransfer_other _ _ _ _ _ _ (destructKnown_success _ _ _ _ _ h).2.1 hs hb

/-- Successful child destruction stays in the enclosing journal. Caller writes
before/after the child are rolled back at the actual outer entry, with its
metadata snapshot; the existing caller journal may already be nonempty. -/
theorem destructKnown_outer_rollback (entry after : Lifecycle D L T)
    (prior later : List (Op D L T)) (static : Bool) (source beneficiary : Address)
    (h : ({ entry with execution := entry.execution.run prior }).destructKnown static source beneficiary = some after)
    (a c : Address) (value : Word) (input : Bytes) (frameStatic : Bool) :
    entry.rollbackDestruction { after with execution := after.execution.run later }
      a c value input frameStatic = entry := by
  have ht := (destructKnown_success _ _ _ _ _ h).2.1
  have hr := destructTransfer_outer_revert entry.execution after.execution prior later (entry.created source)
    source beneficiary ht a c value input frameStatic
  simpa only [Lifecycle.rollbackDestruction, CallFrame.commit] using
    congrArg (fun execution => { entry with execution := execution }) hr

/-- Inversion of the actual terminating transition retains its exact outcome. -/
theorem destructTerminate_success (s : Lifecycle D L T) (static : Bool) (source beneficiary : Address)
    (result : Lifecycle D L T × Outcome)
    (h : s.destructTerminate static source beneficiary = some result) :
    s.destructKnown static source beneficiary = some result.1 ∧ result.2 = .success [] := by
  cases hk : s.destructKnown static source beneficiary with
  | none => simp only [Lifecycle.destructTerminate, hk, Option.map_none] at h; cases h
  | some after =>
    simp only [Lifecycle.destructTerminate, hk, Option.map_some, Option.some.injEq] at h
    cases h
    exact ⟨rfl, rfl⟩

/-- Lean-only terminating rule over the actual function, not a source dl rule.
Both state and outcome are fixed; successful SELFDESTRUCT cannot continue with
an arbitrary return buffer or be relabelled as a reverted call. -/
theorem destruct_termination_rule (s after : Lifecycle D L T) (static : Bool) (source beneficiary : Address)
    (h : s.destructKnown static source beneficiary = some after) :
    ∀ result, s.destructTerminate static source beneficiary = some result → result = (after, .success []) := by
  intro result hr
  rw [Lifecycle.destructTerminate, h, Option.map_some] at hr
  exact (Option.some.inj hr).symm

theorem static_destruction_rule (s : Lifecycle D L T) (source beneficiary : Address) :
    ∀ result, s.destructTerminate true source beneficiary ≠ some result := by
  intro result h
  cases h

/-- Opcode-facing context adapter: SELFDESTRUCT affects the frame's storage
address, even when delegatecall selected code from a different address. -/
def Lifecycle.destructAtFrame (s : Lifecycle D L T) (frame : CallFrame) (beneficiary : Address) :
    Option (Lifecycle D L T × Outcome) :=
  s.destructTerminate frame.static frame.this beneficiary

theorem destructAtFrame_static (s : Lifecycle D L T) (frame : CallFrame) (beneficiary : Address)
    (h : frame.static = true) : s.destructAtFrame frame beneficiary = none := by
  simp only [Lifecycle.destructAtFrame, h]
  rfl

end Solidity.Yul.World
