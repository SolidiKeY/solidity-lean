import Solidity.Source.World

/-! Consumers of the published independent source journal. An installation
operation below is a journalled account update, not Source.deploy/CREATE or a
constructor execution. No source/EVM simulation or failure bytes are supplied. -/
namespace Solidity.Backend.Executable.SourceJournal
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes)
variable {D : Layout} {L T : Address → SPath → STy}

/-- An actual funded transfer exposes its existing journal operation sequence.
This extracts a trace from the original function, not another payment runner. -/
theorem transfer_operations (s paid : ExecState D L T) (src dst : Address)
    (distinct : src ≠ dst) (amount : Word) (funded : s.transfer src dst amount = some paid) :
    ∃ ops : List (Op D L T), s.run ops = paid := by
  simp only [ExecState.transfer, distinct, if_false] at funded
  split at funded
  · rename_i valid
    cases funded
    exact ⟨[.account src (fun x => x.withBalance
        ⟨(s.world.accounts src).balance.val - amount.val, by omega⟩),
      .account dst (fun x => x.withBalance
        ⟨(s.world.accounts dst).balance.val + amount.val, valid.2⟩)], rfl⟩
  · cases funded

/-- Three actual boundaries: inner revert keeps payment; payment-frame revert
keeps earlier installation; outer revert removes that earlier prefix too. -/
theorem paid_inner_outer (s paid : ExecState D L T) (installOps : List (Op D L T))
    (src dst : Address) (distinct : src ≠ dst) (amount : Word)
    (funded : (s.run installOps).transfer src dst amount = some paid)
    (innerOps : List (Op D L T)) (this caller : Address) (input : Bytes) :
    (paid.enter this caller amount input false).rollback (paid.run innerOps) = paid ∧
    ((s.run installOps).enter this caller amount input false).rollback
      ((paid.enter this caller amount input false).rollback (paid.run innerOps)) = s.run installOps ∧
    (s.enter this caller amount input false).rollback
      (((s.run installOps).enter this caller amount input false).rollback
        ((paid.enter this caller amount input false).rollback (paid.run innerOps))) = s := by
  have inner := rollback_run paid innerOps this caller amount input false
  have payment := rollback_transfer (s.run installOps) paid distinct amount funded this caller input false
  rw [inner, payment]
  exact ⟨rfl,rfl,rollback_run s installOps this caller amount input false⟩

/-- A committed inner call and later writes are still undone by the outer
frame, including the actual paid transfer and earlier installation prefix. -/
theorem paid_commit_outer (s paid : ExecState D L T) (installOps : List (Op D L T))
    (src dst : Address) (distinct : src ≠ dst) (amount : Word)
    (funded : (s.run installOps).transfer src dst amount = some paid)
    (innerOps rest : List (Op D L T)) (this caller : Address) (input : Bytes) :
    (s.enter this caller amount input false).rollback
      (((paid.enter this caller amount input false).commit (paid.run innerOps)).run rest) = s := by
  obtain ⟨payments, actual⟩ := transfer_operations (s.run installOps) paid src dst distinct amount funded
  have joined : s.run (installOps ++ payments) = paid := by rw [run_append, actual]
  have rollback := rollback_outer_after_commit s (installOps ++ payments) innerOps rest this caller amount input false
  rw [joined] at rollback
  exact rollback

namespace Controls
def layout : Layout := ⟨fun _ => [], fun _ => 0, fun _ => .bool⟩
def cells : Address → SPath → STy := fun _ _ => .bool
def src : Address := ⟨1, by decide⟩
def dst : Address := ⟨2, by decide⟩
def zero : Word := ⟨0, by decide⟩
def one : Word := ⟨1, by decide⟩
def three : Word := ⟨3, by decide⟩
def initial : ExecState layout cells cells :=
  ⟨⟨fun a => {Account.empty (cells a) with balance := if a = src then three else zero}⟩, Transient.empty, []⟩
def installOps : List (Op layout cells cells) :=
  [.account dst (fun old => {old with nonce := 1, code := some 0})]
def installed := initial.run installOps
private def valueOr {α : Type} (r : Option α) (fallback : α) : α :=
  match r with | some value => value | none => fallback
private theorem recover {α : Type} (r : Option α) (fallback : α) (present : r.isSome = true) :
    r = some (valueOr r fallback) := by cases r with | some value => rfl | none => cases present

def paid : ExecState layout cells cells := valueOr (installed.transfer src dst one) installed
theorem funded : installed.transfer src dst one = some paid := recover _ _ (by decide +kernel)
def path : SPath := ⟨⟨some "Fixture", "cell"⟩, []⟩
def innerOps : List (Op layout cells cells) :=
  [.account dst (fun old => {old with storage := old.storage.write path (.bool true)}),
   .transient dst (fun old => old.write path (.bool true))]
def rest : List (Op layout cells cells) := [.account src (fun old => {old with nonce := 9})]

theorem actual_boundaries :
    (paid.enter dst src one [] false).rollback (paid.run innerOps) = paid ∧
    (installed.enter dst src one [] false).rollback ((paid.enter dst src one [] false).rollback (paid.run innerOps)) = installed ∧
    (initial.enter dst src one [] false).rollback
      ((installed.enter dst src one [] false).rollback ((paid.enter dst src one [] false).rollback (paid.run innerOps))) = initial :=
  paid_inner_outer initial paid installOps src dst (by decide) one funded innerOps dst src []

theorem actual_commit_rollback : (initial.enter dst src one [] false).rollback
    (((paid.enter dst src one [] false).commit (paid.run innerOps)).run rest) = initial :=
  paid_commit_outer initial paid installOps src dst (by decide) one funded innerOps rest dst src []

example : ((paid.world.accounts src).balance.val, (paid.world.accounts dst).balance.val) = (2,1) ∧
    (paid.world.accounts dst).code = some 0 ∧ (paid.world.accounts dst).nonce = 1 ∧ paid.journal.length = 3 := by decide +kernel
private def boolOf {D : Layout} : Option (Val D .bool) → Option Bool
  | some (.bool value) => some value | none => none
private theorem recover_bool {D : Layout} (v : Option (Val D .bool)) (b : Bool)
    (observed : boolOf v = some b) : v = some (.bool b) := by
  cases v with
  | none => cases observed
  | some value =>
    cases value with
    | bool actual => cases Option.some.inj observed; rfl
    | memRef h _ => cases h
    | storRef h _ => cases h
    | cdRef h _ => cases h

example : ((paid.run innerOps).world.accounts dst).storage.read path = some (.bool true) ∧
    ((paid.run innerOps).transient.cells dst).read path = some (.bool true) ∧
    (paid.run innerOps).journal.length = 5 := by
  refine ⟨?_,?_,by decide +kernel⟩
  · apply recover_bool; decide +kernel
  · apply recover_bool; decide +kernel
example : (paid.world.accounts dst).storage.read path = some (.bool false) ∧
    (paid.transient.cells dst).read path = some (.bool false) ∧
    (initial.world.accounts dst).code = none := by
  refine ⟨?_,?_,by decide +kernel⟩
  · apply recover_bool; decide +kernel
  · apply recover_bool; decide +kernel
example : (paid.transfer src dst three).isNone = true := by decide +kernel
example : (paid.transfer src src three).isNone = true ∧
    (paid.transfer src src one).isSome = true := by decide +kernel
def full : ExecState layout cells cells := paid.apply (.account dst (fun old =>
  {old with balance := ⟨2^256-1, by decide +kernel⟩}))
example : (full.transfer src dst one).isNone = true ∧
    one.val ≤ (full.world.accounts src).balance.val := by decide +kernel
theorem self_identity : paid.transfer src src one = some paid := by
  have enough : one.val ≤ (paid.world.accounts src).balance.val := by decide +kernel
  simp only [ExecState.transfer, if_pos enough, if_true]

def committed : ExecState layout cells cells :=
  ((paid.enter dst src one [] false).commit (paid.run innerOps)).run rest
example : (committed.world.accounts src).nonce = 9 ∧ committed.journal.length = 6 := by decide +kernel

/-- The retained inner checkpoint and the restored outer checkpoint differ. -/
theorem checkpoints_distinct : initial ≠ paid := by
  have different : (initial.world.accounts dst).code ≠ (paid.world.accounts dst).code := by decide +kernel
  intro same
  exact different (congrArg (fun state : ExecState layout cells cells => (state.world.accounts dst).code) same)
example : (paid.enter dst src one [] false).rollback (paid.run innerOps) ≠ initial := by
  rw [actual_boundaries.1]
  exact fun same => checkpoints_distinct same.symm
end Controls
/-- info: 'Solidity.Backend.Executable.SourceJournal.transfer_operations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transfer_operations
/-- info: 'Solidity.Backend.Executable.SourceJournal.paid_inner_outer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms paid_inner_outer
/-- info: 'Solidity.Backend.Executable.SourceJournal.paid_commit_outer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms paid_commit_outer
/-- info: 'Solidity.Backend.Executable.SourceJournal.Controls.actual_boundaries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Controls.actual_boundaries
/-- info: 'Solidity.Backend.Executable.SourceJournal.Controls.actual_commit_rollback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Controls.actual_commit_rollback
/-- info: 'Solidity.Backend.Executable.SourceJournal.Controls.checkpoints_distinct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Controls.checkpoints_distinct
end Solidity.Backend.Executable.SourceJournal
