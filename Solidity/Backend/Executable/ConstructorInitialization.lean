import Solidity.Backend.Executable.ConstructorStorageFailure

/-! Exact native initializer composition and its ordering relative to failed
base arguments. Programs are supplied typed fixtures; no canonical elaboration,
source-to-backend lowering or transaction rollback is claimed. -/
namespace Solidity.Backend.Executable.ConstructorInitialization
open Solidity Source

/-- Splitting the existing initializer list preserves its entire computation,
including ordered state effects and the exact first halt. -/
theorem append (G : Glob E) (F : Fr) (n : Nat) (xs ys : List (RInit E)) :
    runInits G F n (xs ++ ys) = (do runInits G F n xs; runInits G F n ys) := by
  induction xs with
  | nil => simp only [List.nil_append,runInits,pure_bind]
  | cons x xs ih => simp only [List.cons_append,runInits,ih,bind_assoc]

namespace Controls
namespace Prior
abbrev E := ConstructorStorageFailure.E
abbrev saved := ConstructorStorageFailure.saved
abbrev caller := ConstructorStorageFailure.caller
abbrev frame := ConstructorStorageFailure.Prior.frame
abbrev before := ConstructorStorageFailure.before
abbrev arguments := ConstructorStorageFailure.arguments
end Prior
open Prior

def initializer : RInit E :=
  ⟨saved,.int IntTy.u8,rfl,.conv (.const (Q.ofInt 7)) (.inl (by decide))⟩
def program : Program E :=
  { ConstructorStorageFailure.program with
    inits name := if name = "Base" then [initializer] else [] }
def global (p : Roadmap.Pipeline) : Glob E :=
  { ConstructorStorageFailure.global p with prog := program }
def initialized : St E :=
  { before with ex := before.ex.apply (.account frame.this (fun account =>
    { account with storage := account.storage.write saved.path (.int 7 (by decide)) })) }
def legacy : St E :=
  { initialized with ex := initialized.ex.apply (.account frame.this (fun account =>
    { account with storage := account.storage.write saved.path (.int 248 (by decide)) })) }

def initializedAgain : St E :=
  { initialized with ex := initialized.ex.apply (.account frame.this (fun account =>
    { account with storage := account.storage.write saved.path (.int 7 (by decide)) })) }

theorem init_run (p : Roadmap.Pipeline) :
    (runInits (global p) frame 4 [initializer]).run (L0 E,before) =
    (.ok (), (L0 E,initialized)) := by
  cases p <;> rfl

/-- Both nonempty initializer segments execute; an equal stored value does
not permit deduplicating their journal effects. -/
theorem split_init_run (p : Roadmap.Pipeline) :
    (runInits (global p) frame 4 ([initializer] ++ [initializer])).run (L0 E,before) =
    (.ok (), (L0 E,initializedAgain)) := by
  rw [append]
  cases p <;> rfl

theorem arguments_after_init (p : Roadmap.Pipeline) :
    (evalConvArgs (global p) frame 4 arguments).run (caller,initialized) =
    (.error (.revert (panicData .arithmetic)), (caller,legacy)) := by
  cases p <;> rfl

theorem legacy_failure :
    (construct (global .legacy) frame 4 "Derived" caller).run (L0 E,before) =
    (.error (.revert (panicData .arithmetic)), (L0 E,legacy)) := by rfl

theorem viaIR_failure :
    (construct (global .viaIR) frame 4 "Derived" caller).run (L0 E,before) =
    (.error (.revert (panicData .arithmetic)), (L0 E,ConstructorStorageFailure.written)) := by rfl

theorem observations :
    (initialized.ex.world.accounts frame.this).storage.read saved.path = some (.int 7 (by decide)) ∧
    (legacy.ex.world.accounts frame.this).storage.read saved.path = some (.int 248 (by decide)) ∧
    initialized.ex.journal.length = 2 ∧ legacy.ex.journal.length = 3 ∧
    ConstructorStorageFailure.written.ex.journal.length = 2 ∧
    legacy.heap = before.heap ∧
    caller.get (Idx.there (Idx.there Idx.here)) = .memRef rfl 0 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Matching panic bytes do not authorize equating the returned full states. -/
theorem different_states : legacy ≠ ConstructorStorageFailure.written := by
  intro same
  have counts := congrArg (fun s : St E => s.ex.journal.length) same
  change (3 : Nat) = 2 at counts
  omega

theorem repeat_not_idempotent : initializedAgain ≠ initialized := by
  intro same
  have counts := congrArg (fun s : St E => s.ex.journal.length) same
  change (3 : Nat) = 2 at counts
  omega

end Controls
end Solidity.Backend.Executable.ConstructorInitialization
