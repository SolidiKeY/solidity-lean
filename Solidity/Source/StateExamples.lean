import Solidity.Source.World
import Solidity.Source.Observe

/-!
# S04.01–S04.03 controls: inhabited state, observations and frames

Each relation of `Solidity/Source/State.lean`, `Observe.lean` and
`World.lean` on concrete data: a memory copy independent of its source,
nested memory aliasing through a pointer, storage round trips, decoded and
rejected ABI words, panic and error data, transfers, and a reverted call
undoing its storage and transient changes.
-/

namespace Solidity.Source.StateExamples

open Solidity.Source
open Solidity.Roadmap (Address Word)

/-- A layout with no structs, enums or user-defined value types. -/
def D₀ : Layout := ⟨fun _ => [], fun _ => 0, fun _ => .bool⟩

/-- `uint256 7` and `uint256 8`. -/
def seven : Val D₀ (.int IntTy.u256) := .int 7 (by decide)
def eight : Val D₀ (.int IntTy.u256) := .int 8 (by decide)

/-- `uint256[] memory` and `uint256[][] memory`. -/
def arrTy : STy := .array .memory (.int IntTy.u256) none
def arr2Ty : STy := .array .memory arrTy none

/-- `[x]`. -/
def single (x : Val D₀ (.int IntTy.u256)) : Data D₀ arrTy :=
  .array 1 (fun _ h => nomatch h) (fun _ => .val x)

/-- A heap with `b = [7]` at 0 and `a = [b]` at 1 (`a`'s element a
pointer to `b`). -/
def heap : Heap D₀ :=
  let h₁ := (Heap.empty.alloc ⟨arrTy, single seven⟩).1
  (h₁.alloc ⟨arr2Ty, .array 1 (fun _ h => nomatch h) (fun _ => .val (.memRef rfl 0))⟩).1

/-- **Nested aliasing**: `b[0] = 8` changes `b`, and `a` still points to
`b`, so `a[0][0]` reads 8. -/
theorem alias_seen :
    (heap.write 0 (single eight) rfl).get 0 = some ⟨arrTy, single eight⟩ ∧
      (heap.write 0 (single eight) rfl).get 1 = heap.get 1 :=
  ⟨Heap.write_get _ _ _ _, Heap.write_other _ (by decide) _ _⟩

/-- **A copy is independent**: copying `b` and writing the copy leaves `b`. -/
theorem copy_independent :
    (((heap.alloc ⟨arrTy, single seven⟩).1).write (heap.alloc ⟨arrTy, single seven⟩).2
      (single eight) rfl).get 0 = some ⟨arrTy, single seven⟩ :=
  Heap.copy_independent heap rfl _ _

/-- Every storage path of the example holds a `uint256`. -/
def L₀ : SPath → STy := fun _ => .int IntTy.u256

/-- State variable `count` of `Counter`. -/
def countPath : SPath := ⟨⟨some "Counter", "count"⟩, []⟩

/-- **Storage reads back a write, and the default elsewhere.** -/
theorem storage_roundtrip :
    ((Storage.empty : Storage D₀ L₀).write countPath seven).read countPath = some seven ∧
      (Storage.empty : Storage D₀ L₀).read ⟨⟨some "Counter", "other"⟩, []⟩ =
        some (.int 0 (IntTy.zero_mem _)) :=
  ⟨Storage.write_read _ _ _, rfl⟩

/-- **Overflow and division by zero are different revert outcomes.** -/
theorem arith_ne_divZero : revertOutcome (panicData .arithmetic) ≠ revertOutcome (panicData .divZero) :=
  fun h => nomatch panic_distinct h

/-- The arithmetic panic's code reads back. -/
theorem panic_arith_code : beValue ((panicData .arithmetic).drop 4) = 0x11 := panicData_code _

/-- `require(false, "no")`'s data starts with `Error(string)`'s selector. -/
theorem error_prefix : (errorData [110, 111]).take 4 = errorSelector := errorData_prefix _

/-- The ABI word of `int8 -1` decodes as `-1`. -/
theorem minusOne_word :
    (Val.int (D := D₀) (t := IntTy.mk true 8 (by decide)) (-1) (by decide)).word.bind
      (readInt ⟨true, 8, by decide⟩) = some (-1) :=
  Val.word_int _ _

/-- An address. -/
def addr (n : Nat) (h : n < 2 ^ 160 := by decide) : Address := ⟨n, h⟩

/-- Every instance's layouts. -/
def LW : Address → SPath → STy := fun _ => L₀

/-- Instance 1's account: 100 wei and `count = 7`. -/
def acc₁ : Account D₀ L₀ := ⟨⟨100, by decide⟩, 0, none, Storage.empty.write countPath seven⟩

/-- Instance 1 holds `acc₁`, every other address nothing; the journal is
empty. -/
def s₀ : ExecState D₀ LW LW :=
  ⟨⟨fun a => if a.val = 1 then acc₁ else Account.empty L₀⟩, Transient.empty, []⟩

/-- **A transfer the sender cannot afford fails**; one it can moves both
balances. -/
theorem transfers :
    (s₀.transfer (addr 1) (addr 2) ⟨200, by decide⟩).isNone = true ∧
      ((s₀.transfer (addr 1) (addr 2) ⟨30, by decide⟩).map fun s =>
        ((s.world.accounts (addr 1)).balance.val, (s.world.accounts (addr 2)).balance.val)) = some (70, 30) := by
  decide

/-- The operations of a call that sets `count = 8` and a transient slot. -/
def callOps : List (Op D₀ LW LW) :=
  [.account (addr 1) fun x => { x with storage := x.storage.write countPath eight },
   .transient (addr 1) fun t => t.write countPath eight]

/-- **A reverted call undoes its writes**: after the call's operations, the
rollback reads `count = 7` again, and the transient slot its default. -/
theorem revert_undoes :
    let f := s₀.enter (addr 1) (addr 2) ⟨0, by decide⟩ [] false
    ((f.rollback (s₀.run callOps)).world.accounts (addr 1)).storage.read countPath = some seven ∧
      ((f.rollback (s₀.run callOps)).transient.cells (addr 1)).read countPath =
        some (.int 0 (IntTy.zero_mem _)) := by
  simp only [rollback_run]
  exact ⟨rfl, rfl⟩

/-- Without the revert, the call's write is visible. -/
theorem commit_visible :
    ((s₀.run callOps).world.accounts (addr 1)).storage.read countPath = some eight := rfl

/-- **Transient storage is cleared between transactions**; the world is
kept. -/
theorem endTx_clears :
    ((s₀.run callOps).endTx.transient.cells (addr 1)).read countPath = some (.int 0 (IntTy.zero_mem _)) ∧
      ((s₀.run callOps).endTx.world.accounts (addr 1)).storage.read countPath = some eight :=
  ⟨rfl, rfl⟩

end Solidity.Source.StateExamples

/-- info: 'Solidity.Source.Heap.copy_independent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.Heap.copy_independent
/-- info: 'Solidity.Source.Storage.write_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.Storage.write_read
/-- info: 'Solidity.Source.panic_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.panic_distinct
/-- info: 'Solidity.Source.Val.word_int' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.Val.word_int
/-- info: 'Solidity.Source.rollback_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.rollback_run
/-- info: 'Solidity.Source.rollback_transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.rollback_transfer
/-- info: 'Solidity.Source.StateExamples.revert_undoes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.StateExamples.revert_undoes
/-- info: 'Solidity.Source.StateExamples.transfers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.StateExamples.transfers
