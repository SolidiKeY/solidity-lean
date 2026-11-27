import Solidity.Source.World
import Solidity.Source.Observe


namespace Solidity.Source.StateExamples

open Solidity.Source
open Solidity.Roadmap (Address Word)

def D₀ : Layout := ⟨fun _ => [], fun _ => 0, fun _ => .bool⟩

def seven : Val D₀ (.int IntTy.u256) := .int 7 (by decide)
def eight : Val D₀ (.int IntTy.u256) := .int 8 (by decide)

def arrTy : STy := .array .memory (.int IntTy.u256) none
def arr2Ty : STy := .array .memory arrTy none

def single (x : Val D₀ (.int IntTy.u256)) : Data D₀ arrTy :=
  .array 1 (fun _ h => nomatch h) (fun _ => .val x)

def heap : Heap D₀ :=
  let h₁ := (Heap.empty.alloc ⟨arrTy, single seven⟩).1
  (h₁.alloc ⟨arr2Ty, .array 1 (fun _ h => nomatch h) (fun _ => .val (.memRef rfl 0))⟩).1

theorem alias_seen :
    (heap.write 0 (single eight) rfl).get 0 = some ⟨arrTy, single eight⟩ ∧
      (heap.write 0 (single eight) rfl).get 1 = heap.get 1 :=
  ⟨Heap.write_get _ _ _ _, Heap.write_other _ (by decide) _ _⟩

example :
    let changed := heap.write 0 (single eight) rfl
    (match changed.get 1 with
    | some ⟨_, .array 1 _ outer⟩ =>
      match outer 0 with
      | .val (.memRef _ address) =>
        match changed.get address with
        | some ⟨_, .array 1 _ inner⟩ =>
          match inner 0 with
          | .val (.int value _) => some value
          | _ => none
        | _ => none
      | _ => none
    | _ => none) = some 8 := by
  rfl

theorem copy_independent :
    (((heap.alloc ⟨arrTy, single seven⟩).1).write (heap.alloc ⟨arrTy, single seven⟩).2
      (single eight) rfl).get 0 = some ⟨arrTy, single seven⟩ :=
  Heap.copy_independent heap rfl _ _

def L₀ : SPath → STy := fun _ => .int IntTy.u256

def countPath : SPath := ⟨⟨some "Counter", "count"⟩, []⟩

theorem storage_roundtrip :
    ((Storage.empty : Storage D₀ L₀).write countPath seven).read countPath = some seven ∧
      (Storage.empty : Storage D₀ L₀).read ⟨⟨some "Counter", "other"⟩, []⟩ =
        some (.int 0 (IntTy.zero_mem _)) :=
  ⟨Storage.write_read _ _ _, rfl⟩

theorem arith_ne_divZero : revertOutcome (panicData .arithmetic) ≠ revertOutcome (panicData .divZero) :=
  fun h => nomatch panic_distinct h

theorem panic_arith_code : beValue ((panicData .arithmetic).drop 4) = 0x11 := panicData_code _

theorem error_prefix : (errorData [110, 111]).take 4 = errorSelector := errorData_prefix _

theorem minusOne_word :
    (Val.int (D := D₀) (t := IntTy.mk true 8 (by decide)) (-1) (by decide)).word.bind
      (readInt ⟨true, 8, by decide⟩) = some (-1) :=
  Val.word_int _ _

def addr (n : Nat) (h : n < 2 ^ 160 := by decide) : Address := ⟨n, h⟩

def LW : Address → SPath → STy := fun _ => L₀

def acc₁ : Account D₀ L₀ := ⟨100, 0, none, Storage.empty.write countPath seven⟩

def s₀ : ExecState D₀ LW LW :=
  ⟨⟨fun a => if a.val = 1 then acc₁ else Account.empty L₀⟩, Transient.empty, []⟩

theorem transfers :
    (s₀.transfer (addr 1) (addr 2) ⟨200, by decide⟩).isNone = true ∧
      ((s₀.transfer (addr 1) (addr 2) ⟨30, by decide⟩).map fun s =>
        ((s.world.accounts (addr 1)).balance, (s.world.accounts (addr 2)).balance)) = some (70, 30) := by
  decide

def callOps : List (Op D₀ LW LW) :=
  [.account (addr 1) fun x => { x with storage := x.storage.write countPath eight },
   .transient (addr 1) fun t => t.write countPath eight]

theorem revert_undoes :
    let f := s₀.enter (addr 1) (addr 2) ⟨0, by decide⟩ [] false
    ((f.rollback (s₀.run callOps)).world.accounts (addr 1)).storage.read countPath = some seven ∧
      ((f.rollback (s₀.run callOps)).transient.cells (addr 1)).read countPath =
        some (.int 0 (IntTy.zero_mem _)) := by
  simp only [rollback_run]
  exact ⟨rfl, rfl⟩

theorem commit_visible :
    ((s₀.run callOps).world.accounts (addr 1)).storage.read countPath = some eight := rfl

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
/-- info: 'Solidity.Source.StateExamples.transfers' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Source.StateExamples.transfers
