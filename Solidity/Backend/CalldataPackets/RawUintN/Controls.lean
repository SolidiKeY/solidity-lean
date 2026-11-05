import Solidity.Backend.CalldataPackets.RawUintN.Execution
import Solidity.Backend.CalldataPackets.RawUint.Controls

/-! Inhabited clean/dirty/zero/padding/entry-order and resolved conversion controls.
All byte observations are kernel checked; no native_decide or assumed run. -/
namespace Solidity.Backend.CalldataPackets.RawUintN.Controls
open Solidity.Backend.MemoryOps
abbrev E0 := RawUint.Controls.E0
abbrev old := RawUint.Controls.old
abbrev frame := RawUint.Controls.frame

def u8 : Width := ⟨8, by decide, by decide, by decide⟩
def u16 : Width := ⟨16, by decide, by decide, by decide⟩
def u248 : Width := ⟨248, by decide, by decide, by decide⟩

def raw : Source.Fr := frame ([171,205,239] ++ Source.natBytes 32 7 ++ Source.natBytes 32 255)
def dirtySecond : Source.Fr := frame (Source.natBytes 32 7 ++ Source.natBytes 32 256)
def cleanValues : List (Source.Val E0.layout (.int u8.intTy)) :=
  [.int 7 (by decide), .int 255 (by decide)]

theorem prefix_values : values E0.layout u8 raw 3 2 = .ok cleanValues := by rfl

theorem prefix_copy : (Source.cdToMem raw (ArrayTy u8) 3 2).run old =
    (.ok (.val (.memRef rfl old.2.heap.next)),
      (old.1,{old.2 with heap := (old.2.heap.alloc ⟨ArrayTy u8,memory E0.layout u8 cleanValues⟩).1})) := by
  rw [copy_run, prefix_values]

theorem keeps_old : ((Source.cdToMem raw (ArrayTy u8) 3 2).run old).2.2.heap.get 0 =
    old.2.heap.get 0 := (copy_state u8 raw 3 2 old).2.2 0 (by decide)

theorem unequal_values : (7 : Nat) ≠ 255 := by decide

theorem dirty_second : (Source.cdToMem dirtySecond (ArrayTy u8) 0 2).run old =
    (.error (.revert []),old) :=
  dirty_copy u8 dirtySecond 0 2 1 (by decide) (by decide) old

theorem dirty_first : (Source.cdToMem (frame (Source.natBytes 32 256)) (ArrayTy u8) 0 1).run old =
    (.error (.revert []),old) :=
  dirty_copy u8 _ 0 1 0 (by decide) (by decide) old

theorem wide_clean : values E0.layout u16 dirtySecond 0 2 =
    .ok [.int 7 (by decide),.int 256 (by decide)] := by rfl

theorem largest_clean : values E0.layout u248 (frame (Source.natBytes 32 (2^248-1))) 0 1 =
    .ok [.int (2^248-1 : Nat) (by decide)] := by rfl

theorem largest_dirty :
    (Source.cdToMem (frame (Source.natBytes 32 (2^248))) (ArrayTy u248) 0 1).run old =
      (.error (.revert []),old) :=
  dirty_copy u248 _ 0 1 0 (by decide) (by decide) old

theorem padded_zeros : values E0.layout u8 (frame []) 123 2 =
    .ok [.int 0 (by decide),.int 0 (by decide)] := by rfl

theorem partial_dirty : (Source.cdToMem (frame [1]) (ArrayTy u8) 0 1).run old =
    (.error (.revert []),old) :=
  dirty_copy u8 _ 0 1 0 (by decide) (by decide) old

theorem empty_allocates :
    (Source.cdToMem (frame []) (ArrayTy u8) 17 0).run old =
      (.ok (.val (.memRef rfl old.2.heap.next)),
        (old.1,{old.2 with heap := (old.2.heap.alloc ⟨ArrayTy u8,memory E0.layout u8 []⟩).1})) :=
  empty_copy u8 _ 17 old

theorem truncated_entry :
    ((Source.EM.lift (Source.cdTail RawUint.Controls.truncated 0 32)) >>= fun p =>
      Source.cdToMem dirtySecond (ArrayTy u8) p.1 p.2).run old =
        (.error (.revert []),old) := by
  rw [guarded_run, RawUint.Controls.entry_truncated]

theorem missing_entry :
    ((Source.EM.lift (Source.cdTail [] 0 32)) >>= fun p =>
      Source.cdToMem raw (ArrayTy u8) p.1 p.2).run old = (.error (.revert []),old) := by
  rw [guarded_run, RawUint.Controls.missing_length_word]

theorem full_entry :
    ((Source.EM.lift (Source.cdTail RawUint.Controls.args 0 32)) >>= fun p =>
      Source.cdToMem RawUint.Controls.full (ArrayTy u8) p.1 p.2).run old =
      (.ok (.val (.memRef rfl old.2.heap.next)),
        (old.1,{old.2 with heap := (old.2.heap.alloc
          ⟨ArrayTy u8,memory E0.layout u8 [.int 7 (by decide),.int 42 (by decide)]⟩).1})) := by
  rw [guarded_run, RawUint.Controls.entry_full]
  dsimp only
  rw [copy_run]
  rfl

def dirtyArgs : List UInt8 := Source.natBytes 32 32 ++ Source.natBytes 32 2 ++
  Source.natBytes 32 7 ++ Source.natBytes 32 256

private theorem dirty_args_off : Source.wordAt dirtyArgs 0 = 32 := by decide
private theorem dirty_args_len : Source.wordAt (dirtyArgs.drop 32) 0 = 2 := by decide
private theorem dirty_args_length : dirtyArgs.length = 128 := by
  simp only [dirtyArgs, Source.natBytes, List.length_append, Source.beBytes_length]

theorem dirty_entry_head : Source.cdTail dirtyArgs 0 32 = .ok (68,2) := by
  unfold Source.cdTail
  rw [dirty_args_off, dirty_args_length]
  dsimp only
  rw [dirty_args_len]
  rfl

theorem dirty_entry :
    ((Source.EM.lift (Source.cdTail dirtyArgs 0 32)) >>= fun p =>
      Source.cdToMem (frame (RawUint.Controls.selectorBytes ++ dirtyArgs)) (ArrayTy u8) p.1 p.2).run old =
        (.error (.revert []),old) := by
  rw [guarded_run, dirty_entry_head]
  exact dirty_copy u8 _ 68 2 1 (by decide) (by decide) old

/-- A dirty word is refused, not silently reduced modulo the narrow width. -/
theorem no_masking : element E0.layout u8 256 = .error (.revert []) := by rfl

theorem wrong_order_rejected :
    cleanValues.map Source.Val.word ≠ [some (Source.toWord 255),some (Source.toWord 7)] := by decide

def localState : Source.EMState E0 [.array .calldata (.int u8.intTy) none] :=
  (.cons (.cdRef rfl 3 2) .nil,old.2)

theorem local_expression (G : Source.Glob E0) (fuel : Nat) :
    (Source.evalE G raw (fuel+2) (copyExpr u8 .here)).run localState =
      (.ok (.val (.memRef rfl localState.2.heap.next)),
        (localState.1,{localState.2 with heap := (localState.2.heap.alloc
          ⟨ArrayTy u8,memory E0.layout u8 cleanValues⟩).1})) := by
  rw [eval_copy u8 G raw fuel localState .here 3 2 rfl, copy_run, prefix_values]

theorem zero_horizon (G : Source.Glob E0) :
    (Source.evalE G raw 0 (copyExpr u8 .here)).run localState = (.error .timeout,localState) := rfl

theorem one_horizon (G : Source.Glob E0) :
    (Source.evalE G raw 1 (copyExpr u8 .here)).run localState = (.error .timeout,localState) := rfl

/-- info: 'Solidity.Backend.CalldataPackets.RawUintN.Controls.prefix_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_copy
/-- info: 'Solidity.Backend.CalldataPackets.RawUintN.Controls.dirty_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dirty_second
/-- info: 'Solidity.Backend.CalldataPackets.RawUintN.Controls.largest_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms largest_clean
/-- info: 'Solidity.Backend.CalldataPackets.RawUintN.Controls.local_expression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms local_expression
end Solidity.Backend.CalldataPackets.RawUintN.Controls
