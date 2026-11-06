import Solidity.Evm.Machine

/-! Runtime-addressed frame words on the EXISTING target machine. The pointer
is read from memory at execution, not expanded into a compile-time call depth.
No evaluator or instruction semantics is added. These slices are not yet a
complete recursive call compiler. Capacity is a real no-wrap premise. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.Stack
open Evm

def pushCode (pointerCell : Nat) : List Instr :=
 [.mload pointerCell,.mstoreAt,.mload pointerCell,.push (.val (wmod 1)),.add,.mstore pointerCell]

def pushed (m : Machine) (pointerCell : Nat) (address : Fin W) (value : Word) : Machine :=
 {m with mem := upd (upd m.mem address.val value) pointerCell (.val (wmod (1 + address.val)))}

/-- Save an actual target word through the runtime frame pointer. The entire
protected evaluation stack and every other machine field are retained. -/
theorem push_run (m : Machine) (pointerCell : Nat) (address : Fin W) (value : Word)
    (pointer : m.mem pointerCell = .val address) (separate : pointerCell ≠ address.val) :
    Evm.run (pushCode pointerCell) (m.push value) = .ok (pushed m pointerCell address value) 0 := by
  have one : (wmod 1).val = 1 := Nat.mod_eq_of_lt (by decide +kernel)
  simp only [pushCode,Evm.run,exec_cons_zero,Instr.step,Machine.push,Machine.next,
    Out.ok_bind,exec_nil,upd,pointer,if_neg separate,one,pushed]

def decrementCode (pointerCell : Nat) : List Instr :=
 [.push (.val (wmod 1)),.mload pointerCell,.sub]
def finishPopCode (pointerCell : Nat) : List Instr := [.dup 1,.mstore pointerCell,.mloadAt]
def popCode (pointerCell : Nat) : List Instr := decrementCode pointerCell ++ finishPopCode pointerCell

def popped (m : Machine) (pointerCell : Nat) (address : Fin W) : Machine :=
 {m with
  stack := m.mem (address.val - 1) :: m.stack
  mem := upd m.mem pointerCell (.val (wmod (address.val - 1)))}

theorem previous_word (address : Fin W) (positive : 0 < address.val) :
    wmod (address.val + (W - 1)) = wmod (address.val - 1) := by
  apply Fin.ext
  change (address.val + (W - 1)) % W = (address.val - 1) % W
  have same : address.val + (W - 1) = (address.val - 1) + W := by omega
  rw [same,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod]

theorem previous_value (address : Fin W) : (wmod (address.val - 1)).val = address.val - 1 :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) address.isLt)

theorem decrement_run (m : Machine) (pointerCell : Nat) (address : Fin W)
    (pointer : m.mem pointerCell = .val address) (positive : 0 < address.val) :
    Evm.run (decrementCode pointerCell) m = .ok (m.push (.val (wmod (address.val - 1)))) 0 := by
  have one : (wmod 1).val = 1 := Nat.mod_eq_of_lt (by decide +kernel)
  simp only [decrementCode,Evm.run,exec_cons_zero,Instr.step,Machine.next,
    Out.ok_bind,exec_nil,pointer,one,previous_word address positive,Machine.push]

theorem finishPop_run (m : Machine) (pointerCell : Nat) (address : Fin W)
    (separate : pointerCell ≠ address.val) :
    Evm.run (finishPopCode pointerCell) (m.push (.val address)) =
      .ok {m with
        stack := m.mem address.val :: m.stack
        mem := upd m.mem pointerCell (.val address)} 0 := by
  simp only [finishPopCode,Evm.run,exec_cons_zero,Instr.step,Machine.push,Machine.next,
    Out.ok_bind,exec_nil,List.getElem?_cons_zero,Nat.sub_self,upd,if_neg (Ne.symm separate)]

/-- Pop the actual saved word. Splitting arithmetic from the final store/read
keeps the checked instruction proof boundaries small. -/
theorem pop_run (m : Machine) (pointerCell : Nat) (address : Fin W)
    (pointer : m.mem pointerCell = .val address) (positive : 0 < address.val)
    (separate : pointerCell ≠ address.val - 1) :
    Evm.run (popCode pointerCell) m = .ok (popped m pointerCell address) 0 := by
  rw [popCode,Evm.run_append_ok (decrement_run m pointerCell address pointer positive)]
  simpa only [previous_value,popped] using
    finishPop_run m pointerCell (wmod (address.val - 1)) (by simpa only [previous_value] using separate)

/-- The payload cell remains written after a balanced push/pop. Only the
pointer is restored; this is deliberately not whole-memory equality. -/
theorem push_pop (m : Machine) (pointerCell : Nat) (address : Fin W) (value : Word)
    (pointer : m.mem pointerCell = .val address) (separate : pointerCell ≠ address.val)
    (capacity : 1 + address.val < W) :
    Evm.run (pushCode pointerCell ++ popCode pointerCell) (m.push value) =
      .ok {m with stack := value :: m.stack,mem := upd m.mem address.val value} 0 := by
  rw [Evm.run_append_ok (push_run m pointerCell address value pointer separate)]
  have next : (wmod (1 + address.val)).val = 1 + address.val := Nat.mod_eq_of_lt capacity
  have current : (pushed m pointerCell address value).mem pointerCell = .val (wmod (1 + address.val)) :=
    upd_same _ _ _
  rw [pop_run _ pointerCell (wmod (1 + address.val)) current (by rw [next];omega)
    (by rw [next];omega)]
  have read : (pushed m pointerCell address value).mem address.val = value := by
    simp only [pushed,upd,if_neg (Ne.symm separate),↓reduceIte]
  have restore : upd (pushed m pointerCell address value).mem pointerCell (.val (wmod address.val)) =
      upd m.mem address.val value := by
    funext x
    by_cases hx : x = pointerCell
    · subst x
      simp only [upd,if_neg separate,pointer,↓reduceIte]
      congr 1
      apply Fin.ext
      exact Nat.mod_eq_of_lt address.isLt
    · simp only [pushed,upd,if_neg hx]
  change Evm.Out.ok {m with
    stack := (pushed m pointerCell address value).mem ((wmod (1 + address.val)).val - 1) :: m.stack
    mem := upd (pushed m pointerCell address value).mem pointerCell (.val (wmod ((wmod (1 + address.val)).val - 1)))} 0 = _
  rw [next,Nat.add_sub_cancel_left,read,restore]
end Solidity.Backend.InternalFlow.RuntimeFrame.Stack
