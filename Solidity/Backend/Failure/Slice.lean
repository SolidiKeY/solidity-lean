import Solidity.Backend.Opcode
import Solidity.Roadmap.Contracts

/-!
# Independent exact byte semantics for a straight-line instruction slice

This module does not import the emitter or its immediate encoder. It defines
the ordinary PUSH/MSTORE8/RETURN/REVERT rules on intrinsic 256-bit words.
Unsupported instructions and underflow fail. Halting ignores the remaining
instruction list. Memory is exact byte-addressed, with no rounded writes.
Gas, expansion charges and global call/world behavior are outside this slice.
-/
namespace Solidity.Backend.Failure.Slice

abbrev Memory := Nat → UInt8

structure Machine where
  stack : List Roadmap.Word
  memory : Memory

def putByte (m : Memory) (a : Nat) (b : UInt8) : Memory :=
  fun x => if x = a then b else m x

def putBytes : Memory → Nat → List UInt8 → Memory
  | m, _, [] => m
  | m, a, b :: bs => putBytes (putByte m a b) (a + 1) bs

def getBytes (m : Memory) : Nat → Nat → List UInt8
  | _, 0 => []
  | a, n + 1 => m a :: getBytes m (a + 1) n

/-- PUSH interprets bytes as a big-endian integer, reduced to a machine word. -/
def pushed (bs : List UInt8) : Roadmap.Word :=
  ⟨bs.foldl (fun a b => a * 256 + b.toNat) 0 % (2 ^ 256), Nat.mod_lt _ (by decide)⟩

/-- The top stack word is the offset, the next is value or size. -/
def step (i : Instr) (s : Machine) : Option (Machine × Option Roadmap.Outcome) :=
  match i with
  | .push _ imm => some ({ s with stack := pushed imm.toList :: s.stack }, none)
  | .op .MSTORE8 =>
    match s.stack with
    | a :: v :: tail => some (⟨tail, putByte s.memory a.val (UInt8.ofNat v.val)⟩, none)
    | _ => none
  | .op .RETURN =>
    match s.stack with
    | a :: n :: tail => some (⟨tail, s.memory⟩, some (.success (getBytes s.memory a.val n.val)))
    | _ => none
  | .op .REVERT =>
    match s.stack with
    | a :: n :: tail => some (⟨tail, s.memory⟩, some (.revert (getBytes s.memory a.val n.val)))
    | _ => none
  | _ => none

def run : Program → Machine → Option (Machine × Option Roadmap.Outcome)
  | [], s => some (s, none)
  | i :: p, s => do
    let (s', o) ← step i s
    match o with
    | none => run p s'
    | some result => some (s', some result)

/-- Independently checks every reached pre/post stack height, stopping at
RETURN/REVERT exactly as run does. Underflow or unsupported opcodes fail. -/
def stackSafe : Program → Machine → Bool
  | [], s => decide (s.stack.length ≤ 1024)
  | i :: p, s => decide (s.stack.length ≤ 1024) &&
    match step i s with
    | none => false
    | some (s', none) => stackSafe p s'
    | some (s', some _) => decide (s'.stack.length ≤ 1024)

/-- Execution with the Osaka stack-height bound enforced. -/
def checkedRun (p : Program) (s : Machine) : Option (Machine × Option Roadmap.Outcome) :=
  if stackSafe p s then run p s else none

theorem putBytes_frame (m : Memory) (a x : Nat) (bs : List UInt8)
    (h : x < a ∨ a + bs.length ≤ x) : putBytes m a bs x = m x := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b bs ih =>
    rw [putBytes, ih]
    · simp only [putByte, if_neg (by simp only [List.length_cons] at h; omega : x ≠ a)]
    · simp only [List.length_cons] at h
      omega

theorem getBytes_putBytes (m : Memory) (a : Nat) (bs : List UInt8) :
    getBytes (putBytes m a bs) a bs.length = bs := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, putBytes, getBytes]
    rw [ih, putBytes_frame (putByte m a b) (a + 1) a bs (Or.inl (by omega))]
    simp only [putByte, ite_true]

theorem putBytes_append (m : Memory) (a : Nat) (xs ys : List UInt8) :
    putBytes m a (xs ++ ys) = putBytes (putBytes m a xs) (a + xs.length) ys := by
  induction xs generalizing m a with
  | nil => simp only [List.nil_append, putBytes, List.length_nil, Nat.add_zero]
  | cons b xs ih =>
    simp only [List.cons_append, putBytes, ih, List.length_cons]
    rw [show a + 1 + xs.length = a + (xs.length + 1) by omega]

theorem getBytes_congr (m n : Memory) (a len : Nat)
    (h : ∀ x, a ≤ x → x < a + len → m x = n x) :
    getBytes m a len = getBytes n a len := by
  induction len generalizing a with
  | zero => rfl
  | succ len ih =>
    simp only [getBytes]
    rw [h a (by omega) (by omega), ih]
    intro x hx hx'
    exact h x (by omega) (by omega)

/-- Extending memory after a slice does not change the observed bytes. -/
theorem getBytes_suffix_write (m : Memory) (a len : Nat) (padding : List UInt8) :
    getBytes (putBytes m (a + len) padding) a len = getBytes m a len := by
  apply getBytes_congr
  intro x _ hx
  exact putBytes_frame m (a + len) x padding (Or.inl hx)

end Solidity.Backend.Failure.Slice
