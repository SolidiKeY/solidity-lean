import Solidity.Backend.Failure.Immediate
import Solidity.RevertBytes
import Solidity.Roadmap.Contracts

/-!
# Executable payload emission

The payload is already evaluated. Custom-error bytes come from the existing
intrinsic ABI evaluation, including their selector. No ABI encoder lives here.
Byte stores avoid over-writing any part of the final partially used word.
The final PUSHes put offset above length, as RETURN and REVERT require.
-/
namespace Solidity.Backend.Failure

inductive Input where
  | empty
  | panic (code : Fin wordLimit)
  | reason (utf8 : Semantics.RevertData)
  | custom (encoded : Semantics.RevertData)
  | returned (encoded : List UInt8)
  deriving DecidableEq, Repr

def Input.bytes : Input → List UInt8
  | .empty => []
  | .panic c => Semantics.encodePanic c.val
  | .reason s => Semantics.encodeError s
  | .custom d => d
  | .returned d => d

def Input.terminal : Input → Op
  | .returned _ => .RETURN
  | _ => .REVERT

def Input.observation (i : Input) : Roadmap.Outcome :=
  match i with
  | .returned d => .success d
  | _ => .revert i.bytes

def pushByte (b : UInt8) : Instr := .push ⟨1, by decide⟩ #v[b]

/-- Increasing addresses, bytes in their original order. -/
def writes : Nat → List UInt8 → Program
  | _, [] => []
  | a, b :: bs => [pushByte b, pushNat a, .op .MSTORE8] ++ writes (a + 1) bs

/-- The length and offset are machine words; correctness requires that they
fit, and that the half-open write interval does not wrap. -/
def emit (a : Nat) (i : Input) : Program :=
  writes a i.bytes ++ [pushNat i.bytes.length, pushNat a, .op i.terminal]

def Fits (a : Nat) (bs : List UInt8) : Prop :=
  a < wordLimit ∧ bs.length < wordLimit ∧ a + bs.length ≤ wordLimit

theorem writes_length (a : Nat) (bs : List UInt8) : (writes a bs).length = 3 * bs.length := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [writes, List.length_append, List.length_cons, List.length_nil, ih]
    omega

theorem writes_append (a : Nat) (xs ys : List UInt8) :
    writes a (xs ++ ys) = writes a xs ++ writes (a + xs.length) ys := by
  induction xs generalizing a with
  | nil => simp only [List.nil_append, writes, List.length_nil, Nat.add_zero]
  | cons b xs ih =>
    simp only [List.cons_append, writes, ih, List.append_assoc, List.length_cons]
    rw [show a + 1 + xs.length = a + (xs.length + 1) by omega]

/-- Any chosen byte is emitted after exactly three instructions per earlier
byte, at its exact address. This also pins the order across word boundaries. -/
theorem writes_decompose (a : Nat) (xs ys : List UInt8) (b : UInt8) :
    writes a (xs ++ b :: ys) = writes a xs ++
      ([pushByte b, pushNat (a + xs.length), .op .MSTORE8] ++
        writes (a + xs.length + 1) ys) := by
  rw [writes_append]
  rfl

theorem emit_length (a : Nat) (i : Input) : (emit a i).length = 3 * i.bytes.length + 3 := by
  simp only [emit, List.length_append, writes_length, List.length_cons, List.length_nil]

theorem emit_empty (a : Nat) : emit a .empty = [pushNat 0, pushNat a, .op .REVERT] := rfl

theorem emit_custom (a : Nat) (d : Semantics.RevertData) :
    emit a (.custom d) = writes a d ++ [pushNat d.length, pushNat a, .op .REVERT] := rfl

theorem emit_returned (a : Nat) (d : List UInt8) :
    emit a (.returned d) = writes a d ++ [pushNat d.length, pushNat a, .op .RETURN] := rfl

theorem panic_length (c : Fin wordLimit) : (Input.panic c).bytes.length = 36 := by
  simp only [Input.bytes, Semantics.encodePanic, Semantics.panicSelector, Semantics.wordBytes,
    List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range]

theorem reason_length (s : List UInt8) :
    (Input.reason s).bytes.length = 68 + s.length + (32 - s.length % 32) % 32 := by
  simp only [Input.bytes, Semantics.encodeError, Semantics.errorSelector, Semantics.wordBytes,
    Semantics.pad32, List.length_append, List.length_cons, List.length_nil,
    List.length_map, List.length_range, List.length_replicate]
  omega

end Solidity.Backend.Failure
