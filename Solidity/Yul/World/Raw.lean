import Solidity.Source.Observe

/-!
# Independent raw-byte boundaries for Y07

Preparation over G01 bytes/words and the existing source byte encoding. These
are not physical-memory adapters. In particular, a caller must prove that its
memory view supplied the input bytes and realizes the copied output window.
-/
namespace Solidity.Yul.World
open Solidity.Roadmap (Address Word Bytes Outcome Fixed)

/-- EIP-211: even a zero-length copy checks the source offset. -/
def returnWindow (data : Bytes) (offset size : Nat) : Option Bytes :=
  if offset + size ≤ data.length then some ((data.drop offset).take size) else none

/-- Exact bounds, with no zero padding (unlike calldata/memory reads). -/
theorem returnWindow_none_iff (data : Bytes) (offset size : Nat) :
    returnWindow data offset size = none ↔ data.length < offset + size := by
  unfold returnWindow
  split
  next h =>
    constructor
    · intro he
      contradiction
    · intro hn
      omega
  next h =>
    constructor
    · intro _
      omega
    · intro _
      rfl

/-- A successful RETURNDATACOPY supplies exactly the requested byte count. -/
theorem returnWindow_length (data out : Bytes) (offset size : Nat)
    (h : returnWindow data offset size = some out) : out.length = size := by
  unfold returnWindow at h
  split at h
  next hb =>
    cases h
    simp only [List.length_take, List.length_drop]
    omega
  next => contradiction

/-- A call's output area copies only the available prefix; the rest is
untouched by the physical-memory adapter. -/
def callOutput (data : Bytes) (capacity : Nat) : Bytes := data.take capacity

theorem callOutput_length (data : Bytes) (capacity : Nat) :
    (callOutput data capacity).length = min capacity data.length := by
  exact List.length_take

/-- The last completed source-level call, including revert bytes. -/
def returnData : Outcome → Bytes
  | .success data | .revert data => data

/-- Replacement, never concatenation. Compiler call-freedom between source
boundaries remains an independent compilation obligation. -/
def overwrite (_old : Bytes) (outcome : Outcome) : Bytes := returnData outcome

theorem overwrite_last (old : Bytes) (first last : Outcome) :
    overwrite (overwrite old first) last = returnData last := rfl

/-- Successful CREATE clears returndata, failed initialization preserves its
revert bytes. Other early failures are represented by `revert []`. -/
def createReturnData : Outcome → Bytes
  | .success _ => []
  | .revert data => data

/-- EIP-1014's 85-byte preimage, including the hash of raw initcode. -/
def create2Input (F : Fixed) (sender : Address) (salt : Word) (initcode : Bytes) : Bytes :=
  [255] ++ Solidity.Source.beBytes 20 sender.val ++ Solidity.Source.wordBytes salt ++
    Solidity.Source.wordBytes (F.hash initcode)

theorem create2Input_length (F : Fixed) (sender : Address) (salt : Word) (initcode : Bytes) :
    (create2Input F sender salt initcode).length = 85 := by
  simp only [create2Input, List.length_append, List.length_singleton,
    Solidity.Source.beBytes_length, Solidity.Source.wordBytes_length]

/-- No injectivity assumption: collision/occupied-address failure belongs to
creation execution. This is the address formula only. -/
def create2Address (F : Fixed) (sender : Address) (salt : Word) (initcode : Bytes) : Address :=
  ⟨(F.hash (create2Input F sender salt initcode)).val % 2 ^ 160,
    Nat.mod_lt _ (by decide)⟩

/-- CREATE uses G01's existing RLP/nonce address formula. -/
def createAddress (F : Fixed) (sender : Address) (nonce : Fin (2 ^ 64)) : Address :=
  F.createAddress sender nonce

/-! ## Exact byte-list contracts (not physical-memory preservation) -/

theorem returnWindow_some_iff (data out : Bytes) (offset size : Nat) :
    returnWindow data offset size = some out ↔
      offset + size ≤ data.length ∧ out = (data.drop offset).take size := by
  unfold returnWindow
  split
  next hb =>
    simp only [Option.some.injEq]
    constructor
    · intro h
      exact ⟨hb, h.symm⟩
    · intro h
      exact h.2.symm
  next hb =>
    constructor
    · intro h
      cases h
    · intro h
      exact False.elim (hb h.1)

theorem returnWindow_contents (data out : Bytes) (offset size : Nat)
    (h : returnWindow data offset size = some out) :
    out = (data.drop offset).take size := (returnWindow_some_iff _ _ _ _).mp h |>.2

/-- Actual success supplies both the byte-count bound and the source bound;
the explicit index premise selects a byte inside that successful window. -/
theorem returnWindow_byte (data out : Bytes) (offset size i : Nat)
    (h : returnWindow data offset size = some out) (hi : i < size) :
    out[i]'(by have hl := returnWindow_length _ _ _ _ h; omega) =
      data[offset + i]'(by have hb := (returnWindow_some_iff _ _ _ _).mp h |>.1; omega) := by
  have hc : out = (data.drop offset).take size := returnWindow_contents _ _ _ _ h
  subst out
  simp only [List.getElem_take, List.getElem_drop]

/-- Successful outer and inner windows yield the identical direct source
window, including zero-sized windows at the exact end of the outer window. -/
theorem returnWindow_compose (data outer inner : Bytes) (offset size subOffset subSize : Nat)
    (ho : returnWindow data offset size = some outer)
    (hi : returnWindow outer subOffset subSize = some inner) :
    returnWindow data (offset + subOffset) subSize = some inner := by
  have hb : offset + size ≤ data.length := (returnWindow_some_iff _ _ _ _).mp ho |>.1
  have hs : subOffset + subSize ≤ size := by
    have hc := (returnWindow_some_iff _ _ _ _).mp hi |>.1
    have hl := returnWindow_length _ _ _ _ ho
    omega
  apply (returnWindow_some_iff _ _ _ _).mpr
  refine ⟨by omega, ?_⟩
  rw [returnWindow_contents _ _ _ _ hi, returnWindow_contents _ _ _ _ ho,
    List.drop_take, List.drop_drop, List.take_take, Nat.min_eq_left (by omega)]

theorem returnWindow_all (data : Bytes) : returnWindow data 0 data.length = some data := by
  apply (returnWindow_some_iff _ _ _ _).mpr
  exact ⟨by omega, by simp only [List.drop_zero, List.take_length]⟩

theorem returnWindow_zero (data : Bytes) (offset : Nat) (h : offset ≤ data.length) :
    returnWindow data offset 0 = some [] := by
  apply (returnWindow_some_iff _ _ _ _).mpr
  exact ⟨by omega, by simp only [List.take_zero]⟩

/-- Decomposition of bytes only; no claim about an actual memory remainder. -/
theorem callOutput_prefix (data : Bytes) (capacity : Nat) :
    callOutput data capacity ++ data.drop capacity = data := List.take_append_drop _ _

theorem callOutput_full (data : Bytes) (capacity : Nat) (h : data.length ≤ capacity) :
    callOutput data capacity = data := List.take_of_length_le h

theorem callOutput_truncate (data : Bytes) (first second : Nat) :
    callOutput (callOutput data first) second = callOutput data (min second first) :=
  List.take_take

theorem callOutput_append (data : Bytes) (first second : Nat) :
    callOutput data (first + second) =
      callOutput data first ++ callOutput (data.drop first) second := List.take_add

theorem callOutput_byte (data : Bytes) (capacity i : Nat)
    (hc : i < capacity) (hi : i < data.length) :
    (callOutput data capacity)[i]'(by rw [callOutput_length]; omega) = data[i] := by
  simp only [callOutput, List.getElem_take]

end Solidity.Yul.World
