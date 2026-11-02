import Solidity.Semantics.AbiEntry
import Solidity.Semantics.Callback

/-!
# Primitive external return bytes at the callback interface

The complete-word check precedes the existing zero-padding ABI load. Only
primitive binders are handled here; contextual narrow/nominal source checks
remain the existing caller checks. Extra return bytes are ignored, including
an incomplete trailing word. No source/native execution adequacy is assumed.
-/
namespace Solidity.ExternalReturnBytes
open Semantics
variable {C : Contract} {H : HTy}

def wordAt (data : List UInt8) (offset : Nat) : Word :=
  ⟨AbiEntry.load data offset, by
    simp only [PrimTy.inRange, decide_eq_true_eq]
    exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr (by
      rw [← AbiEntry.W_eq]
      exact AbiEntry.load_lt data offset)⟩⟩

/-- Load only complete required words. The length check prevents the entry
loader's zero padding from accepting truncated return data. -/
def words (count : Nat) (data : List UInt8) : TRes (List Word) :=
  if count * 32 ≤ data.length then
    .ok ((List.range count).map fun i => wordAt data (i * 32))
  else .error .revert

/-- The existing typed decoder consumes the words actually read from bytes. -/
def decode {ρ : Ctx} (rets : Binders ρ) (data : List UInt8) :
    TRes (TEnv C H ρ × List Word) := do
  let vs ← words ρ.length data
  rets.decodeT vs

theorem complete_word {count : Nat} {data : List UInt8} {vs : List Word}
    (read : words count data = .ok vs) {i : Nat} (index : i < count) :
    i * 32 + 32 ≤ data.length := by
  unfold words at read
  split at read
  · omega
  · cases read

theorem decode_ok {ρ : Ctx} {rets : Binders ρ} {data : List UInt8}
    {r : TEnv C H ρ} {rest : List Word}
    (decoded : decode rets data = .ok (r, rest)) :
    ∃ vs, words ρ.length data = .ok vs ∧ rets.decodeT vs = .ok (r, rest) := by
  cases read : words ρ.length data with
  | error e => simp only [decode, read] at decoded; cases decoded
  | ok vs => exact ⟨vs, rfl, by simpa only [decode, read, Except.bind] using decoded⟩

/-- Even a single demanded primitive cannot decode an absent word. -/
theorem empty_snoc {ρ : Ctx} (bs : Binders ρ) (p : PrimTy) (x : Var) :
    (bs.snoc p x).decodeT (C := C) (H := H) [] = .error .revert := by
  induction bs generalizing p x with
  | nil => rfl
  | snoc bs q y ih =>
    change (do
      let (e, rest) ← (bs.snoc q y).decodeT (C := C) (H := H) []
      match rest with
      | v :: rest => match PrimTy.ofWord? p v with
        | some value => pure ((value, e), rest)
        | none => .error .revert
      | [] => .error .revert) = .error .revert
    rw [ih q y]
    rfl

/-- Decoder failure has a witness in the existing callback-decoder relation.
Short input uses the empty word list; this existence theorem does not identify
that witness with a successful complete-word read of the original bytes. -/
theorem decode_error {ρ : Ctx} {rets : Binders ρ} {data : List UInt8}
    (failed : decode (C := C) (H := H) rets data = .error .revert) :
    ∃ vs, rets.decodeT (C := C) (H := H) vs = .error .revert := by
  cases read : words ρ.length data with
  | ok vs => exact ⟨vs, by simpa only [decode, read, Except.bind] using failed⟩
  | error e =>
    cases rets with
    | nil => simp only [words, List.length_nil, Nat.zero_mul, Nat.zero_le,
        if_true, List.range_zero, List.map_nil] at read; cases read
    | snoc bs p x => exact ⟨[], empty_snoc bs p x⟩

/-- The view never replaces the original bytes. Raw catches use those bytes,
not a canonical re-encoding of the decoded reason/code. -/
inductive Failure where
  | error (reason : List UInt8)
  | panic (code : Word)
  | other
  deriving DecidableEq, Repr

def classify (data : List UInt8) : Failure :=
  match decodeError data with
  | some reason => .error reason
  | none => match decodePanic data with
    | some code => .panic code
    | none => .other

theorem classify_error {data reason : List UInt8}
    (h : decodeError data = some reason) : classify data = .error reason := by
  simp only [classify, h]

theorem classify_panic {data : List UInt8} {code : Word}
    (error : decodeError data = none) (panic : decodePanic data = some code) :
    classify data = .panic code := by simp only [classify, error, panic]

theorem classify_other {data : List UInt8}
    (error : decodeError data = none) (panic : decodePanic data = none) :
    classify data = .other := by simp only [classify, error, panic]

/-- This invokes the actual existing raw-catch decoder; no re-encoding occurs. -/
theorem raw_data_exact (data : List UInt8) (bound : data.length < 2 ^ 256) :
    CatchKind.raw.decode data = some data := by
  simp only [CatchKind.decode, if_pos bound]

/-- info: 'Solidity.ExternalReturnBytes.decode_ok' depends on axioms: [propext] -/
#guard_msgs in
#print axioms decode_ok
/-- info: 'Solidity.ExternalReturnBytes.decode_error' depends on axioms: [propext] -/
#guard_msgs in
#print axioms decode_error
end Solidity.ExternalReturnBytes
