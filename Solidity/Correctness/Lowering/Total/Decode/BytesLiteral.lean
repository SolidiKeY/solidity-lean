import Solidity.Correctness.Lowering.Total.Decode.Tables

namespace Solidity.Correctness.Lowering.Total.Decode.BytesLiteral

/-- The model folds natural-number literal components before checking the result.
It does not truncate each component to one byte. -/
def value (bs : List Nat) : Nat := bs.foldl (fun a b => 256 * a + b) 0

/-- Canonical big-endian digits, retaining the literal length. Faithfulness below
uses the range check of a successful fixed-bytes conversion, not a new admission. -/
def bytes (bs : List Nat) : List UInt8 := Source.beBytes bs.length (value bs)

/-- The literal always has its model length, including the empty literal. -/
theorem length (bs : List Nat) : (bytes bs).length = bs.length := Source.beBytes_length _ _

/-- A Source spelling for the normalized fixed-bytes literal. Dynamic-byte
allocation and integration into the shared statement decoder remain separate. -/
def spelling (bs : List Nat) : Source.Syn .expr := .lit (.hexStr (bytes bs))

/-- Decode the model literal encoding; other calls are not literals. -/
def decode (e : RawExpr) : Option (Source.Syn .expr) := e.bytesLit?.map spelling

private theorem fold_zeros (k a : Nat) :
    (List.replicate k 0).foldl (fun a b => 256 * a + b) a = a * 256 ^ k := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.foldl_cons, Nat.add_zero, ih, Nat.pow_succ]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

private theorem align_value {n : Nat} {bs : List Nat} {v : Nat}
    (h : bytesAlign n bs = .ok v) :
    bs.length ≤ n ∧ v = value bs * 256 ^ (n - bs.length) := by
  unfold bytesAlign at h
  split at h
  · cases h
  · rename_i fits
    simp only [List.foldl_append, fold_zeros] at h
    exact ⟨by omega, (Except.ok.inj h).symm⟩

private theorem source_pad (bs : List UInt8) (k : Nat) :
    Source.beValue (bs ++ List.replicate k 0) = Source.beValue bs * 256 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ', ← List.append_assoc, Source.beValue_append, ih]
    simp [Nat.pow_succ, Nat.mul_assoc]

/-- A successful model conversion that fits its target width forces the folded
literal to fit its original length, even when individual components exceed 255. -/
theorem fits {n : Nat} {bs : List Nat} {v : Nat}
    (aligned : bytesAlign n bs = .ok v) (range : v < 256 ^ n) :
    value bs < 256 ^ bs.length := by
  obtain ⟨len, rfl⟩ := align_value aligned
  have hp : 256 ^ n = 256 ^ bs.length * 256 ^ (n - bs.length) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hp] at range
  exact Nat.lt_of_mul_lt_mul_right range

/-- Fixed-bytes literal faithfulness: Source padding of the canonical spelling
has exactly the value returned by the model conversion. No admission predicate
is changed; integration must derive these premises from the successful
contextual conversion. -/
theorem faithful {n : Nat} {bs : List Nat} {v : Nat}
    (aligned : bytesAlign n bs = .ok v) (range : v < 256 ^ n) :
    Source.bytesNat (Source.fitBytes n (bytes bs)) = v := by
  obtain ⟨len, hv⟩ := align_value aligned
  have bl : (bytes bs).length = bs.length := length bs
  have bv : Source.beValue (bytes bs) = value bs :=
    Source.beValue_beBytes _ _ (fits aligned range)
  simp only [Source.bytesNat, Source.fitBytes, List.take_append, List.take_replicate,
    List.take_of_length_le (bl ▸ len), bl, Nat.min_eq_left (Nat.sub_le _ _)]
  rw [source_pad, bv, hv]

end Solidity.Correctness.Lowering.Total.Decode.BytesLiteral
