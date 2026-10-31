import Solidity.Yul.Views.ScalarCodecs
import Solidity.Source.WellTyped

/-! Canonical MEMORY scalar words use ACTUAL Source.Val.word, never storage
payload alignment. Signed integers are full-word sign extensions; bytesN is
left aligned. Candidate words are checked EXACTLY, no dirty-bit cleaning.
None is unsupported canonical preparation, not a Yul refusal/no-op policy. -/
namespace Solidity.Yul.Views

def CanonicalScalarType (D : Source.Layout) : Source.STy → Prop
  | .int _ | .bool | .address _ | .fixedBytes _ _ | .contract _ => True
  | .enum d => D.enumSize d ≤ 2 ^ 256
  | _ => False

def memoryScalarCandidate (D : Source.Layout) (τ : Source.STy) (word : Roadmap.Word) : Option (Source.Val D τ) :=
  match τ with
  | .int t => if range : t.lo ≤ Source.wordInt t word ∧ Source.wordInt t word ≤ t.hi then some (.int (Source.wordInt t word) range) else none
  | .bool => if word = 0 then some (.bool false) else if word = 1 then some (.bool true) else none
  | .address p => if range : word.val < 2 ^ 160 then some (.address ⟨word.val, range⟩) else none
  | .contract d => if range : word.val < 2 ^ 160 then some (.contract ⟨word.val, range⟩) else none
  | .fixedBytes n h => some (.fixedBytes ((Source.wordBytes word).take n) (by
      rw [List.length_take, Source.wordBytes_length, Nat.min_eq_left h.2]))
  | .enum d => if range : word.val < D.enumSize d then some (.enum ⟨word.val, range⟩) else none
  | _ => none

def decodeCanonicalScalar (D : Source.Layout) (τ : Source.STy) (word : Roadmap.Word) : Option (Source.Val D τ) := do
  let v ← memoryScalarCandidate D τ word
  if v.word = some word then some v else none

theorem decodeCanonicalScalar_word (D : Source.Layout) (τ : Source.STy) (word : Roadmap.Word) (v : Source.Val D τ)
    (decoded : decodeCanonicalScalar D τ word = some v) : v.word = some word := by
  unfold decodeCanonicalScalar at decoded
  cases hc : memoryScalarCandidate D τ word with
  | none => rw [hc] at decoded; cases decoded
  | some candidate =>
    rw [hc] at decoded
    change (if candidate.word = some word then some candidate else none) = some v at decoded
    split at decoded
    · cases decoded; assumption
    · cases decoded

theorem memoryScalarCandidate_refOK (E : Source.Env) (H : Source.HeapTy) (τ : Source.STy) (word : Roadmap.Word)
    (v : Source.Val E.layout τ) (candidate : memoryScalarCandidate E.layout τ word = some v) : Source.Val.RefOK E H v := by
  cases τ <;> simp only [memoryScalarCandidate] at candidate <;> try cases candidate
  all_goals try (split at candidate <;> try cases candidate)
  all_goals try (split at candidate <;> try cases candidate)
  all_goals trivial

theorem decodeCanonicalScalar_refOK (E : Source.Env) (H : Source.HeapTy) (τ : Source.STy) (word : Roadmap.Word)
    (v : Source.Val E.layout τ) (decoded : decodeCanonicalScalar E.layout τ word = some v) : Source.Val.RefOK E H v := by
  unfold decodeCanonicalScalar at decoded
  cases hc : memoryScalarCandidate E.layout τ word with
  | none => rw [hc] at decoded; cases decoded
  | some candidate =>
    rw [hc] at decoded
    change (if candidate.word = some word then some candidate else none) = some v at decoded
    split at decoded
    · cases decoded; exact memoryScalarCandidate_refOK E H τ word v hc
    · cases decoded

theorem wordBytes_toWord_padded (bs : List UInt8) (length : bs.length ≤ 32) :
    Source.wordBytes (Source.toWord (Source.beValue (bs ++ List.replicate (32 - bs.length) 0))) = bs ++ List.replicate (32 - bs.length) 0 := by
  let padded := bs ++ List.replicate (32 - bs.length) 0
  have hp : padded.length = 32 := by simp only [padded, List.length_append, List.length_replicate]; omega
  have bound : Source.beValue padded < 2 ^ 256 := by
    have hb := scalar_beValue_bound padded
    rw [hp] at hb
    exact hb
  change Source.beBytes 32 (Source.beValue padded % 2 ^ 256) = padded
  rw [Nat.mod_eq_of_lt bound, ← hp]
  exact scalar_beBytes_value padded

theorem memoryScalarCandidate_encode (D : Source.Layout) (τ : Source.STy) (supported : CanonicalScalarType D τ)
    (v : Source.Val D τ) (word : Roadmap.Word) (encoded : v.word = some word) : memoryScalarCandidate D τ word = some v := by
  cases v with
  | @int t value range =>
    have inverse := Source.Val.word_int (D := D) value range
    rw [encoded] at inverse
    change Source.readInt t word = some value at inverse
    unfold Source.readInt at inverse
    dsimp only at inverse
    split at inverse
    · cases inverse
      exact dif_pos range
    · cases inverse
  | bool b =>
    cases b
    · have raw : word = 0 := (Option.some.inj encoded).symm
      subst word; rfl
    · have raw : word = 1 := (Option.some.inj encoded).symm
      subst word; rfl
  | address a =>
    have bound : a.val < 2 ^ 256 := Nat.lt_of_lt_of_le a.isLt (by decide)
    have raw : word.val = a.val := by
      have eq := congrArg Fin.val (Option.some.inj encoded)
      change a.val % 2 ^ 256 = word.val at eq
      rw [Nat.mod_eq_of_lt bound] at eq
      exact eq.symm
    unfold memoryScalarCandidate
    dsimp only
    rw [dif_pos (show word.val < 2 ^ 160 from raw ▸ a.isLt)]
    apply congrArg some
    apply congrArg Source.Val.address
    exact Fin.ext raw
  | contract a =>
    have bound : a.val < 2 ^ 256 := Nat.lt_of_lt_of_le a.isLt (by decide)
    have raw : word.val = a.val := by
      have eq := congrArg Fin.val (Option.some.inj encoded)
      change a.val % 2 ^ 256 = word.val at eq
      rw [Nat.mod_eq_of_lt bound] at eq
      exact eq.symm
    unfold memoryScalarCandidate
    dsimp only
    rw [dif_pos (show word.val < 2 ^ 160 from raw ▸ a.isLt)]
    apply congrArg some
    apply congrArg Source.Val.contract
    exact Fin.ext raw
  | @fixedBytes n h bs hl =>
    have raw := (Option.some.inj encoded).symm
    subst word
    have bytes := wordBytes_toWord_padded bs (by omega)
    unfold memoryScalarCandidate
    apply congrArg some
    have take : (Source.wordBytes (Source.toWord (Source.beValue (bs ++ List.replicate (32 - bs.length) 0)))).take n = bs := by
      rw [bytes, ← hl, List.take_left]
    simp only [take]
  | @enum d i =>
    have bound : i.val < 2 ^ 256 := Nat.lt_of_lt_of_le i.isLt supported
    have raw : word.val = i.val := by
      have eq := congrArg Fin.val (Option.some.inj encoded)
      change i.val % 2 ^ 256 = word.val at eq
      rw [Nat.mod_eq_of_lt bound] at eq
      exact eq.symm
    unfold memoryScalarCandidate
    dsimp only
    rw [dif_pos (show word.val < D.enumSize d from raw ▸ i.isLt)]
    apply congrArg some
    apply congrArg Source.Val.enum
    exact Fin.ext raw
  | fixed value range | udvt value | internalFn _ | externalFn _ _ _ => cases supported
  | memRef _ _ | storRef _ _ | cdRef _ _ => cases encoded

theorem decodeCanonicalScalar_encode (D : Source.Layout) (τ : Source.STy) (supported : CanonicalScalarType D τ)
    (v : Source.Val D τ) (word : Roadmap.Word) (encoded : v.word = some word) : decodeCanonicalScalar D τ word = some v := by
  unfold decodeCanonicalScalar
  rw [memoryScalarCandidate_encode D τ supported v word encoded]
  change (if v.word = some word then some v else none) = some v
  rw [if_pos encoded]

end Solidity.Yul.Views
