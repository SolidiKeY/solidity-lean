import Solidity.Frontend.Checked.Print

/-!
# Reconstruction of concatenated literal payloads

Arbitrary fragment lengths and byte lists are handled by induction. Zero-length
fragments remain permitted. No layout equality premise is imposed.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem chunks_spec (bs : Bytes) (ns : List Nat) (cs : List Bytes)
    (h : chunks bs ns = some cs) : cs.flatten = bs ∧ cs.length = ns.length := by
  induction ns generalizing bs cs with
  | nil =>
    cases bs with
    | nil => cases h; exact ⟨rfl, rfl⟩
    | cons b bs => cases h
  | cons n ns ih =>
    change (chunks (bs.drop n) ns).bind
      (fun rest => if n ≤ bs.length then some (bs.take n :: rest) else none) = some cs at h
    cases hc : chunks (bs.drop n) ns with
    | none =>
      rw [hc] at h
      cases h
    | some rest =>
      rw [hc] at h
      by_cases hn : n ≤ bs.length
      · simp only [Option.bind_some, hn, ↓reduceIte, Option.some.injEq] at h
        subst cs
        have hi := ih (bs.drop n) rest hc
        constructor
        · rw [List.flatten_cons, hi.1]
          exact List.take_append_drop n bs
        · exact congrArg Nat.succ hi.2
      · simp only [Option.bind_some, hn, ↓reduceIte] at h
        cases h

theorem fragsP_spec (mk : Bytes → Tok) (bs : Bytes) (L rest : List Choice) (ts : List Tok)
    (h : fragsP mk bs L = some (ts, rest)) :
    ∃ cs, cs.flatten = bs ∧ ts = cs.map mk ∧ cs ≠ [] := by
  cases L with
  | nil => cases h
  | cons choice remaining =>
    cases choice with
    | attrs order => cases h
    | layoutFirst flag => cases h
    | frags ns =>
      cases ns with
      | nil => cases h
      | cons n ns =>
        change (((chunks bs (n :: ns)).map fun cs => (cs, remaining)).bind
          fun pair => some (pair.1.map mk, pair.2)) = some (ts, rest) at h
        cases hc : chunks bs (n :: ns) with
        | none => rw [hc] at h; cases h
        | some cs =>
          simp only [hc, Option.map_some, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          have hi := chunks_spec bs (n :: ns) cs hc
          refine ⟨cs, hi.1, h.1.symm, ?_⟩
          intro empty
          rw [empty] at hi
          cases hi.2

/-- Payload projection only; token tags remain in the original token list. -/
def stringPayload : Tok → Bytes
  | .str bs | .hexStr bs | .unicodeStr bs => bs
  | _ => []

theorem fragsP_reconstruct (mk : Bytes → Tok) (mkPayload : ∀ bs, stringPayload (mk bs) = bs)
    (bs : Bytes) (L rest : List Choice) (ts : List Tok)
    (h : fragsP mk bs L = some (ts, rest)) : ts.flatMap stringPayload = bs := by
  obtain ⟨cs, hc, ht, _⟩ := fragsP_spec mk bs L rest ts h
  rw [ht, List.flatMap_map]
  simpa only [Function.comp_def, mkPayload, List.flatMap_id'] using hc

/-- Same token fragments reconstruct the same bytes under independent layouts. -/
theorem fragsP_bytes_unique (mk : Bytes → Tok)
    (mkPayload : ∀ bs, stringPayload (mk bs) = bs)
    (a b : Bytes) (La Lb ra rb : List Choice) (ts : List Tok)
    (ha : fragsP mk a La = some (ts, ra)) (hb : fragsP mk b Lb = some (ts, rb)) : a = b :=
  (fragsP_reconstruct mk mkPayload a La ra ts ha).symm.trans
    (fragsP_reconstruct mk mkPayload b Lb rb ts hb)

theorem chunks_single (bs : Bytes) : chunks bs [bs.length] = some [bs] := by
  simp only [chunks, List.drop_length, List.isEmpty_nil, ↓reduceIte,
    Option.bind_some, Nat.le_refl, List.take_length]

theorem fragsP_single (mk : Bytes → Tok) (bs : Bytes) (rest : List Choice) :
    fragsP mk bs (.frags [bs.length] :: rest) = some ([mk bs], rest) := by
  change (((chunks bs [bs.length]).map fun cs => (cs, rest)).bind
    fun pair => some (pair.1.map mk, pair.2)) = _
  rw [chunks_single]
  rfl

theorem fragsP_leading_empty (mk : Bytes → Tok) (bs : Bytes) (rest : List Choice) :
    fragsP mk bs (.frags [0, bs.length] :: rest) = some ([mk [], mk bs], rest) := by
  change (((chunks bs [0, bs.length]).map fun cs => (cs, rest)).bind
    fun pair => some (pair.1.map mk, pair.2)) = _
  have hc : chunks bs [0, bs.length] = some [[], bs] := by
    simp only [chunks, List.drop_zero, List.drop_length, List.isEmpty_nil,
      ↓reduceIte, Option.bind_some, Nat.le_refl, Nat.zero_le, List.take_zero, List.take_length]
  rw [hc]
  rfl

theorem fragment_layouts_distinct (bs : Bytes) :
    ([Choice.frags [bs.length]] : List Choice) ≠ [.frags [0, bs.length]] := by
  intro h
  have hh := Choice.frags.inj (List.cons.inj h).1
  have hl := congrArg List.length hh
  cases hl

end Solidity.Frontend.ExpressionUniqueness
