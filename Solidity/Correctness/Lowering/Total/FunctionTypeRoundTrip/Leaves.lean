import Solidity.Correctness.Lowering.Total.FunctionTypeDecode
import Solidity.Correctness.Lowering.Total.FunctionTypeParserLaws
import Solidity.Correctness.Lowering.Total.FunctionTypeRoundTrip.Nat

/-!
# Function-signature round trip: the leaf reader on character lists

`FunctionTypeDecode.leaf` reads a component through `Decode.typeNameB`
(`bytesTy?`, `narrowTy?`) and `locSuffix`, none of which reduces in the
kernel. Each is proved equal to a character-list form (`leaf_mk`), from which:

* `spelled_leaf`: every elementary type `elemName` spells (`Spelled`: `bool`,
  `address`, `uintN`/`intN` at every width, `bytesN`) is read back at its type
  and width, is no function type and is `Well` (all widths by kernel
  evaluation, `intsOk`, `bytesOk`);
* `ElemFree` (decidable): no elementary reading; sufficient (`elemFree_of_last`): a
  component not ending in a digit and none of `bool`, `address`, `uint`, `int`;
* `leaf_located`: `b ++ locName d` is read as `b` at `d`, for every base.
-/

namespace Solidity.Correctness.Lowering.Total.FunctionTypeRoundTrip

open Source (Syn DataLoc)
open FunctionTypeDecode
open FunctionTypeParserLaws (startsWith_lit endsWith_lit fnTy?_mk Well)
open FunctionTypeParserLaws.Str (drop_mk dropRight_mk)

/-- `narrowTy?` on a character list. -/
def narrowL (l : List Char) : Option (PrimTy × Nat) :=
  let (p, ds) :=
    if l.take 4 = "uint".data then (PrimTy.uint, l.drop 4)
    else if l.take 3 = "int".data then (PrimTy.int, l.drop 3)
    else (PrimTy.bool, [])
  match natL ds with
  | some n =>
    if p != .bool && 8 ≤ n && n < 256 && n % 8 == 0 && toString n == String.mk ds then some (p, n)
    else none
  | none => none

theorem narrowTy?_mk (l : List Char) : narrowTy? ⟨l⟩ = narrowL l := by
  have u : "uint".length = 4 := rfl
  have i : "int".length = 3 := rfl
  have e : ("" : String) = ⟨[]⟩ := rfl
  unfold narrowTy? narrowL
  simp only [startsWith_lit, u, i, drop_mk]
  by_cases h4 : l.take 4 = "uint".data
  · simp only [h4, decide_true, if_true, toNat?_mk]
    rfl
  · by_cases h3 : l.take 3 = "int".data
    · simp only [h4, h3, decide_true, decide_false, if_true, toNat?_mk, Bool.false_eq_true,
        if_false]
      rfl
    · simp only [h4, h3, decide_false, Bool.false_eq_true, if_false, e, toNat?_mk]
      rfl

/-- `bytesTy?` on a character list. -/
def bytesL (l : List Char) : Option Nat :=
  if l.take 5 = "bytes".data then
    match natL (l.drop 5) with
    | some n => if 1 ≤ n && n ≤ 32 && toString n == String.mk (l.drop 5) then some n else none
    | none => none
  else none

theorem bytesTy?_mk (l : List Char) : bytesTy? ⟨l⟩ = bytesL l := by
  have b : "bytes".length = 5 := rfl
  unfold bytesTy? bytesL
  simp only [startsWith_lit, b, drop_mk]
  by_cases h5 : l.take 5 = "bytes".data
  · simp only [h5, decide_true, if_true, toNat?_mk]
    rfl
  · simp only [h5, decide_false, Bool.false_eq_true, if_false]

/-- `Decode.typeNameW` of a name, on its characters. -/
def typeNameWL (l : List Char) : Option (Syn .typeName) :=
  if String.mk l = "bool" then some (.elem .bool)
  else if String.mk l = "uint" ∨ String.mk l = "uint256" then
    (Decode.primElem .uint 256).map .elem
  else if String.mk l = "int" ∨ String.mk l = "int256" then
    (Decode.primElem .int 256).map .elem
  else match narrowL l with
    | some (p, bits) => (Decode.primElem p bits).map .elem
    | none => none

/-- `Decode.typeNameB` of a name, on its characters. -/
def typeNameL (l : List Char) : Option (Syn .typeName) :=
  match bytesL l with
  | some n => (Decode.bytesElem n).map .elem
  | none => if String.mk l = "address" then some (.elem .address) else typeNameWL l

theorem typeNameW_mk (l : List Char) : Decode.typeNameW (.named ⟨l⟩) = typeNameWL l := by
  rw [Decode.typeNameW.eq_1, narrowTy?_mk]
  rfl

theorem typeNameB_mk (l : List Char) : Decode.typeNameB (.named ⟨l⟩) = typeNameL l := by
  dsimp only [Decode.typeNameB, typeNameL]
  rw [bytesTy?_mk]
  cases bytesL l with
  | some n => rfl
  | none =>
    dsimp only
    rw [Decode.typeNameA.eq_1, typeNameW_mk]

/-- `locSuffix` on a character list. -/
def locL (l : List Char) : Option (String × DataLoc) :=
  if l.drop (l.length - 6) = "memory".data then some (⟨l.take (l.length - 6)⟩, .memory)
  else if l.drop (l.length - 7) = "storage".data then some (⟨l.take (l.length - 7)⟩, .storage)
  else if l.drop (l.length - 8) = "calldata".data then some (⟨l.take (l.length - 8)⟩, .calldata)
  else none

theorem locSuffix_mk (l : List Char) : locSuffix ⟨l⟩ = locL l := by
  have m : "memory".length = 6 := rfl
  have s : "storage".length = 7 := rfl
  have c : "calldata".length = 8 := rfl
  unfold locSuffix locL
  simp only [endsWith_lit, m, s, c, dropRight_mk, decide_eq_true_eq]

/-- `leaf` on a character list. -/
def leafL (l : List Char) : Part Unit :=
  match typeNameL l with
  | some (.elem e) => .elem e
  | _ =>
    match locL l with
    | some (b, d) => .located b d
    | none => .named ⟨l⟩

/-- `leaf` is `leafL` of the characters, on every component. -/
theorem leaf_mk (l : List Char) : leaf ⟨l⟩ = leafL l := by
  unfold leaf leafL
  rw [typeNameB_mk, locSuffix_mk]
  rfl

/-! ## Elementary leaves -/

/-- The elementary types `elemName` spells and `leaf` reads back: `bool`,
`address`, `uintN`/`intN` at every width and `bytesN`. `address payable`,
`string`, `bytes` and `fixed` types are not spelled by `elemName` (`""`). -/
def Spelled : Source.Elem → Prop
  | .bool | .address | .int .. | .fixedBytes .. => True
  | _ => False

/-- The three facts a spelled elementary leaf needs, on its characters. -/
def elemOk (e : Source.Elem) : Bool :=
  leafL (elemName e).data == .elem e && !decide ((elemName e).data.take 9 = "function(".data) &&
    decide (Well (elemName e))

/-- Every integer width, both signs (kernel evaluation, no native code). -/
theorem intsOk : (List.range 257).all (fun b =>
    (Decode.primElem .uint b).all elemOk && (Decode.primElem .int b).all elemOk) = true := by
  decide +kernel

/-- Every `bytesN` width. -/
theorem bytesOk : (List.range 33).all (fun n => (Decode.bytesElem n).all elemOk) = true := by
  decide +kernel

theorem elemOk_of_spelled : ∀ {e : Source.Elem}, Spelled e → elemOk e = true
  | .bool, _ => by decide +kernel
  | .address, _ => by decide +kernel
  | .int s bits h, _ => by
    have := List.all_eq_true.1 intsOk bits (List.mem_range.2 (by omega))
    cases s
    · have p : Decode.primElem .uint bits = some (.int false bits h) := by
        simp [Decode.primElem, h]
      rw [p] at this
      simp only [Option.all_some, Bool.and_eq_true] at this
      exact this.1
    · have p : Decode.primElem .int bits = some (.int true bits h) := by
        simp [Decode.primElem, h]
      rw [p] at this
      simp only [Option.all_some, Bool.and_eq_true] at this
      exact this.2
  | .fixedBytes n h, _ => by
    have := List.all_eq_true.1 bytesOk n (List.mem_range.2 (by omega))
    have p : Decode.bytesElem n = some (.fixedBytes n h) := by simp [Decode.bytesElem, h]
    rw [p] at this
    exact this
  | .addressPayable, h | .string, h | .bytes, h | .fixed .., h => nomatch h

/-- **Elementary leaves.** A spelled elementary type is no function type, is a
`Well` component, and `leaf` reads it back at its type and width. -/
theorem spelled_leaf {e : Source.Elem} (h : Spelled e) :
    leaf (elemName e) = .elem e ∧ fnTy? (elemName e) = false ∧ Well (elemName e) := by
  have ok := elemOk_of_spelled h
  simp only [elemOk, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at ok
  obtain ⟨⟨hl, hf⟩, hw⟩ := ok
  refine ⟨(leaf_mk _).trans hl, ?_, hw⟩
  exact (fnTy?_mk _).trans (decide_eq_false hf)

/-! ## Components no elementary type is read from -/

/-- No elementary type is read from the component: the condition under which
`leaf` does not take its first branch. -/
def ElemFree (c : String) : Prop := ∀ e, Decode.typeNameB (.named c) ≠ some (.elem e)

/-- `ElemFree`, on characters. -/
def elemFreeL (l : List Char) : Bool :=
  match typeNameL l with
  | some (.elem _) => false
  | _ => true

theorem elemFree_iff (c : String) : ElemFree c ↔ elemFreeL c.data = true := by
  have e : Decode.typeNameB (.named c) = typeNameL c.data := typeNameB_mk c.data
  unfold ElemFree elemFreeL
  rw [e]
  split <;> simp_all

instance (c : String) : Decidable (ElemFree c) := decidable_of_iff _ (elemFree_iff c).symm

theorem natL_some {ds : List Char} {n : Nat} (h : natL ds = some n) :
    ds ≠ [] ∧ ds.all Char.isDigit = true := by
  unfold natL at h
  split at h
  · assumption
  · cases h

theorem last_digit {l : List Char} (k : Nat) (ne : l.drop k ≠ [])
    (dig : (l.drop k).all Char.isDigit = true) : ∃ c, l.getLast? = some c ∧ c.isDigit = true := by
  obtain ⟨c, hc⟩ : ∃ c, (l.drop k).getLast? = some c := by
    cases h : (l.drop k).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 h) ne
    | some c => exact ⟨c, rfl⟩
  refine ⟨c, ?_, List.all_eq_true.1 dig c (List.mem_of_getLast? hc)⟩
  rw [← List.take_append_drop k l, List.getLast?_append, hc]
  rfl

/-- What an elementary reading's spelling looks like: one of four words, or
ending in a digit. -/
theorem elem_spelling {l : List Char} {e : Source.Elem} (h : typeNameL l = some (.elem e)) :
    l = "bool".data ∨ l = "address".data ∨ l = "uint".data ∨ l = "int".data ∨
      ∃ c, l.getLast? = some c ∧ c.isDigit = true := by
  unfold typeNameL at h
  split at h
  · rename_i n hb
    unfold bytesL at hb
    split at hb
    · split at hb
      · rename_i m hm
        have ⟨ne, dig⟩ := natL_some hm
        exact Or.inr (Or.inr (Or.inr (Or.inr (last_digit 5 ne dig))))
      · cases hb
    · cases hb
  · have dat : ∀ {t : String}, String.mk l = t → l = t.data := fun h => congrArg String.data h
    split at h
    · exact Or.inr (Or.inl (dat ‹_›))
    unfold typeNameWL at h
    split at h
    · exact Or.inl (dat ‹_›)
    split at h
    · rename_i hu
      rcases hu with hu | hu
      · exact Or.inr (Or.inr (Or.inl (dat hu)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨'6', by rw [dat hu]; rfl, rfl⟩)))
    split at h
    · rename_i hi
      rcases hi with hi | hi
      · exact Or.inr (Or.inr (Or.inr (Or.inl (dat hi))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨'6', by rw [dat hi]; rfl, rfl⟩)))
    split at h
    · rename_i p bits hn
      unfold narrowL at hn
      refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      by_cases h4 : l.take 4 = "uint".data
      · simp only [h4, if_true] at hn
        split at hn
        · rename_i m hm; obtain ⟨ne, dig⟩ := natL_some hm; exact last_digit 4 ne dig
        · cases hn
      · by_cases h3 : l.take 3 = "int".data
        · simp only [h4, h3, if_true, if_false] at hn
          split at hn
          · rename_i m hm; obtain ⟨ne, dig⟩ := natL_some hm; exact last_digit 3 ne dig
          · cases hn
        · have z : natL [] = none := rfl
          simp only [h4, h3, if_false, z] at hn
          cases hn
    · cases h

/-- **A syntactic criterion.** A component that does not end in a digit and is
none of `bool`, `address`, `uint`, `int` is read as no elementary type. -/
theorem elemFree_of_last {c : String}
    (last : ∀ x, c.data.getLast? = some x → x.isDigit = false)
    (word : c.data ≠ "bool".data ∧ c.data ≠ "address".data ∧ c.data ≠ "uint".data ∧
      c.data ≠ "int".data) : ElemFree c := by
  intro e h
  rw [show Decode.typeNameB (.named c) = typeNameL c.data from typeNameB_mk c.data] at h
  rcases elem_spelling h with b | b | b | b | ⟨x, hx, dx⟩
  · exact word.1 b
  · exact word.2.1 b
  · exact word.2.2.1 b
  · exact word.2.2.2 b
  · rw [last x hx] at dx; cases dx

/-! ## Located leaves: the spelled boundary -/

theorem drop_end (a m : List Char) {k : Nat} (le : k ≤ m.length) :
    (a ++ m).drop ((a ++ m).length - k) = m.drop (m.length - k) := by
  rw [List.length_append, show a.length + m.length - k = a.length + (m.length - k) by omega,
    List.drop_append]
  simp

theorem take_end (a m : List Char) {k : Nat} (le : k ≤ m.length) :
    (a ++ m).take ((a ++ m).length - k) = a ++ m.take (m.length - k) := by
  rw [List.length_append, show a.length + m.length - k = a.length + (m.length - k) by omega,
    List.take_append]
  simp [List.take_of_length_le]

/-- The last character of a location. -/
def locLast : DataLoc → Char
  | .memory => 'y'
  | .storage => 'e'
  | .calldata => 'a'

/-- `locSuffix` splits a located spelling exactly at its location, whatever
the base (even one that itself ends in a location word). -/
theorem locL_located (b : String) (d : DataLoc) :
    locL (b.data ++ (locName d).data) = some (b, d) := by
  unfold locL
  cases d
  · rw [drop_end _ _ (by decide), take_end _ _ (by decide)]
    simp only [locName]
    rw [if_pos (by decide)]
    simp
  · rw [drop_end _ _ (by decide), drop_end _ _ (by decide), take_end _ _ (by decide)]
    simp only [locName]
    rw [if_neg (by decide), if_pos (by decide)]
    simp
  · rw [drop_end _ _ (by decide), drop_end _ _ (by decide), drop_end _ _ (by decide),
      take_end _ _ (by decide)]
    simp only [locName]
    rw [if_neg (by decide), if_neg (by decide), if_pos (by decide)]
    simp

theorem last_located (b : String) (d : DataLoc) :
    (b.data ++ (locName d).data).getLast? = some (locLast d) := by
  rw [List.getLast?_append]
  cases d <;> rfl

/-- A located spelling is read as no elementary type. -/
theorem elemFree_located (b : String) (d : DataLoc) : ElemFree (b ++ locName d) := by
  apply elemFree_of_last
  · intro x hx
    rw [String.data_append, last_located] at hx
    cases hx
    cases d <;> rfl
  · rw [String.data_append]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> have := last_located b d <;> rw [h] at this <;>
      cases d <;> cases this

/-- **Located leaves.** A spelling `b ++ locName d` is read back as the base
`b` at the location `d`. -/
theorem leaf_located (b : String) (d : DataLoc) : leaf (b ++ locName d) = .located b d := by
  have free := elemFree_located b d
  have e := leaf_mk (b ++ locName d).data
  refine e.trans ?_
  unfold leafL
  split
  · rename_i e' h
    exact absurd ((typeNameB_mk _).trans h) (free e')
  · rw [String.data_append, locL_located]

end Solidity.Correctness.Lowering.Total.FunctionTypeRoundTrip
