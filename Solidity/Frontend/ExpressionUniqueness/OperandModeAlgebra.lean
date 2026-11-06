import Solidity.Frontend.ExpressionUniqueness.OperandMode
import Solidity.Frontend.ExpressionUniqueness.AttributeBalance

/-!
# Operand-mode algebra for literal fragments, types and attribute layouts

Completion is forced by every atom and outer enclosure. Completed-state-preserving
words form a monoid, including empty attribute words and arbitrary successful
existing attribute orderings. Literal fragment vectors are nonempty by their
actual layout certificate, even for empty payload bytes.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def ModeStableItems (items : List (List Tok)) : Prop := ∀ ts, ts ∈ items → ModeStable ts

theorem modeStableItems_nil : ModeStableItems [] := by
  intro ts ht
  cases ht

theorem modeStableItems_tail {ts : List Tok} {items : List (List Tok)}
    (h : ModeStableItems (ts :: items)) : ModeStableItems items := by
  intro xs hx
  exact h xs (List.mem_cons.mpr (Or.inr hx))

theorem modeStable_flatMap {α : Type} (xs : List α) (f : α → List Tok)
    (h : ∀ x, x ∈ xs → ModeStable (f x)) : ModeStable (xs.flatMap f) := by
  induction xs with
  | nil => exact modeStable_nil
  | cons x xs ih =>
    apply modeStable_append (h x (List.mem_cons.mpr (Or.inl rfl)))
    exact ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))

theorem modeStable_of_atoms (ts : List Tok)
    (h : ∀ t, t ∈ ts → bracket t = none ∧ modeToken true t = true) : ModeStable ts := by
  induction ts with
  | nil => exact modeStable_nil
  | cons t ts ih =>
    apply modeStable_append (modeStable_atom t (h t (List.mem_cons.mpr (Or.inl rfl))).1
      (h t (List.mem_cons.mpr (Or.inl rfl))).2)
    exact ih (fun u hu => h u (List.mem_cons.mpr (Or.inr hu)))

theorem modeDone_map_nonempty {α : Type} (xs : List α) (mk : α → Tok) (hne : xs ≠ [])
    (hb : ∀ x, bracket (mk x) = none) (hm : ∀ x finished, modeToken finished (mk x) = true) :
    ModeDone (xs.map mk) := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
    apply modeDone_stable_append (modeDone_atom (mk x) (hb x) (hm x))
    apply modeStable_of_atoms
    intro t ht
    obtain ⟨value, _, rfl⟩ := List.mem_map.mp ht
    exact ⟨hb value, hm value true⟩

theorem modeDone_parens {ts : List Tok} (h : Balanced ts) : ModeDone (parens ts) :=
  modeDone_enclose .round ts h

theorem modeDone_braces {ts : List Tok} (h : Balanced ts) : ModeDone (braces ts) :=
  modeDone_enclose .curly ts h

theorem modeDone_square {ts : List Tok} (h : Balanced ts) :
    ModeDone (pu .lbrack ++ ts ++ pu .rbrack) := modeDone_enclose .square ts h

theorem modeDone_idt (name : String) : ModeDone (idt name) :=
  modeDone_atom _ rfl (fun _ => rfl)

theorem modeDone_path (path : IdPath) : ModeDone path.toks := by
  apply modeDone_stable_append (modeDone_idt path.head)
  apply modeStable_flatMap path.tail
  intro name _
  apply modeDone_stable
  apply modeDone_append (balanced_modeAny _ (balanced_atom rfl)) (modeDone_idt name)

theorem modeDone_elem (e : Elem) : ModeDone e.toks := by
  cases e <;> first
    | exact modeDone_atom _ rfl (fun _ => rfl)
    | exact modeDone_stable_append (modeDone_atom _ rfl (fun _ => rfl))
        (modeStable_atom _ rfl rfl)

theorem modeStable_visibility (v : Visibility) : ModeStable v.toks := by
  cases v <;> exact modeStable_atom _ rfl rfl

theorem modeStable_mutability (m : Mutability) : ModeStable m.toks := by
  cases m <;> exact modeStable_atom _ rfl rfl

theorem modeStable_dataLoc (l : DataLoc) : ModeStable l.toks := by
  cases l <;> exact modeStable_atom _ rfl rfl

theorem modeStable_optToks {α : Type} (f : α → List Tok) (h : ∀ x, ModeStable (f x))
    (value : Option α) : ModeStable (optToks f value) := by
  cases value with
  | none => exact modeStable_nil
  | some x => exact h x

theorem fragsP_modeDone (mk : Bytes → Tok) (hb : ∀ bs, bracket (mk bs) = none)
    (hm : ∀ bs finished, modeToken finished (mk bs) = true) (bs : Bytes) :
    Produces (fragsP mk bs) ModeDone := by
  intro initial ts rest h
  obtain ⟨cs, _, ht, hcs⟩ := fragsP_spec mk bs initial rest ts h
  rw [ht]
  exact modeDone_map_nonempty cs mk hcs hb hm

theorem litP_modeDone (l : Lit) : Produces (litP l) ModeDone := by
  cases l with
  | bool b => exact produces_pure _ _ (modeDone_atom _ rfl (fun _ => rfl))
  | num n => exact produces_pure _ _ (modeDone_atom _ rfl (fun _ => rfl))
  | str bs => exact fragsP_modeDone Tok.str (fun _ => rfl) (fun _ _ => rfl) bs
  | hexStr bs => exact fragsP_modeDone Tok.hexStr (fun _ => rfl) (fun _ _ => rfl) bs
  | unicodeStr bs => exact fragsP_modeDone Tok.unicodeStr (fun _ => rfl) (fun _ _ => rfl) bs

def ModeStableAttrs (entries : List (Slot × List Tok)) : Prop :=
  ∀ entry, entry ∈ entries → ModeStable entry.2

theorem modeStableAttrs_append {xs ys : List (Slot × List Tok)}
    (hx : ModeStableAttrs xs) (hy : ModeStableAttrs ys) : ModeStableAttrs (xs ++ ys) := by
  intro entry h
  rcases List.mem_append.mp h with h | h
  · exact hx entry h
  · exact hy entry h

theorem modeStable_single (slot : Slot) (ts : List Tok) (h : ModeStable ts) :
    ModeStableAttrs (single slot ts) := by
  unfold single
  split
  · intro entry he; cases he
  · intro entry he
    have heq : entry = (slot, ts) := by simpa only [List.mem_singleton] using he
    exact heq ▸ h

theorem arrange_modeStable (order : List Slot) (singles : List (Slot × List Tok))
    (mods : List (List Tok)) (ts : List Tok) (hs : ModeStableAttrs singles)
    (hm : ModeStableItems mods) (h : arrange order singles mods = some ts) : ModeStable ts := by
  induction order generalizing singles mods ts with
  | nil =>
    cases singles <;> cases mods <;> cases h
    exact modeStable_nil
  | cons slot order ih =>
    by_cases hslot : slot = .modInv
    · subst slot
      cases mods with
      | nil => cases h
      | cons word mods =>
        change (arrange order singles mods).map (word ++ ·) = some ts at h
        cases hr : arrange order singles mods with
        | none => rw [hr] at h; cases h
        | some suffix =>
          rw [hr] at h
          have heq : word ++ suffix = ts := Option.some.inj h
          apply heq ▸ modeStable_append (hm word (List.mem_cons.mpr (Or.inl rfl)))
          exact ih singles mods suffix hs (modeStableItems_tail hm) hr
    · rw [arrange_nonModifier slot hslot] at h
      cases hf : singles.find? (·.1 == slot) with
      | none => rw [hf] at h; cases h
      | some entry =>
        rw [hf] at h
        have he : ModeStable entry.2 := hs entry (List.mem_of_find?_eq_some hf)
        have hs' : ModeStableAttrs (singles.filter (·.1 != slot)) := by
          intro value hv
          exact hs value (List.mem_filter.mp hv).1
        cases hr : arrange order (singles.filter (·.1 != slot)) mods with
        | none => rw [hr] at h; cases h
        | some suffix =>
          rw [hr] at h
          have heq : entry.2 ++ suffix = ts := Option.some.inj h
          exact heq ▸ modeStable_append he (ih _ mods suffix hs' hm hr)

theorem attrsP_modeStable (singles : List (Slot × List Tok)) (mods : List (List Tok))
    (order : List Slot) (hs : ModeStableAttrs singles) (hm : ModeStableItems mods) :
    Produces (attrsP singles mods order) ModeStable := by
  intro initial ts rest h
  change (arrange order singles mods).map (fun word => (word, initial)) = some (ts, rest) at h
  cases ha : arrange order singles mods with
  | none => rw [ha] at h; cases h
  | some word =>
    rw [ha] at h
    have heq : word = ts := (Prod.mk.inj (Option.some.inj h)).1
    exact heq ▸ arrange_modeStable order singles mods word hs hm ha

end Solidity.Frontend.ExpressionUniqueness
