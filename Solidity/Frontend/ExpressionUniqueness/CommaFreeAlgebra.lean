import Solidity.Frontend.ExpressionUniqueness.ExpressionBalance
import Solidity.Frontend.ExpressionUniqueness.SeparatorSplit

/-!
# Comma-free token algebra for expression spans

Every comma-free word below is balanced. Enclosures use the established weaker
balanced-interior invariant, allowing arbitrarily many commas inside delimiters.
Function-type attribute ordering is handled through the existing layout API.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem run_of_skip (p : Tok → Bool) (ts : List Tok) (s next : List Bracket)
    (h : skip p s ts = some next) : run s ts = some next := by
  induction ts generalizing s with
  | nil => exact h
  | cons t ts ih =>
    cases hit : s.isEmpty && p t with
    | true => simp only [skip, hit, ↓reduceIte] at h; cases h
    | false =>
      cases hs : step s t with
      | none => simp only [skip, hit, Bool.false_eq_true, ↓reduceIte, hs, Option.bind_none] at h; cases h
      | some middle =>
        simp only [skip, hit, Bool.false_eq_true, ↓reduceIte, hs, Option.bind_some] at h
        simp only [run, hs, Option.bind_some]
        exact ih middle h

theorem commaFree_balanced {ts : List Tok} (h : CommaFree ts) : Balanced ts :=
  (balanced_iff_empty ts).mpr (run_of_skip isComma ts [] [] h)

theorem commaFreeItems_balanced {items : List (List Tok)} (h : CommaFreeItems items) :
    BalancedItems items := fun ts ht => commaFree_balanced (h ts ht)

theorem commaFree_append {xs ys : List Tok} (hx : CommaFree xs) (hy : CommaFree ys) :
    CommaFree (xs ++ ys) := by
  change skip isComma [] (xs ++ ys) = some []
  rw [skip_append, hx, Option.bind_some]
  exact hy

theorem commaFree_atom {t : Tok} (hb : bracket t = none) (hc : isComma t = false) :
    CommaFree [t] := by
  simp only [CommaFree, skip, List.isEmpty_nil, Bool.true_and, hc,
    Bool.false_eq_true, ↓reduceIte, step, hb, Option.bind_some]

theorem commaFreeItems_nil : CommaFreeItems [] := by
  intro ts h
  cases h

theorem commaFreeItems_cons {ts : List Tok} {items : List (List Tok)}
    (h : CommaFree ts) (hs : CommaFreeItems items) : CommaFreeItems (ts :: items) := by
  intro xs hx
  rcases List.mem_cons.mp hx with he | hr
  · exact he ▸ h
  · exact hs xs hr

theorem commaFreeItems_single {ts : List Tok} (h : CommaFree ts) : CommaFreeItems [ts] :=
  commaFreeItems_cons h commaFreeItems_nil

theorem commaFreeItems_dropHead {ts : List Tok} {items : List (List Tok)}
    (h : CommaFreeItems (ts :: items)) : CommaFreeItems items := by
  intro xs hx
  exact h xs (List.mem_cons.mpr (Or.inr hx))

theorem commaFreeItems_flatten {items : List (List Tok)} (h : CommaFreeItems items) :
    CommaFree items.flatten := by
  induction items with
  | nil => exact commaFree_nil
  | cons ts items ih =>
    exact commaFree_append (h ts (List.mem_cons.mpr (Or.inl rfl))) (ih (commaFreeItems_dropHead h))

theorem commaFree_flatMap {α : Type} (xs : List α) (f : α → List Tok)
    (h : ∀ x, x ∈ xs → CommaFree (f x)) : CommaFree (xs.flatMap f) := by
  induction xs with
  | nil => exact commaFree_nil
  | cons x xs ih =>
    apply commaFree_append (h x (List.mem_cons.mpr (Or.inl rfl)))
    exact ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))

theorem commaFree_of_atoms (ts : List Tok) (h : ∀ t, t ∈ ts → bracket t = none ∧ isComma t = false) :
    CommaFree ts := by
  induction ts with
  | nil => exact commaFree_nil
  | cons t ts ih =>
    apply commaFree_append (commaFree_atom (h t (List.mem_cons.mpr (Or.inl rfl))).1 (h t (List.mem_cons.mpr (Or.inl rfl))).2)
    exact ih (fun u hu => h u (List.mem_cons.mpr (Or.inr hu)))

theorem commaFree_parens {ts : List Tok} (h : Balanced ts) : CommaFree (parens ts) := by
  exact skip_enclose isComma .round h rfl

theorem commaFree_braces {ts : List Tok} (h : Balanced ts) : CommaFree (braces ts) := by
  exact skip_enclose isComma .curly h rfl

theorem commaFree_square {ts : List Tok} (h : Balanced ts) :
    CommaFree (pu .lbrack ++ ts ++ pu .rbrack) := by
  exact skip_enclose isComma .square h rfl

theorem commaFree_tk (k : Kw) : CommaFree (tk k) := commaFree_atom rfl rfl

theorem commaFree_idt (name : String) : CommaFree (idt name) := commaFree_atom rfl rfl

theorem commaFree_path (p : IdPath) : CommaFree p.toks := by
  apply commaFree_append (commaFree_idt p.head)
  apply commaFree_flatMap p.tail
  intro name _
  exact commaFree_append (commaFree_atom rfl rfl) (commaFree_idt name)

theorem commaFree_elem (e : Elem) : CommaFree e.toks := by
  cases e <;> first
    | exact commaFree_atom rfl rfl
    | exact commaFree_append (commaFree_atom rfl rfl) (commaFree_atom rfl rfl)

theorem commaFree_visibility (v : Visibility) : CommaFree v.toks := by
  cases v <;> exact commaFree_tk _

theorem commaFree_mutability (m : Mutability) : CommaFree m.toks := by
  cases m <;> exact commaFree_tk _

theorem commaFree_dataLoc (l : DataLoc) : CommaFree l.toks := by
  cases l <;> exact commaFree_tk _

theorem commaFree_optToks {α : Type} (f : α → List Tok) (h : ∀ a, CommaFree (f a))
    (value : Option α) : CommaFree (optToks f value) := by
  cases value with
  | none => exact commaFree_nil
  | some a => exact h a

theorem commaFree_prefix (op : PrefixOp) : CommaFree op.punct := by
  cases op <;> exact commaFree_atom rfl rfl

theorem commaFree_suffix (op : SuffixOp) : CommaFree (pu op.punct) := by
  cases op <;> exact commaFree_atom rfl rfl

theorem commaFree_mul (op : MulOp) : CommaFree (pu op.punct) := by
  cases op <;> exact commaFree_atom rfl rfl

theorem commaFree_add (op : AddOp) : CommaFree (pu op.punct) := by
  cases op <;> exact commaFree_atom rfl rfl

theorem commaFree_shift (op : ShiftOp) : CommaFree (pu op.punct) := by
  cases op <;> exact commaFree_atom rfl rfl

theorem commaFree_order (op : OrderOp) : CommaFree (pu op.punct) := by
  cases op <;> exact commaFree_atom rfl rfl

theorem commaFree_equality (op : EqOp) : CommaFree (pu op.punct) := by
  cases op <;> exact commaFree_atom rfl rfl

theorem commaFree_assign (op : AssignOp) : CommaFree (pu op.punct) := by
  cases op <;> exact commaFree_atom rfl rfl

theorem fragsP_commaFree (mk : Bytes → Tok) (hm : ∀ bs, bracket (mk bs) = none ∧ isComma (mk bs) = false)
    (bs : Bytes) : Produces (fragsP mk bs) CommaFree := by
  intro initial ts rest h
  obtain ⟨cs, _, ht, _⟩ := fragsP_spec mk bs initial rest ts h
  rw [ht]
  apply commaFree_of_atoms
  intro t ht
  obtain ⟨bytes, _, rfl⟩ := List.mem_map.mp ht
  exact hm bytes

theorem litP_commaFree (l : Lit) : Produces (litP l) CommaFree := by
  cases l with
  | bool b => exact produces_pure _ _ (commaFree_atom rfl rfl)
  | num n => exact produces_pure _ _ (commaFree_atom rfl rfl)
  | str bs => exact fragsP_commaFree Tok.str (fun _ => ⟨rfl, rfl⟩) bs
  | hexStr bs => exact fragsP_commaFree Tok.hexStr (fun _ => ⟨rfl, rfl⟩) bs
  | unicodeStr bs => exact fragsP_commaFree Tok.unicodeStr (fun _ => ⟨rfl, rfl⟩) bs

def CommaFreeAttrs (entries : List (Slot × List Tok)) : Prop :=
  ∀ entry, entry ∈ entries → CommaFree entry.2

theorem commaFreeAttrs_append {xs ys : List (Slot × List Tok)}
    (hx : CommaFreeAttrs xs) (hy : CommaFreeAttrs ys) : CommaFreeAttrs (xs ++ ys) := by
  intro entry h
  rcases List.mem_append.mp h with h | h
  · exact hx entry h
  · exact hy entry h

theorem commaFree_single (slot : Slot) (ts : List Tok) (h : CommaFree ts) :
    CommaFreeAttrs (single slot ts) := by
  unfold single
  split
  · intro entry he; cases he
  · intro entry he
    have heq : entry = (slot, ts) := by simpa only [List.mem_singleton] using he
    exact heq ▸ h

theorem arrange_commaFree (order : List Slot) (singles : List (Slot × List Tok))
    (mods : List (List Tok)) (ts : List Tok) (hs : CommaFreeAttrs singles)
    (hm : CommaFreeItems mods) (h : arrange order singles mods = some ts) : CommaFree ts := by
  induction order generalizing singles mods ts with
  | nil =>
    cases singles <;> cases mods <;> cases h
    exact commaFree_nil
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
          apply heq ▸ commaFree_append (hm word (List.mem_cons.mpr (Or.inl rfl)))
          exact ih singles mods suffix hs (commaFreeItems_dropHead hm) hr
    · rw [arrange_nonModifier slot hslot] at h
      cases hf : singles.find? (·.1 == slot) with
      | none => rw [hf] at h; cases h
      | some entry =>
        rw [hf] at h
        have he : CommaFree entry.2 := hs entry (List.mem_of_find?_eq_some hf)
        have hs' : CommaFreeAttrs (singles.filter (·.1 != slot)) := by
          intro value hv
          exact hs value (List.mem_filter.mp hv).1
        cases hr : arrange order (singles.filter (·.1 != slot)) mods with
        | none => rw [hr] at h; cases h
        | some suffix =>
          rw [hr] at h
          have heq : entry.2 ++ suffix = ts := Option.some.inj h
          exact heq ▸ commaFree_append he (ih _ mods suffix hs' hm hr)

theorem attrsP_commaFree (singles : List (Slot × List Tok)) (mods : List (List Tok))
    (order : List Slot) (hs : CommaFreeAttrs singles) (hm : CommaFreeItems mods) :
    Produces (attrsP singles mods order) CommaFree := by
  intro initial ts rest h
  change (arrange order singles mods).map (fun word => (word, initial)) = some (ts, rest) at h
  cases ha : arrange order singles mods with
  | none => rw [ha] at h; cases h
  | some word =>
    rw [ha] at h
    have heq : word = ts := (Prod.mk.inj (Option.some.inj h)).1
    exact heq ▸ arrange_commaFree order singles mods word hs hm ha

end Solidity.Frontend.ExpressionUniqueness
