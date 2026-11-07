import Solidity.Frontend.ExpressionUniqueness.ConditionalBalance
import Solidity.Frontend.ExpressionUniqueness.ExpressionBalance

/-!
# Conditional balance algebra for successful intrinsic yields

Neutral punctuation preserves the question depth. Enclosures rely only on raw
balanced interiors, so named-argument and slice colons remain permitted inside.
Actual attribute layout execution preserves this invariant.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def QBalancedItems (items : List (List Tok)) : Prop :=
  ∀ ts, ts ∈ items → QBalanced ts

theorem qBalancedItems_balanced {items : List (List Tok)} (h : QBalancedItems items) :
    BalancedItems items := fun ts ht => qBalanced_balanced (h ts ht)

theorem qBalancedItems_nil : QBalancedItems [] := by
  intro ts h
  cases h

theorem qBalancedItems_cons {ts : List Tok} {items : List (List Tok)}
    (h : QBalanced ts) (hs : QBalancedItems items) : QBalancedItems (ts :: items) := by
  intro xs hx
  rcases List.mem_cons.mp hx with he | hr
  · exact he ▸ h
  · exact hs xs hr

theorem qBalancedItems_single {ts : List Tok} (h : QBalanced ts) : QBalancedItems [ts] :=
  qBalancedItems_cons h qBalancedItems_nil

theorem qBalancedItems_dropHead {ts : List Tok} {items : List (List Tok)}
    (h : QBalancedItems (ts :: items)) : QBalancedItems items := by
  intro xs hx
  exact h xs (List.mem_cons.mpr (Or.inr hx))

theorem qBalancedItems_flatten {items : List (List Tok)} (h : QBalancedItems items) :
    QBalanced items.flatten := by
  induction items with
  | nil => exact qBalanced_nil
  | cons ts items ih =>
    exact qBalanced_append (h ts (List.mem_cons.mpr (Or.inl rfl))) (ih (qBalancedItems_dropHead h))

theorem qBalanced_flatMap {α : Type} (xs : List α) (f : α → List Tok)
    (h : ∀ x, x ∈ xs → QBalanced (f x)) : QBalanced (xs.flatMap f) := by
  induction xs with
  | nil => exact qBalanced_nil
  | cons x xs ih =>
    apply qBalanced_append (h x (List.mem_cons.mpr (Or.inl rfl)))
    exact ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))

theorem qBalanced_of_atoms (ts : List Tok) (h : ∀ t, t ∈ ts → bracket t = none ∧ qNeutral t = true) :
    QBalanced ts := by
  induction ts with
  | nil => exact qBalanced_nil
  | cons t ts ih =>
    apply qBalanced_append (qNeutral_atom (h t (List.mem_cons.mpr (Or.inl rfl))).1 (h t (List.mem_cons.mpr (Or.inl rfl))).2)
    exact ih (fun u hu => h u (List.mem_cons.mpr (Or.inr hu)))

theorem qBalanced_parens {ts : List Tok} (h : Balanced ts) : QBalanced (parens ts) := by
  exact qBalanced_enclose .round _ h

theorem qBalanced_braces {ts : List Tok} (h : Balanced ts) : QBalanced (braces ts) := by
  exact qBalanced_enclose .curly _ h

theorem qBalanced_square {ts : List Tok} (h : Balanced ts) :
    QBalanced (pu .lbrack ++ ts ++ pu .rbrack) := by
  exact qBalanced_enclose .square _ h

theorem qBalanced_tk (k : Kw) : QBalanced (tk k) := qNeutral_atom rfl rfl

theorem qBalanced_idt (name : String) : QBalanced (idt name) := qNeutral_atom rfl rfl

theorem qBalanced_path (p : IdPath) : QBalanced p.toks := by
  apply qBalanced_append (qBalanced_idt p.head)
  apply qBalanced_flatMap p.tail
  intro name _
  exact qBalanced_append (qNeutral_atom rfl rfl) (qBalanced_idt name)

theorem qBalanced_elem (e : Elem) : QBalanced e.toks := by
  cases e <;> first
    | exact qNeutral_atom rfl rfl
    | exact qBalanced_append (qNeutral_atom rfl rfl) (qNeutral_atom rfl rfl)

theorem qBalanced_visibility (v : Visibility) : QBalanced v.toks := by
  cases v <;> exact qBalanced_tk _

theorem qBalanced_mutability (m : Mutability) : QBalanced m.toks := by
  cases m <;> exact qBalanced_tk _

theorem qBalanced_dataLoc (l : DataLoc) : QBalanced l.toks := by
  cases l <;> exact qBalanced_tk _

theorem qBalanced_optToks {α : Type} (f : α → List Tok) (h : ∀ a, QBalanced (f a))
    (value : Option α) : QBalanced (optToks f value) := by
  cases value with
  | none => exact qBalanced_nil
  | some a => exact h a

theorem qBalanced_prefix (op : PrefixOp) : QBalanced op.punct := by
  cases op <;> exact qNeutral_atom rfl rfl

theorem qBalanced_suffix (op : SuffixOp) : QBalanced (pu op.punct) := by
  cases op <;> exact qNeutral_atom rfl rfl

theorem qBalanced_mul (op : MulOp) : QBalanced (pu op.punct) := by
  cases op <;> exact qNeutral_atom rfl rfl

theorem qBalanced_add (op : AddOp) : QBalanced (pu op.punct) := by
  cases op <;> exact qNeutral_atom rfl rfl

theorem qBalanced_shift (op : ShiftOp) : QBalanced (pu op.punct) := by
  cases op <;> exact qNeutral_atom rfl rfl

theorem qBalanced_order (op : OrderOp) : QBalanced (pu op.punct) := by
  cases op <;> exact qNeutral_atom rfl rfl

theorem qBalanced_equality (op : EqOp) : QBalanced (pu op.punct) := by
  cases op <;> exact qNeutral_atom rfl rfl

theorem qBalanced_assign (op : AssignOp) : QBalanced (pu op.punct) := by
  cases op <;> exact qNeutral_atom rfl rfl

theorem fragsP_qBalanced (mk : Bytes → Tok) (hm : ∀ bs, bracket (mk bs) = none ∧ qNeutral (mk bs) = true)
    (bs : Bytes) : Produces (fragsP mk bs) QBalanced := by
  intro initial ts rest h
  obtain ⟨cs, _, ht, _⟩ := fragsP_spec mk bs initial rest ts h
  rw [ht]
  apply qBalanced_of_atoms
  intro t ht
  obtain ⟨bytes, _, rfl⟩ := List.mem_map.mp ht
  exact hm bytes

theorem litP_qBalanced (l : Lit) : Produces (litP l) QBalanced := by
  cases l with
  | bool b => exact produces_pure _ _ (qNeutral_atom rfl rfl)
  | num n => exact produces_pure _ _ (qNeutral_atom rfl rfl)
  | str bs => exact fragsP_qBalanced Tok.str (fun _ => ⟨rfl, rfl⟩) bs
  | hexStr bs => exact fragsP_qBalanced Tok.hexStr (fun _ => ⟨rfl, rfl⟩) bs
  | unicodeStr bs => exact fragsP_qBalanced Tok.unicodeStr (fun _ => ⟨rfl, rfl⟩) bs

def QBalancedAttrs (entries : List (Slot × List Tok)) : Prop :=
  ∀ entry, entry ∈ entries → QBalanced entry.2

theorem qBalancedAttrs_append {xs ys : List (Slot × List Tok)}
    (hx : QBalancedAttrs xs) (hy : QBalancedAttrs ys) : QBalancedAttrs (xs ++ ys) := by
  intro entry h
  rcases List.mem_append.mp h with h | h
  · exact hx entry h
  · exact hy entry h

theorem qBalanced_single (slot : Slot) (ts : List Tok) (h : QBalanced ts) :
    QBalancedAttrs (single slot ts) := by
  unfold single
  split
  · intro entry he; cases he
  · intro entry he
    have heq : entry = (slot, ts) := by simpa only [List.mem_singleton] using he
    exact heq ▸ h

theorem arrange_qBalanced (order : List Slot) (singles : List (Slot × List Tok))
    (mods : List (List Tok)) (ts : List Tok) (hs : QBalancedAttrs singles)
    (hm : QBalancedItems mods) (h : arrange order singles mods = some ts) : QBalanced ts := by
  induction order generalizing singles mods ts with
  | nil =>
    cases singles <;> cases mods <;> cases h
    exact qBalanced_nil
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
          apply heq ▸ qBalanced_append (hm word (List.mem_cons.mpr (Or.inl rfl)))
          exact ih singles mods suffix hs (qBalancedItems_dropHead hm) hr
    · rw [arrange_nonModifier slot hslot] at h
      cases hf : singles.find? (·.1 == slot) with
      | none => rw [hf] at h; cases h
      | some entry =>
        rw [hf] at h
        have he : QBalanced entry.2 := hs entry (List.mem_of_find?_eq_some hf)
        have hs' : QBalancedAttrs (singles.filter (·.1 != slot)) := by
          intro value hv
          exact hs value (List.mem_filter.mp hv).1
        cases hr : arrange order (singles.filter (·.1 != slot)) mods with
        | none => rw [hr] at h; cases h
        | some suffix =>
          rw [hr] at h
          have heq : entry.2 ++ suffix = ts := Option.some.inj h
          exact heq ▸ qBalanced_append he (ih _ mods suffix hs' hm hr)

theorem attrsP_qBalanced (singles : List (Slot × List Tok)) (mods : List (List Tok))
    (order : List Slot) (hs : QBalancedAttrs singles) (hm : QBalancedItems mods) :
    Produces (attrsP singles mods order) QBalanced := by
  intro initial ts rest h
  change (arrange order singles mods).map (fun word => (word, initial)) = some (ts, rest) at h
  cases ha : arrange order singles mods with
  | none => rw [ha] at h; cases h
  | some word =>
    rw [ha] at h
    have heq : word = ts := (Prod.mk.inj (Option.some.inj h)).1
    exact heq ▸ arrange_qBalanced order singles mods word hs hm ha

end Solidity.Frontend.ExpressionUniqueness
