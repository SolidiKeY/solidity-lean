import Solidity.Frontend.ExpressionUniqueness.CommaFreeAlgebra
import Solidity.Frontend.ExpressionUniqueness.ReverseSplit

/-!
# Unary-marker freedom above unary expression roots

The selector includes all six prefix tokens and both suffix tokens. High-root
expression and type/call-argument freedom is derived separately from original
certificates; no original syntax or uniqueness target is restricted.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def unaryMarker : Tok → Bool
  | .punct .inc | .punct .dec | .punct .not | .punct .bitNot | .punct .sub | .kw .delete => true
  | _ => false

def UnaryFree (ts : List Tok) : Prop := skip unaryMarker [] ts = some []

def UnaryFreeItems (items : List (List Tok)) : Prop := ∀ ts, ts ∈ items → UnaryFree ts

theorem unaryMarker_atomic : AtomicSelector unaryMarker := by
  intro k
  cases k <;> exact ⟨rfl, rfl⟩

theorem unaryFree_nil : UnaryFree [] := rfl

theorem unaryFree_balanced {ts : List Tok} (h : UnaryFree ts) : Balanced ts :=
  (balanced_iff_empty ts).mpr (run_of_skip unaryMarker ts [] [] h)

theorem unaryFreeItems_balanced {items : List (List Tok)} (h : UnaryFreeItems items) :
    BalancedItems items := fun ts ht => unaryFree_balanced (h ts ht)

theorem unaryFree_append {xs ys : List Tok} (hx : UnaryFree xs) (hy : UnaryFree ys) :
    UnaryFree (xs ++ ys) := by
  change skip unaryMarker [] (xs ++ ys) = some []
  rw [skip_append, hx, Option.bind_some]
  exact hy

theorem unaryFree_atom {t : Tok} (hb : bracket t = none) (hc : unaryMarker t = false) :
    UnaryFree [t] := by
  simp only [UnaryFree, skip, List.isEmpty_nil, Bool.true_and, hc,
    Bool.false_eq_true, ↓reduceIte, step, hb, Option.bind_some]

theorem unaryFreeItems_nil : UnaryFreeItems [] := by
  intro ts h
  cases h

theorem unaryFreeItems_cons {ts : List Tok} {items : List (List Tok)}
    (h : UnaryFree ts) (hs : UnaryFreeItems items) : UnaryFreeItems (ts :: items) := by
  intro xs hx
  rcases List.mem_cons.mp hx with he | hr
  · exact he ▸ h
  · exact hs xs hr

theorem unaryFreeItems_single {ts : List Tok} (h : UnaryFree ts) : UnaryFreeItems [ts] :=
  unaryFreeItems_cons h unaryFreeItems_nil

theorem unaryFreeItems_dropHead {ts : List Tok} {items : List (List Tok)}
    (h : UnaryFreeItems (ts :: items)) : UnaryFreeItems items := by
  intro xs hx
  exact h xs (List.mem_cons.mpr (Or.inr hx))

theorem unaryFreeItems_flatten {items : List (List Tok)} (h : UnaryFreeItems items) :
    UnaryFree items.flatten := by
  induction items with
  | nil => exact unaryFree_nil
  | cons ts items ih =>
    exact unaryFree_append (h ts (List.mem_cons.mpr (Or.inl rfl))) (ih (unaryFreeItems_dropHead h))

theorem unaryFree_flatMap {α : Type} (xs : List α) (f : α → List Tok)
    (h : ∀ x, x ∈ xs → UnaryFree (f x)) : UnaryFree (xs.flatMap f) := by
  induction xs with
  | nil => exact unaryFree_nil
  | cons x xs ih =>
    apply unaryFree_append (h x (List.mem_cons.mpr (Or.inl rfl)))
    exact ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))

theorem unaryFree_of_atoms (ts : List Tok) (h : ∀ t, t ∈ ts → bracket t = none ∧ unaryMarker t = false) :
    UnaryFree ts := by
  induction ts with
  | nil => exact unaryFree_nil
  | cons t ts ih =>
    apply unaryFree_append (unaryFree_atom (h t (List.mem_cons.mpr (Or.inl rfl))).1 (h t (List.mem_cons.mpr (Or.inl rfl))).2)
    exact ih (fun u hu => h u (List.mem_cons.mpr (Or.inr hu)))

theorem unaryFree_parens {ts : List Tok} (h : Balanced ts) : UnaryFree (parens ts) := by
  exact skip_enclose unaryMarker .round h rfl

theorem unaryFree_braces {ts : List Tok} (h : Balanced ts) : UnaryFree (braces ts) := by
  exact skip_enclose unaryMarker .curly h rfl

theorem unaryFree_square {ts : List Tok} (h : Balanced ts) :
    UnaryFree (pu .lbrack ++ ts ++ pu .rbrack) := by
  exact skip_enclose unaryMarker .square h rfl

theorem unaryFree_tk (k : Kw) (h : unaryMarker (.kw k) = false) : UnaryFree (tk k) := unaryFree_atom rfl h

theorem unaryFree_idt (name : String) : UnaryFree (idt name) := unaryFree_atom rfl rfl

theorem unaryFree_path (p : IdPath) : UnaryFree p.toks := by
  apply unaryFree_append (unaryFree_idt p.head)
  apply unaryFree_flatMap p.tail
  intro name _
  exact unaryFree_append (unaryFree_atom rfl rfl) (unaryFree_idt name)

theorem unaryFree_elem (e : Elem) : UnaryFree e.toks := by
  cases e <;> first
    | exact unaryFree_atom rfl rfl
    | exact unaryFree_append (unaryFree_atom rfl rfl) (unaryFree_atom rfl rfl)

theorem unaryFree_visibility (v : Visibility) : UnaryFree v.toks := by
  cases v <;> exact unaryFree_tk _ rfl

theorem unaryFree_mutability (m : Mutability) : UnaryFree m.toks := by
  cases m <;> exact unaryFree_tk _ rfl

theorem unaryFree_dataLoc (l : DataLoc) : UnaryFree l.toks := by
  cases l <;> exact unaryFree_tk _ rfl

theorem unaryFree_optToks {α : Type} (f : α → List Tok) (h : ∀ a, UnaryFree (f a))
    (value : Option α) : UnaryFree (optToks f value) := by
  cases value with
  | none => exact unaryFree_nil
  | some a => exact h a

theorem unaryFree_mul (op : MulOp) : UnaryFree (pu op.punct) := by
  cases op <;> exact unaryFree_atom rfl rfl

theorem unaryFree_shift (op : ShiftOp) : UnaryFree (pu op.punct) := by
  cases op <;> exact unaryFree_atom rfl rfl

theorem unaryFree_order (op : OrderOp) : UnaryFree (pu op.punct) := by
  cases op <;> exact unaryFree_atom rfl rfl

theorem unaryFree_equality (op : EqOp) : UnaryFree (pu op.punct) := by
  cases op <;> exact unaryFree_atom rfl rfl

theorem fragsP_unaryFree (mk : Bytes → Tok) (hm : ∀ bs, bracket (mk bs) = none ∧ unaryMarker (mk bs) = false)
    (bs : Bytes) : Produces (fragsP mk bs) UnaryFree := by
  intro initial ts rest h
  obtain ⟨cs, _, ht, _⟩ := fragsP_spec mk bs initial rest ts h
  rw [ht]
  apply unaryFree_of_atoms
  intro t ht
  obtain ⟨bytes, _, rfl⟩ := List.mem_map.mp ht
  exact hm bytes

theorem litP_unaryFree (l : Lit) : Produces (litP l) UnaryFree := by
  cases l with
  | bool b => exact produces_pure _ _ (unaryFree_atom rfl rfl)
  | num n => exact produces_pure _ _ (unaryFree_atom rfl rfl)
  | str bs => exact fragsP_unaryFree Tok.str (fun _ => ⟨rfl, rfl⟩) bs
  | hexStr bs => exact fragsP_unaryFree Tok.hexStr (fun _ => ⟨rfl, rfl⟩) bs
  | unicodeStr bs => exact fragsP_unaryFree Tok.unicodeStr (fun _ => ⟨rfl, rfl⟩) bs

def UnaryFreeAttrs (entries : List (Slot × List Tok)) : Prop :=
  ∀ entry, entry ∈ entries → UnaryFree entry.2

theorem unaryFreeAttrs_append {xs ys : List (Slot × List Tok)}
    (hx : UnaryFreeAttrs xs) (hy : UnaryFreeAttrs ys) : UnaryFreeAttrs (xs ++ ys) := by
  intro entry h
  rcases List.mem_append.mp h with h | h
  · exact hx entry h
  · exact hy entry h

theorem unaryFree_single (slot : Slot) (ts : List Tok) (h : UnaryFree ts) :
    UnaryFreeAttrs (single slot ts) := by
  unfold single
  split
  · intro entry he; cases he
  · intro entry he
    have heq : entry = (slot, ts) := by simpa only [List.mem_singleton] using he
    exact heq ▸ h

theorem arrange_unaryFree (order : List Slot) (singles : List (Slot × List Tok))
    (mods : List (List Tok)) (ts : List Tok) (hs : UnaryFreeAttrs singles)
    (hm : UnaryFreeItems mods) (h : arrange order singles mods = some ts) : UnaryFree ts := by
  induction order generalizing singles mods ts with
  | nil =>
    cases singles <;> cases mods <;> cases h
    exact unaryFree_nil
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
          apply heq ▸ unaryFree_append (hm word (List.mem_cons.mpr (Or.inl rfl)))
          exact ih singles mods suffix hs (unaryFreeItems_dropHead hm) hr
    · rw [arrange_nonModifier slot hslot] at h
      cases hf : singles.find? (·.1 == slot) with
      | none => rw [hf] at h; cases h
      | some entry =>
        rw [hf] at h
        have he : UnaryFree entry.2 := hs entry (List.mem_of_find?_eq_some hf)
        have hs' : UnaryFreeAttrs (singles.filter (·.1 != slot)) := by
          intro value hv
          exact hs value (List.mem_filter.mp hv).1
        cases hr : arrange order (singles.filter (·.1 != slot)) mods with
        | none => rw [hr] at h; cases h
        | some suffix =>
          rw [hr] at h
          have heq : entry.2 ++ suffix = ts := Option.some.inj h
          exact heq ▸ unaryFree_append he (ih _ mods suffix hs' hm hr)

theorem attrsP_unaryFree (singles : List (Slot × List Tok)) (mods : List (List Tok))
    (order : List Slot) (hs : UnaryFreeAttrs singles) (hm : UnaryFreeItems mods) :
    Produces (attrsP singles mods order) UnaryFree := by
  intro initial ts rest h
  change (arrange order singles mods).map (fun word => (word, initial)) = some (ts, rest) at h
  cases ha : arrange order singles mods with
  | none => rw [ha] at h; cases h
  | some word =>
    rw [ha] at h
    have heq : word = ts := (Prod.mk.inj (Option.some.inj h)).1
    exact heq ▸ arrange_unaryFree order singles mods word hs hm ha

end Solidity.Frontend.ExpressionUniqueness
