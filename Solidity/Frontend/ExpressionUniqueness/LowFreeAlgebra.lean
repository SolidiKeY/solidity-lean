import Solidity.Frontend.ExpressionUniqueness.CommaFreeAlgebra
import Solidity.Frontend.ExpressionUniqueness.ReverseSplit

/-!
# Joint assignment and conditional marker algebra

The first loose-root selector includes every assignment operator and question
mark. Conditional middle branches may contain arbitrary assignments; selecting
the first marker is therefore essential. Expression precedence invariants are
proved separately, not supplied as a new producer premise.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def lowMarker : Tok → Bool
  | .punct .question | .punct .assign | .punct .assignBitOr | .punct .assignBitXor
  | .punct .assignBitAnd | .punct .assignShl | .punct .assignSar | .punct .assignShr
  | .punct .assignAdd | .punct .assignSub | .punct .assignMul | .punct .assignDiv
  | .punct .assignMod => true
  | _ => false

def LowFree (ts : List Tok) : Prop := skip lowMarker [] ts = some []

def LowFreeItems (items : List (List Tok)) : Prop := ∀ ts, ts ∈ items → LowFree ts

theorem lowMarker_atomic : AtomicSelector lowMarker := by
  intro k
  cases k <;> exact ⟨rfl, rfl⟩

theorem lowFree_nil : LowFree [] := rfl

theorem assignment_lowMarker (op : AssignOp) : lowMarker (.punct op.punct) = true := by
  cases op <;> rfl

theorem lowFree_balanced {ts : List Tok} (h : LowFree ts) : Balanced ts :=
  (balanced_iff_empty ts).mpr (run_of_skip lowMarker ts [] [] h)

theorem lowFreeItems_balanced {items : List (List Tok)} (h : LowFreeItems items) :
    BalancedItems items := fun ts ht => lowFree_balanced (h ts ht)

theorem lowFree_append {xs ys : List Tok} (hx : LowFree xs) (hy : LowFree ys) :
    LowFree (xs ++ ys) := by
  change skip lowMarker [] (xs ++ ys) = some []
  rw [skip_append, hx, Option.bind_some]
  exact hy

theorem lowFree_atom {t : Tok} (hb : bracket t = none) (hc : lowMarker t = false) :
    LowFree [t] := by
  simp only [LowFree, skip, List.isEmpty_nil, Bool.true_and, hc,
    Bool.false_eq_true, ↓reduceIte, step, hb, Option.bind_some]

theorem lowFreeItems_nil : LowFreeItems [] := by
  intro ts h
  cases h

theorem lowFreeItems_cons {ts : List Tok} {items : List (List Tok)}
    (h : LowFree ts) (hs : LowFreeItems items) : LowFreeItems (ts :: items) := by
  intro xs hx
  rcases List.mem_cons.mp hx with he | hr
  · exact he ▸ h
  · exact hs xs hr

theorem lowFreeItems_single {ts : List Tok} (h : LowFree ts) : LowFreeItems [ts] :=
  lowFreeItems_cons h lowFreeItems_nil

theorem lowFreeItems_dropHead {ts : List Tok} {items : List (List Tok)}
    (h : LowFreeItems (ts :: items)) : LowFreeItems items := by
  intro xs hx
  exact h xs (List.mem_cons.mpr (Or.inr hx))

theorem lowFreeItems_flatten {items : List (List Tok)} (h : LowFreeItems items) :
    LowFree items.flatten := by
  induction items with
  | nil => exact lowFree_nil
  | cons ts items ih =>
    exact lowFree_append (h ts (List.mem_cons.mpr (Or.inl rfl))) (ih (lowFreeItems_dropHead h))

theorem lowFree_flatMap {α : Type} (xs : List α) (f : α → List Tok)
    (h : ∀ x, x ∈ xs → LowFree (f x)) : LowFree (xs.flatMap f) := by
  induction xs with
  | nil => exact lowFree_nil
  | cons x xs ih =>
    apply lowFree_append (h x (List.mem_cons.mpr (Or.inl rfl)))
    exact ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))

theorem lowFree_of_atoms (ts : List Tok) (h : ∀ t, t ∈ ts → bracket t = none ∧ lowMarker t = false) :
    LowFree ts := by
  induction ts with
  | nil => exact lowFree_nil
  | cons t ts ih =>
    apply lowFree_append (lowFree_atom (h t (List.mem_cons.mpr (Or.inl rfl))).1 (h t (List.mem_cons.mpr (Or.inl rfl))).2)
    exact ih (fun u hu => h u (List.mem_cons.mpr (Or.inr hu)))

theorem lowFree_parens {ts : List Tok} (h : Balanced ts) : LowFree (parens ts) := by
  exact skip_enclose lowMarker .round h rfl

theorem lowFree_braces {ts : List Tok} (h : Balanced ts) : LowFree (braces ts) := by
  exact skip_enclose lowMarker .curly h rfl

theorem lowFree_square {ts : List Tok} (h : Balanced ts) :
    LowFree (pu .lbrack ++ ts ++ pu .rbrack) := by
  exact skip_enclose lowMarker .square h rfl

theorem lowFree_tk (k : Kw) : LowFree (tk k) := lowFree_atom rfl rfl

theorem lowFree_idt (name : String) : LowFree (idt name) := lowFree_atom rfl rfl

theorem lowFree_path (p : IdPath) : LowFree p.toks := by
  apply lowFree_append (lowFree_idt p.head)
  apply lowFree_flatMap p.tail
  intro name _
  exact lowFree_append (lowFree_atom rfl rfl) (lowFree_idt name)

theorem lowFree_elem (e : Elem) : LowFree e.toks := by
  cases e <;> first
    | exact lowFree_atom rfl rfl
    | exact lowFree_append (lowFree_atom rfl rfl) (lowFree_atom rfl rfl)

theorem lowFree_visibility (v : Visibility) : LowFree v.toks := by
  cases v <;> exact lowFree_tk _

theorem lowFree_mutability (m : Mutability) : LowFree m.toks := by
  cases m <;> exact lowFree_tk _

theorem lowFree_dataLoc (l : DataLoc) : LowFree l.toks := by
  cases l <;> exact lowFree_tk _

theorem lowFree_optToks {α : Type} (f : α → List Tok) (h : ∀ a, LowFree (f a))
    (value : Option α) : LowFree (optToks f value) := by
  cases value with
  | none => exact lowFree_nil
  | some a => exact h a

theorem lowFree_prefix (op : PrefixOp) : LowFree op.punct := by
  cases op <;> exact lowFree_atom rfl rfl

theorem lowFree_suffix (op : SuffixOp) : LowFree (pu op.punct) := by
  cases op <;> exact lowFree_atom rfl rfl

theorem lowFree_mul (op : MulOp) : LowFree (pu op.punct) := by
  cases op <;> exact lowFree_atom rfl rfl

theorem lowFree_add (op : AddOp) : LowFree (pu op.punct) := by
  cases op <;> exact lowFree_atom rfl rfl

theorem lowFree_shift (op : ShiftOp) : LowFree (pu op.punct) := by
  cases op <;> exact lowFree_atom rfl rfl

theorem lowFree_order (op : OrderOp) : LowFree (pu op.punct) := by
  cases op <;> exact lowFree_atom rfl rfl

theorem lowFree_equality (op : EqOp) : LowFree (pu op.punct) := by
  cases op <;> exact lowFree_atom rfl rfl

theorem fragsP_lowFree (mk : Bytes → Tok) (hm : ∀ bs, bracket (mk bs) = none ∧ lowMarker (mk bs) = false)
    (bs : Bytes) : Produces (fragsP mk bs) LowFree := by
  intro initial ts rest h
  obtain ⟨cs, _, ht, _⟩ := fragsP_spec mk bs initial rest ts h
  rw [ht]
  apply lowFree_of_atoms
  intro t ht
  obtain ⟨bytes, _, rfl⟩ := List.mem_map.mp ht
  exact hm bytes

theorem litP_lowFree (l : Lit) : Produces (litP l) LowFree := by
  cases l with
  | bool b => exact produces_pure _ _ (lowFree_atom rfl rfl)
  | num n => exact produces_pure _ _ (lowFree_atom rfl rfl)
  | str bs => exact fragsP_lowFree Tok.str (fun _ => ⟨rfl, rfl⟩) bs
  | hexStr bs => exact fragsP_lowFree Tok.hexStr (fun _ => ⟨rfl, rfl⟩) bs
  | unicodeStr bs => exact fragsP_lowFree Tok.unicodeStr (fun _ => ⟨rfl, rfl⟩) bs

def LowFreeAttrs (entries : List (Slot × List Tok)) : Prop :=
  ∀ entry, entry ∈ entries → LowFree entry.2

theorem lowFreeAttrs_append {xs ys : List (Slot × List Tok)}
    (hx : LowFreeAttrs xs) (hy : LowFreeAttrs ys) : LowFreeAttrs (xs ++ ys) := by
  intro entry h
  rcases List.mem_append.mp h with h | h
  · exact hx entry h
  · exact hy entry h

theorem lowFree_single (slot : Slot) (ts : List Tok) (h : LowFree ts) :
    LowFreeAttrs (single slot ts) := by
  unfold single
  split
  · intro entry he; cases he
  · intro entry he
    have heq : entry = (slot, ts) := by simpa only [List.mem_singleton] using he
    exact heq ▸ h

theorem arrange_lowFree (order : List Slot) (singles : List (Slot × List Tok))
    (mods : List (List Tok)) (ts : List Tok) (hs : LowFreeAttrs singles)
    (hm : LowFreeItems mods) (h : arrange order singles mods = some ts) : LowFree ts := by
  induction order generalizing singles mods ts with
  | nil =>
    cases singles <;> cases mods <;> cases h
    exact lowFree_nil
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
          apply heq ▸ lowFree_append (hm word (List.mem_cons.mpr (Or.inl rfl)))
          exact ih singles mods suffix hs (lowFreeItems_dropHead hm) hr
    · rw [arrange_nonModifier slot hslot] at h
      cases hf : singles.find? (·.1 == slot) with
      | none => rw [hf] at h; cases h
      | some entry =>
        rw [hf] at h
        have he : LowFree entry.2 := hs entry (List.mem_of_find?_eq_some hf)
        have hs' : LowFreeAttrs (singles.filter (·.1 != slot)) := by
          intro value hv
          exact hs value (List.mem_filter.mp hv).1
        cases hr : arrange order (singles.filter (·.1 != slot)) mods with
        | none => rw [hr] at h; cases h
        | some suffix =>
          rw [hr] at h
          have heq : entry.2 ++ suffix = ts := Option.some.inj h
          exact heq ▸ lowFree_append he (ih _ mods suffix hs' hm hr)

theorem attrsP_lowFree (singles : List (Slot × List Tok)) (mods : List (List Tok))
    (order : List Slot) (hs : LowFreeAttrs singles) (hm : LowFreeItems mods) :
    Produces (attrsP singles mods order) LowFree := by
  intro initial ts rest h
  change (arrange order singles mods).map (fun word => (word, initial)) = some (ts, rest) at h
  cases ha : arrange order singles mods with
  | none => rw [ha] at h; cases h
  | some word =>
    rw [ha] at h
    have heq : word = ts := (Prod.mk.inj (Option.some.inj h)).1
    exact heq ▸ arrange_lowFree order singles mods word hs hm ha

end Solidity.Frontend.ExpressionUniqueness
