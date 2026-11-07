import Solidity.Frontend.ExpressionUniqueness.ExpressionBalance
import Solidity.Frontend.ExpressionUniqueness.SeparatorSplit

/-!
# Balanced words which do not begin with an opening brace

This is a first-token invariant only. Internal and later braces are permitted.
The original call-option constructor uses its nonempty base to preserve it.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def NoInitialCurly (ts : List Tok) : Prop := ∀ tail, ts ≠ .punct .lbrace :: tail

def StartFree (ts : List Tok) : Prop := Balanced ts ∧ NoInitialCurly ts

def StartFreeItems (items : List (List Tok)) : Prop := ∀ ts, ts ∈ items → StartFree ts

def curlyHead : Tok → Bool
  | .punct .lbrace => true
  | _ => false

theorem noInitialCurly_nil : NoInitialCurly [] := by intro tail h; cases h

theorem noInitialCurly_append_any {xs ys : List Tok} (hx : NoInitialCurly xs) (hne : xs ≠ []) :
    NoInitialCurly (xs ++ ys) := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons t ts =>
    intro tail he
    have token : t = .punct .lbrace := (List.cons.inj he).1
    exact hx ts (by rw [token])

theorem noInitialCurly_append {xs ys : List Tok} (hx : NoInitialCurly xs) (hy : NoInitialCurly ys) :
    NoInitialCurly (xs ++ ys) := by
  cases xs with
  | nil => exact hy
  | cons t ts => exact noInitialCurly_append_any hx (by intro h; cases h)

theorem startFree_nil : StartFree [] := ⟨balanced_nil, noInitialCurly_nil⟩

theorem startFree_balanced {ts : List Tok} (h : StartFree ts) : Balanced ts := h.1

theorem startFreeItems_balanced {items : List (List Tok)} (h : StartFreeItems items) :
    BalancedItems items := fun ts ht => (h ts ht).1

theorem startFree_append {xs ys : List Tok} (hx : StartFree xs) (hy : StartFree ys) :
    StartFree (xs ++ ys) := ⟨balanced_append hx.1 hy.1, noInitialCurly_append hx.2 hy.2⟩

theorem startFree_append_any {xs ys : List Tok} (hx : StartFree xs) (hne : xs ≠ []) (hy : Balanced ys) :
    StartFree (xs ++ ys) := ⟨balanced_append hx.1 hy, noInitialCurly_append_any hx.2 hne⟩

theorem startFree_atom {t : Tok} (hb : bracket t = none) (hc : curlyHead t = false) : StartFree [t] := by
  refine ⟨balanced_atom hb, ?_⟩
  intro tail he
  have token : t = .punct .lbrace := (List.cons.inj he).1
  rw [token] at hc
  cases hc

theorem startFreeItems_nil : StartFreeItems [] := by
  intro ts h
  cases h

theorem startFreeItems_cons {ts : List Tok} {items : List (List Tok)}
    (h : StartFree ts) (hs : StartFreeItems items) : StartFreeItems (ts :: items) := by
  intro xs hx
  rcases List.mem_cons.mp hx with he | hr
  · exact he ▸ h
  · exact hs xs hr

theorem startFreeItems_single {ts : List Tok} (h : StartFree ts) : StartFreeItems [ts] :=
  startFreeItems_cons h startFreeItems_nil

theorem startFreeItems_dropHead {ts : List Tok} {items : List (List Tok)}
    (h : StartFreeItems (ts :: items)) : StartFreeItems items := by
  intro xs hx
  exact h xs (List.mem_cons.mpr (Or.inr hx))

theorem startFreeItems_flatten {items : List (List Tok)} (h : StartFreeItems items) :
    StartFree items.flatten := by
  induction items with
  | nil => exact startFree_nil
  | cons ts items ih =>
    exact startFree_append (h ts (List.mem_cons.mpr (Or.inl rfl))) (ih (startFreeItems_dropHead h))

theorem startFree_flatMap {α : Type} (xs : List α) (f : α → List Tok)
    (h : ∀ x, x ∈ xs → StartFree (f x)) : StartFree (xs.flatMap f) := by
  induction xs with
  | nil => exact startFree_nil
  | cons x xs ih =>
    apply startFree_append (h x (List.mem_cons.mpr (Or.inl rfl)))
    exact ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))

theorem startFree_of_atoms (ts : List Tok) (h : ∀ t, t ∈ ts → bracket t = none ∧ curlyHead t = false) :
    StartFree ts := by
  induction ts with
  | nil => exact startFree_nil
  | cons t ts ih =>
    apply startFree_append (startFree_atom (h t (List.mem_cons.mpr (Or.inl rfl))).1 (h t (List.mem_cons.mpr (Or.inl rfl))).2)
    exact ih (fun u hu => h u (List.mem_cons.mpr (Or.inr hu)))

theorem startFree_parens {ts : List Tok} (h : Balanced ts) : StartFree (parens ts) := by
  refine ⟨balanced_parens h, ?_⟩
  intro tail he
  cases he

theorem startFree_square {ts : List Tok} (h : Balanced ts) :
    StartFree (pu .lbrack ++ ts ++ pu .rbrack) := by
  refine ⟨balanced_square h, ?_⟩
  intro tail he
  cases he

theorem startFree_tk (k : Kw) : StartFree (tk k) := startFree_atom rfl rfl

theorem startFree_idt (name : String) : StartFree (idt name) := startFree_atom rfl rfl

theorem startFree_path (p : IdPath) : StartFree p.toks := by
  apply startFree_append (startFree_idt p.head)
  apply startFree_flatMap p.tail
  intro name _
  exact startFree_append (startFree_atom rfl rfl) (startFree_idt name)

theorem startFree_elem (e : Elem) : StartFree e.toks := by
  cases e <;> first
    | exact startFree_atom rfl rfl
    | exact startFree_append (startFree_atom rfl rfl) (startFree_atom rfl rfl)

theorem startFree_visibility (v : Visibility) : StartFree v.toks := by
  cases v <;> exact startFree_tk _

theorem startFree_mutability (m : Mutability) : StartFree m.toks := by
  cases m <;> exact startFree_tk _

theorem startFree_dataLoc (l : DataLoc) : StartFree l.toks := by
  cases l <;> exact startFree_tk _

theorem startFree_optToks {α : Type} (f : α → List Tok) (h : ∀ a, StartFree (f a))
    (value : Option α) : StartFree (optToks f value) := by
  cases value with
  | none => exact startFree_nil
  | some a => exact h a

theorem startFree_prefix (op : PrefixOp) : StartFree op.punct := by
  cases op <;> exact startFree_atom rfl rfl

theorem startFree_suffix (op : SuffixOp) : StartFree (pu op.punct) := by
  cases op <;> exact startFree_atom rfl rfl

theorem startFree_mul (op : MulOp) : StartFree (pu op.punct) := by
  cases op <;> exact startFree_atom rfl rfl

theorem startFree_add (op : AddOp) : StartFree (pu op.punct) := by
  cases op <;> exact startFree_atom rfl rfl

theorem startFree_shift (op : ShiftOp) : StartFree (pu op.punct) := by
  cases op <;> exact startFree_atom rfl rfl

theorem startFree_order (op : OrderOp) : StartFree (pu op.punct) := by
  cases op <;> exact startFree_atom rfl rfl

theorem startFree_equality (op : EqOp) : StartFree (pu op.punct) := by
  cases op <;> exact startFree_atom rfl rfl

theorem startFree_assign (op : AssignOp) : StartFree (pu op.punct) := by
  cases op <;> exact startFree_atom rfl rfl

theorem fragsP_startFree (mk : Bytes → Tok) (hm : ∀ bs, bracket (mk bs) = none ∧ curlyHead (mk bs) = false)
    (bs : Bytes) : Produces (fragsP mk bs) StartFree := by
  intro initial ts rest h
  obtain ⟨cs, _, ht, _⟩ := fragsP_spec mk bs initial rest ts h
  rw [ht]
  apply startFree_of_atoms
  intro t ht
  obtain ⟨bytes, _, rfl⟩ := List.mem_map.mp ht
  exact hm bytes

theorem litP_startFree (l : Lit) : Produces (litP l) StartFree := by
  cases l with
  | bool b => exact produces_pure _ _ (startFree_atom rfl rfl)
  | num n => exact produces_pure _ _ (startFree_atom rfl rfl)
  | str bs => exact fragsP_startFree Tok.str (fun _ => ⟨rfl, rfl⟩) bs
  | hexStr bs => exact fragsP_startFree Tok.hexStr (fun _ => ⟨rfl, rfl⟩) bs
  | unicodeStr bs => exact fragsP_startFree Tok.unicodeStr (fun _ => ⟨rfl, rfl⟩) bs

def StartFreeAttrs (entries : List (Slot × List Tok)) : Prop :=
  ∀ entry, entry ∈ entries → StartFree entry.2

theorem startFreeAttrs_append {xs ys : List (Slot × List Tok)}
    (hx : StartFreeAttrs xs) (hy : StartFreeAttrs ys) : StartFreeAttrs (xs ++ ys) := by
  intro entry h
  rcases List.mem_append.mp h with h | h
  · exact hx entry h
  · exact hy entry h

theorem startFree_single (slot : Slot) (ts : List Tok) (h : StartFree ts) :
    StartFreeAttrs (single slot ts) := by
  unfold single
  split
  · intro entry he; cases he
  · intro entry he
    have heq : entry = (slot, ts) := by simpa only [List.mem_singleton] using he
    exact heq ▸ h

theorem arrange_startFree (order : List Slot) (singles : List (Slot × List Tok))
    (mods : List (List Tok)) (ts : List Tok) (hs : StartFreeAttrs singles)
    (hm : StartFreeItems mods) (h : arrange order singles mods = some ts) : StartFree ts := by
  induction order generalizing singles mods ts with
  | nil =>
    cases singles <;> cases mods <;> cases h
    exact startFree_nil
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
          apply heq ▸ startFree_append (hm word (List.mem_cons.mpr (Or.inl rfl)))
          exact ih singles mods suffix hs (startFreeItems_dropHead hm) hr
    · rw [arrange_nonModifier slot hslot] at h
      cases hf : singles.find? (·.1 == slot) with
      | none => rw [hf] at h; cases h
      | some entry =>
        rw [hf] at h
        have he : StartFree entry.2 := hs entry (List.mem_of_find?_eq_some hf)
        have hs' : StartFreeAttrs (singles.filter (·.1 != slot)) := by
          intro value hv
          exact hs value (List.mem_filter.mp hv).1
        cases hr : arrange order (singles.filter (·.1 != slot)) mods with
        | none => rw [hr] at h; cases h
        | some suffix =>
          rw [hr] at h
          have heq : entry.2 ++ suffix = ts := Option.some.inj h
          exact heq ▸ startFree_append he (ih _ mods suffix hs' hm hr)

theorem attrsP_startFree (singles : List (Slot × List Tok)) (mods : List (List Tok))
    (order : List Slot) (hs : StartFreeAttrs singles) (hm : StartFreeItems mods) :
    Produces (attrsP singles mods order) StartFree := by
  intro initial ts rest h
  change (arrange order singles mods).map (fun word => (word, initial)) = some (ts, rest) at h
  cases ha : arrange order singles mods with
  | none => rw [ha] at h; cases h
  | some word =>
    rw [ha] at h
    have heq : word = ts := (Prod.mk.inj (Option.some.inj h)).1
    exact heq ▸ arrange_startFree order singles mods word hs hm ha

end Solidity.Frontend.ExpressionUniqueness
