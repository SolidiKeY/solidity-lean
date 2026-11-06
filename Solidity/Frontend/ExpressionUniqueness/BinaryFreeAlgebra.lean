import Solidity.Frontend.ExpressionUniqueness.LowFreeAlgebra

/-!
# Parameterized binary marker algebra

Marker levels follow the existing Syn.level values. Their operator punctuation
is disjoint from delimiters. Prefix minus shares the level-10 marker, so the
prefix helper states that precise limitation; no expression uniqueness theorem
is restricted or replaced by this intermediate token algebra.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def binaryMarker (rank : Nat) : Tok → Bool
  | .punct .or => decide (rank = 2)
  | .punct .and => decide (rank = 3)
  | .punct .equal | .punct .notEqual => decide (rank = 4)
  | .punct .lt | .punct .gt | .punct .le | .punct .ge => decide (rank = 5)
  | .punct .bitOr => decide (rank = 6)
  | .punct .bitXor => decide (rank = 7)
  | .punct .bitAnd => decide (rank = 8)
  | .punct .shl | .punct .sar | .punct .shr => decide (rank = 9)
  | .punct .add | .punct .sub => decide (rank = 10)
  | .punct .mul | .punct .div | .punct .mod => decide (rank = 11)
  | .punct .exp => decide (rank = 12)
  | _ => false

def BinaryFree (rank : Nat) (ts : List Tok) : Prop := skip (binaryMarker rank) [] ts = some []

def BinaryFreeItems (rank : Nat) (items : List (List Tok)) : Prop :=
  ∀ ts, ts ∈ items → BinaryFree rank ts

theorem binaryMarker_atomic (rank : Nat) : AtomicSelector (binaryMarker rank) := by
  intro k
  cases k <;> exact ⟨rfl, rfl⟩

theorem binaryFree_nil {rank : Nat} : BinaryFree rank [] := rfl

theorem binaryFree_balanced {rank : Nat} {ts : List Tok} (h : (BinaryFree rank) ts) : Balanced ts :=
  (balanced_iff_empty ts).mpr (run_of_skip (binaryMarker rank) ts [] [] h)

theorem binaryFreeItems_balanced {rank : Nat} {items : List (List Tok)} (h : (BinaryFreeItems rank) items) :
    BalancedItems items := fun ts ht => binaryFree_balanced (h ts ht)

theorem binaryFree_append {rank : Nat} {xs ys : List Tok} (hx : (BinaryFree rank) xs) (hy : (BinaryFree rank) ys) :
    (BinaryFree rank) (xs ++ ys) := by
  change skip (binaryMarker rank) [] (xs ++ ys) = some []
  rw [skip_append, hx, Option.bind_some]
  exact hy

theorem binaryFree_atom {rank : Nat} {t : Tok} (hb : bracket t = none) (hc : (binaryMarker rank) t = false) :
    (BinaryFree rank) [t] := by
  simp only [BinaryFree, skip, List.isEmpty_nil, Bool.true_and, hc,
    Bool.false_eq_true, ↓reduceIte, step, hb, Option.bind_some]

theorem binaryFreeItems_nil {rank : Nat} : (BinaryFreeItems rank) [] := by
  intro ts h
  cases h

theorem binaryFreeItems_cons {rank : Nat} {ts : List Tok} {items : List (List Tok)}
    (h : (BinaryFree rank) ts) (hs : (BinaryFreeItems rank) items) : (BinaryFreeItems rank) (ts :: items) := by
  intro xs hx
  rcases List.mem_cons.mp hx with he | hr
  · exact he ▸ h
  · exact hs xs hr

theorem binaryFreeItems_single {rank : Nat} {ts : List Tok} (h : (BinaryFree rank) ts) : (BinaryFreeItems rank) [ts] :=
  binaryFreeItems_cons h binaryFreeItems_nil

theorem binaryFreeItems_dropHead {rank : Nat} {ts : List Tok} {items : List (List Tok)}
    (h : (BinaryFreeItems rank) (ts :: items)) : (BinaryFreeItems rank) items := by
  intro xs hx
  exact h xs (List.mem_cons.mpr (Or.inr hx))

theorem binaryFreeItems_flatten {rank : Nat} {items : List (List Tok)} (h : (BinaryFreeItems rank) items) :
    (BinaryFree rank) items.flatten := by
  induction items with
  | nil => exact binaryFree_nil
  | cons ts items ih =>
    exact binaryFree_append (h ts (List.mem_cons.mpr (Or.inl rfl))) (ih (binaryFreeItems_dropHead h))

theorem binaryFree_flatMap {rank : Nat} {α : Type} (xs : List α) (f : α → List Tok)
    (h : ∀ x, x ∈ xs → (BinaryFree rank) (f x)) : (BinaryFree rank) (xs.flatMap f) := by
  induction xs with
  | nil => exact binaryFree_nil
  | cons x xs ih =>
    apply binaryFree_append (h x (List.mem_cons.mpr (Or.inl rfl)))
    exact ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))

theorem binaryFree_of_atoms {rank : Nat} (ts : List Tok) (h : ∀ t, t ∈ ts → bracket t = none ∧ (binaryMarker rank) t = false) :
    (BinaryFree rank) ts := by
  induction ts with
  | nil => exact binaryFree_nil
  | cons t ts ih =>
    apply binaryFree_append (binaryFree_atom (h t (List.mem_cons.mpr (Or.inl rfl))).1 (h t (List.mem_cons.mpr (Or.inl rfl))).2)
    exact ih (fun u hu => h u (List.mem_cons.mpr (Or.inr hu)))

theorem binaryFree_parens {rank : Nat} {ts : List Tok} (h : Balanced ts) : (BinaryFree rank) (parens ts) := by
  exact skip_enclose (binaryMarker rank) .round h rfl

theorem binaryFree_braces {rank : Nat} {ts : List Tok} (h : Balanced ts) : (BinaryFree rank) (braces ts) := by
  exact skip_enclose (binaryMarker rank) .curly h rfl

theorem binaryFree_square {rank : Nat} {ts : List Tok} (h : Balanced ts) :
    (BinaryFree rank) (pu .lbrack ++ ts ++ pu .rbrack) := by
  exact skip_enclose (binaryMarker rank) .square h rfl

theorem binaryFree_tk {rank : Nat} (k : Kw) : (BinaryFree rank) (tk k) := binaryFree_atom rfl rfl

theorem binaryFree_idt {rank : Nat} (name : String) : (BinaryFree rank) (idt name) := binaryFree_atom rfl rfl

theorem binaryFree_path {rank : Nat} (p : IdPath) : (BinaryFree rank) p.toks := by
  apply binaryFree_append (binaryFree_idt p.head)
  apply binaryFree_flatMap p.tail
  intro name _
  exact binaryFree_append (binaryFree_atom rfl rfl) (binaryFree_idt name)

theorem binaryFree_elem {rank : Nat} (e : Elem) : (BinaryFree rank) e.toks := by
  cases e <;> first
    | exact binaryFree_atom rfl rfl
    | exact binaryFree_append (binaryFree_atom rfl rfl) (binaryFree_atom rfl rfl)

theorem binaryFree_visibility {rank : Nat} (v : Visibility) : (BinaryFree rank) v.toks := by
  cases v <;> exact binaryFree_tk _

theorem binaryFree_mutability {rank : Nat} (m : Mutability) : (BinaryFree rank) m.toks := by
  cases m <;> exact binaryFree_tk _

theorem binaryFree_dataLoc {rank : Nat} (l : DataLoc) : (BinaryFree rank) l.toks := by
  cases l <;> exact binaryFree_tk _

theorem binaryFree_optToks {rank : Nat} {α : Type} (f : α → List Tok) (h : ∀ a, (BinaryFree rank) (f a))
    (value : Option α) : (BinaryFree rank) (optToks f value) := by
  cases value with
  | none => exact binaryFree_nil
  | some a => exact h a

theorem binaryFree_prefix {rank : Nat} (op : PrefixOp) (hskip : rank ≠ 10) :
    (BinaryFree rank) op.punct := by
  cases op <;> apply binaryFree_atom rfl
  all_goals first | rfl | exact decide_eq_false hskip

theorem binaryFree_suffix {rank : Nat} (op : SuffixOp) : (BinaryFree rank) (pu op.punct) := by
  cases op <;> exact binaryFree_atom rfl rfl

theorem binaryFree_mul {rank : Nat} (op : MulOp) (hne : rank ≠ 11) :
    (BinaryFree rank) (pu op.punct) := by
  cases op <;> exact binaryFree_atom rfl (decide_eq_false hne)

theorem binaryFree_add {rank : Nat} (op : AddOp) (hne : rank ≠ 10) :
    (BinaryFree rank) (pu op.punct) := by
  cases op <;> exact binaryFree_atom rfl (decide_eq_false hne)

theorem binaryFree_shift {rank : Nat} (op : ShiftOp) (hne : rank ≠ 9) :
    (BinaryFree rank) (pu op.punct) := by
  cases op <;> exact binaryFree_atom rfl (decide_eq_false hne)

theorem binaryFree_order {rank : Nat} (op : OrderOp) (hne : rank ≠ 5) :
    (BinaryFree rank) (pu op.punct) := by
  cases op <;> exact binaryFree_atom rfl (decide_eq_false hne)

theorem binaryFree_equality {rank : Nat} (op : EqOp) (hne : rank ≠ 4) :
    (BinaryFree rank) (pu op.punct) := by
  cases op <;> exact binaryFree_atom rfl (decide_eq_false hne)

theorem fragsP_binaryFree {rank : Nat} (mk : Bytes → Tok) (hm : ∀ bs, bracket (mk bs) = none ∧ (binaryMarker rank) (mk bs) = false)
    (bs : Bytes) : Produces (fragsP mk bs) (BinaryFree rank) := by
  intro initial ts rest h
  obtain ⟨cs, _, ht, _⟩ := fragsP_spec mk bs initial rest ts h
  rw [ht]
  apply binaryFree_of_atoms
  intro t ht
  obtain ⟨bytes, _, rfl⟩ := List.mem_map.mp ht
  exact hm bytes

theorem litP_binaryFree {rank : Nat} (l : Lit) : Produces (litP l) (BinaryFree rank) := by
  cases l with
  | bool b => exact produces_pure _ _ (binaryFree_atom rfl rfl)
  | num n => exact produces_pure _ _ (binaryFree_atom rfl rfl)
  | str bs => exact fragsP_binaryFree Tok.str (fun _ => ⟨rfl, rfl⟩) bs
  | hexStr bs => exact fragsP_binaryFree Tok.hexStr (fun _ => ⟨rfl, rfl⟩) bs
  | unicodeStr bs => exact fragsP_binaryFree Tok.unicodeStr (fun _ => ⟨rfl, rfl⟩) bs

def BinaryFreeAttrs (rank : Nat) (entries : List (Slot × List Tok)) : Prop :=
  ∀ entry, entry ∈ entries → (BinaryFree rank) entry.2

theorem binaryFreeAttrs_append {rank : Nat} {xs ys : List (Slot × List Tok)}
    (hx : (BinaryFreeAttrs rank) xs) (hy : (BinaryFreeAttrs rank) ys) : (BinaryFreeAttrs rank) (xs ++ ys) := by
  intro entry h
  rcases List.mem_append.mp h with h | h
  · exact hx entry h
  · exact hy entry h

theorem binaryFree_single {rank : Nat} (slot : Slot) (ts : List Tok) (h : (BinaryFree rank) ts) :
    (BinaryFreeAttrs rank) (single slot ts) := by
  unfold single
  split
  · intro entry he; cases he
  · intro entry he
    have heq : entry = (slot, ts) := by simpa only [List.mem_singleton] using he
    exact heq ▸ h

theorem arrange_binaryFree {rank : Nat} (order : List Slot) (singles : List (Slot × List Tok))
    (mods : List (List Tok)) (ts : List Tok) (hs : (BinaryFreeAttrs rank) singles)
    (hm : (BinaryFreeItems rank) mods) (h : arrange order singles mods = some ts) : (BinaryFree rank) ts := by
  induction order generalizing singles mods ts with
  | nil =>
    cases singles <;> cases mods <;> cases h
    exact binaryFree_nil
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
          apply heq ▸ binaryFree_append (hm word (List.mem_cons.mpr (Or.inl rfl)))
          exact ih singles mods suffix hs (binaryFreeItems_dropHead hm) hr
    · rw [arrange_nonModifier slot hslot] at h
      cases hf : singles.find? (·.1 == slot) with
      | none => rw [hf] at h; cases h
      | some entry =>
        rw [hf] at h
        have he : (BinaryFree rank) entry.2 := hs entry (List.mem_of_find?_eq_some hf)
        have hs' : (BinaryFreeAttrs rank) (singles.filter (·.1 != slot)) := by
          intro value hv
          exact hs value (List.mem_filter.mp hv).1
        cases hr : arrange order (singles.filter (·.1 != slot)) mods with
        | none => rw [hr] at h; cases h
        | some suffix =>
          rw [hr] at h
          have heq : entry.2 ++ suffix = ts := Option.some.inj h
          exact heq ▸ binaryFree_append he (ih _ mods suffix hs' hm hr)

theorem attrsP_binaryFree {rank : Nat} (singles : List (Slot × List Tok)) (mods : List (List Tok))
    (order : List Slot) (hs : (BinaryFreeAttrs rank) singles) (hm : (BinaryFreeItems rank) mods) :
    Produces (attrsP singles mods order) (BinaryFree rank) := by
  intro initial ts rest h
  change (arrange order singles mods).map (fun word => (word, initial)) = some (ts, rest) at h
  cases ha : arrange order singles mods with
  | none => rw [ha] at h; cases h
  | some word =>
    rw [ha] at h
    have heq : word = ts := (Prod.mk.inj (Option.some.inj h)).1
    exact heq ▸ arrange_binaryFree order singles mods word hs hm ha

end Solidity.Frontend.ExpressionUniqueness
