import Solidity.Frontend.ExpressionUniqueness.AddScan
import Solidity.Frontend.ExpressionUniqueness.AttributeBalance

/-!
# Operand-sensitive additive algebra

Expression freedom starts unfinished. Type/argument atoms and enclosures finish
from either bit; attribute/suffix words preserve a finished bit. Prefix and
reset words explicitly state their different entry/exit modes.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def AddFree (ts : List Tok) : Prop := addSkip ([], false) ts = some ([], true)
def AddStable (ts : List Tok) : Prop := addSkip ([], true) ts = some ([], true)
def AddPrefix (ts : List Tok) : Prop := addSkip ([], false) ts = some ([], false)
def AddReset (ts : List Tok) : Prop := addSkip ([], true) ts = some ([], false)
def AddDone (ts : List Tok) : Prop := ∀ finished, addSkip ([], finished) ts = some ([], true)
def AddStableItems (items : List (List Tok)) : Prop := ∀ ts, ts ∈ items → AddStable ts

theorem addDone_free {ts : List Tok} (h : AddDone ts) : AddFree ts := h false

theorem addDone_stable {ts : List Tok} (h : AddDone ts) : AddStable ts := h true

theorem addStable_nil : AddStable [] := rfl

theorem addStableItems_nil : AddStableItems [] := by
  intro ts ht
  cases ht

theorem addStableItems_tail {ts : List Tok} {items : List (List Tok)}
    (h : AddStableItems (ts :: items)) : AddStableItems items := by
  intro xs hx
  exact h xs (List.mem_cons.mpr (Or.inr hx))

theorem addStable_append {xs ys : List Tok} (hx : AddStable xs) (hy : AddStable ys) :
    AddStable (xs ++ ys) := by
  rw [AddStable, addSkip_append, hx, Option.bind_some]
  exact hy

theorem addDone_stable_append {xs ys : List Tok} (hx : AddDone xs) (hy : AddStable ys) :
    AddDone (xs ++ ys) := by
  intro finished
  rw [addSkip_append, hx finished, Option.bind_some]
  exact hy

theorem addFree_stable_append {xs ys : List Tok} (hx : AddFree xs) (hy : AddStable ys) :
    AddFree (xs ++ ys) := by
  rw [AddFree, addSkip_append, hx, Option.bind_some]
  exact hy

theorem addPrefix_free_append {xs ys : List Tok} (hx : AddPrefix xs) (hy : AddFree ys) :
    AddFree (xs ++ ys) := by
  rw [AddFree, addSkip_append, hx, Option.bind_some]
  exact hy

theorem addReset_free_append {xs ys : List Tok} (hx : AddReset xs) (hy : AddFree ys) :
    AddStable (xs ++ ys) := by
  rw [AddStable, addSkip_append, hx, Option.bind_some]
  exact hy

theorem addFree_binary {xs op ys : List Tok} (hx : AddFree xs) (ho : AddReset op)
    (hy : AddFree ys) : AddFree (xs ++ op ++ ys) := by
  rw [AddFree, addSkip_append, addSkip_append, hx, Option.bind_some, ho, Option.bind_some]
  exact hy

theorem addStable_atom (t : Tok) (hb : bracket t = none) (hh : addHit ([], true) t = false)
    (hm : modeToken true t = true) : AddStable [t] := by
  simpa only [hm] using addSkip_atom t true hb hh

theorem addDone_atom (t : Tok) (hb : bracket t = none)
    (hh : ∀ finished, addHit ([], finished) t = false)
    (hm : ∀ finished, modeToken finished t = true) : AddDone [t] := by
  intro finished
  simpa only [hm finished] using addSkip_atom t finished hb (hh finished)

theorem addDone_parens {ts : List Tok} (h : Balanced ts) : AddDone (parens ts) :=
  fun finished => addSkip_enclose .round ts finished h

theorem addDone_braces {ts : List Tok} (h : Balanced ts) : AddDone (braces ts) :=
  fun finished => addSkip_enclose .curly ts finished h

theorem addDone_square {ts : List Tok} (h : Balanced ts) :
    AddDone (pu .lbrack ++ ts ++ pu .rbrack) := fun finished => addSkip_enclose .square ts finished h

theorem addStable_flatMap {α : Type} (xs : List α) (f : α → List Tok)
    (h : ∀ x, x ∈ xs → AddStable (f x)) : AddStable (xs.flatMap f) := by
  induction xs with
  | nil => exact addStable_nil
  | cons x xs ih =>
    apply addStable_append (h x (List.mem_cons.mpr (Or.inl rfl)))
    exact ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))

theorem addStable_of_atoms (ts : List Tok)
    (h : ∀ t, t ∈ ts → bracket t = none ∧ addHit ([], true) t = false ∧ modeToken true t = true) :
    AddStable ts := by
  induction ts with
  | nil => exact addStable_nil
  | cons t ts ih =>
    have ht : bracket t = none ∧ addHit ([], true) t = false ∧ modeToken true t = true :=
      h t (List.mem_cons.mpr (Or.inl rfl))
    apply addStable_append (addStable_atom t ht.1 ht.2.1 ht.2.2)
    exact ih (fun u hu => h u (List.mem_cons.mpr (Or.inr hu)))

theorem addDone_map_nonempty {α : Type} (xs : List α) (mk : α → Tok) (hne : xs ≠ [])
    (hb : ∀ x, bracket (mk x) = none) (hh : ∀ x finished, addHit ([], finished) (mk x) = false)
    (hm : ∀ x finished, modeToken finished (mk x) = true) : AddDone (xs.map mk) := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
    apply addDone_stable_append (addDone_atom (mk x) (hb x) (hh x) (hm x))
    apply addStable_of_atoms
    intro t ht
    obtain ⟨value, _, rfl⟩ := List.mem_map.mp ht
    exact ⟨hb value, hh value true, hm value true⟩

theorem addDone_idt (name : String) : AddDone (idt name) :=
  addDone_atom _ rfl (fun _ => rfl) (fun _ => rfl)

theorem addReset_period : AddReset (pu .period) := rfl

theorem addDone_path (path : IdPath) : AddDone path.toks := by
  apply addDone_stable_append (addDone_idt path.head)
  apply addStable_flatMap path.tail
  intro name _
  exact addReset_free_append addReset_period (addDone_free (addDone_idt name))

theorem addDone_elem (e : Elem) : AddDone e.toks := by
  cases e <;> first
    | exact addDone_atom _ rfl (fun _ => rfl) (fun _ => rfl)
    | exact addDone_stable_append (addDone_atom _ rfl (fun _ => rfl) (fun _ => rfl))
        (addStable_atom _ rfl rfl rfl)

theorem addStable_visibility (v : Visibility) : AddStable v.toks := by
  cases v <;> exact addStable_atom _ rfl rfl rfl

theorem addStable_mutability (m : Mutability) : AddStable m.toks := by
  cases m <;> exact addStable_atom _ rfl rfl rfl

theorem addStable_optToks {α : Type} (f : α → List Tok) (h : ∀ x, AddStable (f x))
    (value : Option α) : AddStable (optToks f value) := by
  cases value with
  | none => exact addStable_nil
  | some x => exact h x

theorem addPrefix_prefix (op : PrefixOp) : AddPrefix op.punct := by
  cases op <;> rfl

theorem addStable_suffix (op : SuffixOp) : AddStable (pu op.punct) := by
  cases op <;> rfl

theorem addReset_mul (op : MulOp) : AddReset (pu op.punct) := by
  cases op <;> rfl

theorem addReset_exp : AddReset (pu .exp) := rfl

theorem addPrefix_new : AddPrefix (tk .new) := rfl

theorem fragsP_addDone (mk : Bytes → Tok) (hb : ∀ bs, bracket (mk bs) = none)
    (hh : ∀ bs finished, addHit ([], finished) (mk bs) = false)
    (hm : ∀ bs finished, modeToken finished (mk bs) = true) (bs : Bytes) :
    Produces (fragsP mk bs) AddDone := by
  intro initial ts rest h
  obtain ⟨cs, _, ht, hcs⟩ := fragsP_spec mk bs initial rest ts h
  rw [ht]
  exact addDone_map_nonempty cs mk hcs hb hh hm

theorem litP_addDone (l : Lit) : Produces (litP l) AddDone := by
  cases l with
  | bool b => exact produces_pure _ _ (addDone_atom _ rfl (fun _ => rfl) (fun _ => rfl))
  | num n => exact produces_pure _ _ (addDone_atom _ rfl (fun _ => rfl) (fun _ => rfl))
  | str bs => exact fragsP_addDone Tok.str (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) bs
  | hexStr bs => exact fragsP_addDone Tok.hexStr (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) bs
  | unicodeStr bs => exact fragsP_addDone Tok.unicodeStr (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) bs

def AddStableAttrs (entries : List (Slot × List Tok)) : Prop :=
  ∀ entry, entry ∈ entries → AddStable entry.2

theorem addStableAttrs_append {xs ys : List (Slot × List Tok)}
    (hx : AddStableAttrs xs) (hy : AddStableAttrs ys) : AddStableAttrs (xs ++ ys) := by
  intro entry h
  rcases List.mem_append.mp h with h | h
  · exact hx entry h
  · exact hy entry h

theorem addStable_single (slot : Slot) (ts : List Tok) (h : AddStable ts) :
    AddStableAttrs (single slot ts) := by
  unfold single
  split
  · intro entry he; cases he
  · intro entry he
    have heq : entry = (slot, ts) := by simpa only [List.mem_singleton] using he
    exact heq ▸ h

theorem arrange_addStable (order : List Slot) (singles : List (Slot × List Tok))
    (mods : List (List Tok)) (ts : List Tok) (hs : AddStableAttrs singles)
    (hm : AddStableItems mods) (h : arrange order singles mods = some ts) : AddStable ts := by
  induction order generalizing singles mods ts with
  | nil =>
    cases singles <;> cases mods <;> cases h
    exact addStable_nil
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
          apply heq ▸ addStable_append (hm word (List.mem_cons.mpr (Or.inl rfl)))
          exact ih singles mods suffix hs (addStableItems_tail hm) hr
    · rw [arrange_nonModifier slot hslot] at h
      cases hf : singles.find? (·.1 == slot) with
      | none => rw [hf] at h; cases h
      | some entry =>
        rw [hf] at h
        have he : AddStable entry.2 := hs entry (List.mem_of_find?_eq_some hf)
        have hs' : AddStableAttrs (singles.filter (·.1 != slot)) := by
          intro value hv
          exact hs value (List.mem_filter.mp hv).1
        cases hr : arrange order (singles.filter (·.1 != slot)) mods with
        | none => rw [hr] at h; cases h
        | some suffix =>
          rw [hr] at h
          have heq : entry.2 ++ suffix = ts := Option.some.inj h
          exact heq ▸ addStable_append he (ih _ mods suffix hs' hm hr)

theorem attrsP_addStable (singles : List (Slot × List Tok)) (mods : List (List Tok))
    (order : List Slot) (hs : AddStableAttrs singles) (hm : AddStableItems mods) :
    Produces (attrsP singles mods order) AddStable := by
  intro initial ts rest h
  change (arrange order singles mods).map (fun word => (word, initial)) = some (ts, rest) at h
  cases ha : arrange order singles mods with
  | none => rw [ha] at h; cases h
  | some word =>
    rw [ha] at h
    have heq : word = ts := (Prod.mk.inj (Option.some.inj h)).1
    exact heq ▸ arrange_addStable order singles mods word hs hm ha

end Solidity.Frontend.ExpressionUniqueness
