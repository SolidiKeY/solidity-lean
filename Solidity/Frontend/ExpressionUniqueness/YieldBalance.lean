import Solidity.Frontend.ExpressionUniqueness.YieldShape
import Solidity.Frontend.ExpressionUniqueness.TokenSplit

/-!
# Balance algebra for the intrinsic expression printer

These token and success-predicate lemmas support the recursive expression/type/
argument category closure. Brackets are actual checked token constructors;
string payload bytes never act as punctuation.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def BalancedItems (items : List (List Tok)) : Prop := ∀ ts, ts ∈ items → Balanced ts

theorem balancedItems_nil : BalancedItems [] := by
  intro ts h
  cases h

theorem balancedItems_cons {ts : List Tok} {items : List (List Tok)}
    (h : Balanced ts) (hs : BalancedItems items) : BalancedItems (ts :: items) := by
  intro xs hx
  rcases List.mem_cons.mp hx with he | hr
  · exact he ▸ h
  · exact hs xs hr

theorem balancedItems_single {ts : List Tok} (h : Balanced ts) : BalancedItems [ts] :=
  balancedItems_cons h balancedItems_nil

theorem balancedItems_tail {ts : List Tok} {items : List (List Tok)}
    (h : BalancedItems (ts :: items)) : BalancedItems items := by
  intro xs hx
  exact h xs (List.mem_cons.mpr (Or.inr hx))

theorem balancedItems_flatten {items : List (List Tok)} (h : BalancedItems items) :
    Balanced items.flatten := by
  induction items with
  | nil => exact balanced_nil
  | cons ts items ih =>
    exact balanced_append (h ts (List.mem_cons.mpr (Or.inl rfl))) (ih (balancedItems_tail h))

theorem balanced_flatMap {α : Type} (xs : List α) (f : α → List Tok)
    (h : ∀ x, x ∈ xs → Balanced (f x)) : Balanced (xs.flatMap f) := by
  induction xs with
  | nil => exact balanced_nil
  | cons x xs ih =>
    apply balanced_append (h x (List.mem_cons.mpr (Or.inl rfl)))
    exact ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))

theorem balanced_of_atoms (ts : List Tok) (h : ∀ t, t ∈ ts → bracket t = none) :
    Balanced ts := by
  induction ts with
  | nil => exact balanced_nil
  | cons t ts ih =>
    apply balanced_append (balanced_atom (h t (List.mem_cons.mpr (Or.inl rfl))))
    exact ih (fun u hu => h u (List.mem_cons.mpr (Or.inr hu)))

theorem balanced_commaSep {items : List (List Tok)} (h : BalancedItems items) :
    Balanced (commaSep items) := by
  induction items with
  | nil => exact balanced_nil
  | cons ts items ih =>
    have ht : Balanced ts := h ts (List.mem_cons.mpr (Or.inl rfl))
    have hr : BalancedItems items := balancedItems_tail h
    cases items with
    | nil => simpa only [commaSep, List.intersperse_single, List.flatten_cons,
        List.flatten_nil, List.append_nil] using ht
    | cons first rest =>
      change Balanced (ts ++ (pu .comma ++ commaSep (first :: rest)))
      exact balanced_append ht (balanced_append (balanced_atom rfl) (ih hr))

theorem balanced_parens {ts : List Tok} (h : Balanced ts) : Balanced (parens ts) :=
  balanced_enclose .round h

theorem balanced_braces {ts : List Tok} (h : Balanced ts) : Balanced (braces ts) :=
  balanced_enclose .curly h

theorem balanced_square {ts : List Tok} (h : Balanced ts) :
    Balanced (pu .lbrack ++ ts ++ pu .rbrack) := balanced_enclose .square h

theorem balanced_tk (k : Kw) : Balanced (tk k) := balanced_atom rfl

theorem balanced_idt (name : String) : Balanced (idt name) := balanced_atom rfl

theorem balanced_path (p : IdPath) : Balanced p.toks := by
  apply balanced_append (balanced_idt p.head)
  apply balanced_flatMap p.tail
  intro name _
  exact balanced_append (balanced_atom rfl) (balanced_idt name)

theorem balanced_elem (e : Elem) : Balanced e.toks := by
  cases e <;> first
    | exact balanced_atom rfl
    | exact balanced_append (balanced_atom rfl) (balanced_atom rfl)

theorem balanced_visibility (v : Visibility) : Balanced v.toks := by
  cases v <;> exact balanced_tk _

theorem balanced_mutability (m : Mutability) : Balanced m.toks := by
  cases m <;> exact balanced_tk _

theorem balanced_dataLoc (l : DataLoc) : Balanced l.toks := by
  cases l <;> exact balanced_tk _

theorem balanced_optToks {α : Type} (f : α → List Tok) (h : ∀ a, Balanced (f a))
    (value : Option α) : Balanced (optToks f value) := by
  cases value with
  | none => exact balanced_nil
  | some a => exact h a

theorem balanced_prefix (op : PrefixOp) : Balanced op.punct := by
  cases op <;> exact balanced_atom rfl

theorem balanced_suffix (op : SuffixOp) : Balanced (pu op.punct) := by
  cases op <;> exact balanced_atom rfl

theorem balanced_mul (op : MulOp) : Balanced (pu op.punct) := by
  cases op <;> exact balanced_atom rfl

theorem balanced_add (op : AddOp) : Balanced (pu op.punct) := by
  cases op <;> exact balanced_atom rfl

theorem balanced_shift (op : ShiftOp) : Balanced (pu op.punct) := by
  cases op <;> exact balanced_atom rfl

theorem balanced_order (op : OrderOp) : Balanced (pu op.punct) := by
  cases op <;> exact balanced_atom rfl

theorem balanced_equality (op : EqOp) : Balanced (pu op.punct) := by
  cases op <;> exact balanced_atom rfl

theorem balanced_assign (op : AssignOp) : Balanced (pu op.punct) := by
  cases op <;> exact balanced_atom rfl

theorem fragsP_balanced (mk : Bytes → Tok) (hm : ∀ bs, bracket (mk bs) = none)
    (bs : Bytes) : Produces (fragsP mk bs) Balanced := by
  intro initial ts rest h
  obtain ⟨cs, _, ht, _⟩ := fragsP_spec mk bs initial rest ts h
  rw [ht]
  apply balanced_of_atoms
  intro t ht
  obtain ⟨bytes, _, rfl⟩ := List.mem_map.mp ht
  exact hm bytes

theorem litP_balanced (l : Lit) : Produces (litP l) Balanced := by
  cases l with
  | bool b => exact produces_pure _ _ (balanced_atom rfl)
  | num n => exact produces_pure _ _ (balanced_atom rfl)
  | str bs => exact fragsP_balanced Tok.str (fun _ => rfl) bs
  | hexStr bs => exact fragsP_balanced Tok.hexStr (fun _ => rfl) bs
  | unicodeStr bs => exact fragsP_balanced Tok.unicodeStr (fun _ => rfl) bs

end Solidity.Frontend.ExpressionUniqueness
