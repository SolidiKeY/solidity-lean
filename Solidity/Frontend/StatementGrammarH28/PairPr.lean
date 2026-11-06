import Solidity.Frontend.StatementGrammarH28.RootHead

/-! H31 two-token framing lemmas for contextual path/statement boundaries.
Only existing tokens and Syn printer computations are observed. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def identToken : Tok → Bool
  | .ident _ => true
  | _ => false

def forbiddenAfterIdent : Tok → Bool
  | .ident _ | .punct .colon => true
  | _ => false

def badAtomPair : List Tok → Bool
  | .ident _ :: second :: _ => forbiddenAfterIdent second
  | _ => false

def AtomPairSafe (ts : List Tok) : Prop := badAtomPair ts = false

def NonIdentStart (ts : List Tok) : Prop :=
  ∃ t rest, ts = t :: rest ∧ identToken t = false

def HeaderSeparator (ts : List Tok) : Prop :=
  ∃ t rest, ts = t :: rest ∧ forbiddenAfterIdent t = false

def ParenStart (ts : List Tok) : Prop := ∃ rest, ts = .punct .lparen :: rest

theorem safe_start_nonempty {ts : List Tok} (h : SafeStart ts) : ts ≠ [] := by
  obtain ⟨t, rest, he, ht⟩ := h
  rw [he]
  intro bad
  cases bad

theorem ensures_both {α : Type} (p : Pr α) (P Q : α → Prop)
    (hp : PrEnsures p P) (hq : PrEnsures p Q) : PrEnsures p (fun a => P a ∧ Q a) :=
  fun L a M h => ⟨hp L a M h, hq L a M h⟩

theorem nonIdent_append {ts : List Tok} (h : NonIdentStart ts) (tail : List Tok) :
    NonIdentStart (ts ++ tail) := by
  obtain ⟨t, rest, he, ht⟩ := h
  subst ts
  exact ⟨t, rest ++ tail, rfl, ht⟩

theorem nonIdent_atom_pair_safe {ts : List Tok} (h : NonIdentStart ts) : AtomPairSafe ts := by
  obtain ⟨t, rest, he, ht⟩ := h
  subst ts
  cases t with
  | ident name => cases ht
  | _ => rfl

theorem paren_separator {ts : List Tok} (h : ParenStart ts) : HeaderSeparator ts := by
  obtain ⟨rest, he⟩ := h
  exact ⟨_, rest, he, rfl⟩

/-- A nonempty atom whose first pair is safe stays safe when continued by a
real non-identifier/non-colon delimiter, followed by arbitrary tokens. -/
theorem atom_pair_safe_frame (xs sep tail : List Tok) (hx : AtomPairSafe xs)
    (hn : xs ≠ []) (hs : HeaderSeparator sep) : AtomPairSafe (xs ++ sep ++ tail) := by
  cases xs with
  | nil => exact False.elim (hn rfl)
  | cons first rest =>
    cases first with
    | ident name =>
      cases rest with
      | nil =>
        obtain ⟨t, after, he, ht⟩ := hs
        subst sep
        exact ht
      | cons second after => exact hx
    | _ => rfl

theorem nonIdent_map {α : Type} (f : α → Tok) (xs : List α) (hn : xs ≠ [])
    (hf : ∀ x, identToken (f x) = false) : NonIdentStart (xs.map f) := by
  cases xs with
  | nil => exact False.elim (hn rfl)
  | cons x xs => exact ⟨f x, xs.map f, rfl, hf x⟩

theorem fragsP_nonIdent (mk : Bytes → Tok) (bs : Bytes)
    (hm : ∀ bytes, identToken (mk bytes) = false) : PrEnsures (fragsP mk bs) NonIdentStart := by
  unfold fragsP
  apply ensures_bind (P := NonIdentStart)
  intro choice
  cases choice with
  | attrs _ => exact ensures_lift_none _
  | layoutFirst _ => exact ensures_lift_none _
  | frags lens =>
    cases lens with
    | nil => exact ensures_lift_none _
    | cons n ns =>
      apply ensures_bind_checked _ _ (fun cs : List Bytes => cs ≠ []) NonIdentStart
        (lift_post _ _ (fun cs hc => chunks_cons_nonempty bs n ns cs hc))
      intro cs hcs
      exact ensures_pure _ NonIdentStart (nonIdent_map mk cs hcs hm)

theorem litP_nonIdent (l : Lit) : PrEnsures (litP l) NonIdentStart := by
  cases l with
  | str b => exact fragsP_nonIdent _ _ (fun _ => rfl)
  | hexStr b => exact fragsP_nonIdent _ _ (fun _ => rfl)
  | unicodeStr b => exact fragsP_nonIdent _ _ (fun _ => rfl)
  | bool b => exact ensures_pure _ NonIdentStart ⟨_, [], rfl, rfl⟩
  | num n => exact ensures_pure _ NonIdentStart ⟨_, [], rfl, rfl⟩

theorem elem_nonIdent (e : Elem) : NonIdentStart e.toks := by
  cases e <;> exact ⟨_, _, rfl, rfl⟩

theorem prefix_nonIdent (op : PrefixOp) : NonIdentStart op.punct := by
  cases op <;> exact ⟨_, _, rfl, rfl⟩

theorem path_atom_pair_safe (p : IdPath) : AtomPairSafe p.toks := by
  cases ht : p.tail with
  | nil => simp only [IdPath.toks, ht, List.flatMap_nil]; rfl
  | cons name rest => simp only [IdPath.toks, ht, List.flatMap_cons, List.cons_append, List.nil_append]; rfl

theorem suffix_separator (op : SuffixOp) : HeaderSeparator (pu op.punct) := by
  cases op <;> exact ⟨_, _, rfl, rfl⟩

theorem mul_separator (op : MulOp) : HeaderSeparator (pu op.punct) := by
  cases op <;> exact ⟨_, _, rfl, rfl⟩

theorem add_separator (op : AddOp) : HeaderSeparator (pu op.punct) := by
  cases op <;> exact ⟨_, _, rfl, rfl⟩

theorem shift_separator (op : ShiftOp) : HeaderSeparator (pu op.punct) := by
  cases op <;> exact ⟨_, _, rfl, rfl⟩

theorem order_separator (op : OrderOp) : HeaderSeparator (pu op.punct) := by
  cases op <;> exact ⟨_, _, rfl, rfl⟩

theorem equality_separator (op : EqOp) : HeaderSeparator (pu op.punct) := by
  cases op <;> exact ⟨_, _, rfl, rfl⟩

theorem assign_separator (op : AssignOp) : HeaderSeparator (pu op.punct) := by
  cases op <;> exact ⟨_, _, rfl, rfl⟩

#print axioms safe_start_nonempty
#print axioms ensures_both
#print axioms nonIdent_append
#print axioms nonIdent_atom_pair_safe
#print axioms paren_separator
#print axioms atom_pair_safe_frame
#print axioms nonIdent_map
#print axioms fragsP_nonIdent
#print axioms litP_nonIdent
#print axioms elem_nonIdent
#print axioms prefix_nonIdent
#print axioms path_atom_pair_safe
#print axioms suffix_separator
#print axioms mul_separator
#print axioms add_separator
#print axioms shift_separator
#print axioms order_separator
#print axioms equality_separator
#print axioms assign_separator
end Solidity.Frontend.StatementGrammarH28
