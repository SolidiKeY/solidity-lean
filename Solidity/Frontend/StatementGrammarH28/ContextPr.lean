import Solidity.Frontend.StatementGrammarH28.SyntaxPair

/-! H31 three-token frames for declaration/simple versus path-revert roots.
These are token predicates over existing yields, not an alternative AST. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def pathStartDelimiter : Tok → Bool
  | .punct .lparen | .punct .period => true
  | _ => false

def badStmtTriple : List Tok → Bool
  | .ident _ :: .ident _ :: third :: _ => pathStartDelimiter third
  | _ => false

def SimpleFrameSafe (ts : List Tok) : Prop := ∀ tail, badStmtTriple (ts ++ tail) = false

def PathTokens (ts : List Tok) : Prop :=
  ∃ name after, ts = .ident name :: after ∧
    (after = [] ∨ ∃ rest, after = .punct .period :: rest)

theorem atom_pair_no_bad_triple {ts : List Tok} (h : AtomPairSafe ts) :
    badStmtTriple ts = false := by
  cases ts with
  | nil => rfl
  | cons first rest =>
    cases first with
    | ident a =>
      cases rest with
      | nil => rfl
      | cons second after =>
        cases second with
        | ident b => cases h
        | _ => rfl
    | _ => rfl

theorem nonIdent_frame_safe {ts : List Tok} (h : NonIdentStart ts) : SimpleFrameSafe ts :=
  fun tail => atom_pair_no_bad_triple (nonIdent_atom_pair_safe (nonIdent_append h tail))

/-- A type is nonempty and lacks an initial identifier/identifier pair. A
variable name can create that pair only at the end of the declaration head;
its initializer or semicolon then closes the contextual-revert possibility. -/
theorem decl_head_no_bad_triple (ty : List Tok) (loc : Option DataLoc) (name : String)
    (init : List (List Tok)) (tail : List Tok) (ht : AtomPairSafe ty) (hn : ty ≠ []) :
    badStmtTriple ((ty ++ optToks DataLoc.toks loc ++ idt name) ++
      (match init with | [e] => pu .assign ++ e | _ => []) ++ pu .semi ++ tail) = false := by
  cases ty with
  | nil => exact False.elim (hn rfl)
  | cons first rest =>
    cases first with
    | ident a =>
      cases rest with
      | nil =>
        cases loc with
        | some place => cases place <;> rfl
        | none =>
          cases init with
          | nil => rfl
          | cons value more => cases more <;> rfl
      | cons second after =>
        cases second with
        | ident b => cases ht
        | _ => rfl
    | _ => rfl

theorem path_append_member {ts : List Tok} (h : PathTokens ts) (member : List Tok) :
    PathTokens (ts ++ pu .period ++ member) := by
  obtain ⟨name, after, he, shape⟩ := h
  subst ts
  cases shape with
  | inl empty =>
    subst after
    exact ⟨name, .punct .period :: member, rfl, Or.inr ⟨member, rfl⟩⟩
  | inr more =>
    obtain ⟨rest, hr⟩ := more
    subst after
    exact ⟨name, .punct .period :: (rest ++ pu .period ++ member), rfl,
      Or.inr ⟨_, rfl⟩⟩

theorem revert_bad_triple (path args tail : List Tok) (hp : PathTokens path)
    (ha : ParenStart args) :
    badStmtTriple (idt "revert" ++ path ++ args ++ pu .semi ++ tail) = true := by
  obtain ⟨name, after, he, shape⟩ := hp
  obtain ⟨rest, hr⟩ := ha
  subst path
  subst args
  cases shape with
  | inl empty => subst after; rfl
  | inr more => obtain ⟨remaining, hrem⟩ := more; subst after; rfl

#print axioms atom_pair_no_bad_triple
#print axioms nonIdent_frame_safe
#print axioms decl_head_no_bad_triple
#print axioms path_append_member
#print axioms revert_bad_triple
end Solidity.Frontend.StatementGrammarH28
