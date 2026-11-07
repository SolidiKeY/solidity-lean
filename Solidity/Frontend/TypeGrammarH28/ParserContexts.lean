import Solidity.Frontend.TypeGrammarH28.ParserArrays

/-! Independent stopping-context certificates for recursive type parsing.
These describe continuation tokens, not an exclusion from the type language. -/
namespace Solidity.Frontend.TypeGrammarH28.ParserContext
open Solidity.Source Solidity.Frontend.Checked ParserBasic ParserPath ParserArray

/-- The continuation positions used by type lists, named mapping fields and
array atoms. No type-parser-success premise is hidden in this certificate. -/
inductive Boundary : List Located → Prop where
  | eof : Boundary []
  | named (name : String) (a b : Nat) (rest : List Located) : Boundary (⟨.ident name, a, b⟩ :: rest)
  | rparen (a b : Nat) (rest : List Located) : Boundary (⟨.punct .rparen, a, b⟩ :: rest)
  | rbrack (a b : Nat) (rest : List Located) : Boundary (⟨.punct .rbrack, a, b⟩ :: rest)
  | rbrace (a b : Nat) (rest : List Located) : Boundary (⟨.punct .rbrace, a, b⟩ :: rest)
  | comma (a b : Nat) (rest : List Located) : Boundary (⟨.punct .comma, a, b⟩ :: rest)
  | semicolon (a b : Nat) (rest : List Located) : Boundary (⟨.punct .semi, a, b⟩ :: rest)
  | arrow (a b : Nat) (rest : List Located) : Boundary (⟨.punct .doubleArrow, a, b⟩ :: rest)
  | memory (a b : Nat) (rest : List Located) : Boundary (⟨.kw .memory, a, b⟩ :: rest)
  | storage (a b : Nat) (rest : List Located) : Boundary (⟨.kw .storage, a, b⟩ :: rest)
  | calldata (a b : Nat) (rest : List Located) : Boundary (⟨.kw .calldata, a, b⟩ :: rest)

theorem boundary_no_payable (rest : List Located) (h : Boundary rest)
    (ch : List Choice) (eof : Nat) :
    eat (.kw .payable) ⟨rest, ch, eof⟩ = .ok (false, ⟨rest, ch, eof⟩) := by
  cases h <;> rfl

theorem boundary_no_suffix (rest : List Located) (h : Boundary rest)
    (ch : List Choice) (eof : Nat) :
    eat (.punct .lbrack) ⟨rest, ch, eof⟩ = .ok (false, ⟨rest, ch, eof⟩) := by
  cases h <;> rfl

theorem boundary_no_path (rest : List Located) (h : Boundary rest)
    (ch : List Choice) (eof : Nat) :
    pathStep ⟨rest, ch, eof⟩ = .ok (none, ⟨rest, ch, eof⟩) := by
  cases h <;> rfl

theorem boundary_no_attrs (fuel : Nat) (rest : List Located) (h : Boundary rest)
    (vis : Option Visibility) (mu : Option Mutability) (order : List Slot)
    (ch : List Choice) (eof : Nat) :
    fnTypeAttrs fuel vis mu order ⟨rest, ch, eof⟩ = .ok ((vis, mu, order.reverse), ⟨rest, ch, eof⟩) := by
  cases fuel with
  | zero => rfl
  | succ n => cases h <;> rfl

theorem boundary_no_returns (fuel : Nat) (rest : List Located) (h : Boundary rest)
    (ch : List Choice) (eof : Nat) :
    returnsOpt (fuel + 1) ⟨rest, ch, eof⟩ = .ok (.nil, ⟨rest, ch, eof⟩) := by
  cases h <;> rfl

theorem brackets_boundary_no_payable (k : Nat) (front rest : List Located)
    (hp : front.map Located.tok = dynamicBrackets k) (h : Boundary rest)
    (ch : List Choice) (eof : Nat) :
    eat (.kw .payable) ⟨front ++ rest, ch, eof⟩ = .ok (false, ⟨front ++ rest, ch, eof⟩) := by
  cases k with
  | zero =>
    have he := located_nil front hp
    cases he
    exact boundary_no_payable rest h ch eof
  | succ k =>
    obtain ⟨head, tail, he, ht, hr⟩ := located_cons front _ _ hp
    cases he
    cases head with
    | mk tok a b => cases ht; rfl

theorem brackets_boundary_no_path (k : Nat) (front rest : List Located)
    (hp : front.map Located.tok = dynamicBrackets k) (h : Boundary rest)
    (ch : List Choice) (eof : Nat) :
    pathStep ⟨front ++ rest, ch, eof⟩ = .ok (none, ⟨front ++ rest, ch, eof⟩) := by
  cases k with
  | zero =>
    have he := located_nil front hp
    cases he
    exact boundary_no_path rest h ch eof
  | succ k =>
    obtain ⟨head, tail, he, ht, hr⟩ := located_cons front _ _ hp
    cases he
    cases head with
    | mk tok a b => cases ht; rfl

theorem dynamic_elem_prefix (e : Elem) (k n : Nat) (front rest : List Located)
    (hp : front.map Located.tok = e.toks ++ dynamicBrackets k) (h : Boundary rest)
    (ch : List Choice) (eof : Nat) :
    typeName (n + k + 2) ⟨front ++ rest, ch, eof⟩ =
      .ok (dynamicTree (.elem e) k, ⟨rest, ch, eof⟩) := by
  obtain ⟨base, suffix, he, hb, hs⟩ := located_append front e.toks (dynamicBrackets k) hp
  cases he
  rw [List.append_assoc]
  rw [elem_then_suffix e (n + k + 1) base (suffix ++ rest) ch eof hb
    (brackets_boundary_no_payable k suffix rest hs h ch eof)]
  exact suffix_dynamic_complete k n (.elem e) suffix rest ch eof hs (boundary_no_suffix rest h ch eof)

theorem dynamic_user_prefix (p : IdPath) (k n : Nat) (front rest : List Located)
    (hp : front.map Located.tok = p.toks ++ dynamicBrackets k) (h : Boundary rest)
    (ch : List Choice) (eof : Nat) :
    typeName (n + k + 2) ⟨front ++ rest, ch, eof⟩ =
      .ok (dynamicTree (.userType p) k, ⟨rest, ch, eof⟩) := by
  obtain ⟨base, suffix, he, hb, hs⟩ := located_append front p.toks (dynamicBrackets k) hp
  cases he
  rw [List.append_assoc]
  rw [user_then_suffix p (n + k + 1) base (suffix ++ rest) ch eof hb
    (brackets_boundary_no_path k suffix rest hs h ch eof)]
  exact suffix_dynamic_complete k n (.userType p) suffix rest ch eof hs (boundary_no_suffix rest h ch eof)

theorem elem_prefix (e : Elem) (n : Nat) (front rest : List Located)
    (hp : front.map Located.tok = e.toks) (h : Boundary rest)
    (ch : List Choice) (eof : Nat) :
    typeName (n + 2) ⟨front ++ rest, ch, eof⟩ = .ok (.elem e, ⟨rest, ch, eof⟩) := by
  have he : front.map Located.tok = e.toks ++ dynamicBrackets 0 := by
    simpa only [dynamicBrackets, List.append_nil] using hp
  exact dynamic_elem_prefix e 0 n front rest he h ch eof

theorem user_prefix (p : IdPath) (n : Nat) (front rest : List Located)
    (hp : front.map Located.tok = p.toks) (h : Boundary rest)
    (ch : List Choice) (eof : Nat) :
    typeName (n + 2) ⟨front ++ rest, ch, eof⟩ = .ok (.userType p, ⟨rest, ch, eof⟩) := by
  have he : front.map Located.tok = p.toks ++ dynamicBrackets 0 := by
    simpa only [dynamicBrackets, List.append_nil] using hp
  exact dynamic_user_prefix p 0 n front rest he h ch eof

/-- A reusable proof contract for a genuine raw type prefix. The returned
layout is explicit and may differ from an original successful yield witness.
This is instantiated below; no global completeness theorem is assumed. -/
def CompleteAt (t : Syn .typeName) (tokens : List Tok) (layout : List Choice)
    (budget : Nat) : Prop :=
  ∀ fuel : Nat, budget ≤ fuel → ∀ front rest : List Located,
    front.map Located.tok = tokens → Boundary rest → ∀ ch : List Choice, ∀ eof : Nat,
    typeName fuel ⟨front ++ rest, ch, eof⟩ = .ok (t, ⟨rest, layout.reverse ++ ch, eof⟩)

theorem complete_elem (e : Elem) : CompleteAt (.elem e) e.toks [] 2 := by
  intro fuel hf front rest hp hb ch eof
  have he : fuel - 2 + 2 = fuel := Nat.sub_add_cancel hf
  change typeName fuel ⟨front ++ rest, ch, eof⟩ = .ok (.elem e, ⟨rest, ch, eof⟩)
  rw [← he]
  exact elem_prefix e _ front rest hp hb ch eof

theorem complete_user (p : IdPath) : CompleteAt (.userType p) p.toks [] 2 := by
  intro fuel hf front rest hp hb ch eof
  have he : fuel - 2 + 2 = fuel := Nat.sub_add_cancel hf
  change typeName fuel ⟨front ++ rest, ch, eof⟩ = .ok (.userType p, ⟨rest, ch, eof⟩)
  rw [← he]
  exact user_prefix p _ front rest hp hb ch eof

theorem complete_dynamic_elem (e : Elem) (k : Nat) :
    CompleteAt (dynamicTree (.elem e) k) (e.toks ++ dynamicBrackets k) [] (k + 2) := by
  intro fuel hf front rest hp hb ch eof
  have he : fuel - (k + 2) + k + 2 = fuel :=
    (Nat.add_assoc _ _ _).trans (Nat.sub_add_cancel hf)
  change typeName fuel ⟨front ++ rest, ch, eof⟩ = .ok (dynamicTree (.elem e) k, ⟨rest, ch, eof⟩)
  rw [← he]
  exact dynamic_elem_prefix e k _ front rest hp hb ch eof

theorem complete_dynamic_user (p : IdPath) (k : Nat) :
    CompleteAt (dynamicTree (.userType p) k) (p.toks ++ dynamicBrackets k) [] (k + 2) := by
  intro fuel hf front rest hp hb ch eof
  have he : fuel - (k + 2) + k + 2 = fuel :=
    (Nat.add_assoc _ _ _).trans (Nat.sub_add_cancel hf)
  change typeName fuel ⟨front ++ rest, ch, eof⟩ = .ok (dynamicTree (.userType p) k, ⟨rest, ch, eof⟩)
  rw [← he]
  exact dynamic_user_prefix p k _ front rest hp hb ch eof

theorem boundary_excludes_array_continuation (a b : Nat) (rest : List Located) :
    ¬ Boundary (⟨.punct .lbrack, a, b⟩ :: rest) := by
  intro h
  cases h

theorem boundary_excludes_visibility_continuation (vis : Visibility)
    (front rest : List Located) (hp : front.map Located.tok = vis.toks) :
    ¬ Boundary (front ++ rest) := by
  cases vis <;> obtain ⟨a, b, he⟩ := located_one front _ hp <;> cases he <;> intro h <;> cases h

theorem boundary_excludes_mutability_continuation (mu : Mutability)
    (front rest : List Located) (hp : front.map Located.tok = mu.toks) :
    ¬ Boundary (front ++ rest) := by
  cases mu <;> obtain ⟨a, b, he⟩ := located_one front _ hp <;> cases he <;> intro h <;> cases h

theorem boundary_excludes_returns_continuation (a b : Nat) (rest : List Located) :
    ¬ Boundary (⟨.kw .returns, a, b⟩ :: rest) := by
  intro h
  cases h

#print axioms boundary_no_payable
#print axioms boundary_no_suffix
#print axioms boundary_no_path
#print axioms boundary_no_attrs
#print axioms boundary_no_returns
#print axioms brackets_boundary_no_payable
#print axioms brackets_boundary_no_path
#print axioms dynamic_elem_prefix
#print axioms dynamic_user_prefix
#print axioms elem_prefix
#print axioms user_prefix
#print axioms complete_elem
#print axioms complete_user
#print axioms complete_dynamic_elem
#print axioms complete_dynamic_user
#print axioms boundary_excludes_array_continuation
#print axioms boundary_excludes_visibility_continuation
#print axioms boundary_excludes_mutability_continuation
#print axioms boundary_excludes_returns_continuation
end Solidity.Frontend.TypeGrammarH28.ParserContext
