import Solidity.Frontend.ExpressionUniqueness.LowRoot
import Solidity.Frontend.ExpressionUniqueness.Families

/-!
# Inhabited loose-root controls with arbitrary conditional middle assignments

Every assignment operator and arbitrary prefix depth occurs in the middle of a
certified conditional. The first loose marker remains the outer question mark.
These controls preserve the documented false-branch assignment refusal.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

theorem assignment_yield_join (op : AssignOp) (a b : Syn .expr)
    (initial middle rest : List Choice) (xs ys : List (List Tok))
    (ha : a.yield initial = some (xs, middle)) (hb : b.yield middle = some (ys, rest)) :
    (Syn.assign op a b).yield initial = some ([xs.flatten ++ pu op.punct ++ ys.flatten], rest) := by
  change ((a.yield initial).bind fun ar => (b.yield ar.2).bind fun br =>
    some ([ar.1.flatten ++ pu op.punct ++ br.1.flatten], br.2)) = _
  rw [ha]
  simp only [Option.bind_some]
  rw [hb]
  rfl

theorem conditional_yield_join (c a b : Syn .expr)
    (initial middle next rest : List Choice) (xs ys zs : List (List Tok))
    (hc : c.yield initial = some (xs, middle)) (ha : a.yield middle = some (ys, next))
    (hb : b.yield next = some (zs, rest)) :
    (Syn.cond c a b).yield initial = some ([xs.flatten ++ pu .question ++ ys.flatten ++
      pu .colon ++ zs.flatten], rest) := by
  change ((c.yield initial).bind fun cr => (a.yield cr.2).bind fun ar =>
    (b.yield ar.2).bind fun br => some ([cr.1.flatten ++ pu .question ++
      ar.1.flatten ++ pu .colon ++ br.1.flatten], br.2)) = _
  rw [hc]
  simp only [Option.bind_some]
  rw [ha]
  simp only [Option.bind_some]
  rw [hb]
  rfl

theorem assignment_prec_join (op : AssignOp) (a b : Syn .expr)
    (ha : a.prec = true) (hb : b.prec = true) (hl : 2 ≤ a.level) :
    (Syn.assign op a b).prec = true := by
  have hr : (Syn.assign op a b).precNode = true := decide_eq_true hl
  have haa : a.all Syn.precNode = true := (Bool.and_eq_true_iff.mp ha).2
  have hba : b.all Syn.precNode = true := (Bool.and_eq_true_iff.mp hb).2
  simp only [Syn.prec, Syn.all, hr, haa, hba, Bool.true_and]

theorem conditional_prec_join (c a b : Syn .expr)
    (hc : c.prec = true) (ha : a.prec = true) (hb : b.prec = true)
    (hcl : 2 ≤ c.level) (hbl : 1 ≤ b.level) : (Syn.cond c a b).prec = true := by
  have hr : (Syn.cond c a b).precNode = true :=
    Bool.and_eq_true_iff.mpr ⟨decide_eq_true hcl, decide_eq_true hbl⟩
  have hca : c.all Syn.precNode = true := (Bool.and_eq_true_iff.mp hc).2
  have haa : a.all Syn.precNode = true := (Bool.and_eq_true_iff.mp ha).2
  have hba : b.all Syn.precNode = true := (Bool.and_eq_true_iff.mp hb).2
  simp only [Syn.prec, Syn.all, hr, hca, haa, hba, Bool.true_and]

def middleAssignment (op : AssignOp) (n : Nat) : Syn .expr :=
  .cond (.ident "c") (.assign op (.ident "a") (negFamily n "x")) (.ident "b")

def middleAssignmentTokens (op : AssignOp) (n : Nat) : List Tok :=
  [.ident "c", .punct .question, .ident "a", .punct op.punct] ++
    negTokens n "x" ++ [.punct .colon, .ident "b"]

theorem middleAssignment_prec (op : AssignOp) (n : Nat) :
    (middleAssignment op n).prec = true := by
  exact conditional_prec_join (.ident "c")
    (.assign op (.ident "a") (negFamily n "x")) (.ident "b") rfl
    (assignment_prec_join op (.ident "a") (negFamily n "x") rfl
      (negFamily_prec n "x") (by exact (by decide : 2 ≤ 16))) rfl
    (by exact (by decide : 2 ≤ 16)) (by exact (by decide : 1 ≤ 16))

theorem middleAssignment_yield (op : AssignOp) (n : Nat) (rest : List Choice) :
    (middleAssignment op n).yield rest = some ([middleAssignmentTokens op n], rest) := by
  have middle : (Syn.assign op (.ident "a") (negFamily n "x")).yield rest =
      some ([[.ident "a"] ++ pu op.punct ++ (negTokens n "x" :: []).flatten], rest) :=
    assignment_yield_join op (.ident "a") (negFamily n "x")
    rest rest rest [[.ident "a"]] [negTokens n "x"] rfl (negFamily_yield n "x" rest)
  simpa only [middleAssignment, middleAssignmentTokens, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.cons_append, List.nil_append, pu,
    List.append_assoc] using
    conditional_yield_join (.ident "c")
      (.assign op (.ident "a") (negFamily n "x")) (.ident "b") rest rest rest rest
      [[.ident "c"]] [[.ident "a"] ++ pu op.punct ++ (negTokens n "x" :: []).flatten]
      [[.ident "b"]] rfl middle rfl

theorem middleAssignment_certified (op : AssignOp) (n : Nat) :
    (middleAssignment op n).Derives (middleAssignmentTokens op n) ∧
      (middleAssignment op n).prec = true := by
  refine ⟨⟨[], ?_⟩, middleAssignment_prec op n⟩
  exact (expr_toks_iff _ [] _).mpr (middleAssignment_yield op n [])

theorem middleAssignment_first_question (op : AssignOp) (n : Nat) :
    firstTop lowMarker [] (middleAssignmentTokens op n) = some (1, .punct .question) := by
  unfold middleAssignmentTokens
  rfl

theorem middleAssignment_marker_not_assignment (op : AssignOp) (n : Nat) (position : Nat) :
    firstTop lowMarker [] (middleAssignmentTokens op n) ≠ some (position, .punct op.punct) := by
  rw [middleAssignment_first_question]
  intro he
  have ht : Tok.punct .question = Tok.punct op.punct := (Prod.mk.inj (Option.some.inj he)).2
  cases op <;> cases ht

end Solidity.Frontend.ExpressionUniqueness
