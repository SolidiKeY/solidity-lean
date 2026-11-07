import Solidity.Frontend.StatementGrammarH28.SemicolonSplit
import Solidity.Frontend.StatementGrammarH28.SyntaxBalance
import Solidity.Frontend.StatementGrammarH28.G0List

/-! Actual mixed statement-list segmentation for six semicolon roots and
arbitrary block statements, against any other successful statement-list yield.
This does not cover open compound statement boundaries or AST uniqueness. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def FramedStatement {k : SCtx} (s : Syn (.stmt k)) : Prop :=
  root s = .block ∨ SemiRoot (root s) = true

def FramedStatements {k : SCtx} (ss : Syn (.list (.stmt k))) : Prop :=
  (g0ListValues ss).foldr (fun s rest => FramedStatement s ∧ rest) True

theorem FramedStatements_nil {k : SCtx} :
    FramedStatements (Syn.nil (c := .stmt k)) = True := rfl

theorem FramedStatements_cons {k : SCtx} (s : Syn (.stmt k)) (ss : Syn (.list (.stmt k))) :
    FramedStatements (.cons s ss) = (FramedStatement s ∧ FramedStatements ss) := rfl

theorem statement_yield_nonempty {k : SCtx} (s : Syn (.stmt k))
    (L M : List Choice) (parts : List (List Tok))
    (hy : s.yield L = some (parts, M)) : parts.flatten ≠ [] := by
  by_cases hs : root s = .simple
  · exact safe_start_nonempty (simple_root_yield_safe s hs L parts M hy)
  · have fixed : ∃ tok, (root s).firstToken = some tok := by
      cases hr : root s <;> first
        | exact ⟨_, rfl⟩
        | exact False.elim (hs hr)
    obtain ⟨tok, ht⟩ := fixed
    have head := statement_fixed_head s tok ht L parts M hy
    change parts.flatten.head? = some tok at head
    intro empty
    rw [empty] at head
    cases head

theorem block_statement_prefix_split {k j : SCtx}
    (s : Syn (.stmt k)) (t : Syn (.stmt j))
    (hs : root s = .block) (ht : root t = .block)
    (L M N P : List Choice) (xs ys : List (List Tok)) (rest tail : List Tok)
    (hyS : s.yield L = some (xs, M)) (hyT : t.yield N = some (ys, P))
    (he : xs.flatten ++ rest = ys.flatten ++ tail) :
    xs.flatten = ys.flatten ∧ rest = tail := by
  cases s with
  | blockStmt b =>
    cases t with
    | blockStmt c =>
      obtain ⟨body, ex, ey, suffix⟩ :=
        arbitrary_block_prefix_split b c L M N P xs ys rest tail hyS hyT he
      exact ⟨by rw [ex, ey], suffix⟩
    | _ => cases ht
  | _ => cases hs

/-- Only the source statement needs a framed root; the target is arbitrary.
No precedence, parser success or atom uniqueness premise is used. -/
theorem framed_statement_prefix_split {k j : SCtx}
    (s : Syn (.stmt k)) (t : Syn (.stmt j)) (hs : FramedStatement s)
    (L M N P : List Choice) (xs ys : List (List Tok)) (rest tail : List Tok)
    (hyS : s.yield L = some (xs, M)) (hyT : t.yield N = some (ys, P))
    (he : xs.flatten ++ rest = ys.flatten ++ tail) :
    xs.flatten = ys.flatten ∧ rest = tail := by
  rcases statement_root_collision_cases s t L M N P xs ys rest tail hyS hyT he with
    equal | ⟨ss, tt⟩ | ⟨ss, tt⟩
  · rcases hs with block | semi
    · exact block_statement_prefix_split s t block (equal.symm.trans block)
        L M N P xs ys rest tail hyS hyT he
    · have target : SemiRoot (root t) = true := by rw [← equal]; exact semi
      exact semicolon_statement_prefix_split s t semi target
        L M N P xs ys rest tail hyS hyT he
  · have source : SemiRoot (root s) = true := by rw [ss]; rfl
    have target : SemiRoot (root t) = true := by rw [tt]; rfl
    exact semicolon_statement_prefix_split s t source target
      L M N P xs ys rest tail hyS hyT he
  · have source : SemiRoot (root s) = true := by rw [ss]; rfl
    have target : SemiRoot (root t) = true := by rw [tt]; rfl
    exact semicolon_statement_prefix_split s t source target
      L M N P xs ys rest tail hyS hyT he

/-- Equality of each actual statement token segment, not syntax-tree equality.
Layout consumption is retained exactly in each recursive decomposition. -/
theorem framed_statement_list_split {k j : SCtx}
    (ss : Syn (.list (.stmt k))) (ts : Syn (.list (.stmt j)))
    (hs : FramedStatements ss)
    (L M N P : List Choice) (xs ys : List (List Tok))
    (hyS : ss.yield L = some (xs, M)) (hyT : ts.yield N = some (ys, P))
    (he : xs.flatten = ys.flatten) : xs = ys := by
  cases ss with
  | nil =>
    have source : xs = [] := congrArg Prod.fst (Option.some.inj hyS).symm
    subst xs
    cases ts with
    | nil => exact congrArg Prod.fst (Option.some.inj hyT)
    | cons t ts =>
      obtain ⟨head, tail, mid, hh, ht, ey⟩ := list_yield_cons_decompose t ts N P ys hyT
      subst ys
      have empty : head.flatten = [] := (List.append_eq_nil_iff.mp he.symm).1
      exact False.elim (statement_yield_nonempty t N mid head hh empty)
  | cons s ss =>
    simp only [FramedStatements_cons] at hs
    obtain ⟨head, tail, mid, hh, ht, ex⟩ := list_yield_cons_decompose s ss L M xs hyS
    subst xs
    cases ts with
    | nil =>
      have target : ys = [] := congrArg Prod.fst (Option.some.inj hyT).symm
      subst ys
      have empty : head.flatten = [] := (List.append_eq_nil_iff.mp he).1
      exact False.elim (statement_yield_nonempty s L mid head hh empty)
    | cons t ts =>
      obtain ⟨headT, tailT, midT, hhT, htT, ey⟩ := list_yield_cons_decompose t ts N P ys hyT
      subst ys
      obtain ⟨first, suffix⟩ :=
        framed_statement_prefix_split s t hs.1 L mid N midT head headT
          tail.flatten tailT.flatten hh hhT he
      have rest : tail = tailT :=
        framed_statement_list_split ss ts hs.2 mid M midT P tail tailT ht htT suffix
      rw [first, rest]
termination_by ss

#print axioms statement_yield_nonempty
#print axioms block_statement_prefix_split
#print axioms framed_statement_prefix_split
#print axioms framed_statement_list_split
end Solidity.Frontend.StatementGrammarH28
