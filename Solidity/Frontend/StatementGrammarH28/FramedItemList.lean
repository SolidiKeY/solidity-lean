import Solidity.Frontend.StatementGrammarH28.BoundaryHead
import Solidity.Frontend.StatementGrammarH28.FramedStatementList

/-! Universal statement continuation-token refusal and actual block-item
segmentation. Source statement items use the existing seven-root fragment;
unchecked items contain arbitrary blocks. Targets remain arbitrary syntax. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

theorem statement_boundary_head {k : SCtx} (s : Syn (.stmt k)) :
    PrEnsures s.yield BoundaryParts := by
  by_cases hs : root s = .simple
  · cases s with
    | simpleStmt a =>
      rw [Syn.yield]
      apply ensures_bind_checked _ _ BoundaryParts BoundaryParts (simple_yield_boundary_start a)
      intro parts hp
      apply ensures_pure _ BoundaryParts
      simpa only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil] using
        boundary_start_append hp (pu .semi)
    | _ => cases hs
  · have fixed : ∃ tok, (root s).firstToken = some tok ∧ boundaryToken tok = false := by
      cases hr : root s <;> first
        | exact ⟨_, rfl, rfl⟩
        | exact False.elim (hs hr)
    obtain ⟨tok, ht, hb⟩ := fixed
    intro L parts M hy
    have head := statement_fixed_head s tok ht L parts M hy
    change parts.flatten.head? = some tok at head
    cases he : parts.flatten with
    | nil => rw [he] at head; cases head
    | cons a rest =>
      rw [he] at head
      have eq : a = tok := Option.some.inj head
      exact ⟨a, rest, he, eq.symm ▸ hb⟩

theorem statement_boundary_prefix_refusal {k : SCtx} (s : Syn (.stmt k))
    (L M : List Choice) (parts : List (List Tok)) (tail : List Tok) (tok : Tok)
    (hy : s.yield L = some (parts, M)) (hb : boundaryToken tok = true) :
    (parts.flatten ++ tail).head? ≠ some tok := by
  obtain ⟨a, rest, he, ha⟩ := statement_boundary_head s L parts M hy
  intro bad
  rw [he] at bad
  have eq : a = tok := Option.some.inj bad
  have contradiction : boundaryToken tok = false := eq ▸ ha
  rw [hb] at contradiction
  cases contradiction

theorem unchecked_yield_decompose {l : Bool} (b : Syn (.block ⟨l, true⟩))
    (L M : List Choice) (parts : List (List Tok))
    (hy : (Syn.uncheckedItem (l := l) b).yield L = some (parts, M)) :
    ∃ chunks, b.yield L = some (chunks, M) ∧
      parts = [tk .unchecked ++ chunks.flatten] := by
  change (b.yield L).bind (fun (chunks, N) =>
    some ([tk .unchecked ++ chunks.flatten], N)) = some (parts, M) at hy
  obtain ⟨⟨chunks, N⟩, hb, he⟩ := Option.bind_eq_some_iff.mp hy
  have eq := Option.some.inj he
  have layout : N = M := congrArg Prod.snd eq
  subst N
  exact ⟨chunks, hb, (congrArg Prod.fst eq).symm⟩

theorem unchecked_yield_head {l : Bool} (b : Syn (.block ⟨l, true⟩))
    (L M : List Choice) (parts : List (List Tok)) (tail : List Tok)
    (hy : (Syn.uncheckedItem (l := l) b).yield L = some (parts, M)) :
    (parts.flatten ++ tail).head? = some (.kw .unchecked) := by
  obtain ⟨chunks, hb, he⟩ := unchecked_yield_decompose b L M parts hy
  rw [he]
  rfl

private def framedItemResult : Cat → Type
  | .item _ => Prop
  | _ => PUnit

private def framedItemAt {category : Cat} (tree : Syn category) : framedItemResult category := by
  apply Syn.casesOn (motive := fun category _ => framedItemResult category) tree
  case stmtItem => intro k s; exact FramedStatement s
  case uncheckedItem => intros; exact True
  all_goals intros; exact PUnit.unit

def FramedItem {k : SCtx} (x : Syn (.item k)) : Prop := framedItemAt x

def FramedItems {k : SCtx} (xs : Syn (.list (.item k))) : Prop :=
  (g0ListValues xs).foldr (fun x rest => FramedItem x ∧ rest) True

theorem FramedItem_stmtItem {k : SCtx} (s : Syn (.stmt k)) :
    FramedItem (.stmtItem s) = FramedStatement s := rfl

theorem FramedItem_uncheckedItem {l : Bool} (b : Syn (.block ⟨l,true⟩)) :
    FramedItem (.uncheckedItem b) = True := rfl

theorem FramedItems_nil {k : SCtx} :
    FramedItems (Syn.nil (c := .item k)) = True := rfl

theorem FramedItems_cons {k : SCtx} (x : Syn (.item k)) (xs : Syn (.list (.item k))) :
    FramedItems (.cons x xs) = (FramedItem x ∧ FramedItems xs) := rfl

theorem item_yield_nonempty {k : SCtx} (x : Syn (.item k))
    (L M : List Choice) (parts : List (List Tok))
    (hy : x.yield L = some (parts, M)) : parts.flatten ≠ [] := by
  cases x with
  | stmtItem s => exact statement_yield_nonempty s L M parts hy
  | uncheckedItem b =>
    have head := unchecked_yield_head b L M parts [] hy
    intro empty
    rw [empty] at head
    cases head

theorem framed_item_prefix_split {k j : SCtx}
    (x : Syn (.item k)) (y : Syn (.item j)) (hx : FramedItem x)
    (L M N P : List Choice) (xs ys : List (List Tok)) (rest tail : List Tok)
    (hyX : x.yield L = some (xs, M)) (hyY : y.yield N = some (ys, P))
    (he : xs.flatten ++ rest = ys.flatten ++ tail) :
    xs.flatten = ys.flatten ∧ rest = tail := by
  cases x with
  | stmtItem s =>
    cases y with
    | stmtItem t => exact framed_statement_prefix_split s t hx L M N P xs ys rest tail hyX hyY he
    | uncheckedItem b =>
      have forbidden := statement_boundary_prefix_refusal s L M xs rest (.kw .unchecked) hyX rfl
      rw [he, unchecked_yield_head b N P ys tail hyY] at forbidden
      exact False.elim (forbidden rfl)
  | uncheckedItem b =>
    cases y with
    | stmtItem t =>
      have forbidden := statement_boundary_prefix_refusal t N P ys tail (.kw .unchecked) hyY rfl
      rw [← he, unchecked_yield_head b L M xs rest hyX] at forbidden
      exact False.elim (forbidden rfl)
    | uncheckedItem c =>
      obtain ⟨bs, hb, ex⟩ := unchecked_yield_decompose b L M xs hyX
      obtain ⟨cs, hc, ey⟩ := unchecked_yield_decompose c N P ys hyY
      subst xs
      subst ys
      have heads : (.kw .unchecked : Tok) :: (bs.flatten ++ rest) =
          .kw .unchecked :: (cs.flatten ++ tail) := by
        simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, tk,
          List.cons_append, List.nil_append] using he
      obtain ⟨body, eb, ec, suffix⟩ :=
        arbitrary_block_prefix_split b c L M N P bs cs rest tail hb hc (List.cons.inj heads).2
      exact ⟨by rw [eb, ec], suffix⟩

theorem framed_item_list_split {k j : SCtx}
    (ss : Syn (.list (.item k))) (ts : Syn (.list (.item j)))
    (hs : FramedItems ss)
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
      exact False.elim (item_yield_nonempty t N mid head hh empty)
  | cons s ss =>
    simp only [FramedItems_cons] at hs
    obtain ⟨head, tail, mid, hh, ht, ex⟩ := list_yield_cons_decompose s ss L M xs hyS
    subst xs
    cases ts with
    | nil =>
      have target : ys = [] := congrArg Prod.fst (Option.some.inj hyT).symm
      subst ys
      have empty : head.flatten = [] := (List.append_eq_nil_iff.mp he).1
      exact False.elim (item_yield_nonempty s L mid head hh empty)
    | cons t ts =>
      obtain ⟨headT, tailT, midT, hhT, htT, ey⟩ := list_yield_cons_decompose t ts N P ys hyT
      subst ys
      obtain ⟨first, suffix⟩ :=
        framed_item_prefix_split s t hs.1 L mid N midT head headT
          tail.flatten tailT.flatten hh hhT he
      have rest : tail = tailT :=
        framed_item_list_split ss ts hs.2 mid M midT P tail tailT ht htT suffix
      rw [first, rest]
termination_by ss

theorem framed_block_item_segments {k j : SCtx}
    (ss : Syn (.list (.item k))) (ts : Syn (.list (.item j))) (hs : FramedItems ss)
    (L M N P : List Choice) (xs ys : List (List Tok)) (rest tail : List Tok)
    (hyS : ss.yield L = some (xs, M)) (hyT : ts.yield N = some (ys, P))
    (he : braces xs.flatten ++ rest = braces ys.flatten ++ tail) :
    xs = ys ∧ rest = tail := by
  have bx := balancedParts_flat (syntax_yield_balanced ss rfl L xs M hyS)
  have by_ := balancedParts_flat (syntax_yield_balanced ts rfl N ys P hyT)
  obtain ⟨body, suffix⟩ := balanced_braced_split bx by_ he
  exact ⟨framed_item_list_split ss ts hs L M N P xs ys hyS hyT body, suffix⟩

end Solidity.Frontend.StatementGrammarH28
