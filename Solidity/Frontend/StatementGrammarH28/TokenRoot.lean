import Solidity.Frontend.StatementGrammarH28.Shape
import Solidity.Frontend.Checked.Print

/-! Fixed leading tokens of actual statement yields. Simple statements are
explicitly unresolved here; no expression uniqueness premise is introduced. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def PrEnsures {α : Type} (p : Pr α) (P : α → Prop) : Prop :=
  ∀ L a M, p L = some (a, M) → P a

theorem ensures_pure {α : Type} (a : α) (P : α → Prop) (ha : P a) :
    PrEnsures (pure a) P := by
  intro L b M h
  change some (a, L) = some (b, M) at h
  have hab : a = b := congrArg Prod.fst (Option.some.inj h)
  exact hab ▸ ha

theorem ensures_bind {α β : Type} (p : Pr α) (f : α → Pr β) (P : β → Prop)
    (hf : ∀ a, PrEnsures (f a) P) : PrEnsures (p >>= f) P := by
  intro L b M h
  change (p L).bind (fun (a, N) => f a N) = some (b, M) at h
  cases hp : p L with
  | none => rw [hp] at h; cases h
  | some pair =>
    obtain ⟨a, N⟩ := pair
    rw [hp] at h
    exact hf a N b M h

/-- All non-simple roots have a fixed leading token. Revert's token is an
identifier, preserving the actual contextual-keyword printing convention. -/
def Root.firstToken : Root → Option Tok
  | .block => some (.punct .lbrace)
  | .simple => none
  | .conditional => some (.kw .if_)
  | .forLoop => some (.kw .for_)
  | .whileLoop => some (.kw .while_)
  | .doLoop => some (.kw .do_)
  | .continueLoop => some (.kw .continue_)
  | .breakLoop => some (.kw .break_)
  | .tryCatch => some (.kw .try_)
  | .returnValue => some (.kw .return_)
  | .emitEvent => some (.kw .emit)
  | .revertError => some (.ident "revert")
  | .assembly => some (.kw .assembly)

theorem statement_fixed_head {k : SCtx} (s : Syn (.stmt k)) (t : Tok)
    (ht : (root s).firstToken = some t) :
    PrEnsures s.yield (fun parts => parts.flatten.head? = some t) := by
  cases s with
  | blockStmt b =>
    cases ht
    cases b with
    | block items =>
      simp only [Syn.yield]
      apply ensures_bind
      intro parts
      apply ensures_pure
      rfl
  | simpleStmt s => cases ht
  | ifStmt c t e =>
    cases ht
    simp only [Syn.yield]
    apply ensures_bind
    intro x
    apply ensures_bind
    intro y
    apply ensures_bind
    intro z
    apply ensures_pure
    rfl
  | forStmt i c v b =>
    cases ht
    simp only [Syn.yield]
    apply ensures_bind
    intro x
    apply ensures_bind
    intro y
    apply ensures_bind
    intro z
    apply ensures_bind
    intro w
    apply ensures_pure
    rfl
  | whileStmt c b =>
    cases ht
    simp only [Syn.yield]
    apply ensures_bind
    intro x
    apply ensures_bind
    intro y
    apply ensures_pure
    rfl
  | doWhile b c =>
    cases ht
    simp only [Syn.yield]
    apply ensures_bind
    intro x
    apply ensures_bind
    intro y
    apply ensures_pure
    rfl
  | continueStmt =>
    cases ht
    exact ensures_pure _ _ rfl
  | breakStmt =>
    cases ht
    exact ensures_pure _ _ rfl
  | tryStmt e rets b c cs =>
    cases ht
    simp only [Syn.yield]
    apply ensures_bind
    intro x
    apply ensures_bind
    intro r
    apply ensures_bind
    intro y
    apply ensures_bind
    intro z
    apply ensures_bind
    intro zs
    apply ensures_pure
    rfl
  | returnStmt e =>
    cases ht
    simp only [Syn.yield]
    apply ensures_bind
    intro x
    apply ensures_pure
    rfl
  | emit e args =>
    cases ht
    simp only [Syn.yield]
    apply ensures_bind
    intro x
    apply ensures_bind
    intro a
    apply ensures_pure
    rfl
  | revert e args =>
    cases ht
    simp only [Syn.yield]
    apply ensures_bind
    intro x
    apply ensures_bind
    intro a
    apply ensures_pure
    rfl
  | assembly evm flags body =>
    cases ht
    simp only [Syn.yield]
    apply ensures_bind
    intro b
    apply ensures_pure
    rfl

theorem root_firstToken_injective (r q : Root)
    (h : r.firstToken = q.firstToken) : r = q := by
  cases r <;> cases q <;> cases h <;> rfl

theorem root_firstToken_defined (r : Root) (h : r ≠ .simple) :
    ∃ t, r.firstToken = some t := by
  cases r <;> first | exact ⟨_, rfl⟩ | exact False.elim (h rfl)

theorem head_append_of_some (xs tail : List Tok) (t : Tok)
    (h : xs.head? = some t) : (xs ++ tail).head? = some t := by
  cases xs with
  | nil => cases h
  | cons x rest => exact h

/-- Equal token prefixes force equal non-simple roots, even when their
suffixes and layout choices differ. This does not compare subtree syntax. -/
theorem nonSimple_root_of_equal_prefix {k j : SCtx}
    (s : Syn (.stmt k)) (t : Syn (.stmt j))
    (hs : root s ≠ .simple) (ht : root t ≠ .simple)
    (L M N P : List Choice) (xs ys : List (List Tok)) (rest tail : List Tok)
    (hyS : s.yield L = some (xs, M)) (hyT : t.yield N = some (ys, P))
    (he : xs.flatten ++ rest = ys.flatten ++ tail) : root s = root t := by
  obtain ⟨a, ha⟩ := root_firstToken_defined (root s) hs
  obtain ⟨b, hb⟩ := root_firstToken_defined (root t) ht
  have headS : xs.flatten.head? = some a := statement_fixed_head s a ha L xs M hyS
  have headT : ys.flatten.head? = some b := statement_fixed_head t b hb N ys P hyT
  have appendS := head_append_of_some xs.flatten rest a headS
  rw [he, head_append_of_some ys.flatten tail b headT] at appendS
  have ab : a = b := (Option.some.inj appendS).symm
  apply root_firstToken_injective
  exact ha.trans ((congrArg some ab).trans hb.symm)

#print axioms root_firstToken_injective
#print axioms root_firstToken_defined
#print axioms head_append_of_some
#print axioms nonSimple_root_of_equal_prefix
#print axioms ensures_pure
#print axioms ensures_bind
#print axioms statement_fixed_head
end Solidity.Frontend.StatementGrammarH28
