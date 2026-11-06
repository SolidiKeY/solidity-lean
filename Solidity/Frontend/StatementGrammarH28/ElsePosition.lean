import Solidity.Frontend.StatementGrammarH28.NearestElse

/-! Unique exposed missing-else position in existing intrinsic statements.
Edges are observations of statement positions, not a syntax representation.
Expression subtrees are never traversed. No token-parse uniqueness is claimed. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source

inductive ElseEdge where
  | thenBranch | elseBranch | forBody | whileBody
  deriving DecidableEq, Repr

/-- The innermost exposed missing else. A root slot is available only when
its then branch is closed; otherwise the unique candidate is inside it. -/
inductive NearestSlot : {k : SCtx} → Syn (.stmt k) → List ElseEdge → Prop where
  | root {k : SCtx} (c : Syn .expr) (t : Syn (.stmt k)) :
      t.openIf = false → NearestSlot (.ifStmt c t .none) []
  | thenBranch {k : SCtx} (c : Syn .expr) (t : Syn (.stmt k)) {p : List ElseEdge} :
      NearestSlot t p → NearestSlot (.ifStmt c t .none) (.thenBranch :: p)
  | elseBranch {k : SCtx} (c : Syn .expr) (t e : Syn (.stmt k)) {p : List ElseEdge} :
      NearestSlot e p → NearestSlot (.ifStmt c t (.some e)) (.elseBranch :: p)
  | forBody {l u : Bool} (i : Syn (.opt .simple)) (c v : Syn (.opt .expr))
      (b : Syn (.stmt ⟨true, u⟩)) {p : List ElseEdge} :
      NearestSlot b p → NearestSlot (.forStmt (l := l) i c v b) (.forBody :: p)
  | whileBody {l u : Bool} (c : Syn .expr) (b : Syn (.stmt ⟨true, u⟩))
      {p : List ElseEdge} :
      NearestSlot b p → NearestSlot (.whileStmt (l := l) c b) (.whileBody :: p)

def NearestSlot.isOpen : {k : SCtx} → {s : Syn (.stmt k)} → {p : List ElseEdge} →
    NearestSlot s p → s.openIf = true
  | _, _, _, .root _ _ _ => rfl
  | _, _, _, .thenBranch _ _ _ => rfl
  | _, _, _, .elseBranch _ _ _ h => h.isOpen
  | _, _, _, .forBody _ _ _ _ h => h.isOpen
  | _, _, _, .whileBody _ _ h => h.isOpen

theorem nearestSlot_unique {k : SCtx} {s : Syn (.stmt k)} {p q : List ElseEdge}
    (hp : NearestSlot s p) (hq : NearestSlot s q) : p = q := by
  induction hp generalizing q with
  | root c t ht =>
    cases hq with
    | root _ _ _ => rfl
    | thenBranch _ _ h =>
      have bad : false = true := ht.symm.trans h.isOpen
      cases bad
  | thenBranch c t h ih =>
    cases hq with
    | root _ _ ht =>
      have bad : false = true := ht.symm.trans h.isOpen
      cases bad
    | thenBranch _ _ hq => exact congrArg (List.cons .thenBranch) (ih hq)
  | elseBranch c t e h ih =>
    cases hq with
    | elseBranch _ _ _ hq => exact congrArg (List.cons .elseBranch) (ih hq)
  | forBody i c v b h ih =>
    cases hq with
    | forBody _ _ _ _ hq => exact congrArg (List.cons .forBody) (ih hq)
  | whileBody c b h ih =>
    cases hq with
    | whileBody _ _ hq => exact congrArg (List.cons .whileBody) (ih hq)

def slotOfOpen : {k : SCtx} → (s : Syn (.stmt k)) →
    s.openIf = true → ∃ p, NearestSlot s p
  | _, .ifStmt c t .none, _ => by
      cases ht : t.openIf with
      | false => exact ⟨[], .root c t ht⟩
      | true =>
        obtain ⟨p, hp⟩ := slotOfOpen t ht
        exact ⟨.thenBranch :: p, .thenBranch c t hp⟩
  | _, .ifStmt c t (.some e), h => by
      obtain ⟨p, hp⟩ := slotOfOpen e h
      exact ⟨.elseBranch :: p, .elseBranch c t e hp⟩
  | _, .forStmt i c v b, h => by
      obtain ⟨p, hp⟩ := slotOfOpen b h
      exact ⟨.forBody :: p, .forBody i c v b hp⟩
  | _, .whileStmt c b, h => by
      obtain ⟨p, hp⟩ := slotOfOpen b h
      exact ⟨.whileBody :: p, .whileBody c b hp⟩
  | _, .blockStmt _, h => by cases h
  | _, .simpleStmt _, h => by cases h
  | _, .doWhile _ _, h => by cases h
  | _, .continueStmt, h => by cases h
  | _, .breakStmt, h => by cases h
  | _, .tryStmt _ _ _ _ _, h => by cases h
  | _, .returnStmt _, h => by cases h
  | _, .emit _ _, h => by cases h
  | _, .revert _ _, h => by cases h
  | _, .assembly _ _ _, h => by cases h

theorem nearestSlot_exists_iff {k : SCtx} (s : Syn (.stmt k)) :
    (∃ p, NearestSlot s p) ↔ s.openIf = true := by
  constructor
  · intro ⟨p, hp⟩
    exact hp.isOpen
  · exact slotOfOpen s

theorem nearestSlot_unique_exists {k : SCtx} (s : Syn (.stmt k))
    (h : s.openIf = true) : ∃ p, NearestSlot s p ∧
      ∀ q, NearestSlot s q → q = p := by
  obtain ⟨p, hp⟩ := slotOfOpen s h
  exact ⟨p, hp, fun q hq => nearestSlot_unique hq hp⟩

/-- The existing else-bearing node contract excludes every attachment slot
inside its then branch, for arbitrary syntax and without expression premises. -/
theorem prec_else_no_then_slot {k : SCtx} (c : Syn .expr) (t e : Syn (.stmt k))
    (h : (Syn.ifStmt c t (.some e)).prec = true) (p : List ElseEdge) :
    ¬ NearestSlot t p := by
  intro hp
  exact nearestElse c t e h (spineOfOpen t hp.isOpen)

#print axioms nearestSlot_unique
#print axioms nearestSlot_exists_iff
#print axioms nearestSlot_unique_exists
#print axioms prec_else_no_then_slot
end Solidity.Frontend.StatementGrammarH28
