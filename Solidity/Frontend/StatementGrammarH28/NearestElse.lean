import Solidity.Frontend.Checked.Prec

/-!
# The intrinsic dangling-else boundary

OpenSpine follows exactly the statement positions to which a following else
can attach. Expressions remain atoms. The relation is indexed by existing
Syn and does not add a syntax representation. These results formalize the
existing precedence contract, not uniqueness of expression token yields.
-/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source

inductive OpenSpine : {k : SCtx} → Syn (.stmt k) → Prop where
  | missing {k : SCtx} (c : Syn .expr) (t : Syn (.stmt k)) :
      OpenSpine (.ifStmt c t .none)
  | elseBranch {k : SCtx} (c : Syn .expr) (t e : Syn (.stmt k)) :
      OpenSpine e → OpenSpine (.ifStmt c t (.some e))
  | forBody {l u : Bool} (i : Syn (.opt .simple))
      (c v : Syn (.opt .expr)) (b : Syn (.stmt ⟨true, u⟩)) :
      OpenSpine b → OpenSpine (.forStmt (l := l) i c v b)
  | whileBody {l u : Bool} (c : Syn .expr) (b : Syn (.stmt ⟨true, u⟩)) :
      OpenSpine b → OpenSpine (.whileStmt (l := l) c b)

def OpenSpine.isOpen : {k : SCtx} → {s : Syn (.stmt k)} →
    OpenSpine s → s.openIf = true
  | _, _, .missing _ _ => rfl
  | _, _, .elseBranch _ _ _ h => h.isOpen
  | _, _, .forBody _ _ _ _ h => h.isOpen
  | _, _, .whileBody _ _ h => h.isOpen

def spineOfOpen : {k : SCtx} → (s : Syn (.stmt k)) →
    s.openIf = true → OpenSpine s
  | _, .ifStmt c t .none, _ => .missing c t
  | _, .ifStmt c t (.some e), h => .elseBranch c t e (spineOfOpen e h)
  | _, .forStmt i c v b, h => .forBody i c v b (spineOfOpen b h)
  | _, .whileStmt c b, h => .whileBody c b (spineOfOpen b h)
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

theorem openSpine_iff {k : SCtx} (s : Syn (.stmt k)) :
    OpenSpine s ↔ s.openIf = true := ⟨OpenSpine.isOpen, spineOfOpen s⟩

/-- At every else-bearing if, the existing node contract prevents capture by
any open if on the then branch's exposed spine. -/
theorem nearestElse_node {k : SCtx} (c : Syn .expr) (t e : Syn (.stmt k))
    (h : (Syn.ifStmt c t (.some e)).precNode = true) : ¬ OpenSpine t := by
  intro hs
  change (!t.openIf) = true at h
  rw [hs.isOpen] at h
  cases h

theorem nearestElse {k : SCtx} (c : Syn .expr) (t e : Syn (.stmt k))
    (h : (Syn.ifStmt c t (.some e)).prec = true) : ¬ OpenSpine t :=
  nearestElse_node c t e (Syn.prec_root h)

/-- A braced block is a closed boundary for arbitrary block contents. -/
theorem block_closed {k : SCtx} (b : Syn (.block k)) :
    ¬ OpenSpine (.blockStmt b) := by
  intro h
  have bad : false = true := h.isOpen
  cases bad

/-- A do-while's trailing while clause closes its body's dangling-if path. -/
theorem doWhile_closed {l u : Bool} (b : Syn (.stmt ⟨true, u⟩)) (c : Syn .expr) :
    ¬ OpenSpine (.doWhile (l := l) b c) := by
  intro h
  have bad : false = true := h.isOpen
  cases bad

#print axioms openSpine_iff
#print axioms nearestElse_node
#print axioms nearestElse
#print axioms block_closed
#print axioms doWhile_closed
end Solidity.Frontend.StatementGrammarH28
