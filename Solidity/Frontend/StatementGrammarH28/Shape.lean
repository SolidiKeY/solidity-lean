import Solidity.Source.Syntax

/-!
# Statement root inventory (H28 G11)

Classification is indexed by the existing `Syn (.stmt k)`; `Root` is a
finite observation, not an alternative syntax tree. No expression subtree
is traversed. Root discrimination here is syntactic, not token uniqueness.
-/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source

inductive Root where
  | block | simple | conditional | forLoop | whileLoop | doLoop
  | continueLoop | breakLoop | tryCatch | returnValue | emitEvent | revertError | assembly
  deriving DecidableEq, Repr

def root {k : SCtx} : Syn (.stmt k) → Root
  | .blockStmt _ => .block
  | .simpleStmt _ => .simple
  | .ifStmt _ _ _ => .conditional
  | .forStmt _ _ _ _ => .forLoop
  | .whileStmt _ _ => .whileLoop
  | .doWhile _ _ => .doLoop
  | .continueStmt => .continueLoop
  | .breakStmt => .breakLoop
  | .tryStmt _ _ _ _ _ => .tryCatch
  | .returnStmt _ => .returnValue
  | .emit _ _ => .emitEvent
  | .revert _ _ => .revertError
  | .assembly _ _ _ => .assembly

/-- Intrinsic shape relation: its subject remains the existing indexed syntax. -/
def HasRoot {k : SCtx} (s : Syn (.stmt k)) (r : Root) : Prop := root s = r

theorem hasRoot_exists {k : SCtx} (s : Syn (.stmt k)) : ∃ r, HasRoot s r :=
  ⟨root s, rfl⟩

theorem hasRoot_unique {k : SCtx} {s : Syn (.stmt k)} {r q : Root}
    (h : HasRoot s r) (h' : HasRoot s q) : r = q := h.symm.trans h'

theorem root_discriminate {k : SCtx} {s t : Syn (.stmt k)}
    (h : root s ≠ root t) : s ≠ t := fun e => h (congrArg root e)

/-- The only restrictions on inhabiting a statement root come from loop control. -/
def Root.allowed (k : SCtx) : Root → Prop
  | .continueLoop | .breakLoop => k.loop = true
  | _ => True

theorem root_allowed {k : SCtx} (s : Syn (.stmt k)) : (root s).allowed k := by
  cases s <;> trivial

/-- Every listed root has an intrinsic representative in exactly its permitted contexts.
This does not assert that arbitrary expression atoms parse or pass admission. -/
theorem root_inhabited (k : SCtx) (r : Root) (h : r.allowed k) :
    ∃ s : Syn (.stmt k), HasRoot s r := by
  obtain ⟨l, u⟩ := k
  cases r with
  | block => exact ⟨.blockStmt (.block .nil), rfl⟩
  | simple => exact ⟨.simpleStmt (.exprStmt (.ident "x")), rfl⟩
  | conditional => exact ⟨.ifStmt (.ident "x") (.returnStmt .none) .none, rfl⟩
  | forLoop => exact ⟨.forStmt .none .none .none (.returnStmt .none), rfl⟩
  | whileLoop => exact ⟨.whileStmt (.ident "x") (.returnStmt .none), rfl⟩
  | doLoop => exact ⟨.doWhile (.returnStmt .none) (.ident "x"), rfl⟩
  | continueLoop =>
    change l = true at h
    subst l
    exact ⟨.continueStmt, rfl⟩
  | breakLoop =>
    change l = true at h
    subst l
    exact ⟨.breakStmt, rfl⟩
  | tryCatch => exact ⟨.tryStmt (.ident "x") .nil (.block .nil)
      (.catchPlain (.block .nil)) .nil, rfl⟩
  | returnValue => exact ⟨.returnStmt .none, rfl⟩
  | emitEvent => exact ⟨.emit (.ident "E") (.positional .nil), rfl⟩
  | revertError => exact ⟨.revert (.ident "E") (.positional .nil), rfl⟩
  | assembly => exact ⟨.assembly false [] .nil, rfl⟩

theorem root_inhabited_iff (k : SCtx) (r : Root) :
    (∃ s : Syn (.stmt k), HasRoot s r) ↔ r.allowed k := by
  constructor
  · rintro ⟨s, hs⟩
    rw [← hs]
    exact root_allowed s
  · exact root_inhabited k r

#print axioms hasRoot_exists
#print axioms hasRoot_unique
#print axioms root_discriminate
#print axioms root_allowed
#print axioms root_inhabited
#print axioms root_inhabited_iff
end Solidity.Frontend.StatementGrammarH28
