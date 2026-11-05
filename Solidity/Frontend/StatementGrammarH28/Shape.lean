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

private def rootResult : Cat → Type
  | .stmt _ => Root
  | _ => PUnit

private def rootAt {category : Cat} (tree : Syn category) : rootResult category := by
  apply Syn.casesOn (motive := fun category _ => rootResult category) tree
  case blockStmt => intros; exact .block
  case simpleStmt => intros; exact .simple
  case ifStmt => intros; exact .conditional
  case forStmt => intros; exact .forLoop
  case whileStmt => intros; exact .whileLoop
  case doWhile => intros; exact .doLoop
  case continueStmt => intros; exact .continueLoop
  case breakStmt => intros; exact .breakLoop
  case tryStmt => intros; exact .tryCatch
  case returnStmt => intros; exact .returnValue
  case emit => intros; exact .emitEvent
  case revert => intros; exact .revertError
  case assembly => intros; exact .assembly
  all_goals intros; exact PUnit.unit

def root {k : SCtx} (s : Syn (.stmt k)) : Root := rootAt s

theorem root_blockStmt {k : SCtx} (b : Syn (.block k)) : root (.blockStmt b) = .block := rfl

theorem root_simpleStmt {k : SCtx} (s : Syn .simple) : root (.simpleStmt (k := k) s) = .simple := rfl

theorem root_ifStmt {k : SCtx} (c : Syn .expr) (t : Syn (.stmt k)) (e : Syn (.opt (.stmt k))) :
    root (.ifStmt c t e) = .conditional := rfl

theorem root_forStmt {l u : Bool} (i : Syn (.opt .simple)) (c v : Syn (.opt .expr))
    (b : Syn (.stmt ⟨true,u⟩)) : root (.forStmt (l := l) i c v b) = .forLoop := rfl

theorem root_whileStmt {l u : Bool} (c : Syn .expr) (b : Syn (.stmt ⟨true,u⟩)) :
    root (.whileStmt (l := l) c b) = .whileLoop := rfl

theorem root_doWhile {l u : Bool} (b : Syn (.stmt ⟨true,u⟩)) (c : Syn .expr) :
    root (.doWhile (l := l) b c) = .doLoop := rfl

theorem root_continueStmt {u : Bool} : root (Syn.continueStmt (u := u)) = .continueLoop := rfl

theorem root_breakStmt {u : Bool} : root (Syn.breakStmt (u := u)) = .breakLoop := rfl

theorem root_tryStmt {k : SCtx} (e : Syn .expr) (rs : Syn (.list .param)) (b : Syn (.block k))
    (h : Syn (.catchClause k)) (hs : Syn (.list (.catchClause k))) :
    root (.tryStmt e rs b h hs) = .tryCatch := rfl

theorem root_returnStmt {k : SCtx} (e : Syn (.opt .expr)) :
    root (.returnStmt (k := k) e) = .returnValue := rfl

theorem root_emit {k : SCtx} (e : Syn .expr) (args : Syn .callArgs) :
    root (.emit (k := k) e args) = .emitEvent := rfl

theorem root_revert {k : SCtx} (e : Syn .expr) (args : Syn .callArgs) :
    root (.revert (k := k) e args) = .revertError := rfl

theorem root_assembly {k : SCtx} (evm : Bool) (flags : List String) (body : Syn (.list .yulStmt)) :
    root (.assembly (k := k) evm flags body) = .assembly := rfl

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
