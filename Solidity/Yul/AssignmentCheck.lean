import Solidity.Yul.ExpressionCheck
import Solidity.Yul.ExternalCheck

/-! Assignment target checking on the original yulAssign path fields.
No intermediate AST is introduced. Supplied declaration-table provenance,
whole-block freshness and tier/safety admission remain separate obligations. -/
namespace Solidity.Yul

structure TargetEnv (X : List ExternalType) (n : Nat) where
  locals : List (String × Fin n)
  declarations : ExternalNames X

inductive TargetD {X n} (E : TargetEnv X n) :
    String → List String → Target X n → Type where
  | local {name i} : Resolves E.locals name i → TargetD E name [] (.«local» i)
  | external {name suffix ref} : (suffix ≠ [] ∨ NoBinding E.locals name) →
      ExternalD E.declarations true name suffix ref →
      TargetD E name suffix (.external ref)

def checkTarget {X n} (E : TargetEnv X n) (name : String) (suffix : List String) :
    Option ((target : Target X n) × TargetD E name suffix target) :=
  if hs : suffix = [] then
    match hl : resolve E.locals name with
    | some i => some ⟨.local i, hs.symm ▸ .local (resolve_sound hl)⟩
    | none => (checkExternal E.declarations name suffix true).map
        (fun ⟨ref, d⟩ => ⟨.external ref, .external (.inr (resolve_none_sound hl)) d⟩)
  else (checkExternal E.declarations name suffix true).map
    (fun ⟨ref, d⟩ => ⟨.external ref, .external (.inl hs) d⟩)

theorem TargetD.complete {X n E name suffix target}
    (d : @TargetD X n E name suffix target) :
    checkTarget E name suffix = some ⟨target, d⟩ := by
  cases d with
  | «local» binding =>
    unfold checkTarget
    rw [dif_pos rfl]
    split
    · next i hi =>
      have eq := Option.some.inj (hi.symm.trans (resolve_complete binding))
      cases eq
      rfl
    · next hi => have eq := resolve_complete binding; rw [hi] at eq; cases eq
  | external priority external =>
    by_cases hs : suffix = []
    · subst suffix
      have hl := resolve_none_complete (priority.resolve_left (fun bad => bad rfl))
      unfold checkTarget
      rw [dif_pos rfl]
      split
      · next i hi => rw [hl] at hi; cases hi
      · rw [external.complete]; rfl
    · unfold checkTarget
      rw [dif_neg hs, external.complete]
      rfl

/-- Nonempty dotted path from the original assignment constructor. -/
inductive TargetPathD {X n} (E : TargetEnv X n) : List String → Target X n → Type where
  | path {head tail target} : TargetD E head tail target → TargetPathD E (head :: tail) target

def checkTargetPath {X n} (E : TargetEnv X n) (path : List String) :
    Option ((target : Target X n) × TargetPathD E path target) :=
  match path with
  | [] => none
  | head :: tail => (checkTarget E head tail).map (fun ⟨target, d⟩ => ⟨target, .path d⟩)

theorem TargetPathD.complete {X n E path target} (d : @TargetPathD X n E path target) :
    checkTargetPath E path = some ⟨target, d⟩ := by
  cases d with
  | path d => change (checkTarget _ _ _).map _ = _; rw [d.complete]; rfl

/-- Independent target sequence semantics; each selected target remains intrinsic. -/
inductive TargetsD {X n} (E : TargetEnv X n) : List (List String) → Type where
  | nil : TargetsD E []
  | cons {path rest target} : TargetPathD E path target → TargetsD E rest →
      TargetsD E (path :: rest)

def checkTargets {X n} (E : TargetEnv X n) : (paths : List (List String)) → Option (TargetsD E paths)
  | [] => some .nil
  | path :: rest => do
    let ⟨_, d⟩ ← checkTargetPath E path
    let ds ← checkTargets E rest
    pure (.cons d ds)

theorem TargetsD.complete {X n E paths} (d : @TargetsD X n E paths) :
    checkTargets E paths = some d := by
  induction d with
  | nil => rfl
  | cons d ds ih =>
    simp only [checkTargets, d.complete, ih]
    rfl

/-- Explicit generalized recursor: no fixed-index match on derivations. -/
def TargetsD.terms {X n E paths} (d : @TargetsD X n E paths) :
    Fin paths.length → Target X n := by
  apply TargetsD.casesOn (motive := fun paths _ => Fin paths.length → Target X n) d
  case nil => exact Fin.elim0
  case cons =>
    intro path rest target _ restD
    exact Fin.cases target restD.terms
termination_by structural d

/-- Independent assignment judgement. Arity is the exact LHS path count;
duplicate paths are refused, including duplicate suffixes. Different fields
of one external function pointer are distinct targets. -/
inductive AssignmentD {F X n} (reads : ExprEnv F X n) (writes : TargetEnv X n)
    (paths : List (List String)) (rhs : Solidity.Source.Syn .yulExpr) : Type where
  | intro : paths ≠ [] → paths.Nodup → TargetsD writes paths → ExprD reads rhs paths.length →
      AssignmentD reads writes paths rhs

def checkAssignment {F X n} (reads : ExprEnv F X n) (writes : TargetEnv X n)
    (paths : List (List String)) (rhs : Solidity.Source.Syn .yulExpr) :
    Option (AssignmentD reads writes paths rhs) :=
  if nonempty : paths ≠ [] then
   if fresh : paths.Nodup then do
    let targets ← checkTargets writes paths
    let ⟨arity, expression⟩ ← inferExpr reads rhs
    if same : arity = paths.length then
      pure (.intro nonempty fresh targets (same ▸ expression))
    else none
   else none
  else none

theorem AssignmentD.complete {F X n reads writes paths rhs}
    (d : @AssignmentD F X n reads writes paths rhs) :
    checkAssignment reads writes paths rhs = some d := by
  cases d with
  | intro nonempty unique targets expression =>
    unfold checkAssignment
    rw [dif_pos nonempty, dif_pos unique, targets.complete]
    change (inferExpr _ _).bind _ = _
    rw [expression.complete]
    change (if same : paths.length = paths.length then _ else _) = _
    rw [dif_pos rfl]
    rfl

/-- Soundness constructs the context/arity-indexed assignment directly. -/
def AssignmentD.statement {F X n reads writes paths rhs}
    (d : @AssignmentD F X n reads writes paths rhs) (c : Control) : Stmt F X c n := by
  cases d with
  | intro _ _ targets expression => exact .assign targets.terms expression.term

theorem checkAssignment_iff {F X n} (reads : ExprEnv F X n) (writes : TargetEnv X n)
    (paths : List (List String)) (rhs : Solidity.Source.Syn .yulExpr) :
    (checkAssignment reads writes paths rhs).isSome = true ↔
      Nonempty (AssignmentD reads writes paths rhs) := by
  constructor
  · intro h
    cases found : checkAssignment reads writes paths rhs with
    | none => rw [found] at h; cases h
    | some d => exact ⟨d⟩
  · rintro ⟨d⟩
    rw [d.complete]
    rfl

end Solidity.Yul
