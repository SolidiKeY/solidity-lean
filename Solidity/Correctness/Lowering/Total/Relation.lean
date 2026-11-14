import Solidity.Correctness.Lowering.Loops.Statement

/-!
# Names at the universal loop-lowering boundary

This interface advances `Solidity.Goals.lowerLoopsCorrect`; it does not bind
that goal. A fresh renaming fixes user names and every caller binding, including
caller bindings which already have fresh identities. It cannot merge flags.
Raw spelling round trips and collision avoidance are separate obligations:
`FreshNames` itself has no laws, and equality of printed strings is not
alpha-equivalence of intrinsic variables.
-/
namespace Solidity.Correctness.Lowering.Total

/-- A bijection of intrinsic names fixing all names observable by the caller.
The inverse is explicit so symmetry never assumes an unproved injectivity law
for a configurable `FreshNames` printer. -/
structure FreshRenaming (live : List Var) where
  forward : Var → Var
  backward : Var → Var
  leftInverse : ∀ x, backward (forward x) = x
  rightInverse : ∀ x, forward (backward x) = x
  user : ∀ x, forward (.user x) = .user x
  caller : ∀ x, x ∈ live → forward x = x

/-- Fresh-name equivalence of an ordered collection of binders/occurrences.
The same bijection acts at every position: repeated occurrences stay repeated,
distinct flags stay distinct, and caller identities cannot be captured.
This is a name interface, not yet a raw-syntax or program equivalence theorem. -/
def FreshNameEquiv (live left right : List Var) : Prop :=
  ∃ permutation : FreshRenaming live, left.map permutation.forward = right

/-- Raw spellings of generated identities must decode to those identities and
must avoid the protected spellings. These conditions are not laws of arbitrary
`FreshNames` instances; a production coverage proof must establish them. -/
def SafeSpellings (names : FreshNames) (protectedNames : List String)
    (generated : List (String × Nat)) : Prop :=
  (∀ id ∈ generated, names.parse (names.name id.1 id.2) = some id) ∧
  (∀ id ∈ generated, names.name id.1 id.2 ∉ protectedNames) ∧
  (∀ id ∈ generated, ∀ spelling ∈ protectedNames, names.parse spelling ≠ some id)

/-- Identity renaming preserves every caller binding. -/
def FreshRenaming.refl (live : List Var) : FreshRenaming live where
  forward := id
  backward := id
  leftInverse _ := rfl
  rightInverse _ := rfl
  user _ := rfl
  caller _ _ := rfl

/-- Reverse a fresh renaming, still fixing user and caller identities. -/
def FreshRenaming.symm {live : List Var} (r : FreshRenaming live) : FreshRenaming live where
  forward := r.backward
  backward := r.forward
  leftInverse := r.rightInverse
  rightInverse := r.leftInverse
  user x := (congrArg r.backward (r.user x)).symm.trans (r.leftInverse (.user x))
  caller x h := (congrArg r.backward (r.caller x h)).symm.trans (r.leftInverse x)

/-- Compose name bijections without changing the caller boundary. -/
def FreshRenaming.trans {live : List Var} (r s : FreshRenaming live) : FreshRenaming live where
  forward := s.forward ∘ r.forward
  backward := r.backward ∘ s.backward
  leftInverse x := (congrArg r.backward (s.leftInverse (r.forward x))).trans (r.leftInverse x)
  rightInverse x := (congrArg s.forward (r.rightInverse (s.backward x))).trans (s.rightInverse x)
  user x := (congrArg s.forward (r.user x)).trans (s.user x)
  caller x h := (congrArg s.forward (r.caller x h)).trans (s.caller x h)

/-- Fresh-name equivalence is reflexive. -/
theorem FreshNameEquiv.refl (live names : List Var) : FreshNameEquiv live names names :=
  ⟨FreshRenaming.refl live, List.map_id names⟩

/-- Fresh-name equivalence is symmetric. -/
theorem FreshNameEquiv.symm {live left right : List Var}
    (h : FreshNameEquiv live left right) : FreshNameEquiv live right left :=
  h.elim fun r eq => ⟨r.symm,
    (congrArg (List.map r.backward) eq).symm.trans
      ((List.map_map).trans (List.map_id'' r.leftInverse left))⟩

/-- Fresh-name equivalence is transitive. -/
theorem FreshNameEquiv.trans {live left middle right : List Var}
    (h : FreshNameEquiv live left middle) (k : FreshNameEquiv live middle right) :
    FreshNameEquiv live left right :=
  h.elim fun r eq => k.elim fun s eq' => ⟨r.trans s,
    (List.map_map (f := r.forward) (g := s.forward) (l := left)).symm.trans
      ((congrArg (List.map s.forward) eq).trans eq')⟩

end Solidity.Correctness.Lowering.Total
