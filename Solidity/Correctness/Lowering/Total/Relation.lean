import Solidity.Correctness.Lowering.Loops.Statement

/-! H503 relational interface for `Solidity.Goals.lowerLoopsCorrect`.
User/caller names are fixed. Raw spelling safety is separate from intrinsic
name equivalence because `FreshNames` carries no printer/parser laws. -/
namespace Solidity.Correctness.Lowering.Total

/-- An intrinsic bijection fixing caller and user identities. -/
structure FreshRenaming (live : List Var) where
  forward : Var → Var
  backward : Var → Var
  leftInverse : ∀ x, backward (forward x) = x
  rightInverse : ∀ x, forward (backward x) = x
  user : ∀ x, forward (.user x) = .user x
  caller : ∀ x, x ∈ live → forward x = x

/-- One bijection for all occurrences: preserve aliasing and caller identities.
This name interface is not a raw-syntax/program transport theorem. -/
def FreshNameEquiv (live left right : List Var) : Prop :=
  ∃ permutation : FreshRenaming live, left.map permutation.forward = right

/-- Required round trips and absence of spelling/parsed-identity capture. -/
def SafeSpellings (names : FreshNames) (protectedNames : List String)
    (generated : List (String × Nat)) : Prop :=
  (∀ id ∈ generated, names.parse (names.name id.1 id.2) = some id) ∧
  (∀ id ∈ generated, names.name id.1 id.2 ∉ protectedNames) ∧
  (∀ id ∈ generated, ∀ spelling ∈ protectedNames, names.parse spelling ≠ some id)

def FreshRenaming.refl (live : List Var) : FreshRenaming live where
  forward := id
  backward := id
  leftInverse _ := rfl
  rightInverse _ := rfl
  user _ := rfl
  caller _ _ := rfl

def FreshRenaming.symm {live : List Var} (r : FreshRenaming live) : FreshRenaming live where
  forward := r.backward
  backward := r.forward
  leftInverse := r.rightInverse
  rightInverse := r.leftInverse
  user x := (congrArg r.backward (r.user x)).symm.trans (r.leftInverse (.user x))
  caller x h := (congrArg r.backward (r.caller x h)).symm.trans (r.leftInverse x)

def FreshRenaming.trans {live : List Var} (r s : FreshRenaming live) : FreshRenaming live where
  forward := s.forward ∘ r.forward
  backward := r.backward ∘ s.backward
  leftInverse x := (congrArg r.backward (s.leftInverse (r.forward x))).trans (r.leftInverse x)
  rightInverse x := (congrArg s.forward (r.rightInverse (s.backward x))).trans (s.rightInverse x)
  user x := (congrArg s.forward (r.user x)).trans (s.user x)
  caller x h := (congrArg s.forward (r.caller x h)).trans (s.caller x h)

theorem FreshNameEquiv.refl (live names : List Var) : FreshNameEquiv live names names :=
  ⟨FreshRenaming.refl live, List.map_id names⟩

theorem FreshNameEquiv.symm {live left right : List Var}
    (h : FreshNameEquiv live left right) : FreshNameEquiv live right left :=
  h.elim fun r eq => ⟨r.symm,
    (congrArg (List.map r.backward) eq).symm.trans
      ((List.map_map).trans (List.map_id'' r.leftInverse left))⟩

theorem FreshNameEquiv.trans {live left middle right : List Var}
    (h : FreshNameEquiv live left middle) (k : FreshNameEquiv live middle right) :
    FreshNameEquiv live left right :=
  h.elim fun r eq => k.elim fun s eq' => ⟨r.trans s,
    (List.map_map (f := r.forward) (g := s.forward) (l := left)).symm.trans
      ((congrArg (List.map s.forward) eq).trans eq')⟩

/-! Finite relational derivations, independent of totalizing production.
Each depth unfolds one layer of the three mutually recursive rules. Depth zero
has no successful derivation. Helpers are exactly the production helpers;
recursive calls to the production kernel are never used here.
These shared step equations are checked against the frozen equations in the
example module, without introducing a Goals import into this interface. -/
section Derivations
variable [FreshNames]

/-- Reuse the production rule representation, without assuming totality. -/
abbrev listStep := Solidity.LowerKernel.listStep

/-- Reuse the production statement rule, including its factored helpers. -/
abbrev stmtStep := Solidity.LowerKernel.stmtStep

/-- Reuse the production loop rule, including its factored finishing step. -/
abbrev loopStep := Solidity.LowerKernel.loopStep

structure Derivation where
  list : Option (List String) → List RawStmt → LowerM (List RawStmt × List Abrupt)
  stmt : Option (List String) → RawStmt → LowerM (RawStmt × List Abrupt)
  loop : Option (List String) → RawStmt → LowerM (RawStmt × List Abrupt)

/-- A depth bound on a derivation, not a bound on accepted source programs.
The zero case only throws; the rules never catch it. -/
def derive : Nat → Derivation
  | 0 => ⟨fun _ _ => throw "no derivation", fun _ _ => throw "no derivation",
      fun _ _ => throw "no derivation"⟩
  | n + 1 => let d := derive n
    ⟨listStep d.list d.stmt, stmtStep d.list d.loop, loopStep d.list d.loop⟩

/-- H503 raw lowering relation: a finite successful rule derivation from the
entire incoming state to the entire outgoing state. The existential depth is
unbounded. No production-success or semantic-equivalence premise is stored.
This is not a graph definition using production `lowerLoops`. -/
def LowersTo (rs : Option (List String)) (input output : List RawStmt)
    (scope : ElabScope) (before after : Checker.Snapshot) : Prop :=
  ∃ depth, (((do pure (← ((derive depth).list rs input).run' {}).1 :
    ElabM (List RawStmt)).run scope).run before.locals).run before.memo =
      .ok ((output, after.locals), after.memo)
end Derivations

end Solidity.Correctness.Lowering.Total
