import Solidity.Calculus.TraceReduction
import Solidity.Calculus.DeclarationStaticReduction
import Solidity.Examples.ReadRealization

/-!
# Dependent read occurrences and aliases

Solver values select later mapping locations during replay. A consistent
false trace materializes an original-source countermodel; a conflicting
self-alias is rejected even if its unconstrained replay says false.
-/

namespace Solidity.Examples.ReadTrace

open Solidity.Decide Solidity.ReadRealization Solidity.Semantics
open Solidity.Examples.ReadRealization (Bank balance three four debt paused)
open scoped Solidity.Scoped

local instance : InContract := ⟨Bank⟩

def values (i : Nat) : (p : PrimTy) → p.Denote
  | .uint => if i % 2 = 0 then PrimTy.ofLit .uint 4 rfl else PrimTy.ofLit .uint 19 rfl
  | .int => PrimTy.ofLit .int (-2) rfl
  | .bool => true

def claim : Fml Bank [] := dl!{ balances[balances[3]] == 17 }
def reduction : TraceReduction claim := (traceReduction? claim).get (by decide +kernel)
def counterstate : { σ : State Bank [] // ¬ holds σ claim } :=
  (reduction.countermodelFromTrace? (State.init Bank) [] values).get (by decide +kernel)

/-- info: (4, 19) -/
#guard_msgs in
#eval ((three.read counterstate.val.storage).val, (four.read counterstate.val.storage).val)

/-- A trace chosen by occurrence refutes the original nested-read formula. -/
theorem invalid : ¬ Valid claim := fun h => counterstate.property (h counterstate.val)

def finiteValues : List CallValue := List.ofFn fun i : Fin reduction.sentence.readBound =>
  .uint (values i .uint)

def finiteCounterstate : { σ : State Bank [] // ¬ holds σ claim } :=
  (reduction.countermodelFromValues? (State.init Bank) [] finiteValues).get (by decide +kernel)

example : (four.read finiteCounterstate.val.storage).val = 19 := by decide +kernel
example : ReadValues.ofList [.bool true] 0 .uint = PrimTy.dflt .uint := rfl

def Follower : Contract := contract!{
  mapping(uint => uint) balances;
  ensures balances[k] == 17;
  function follow(uint k) { balances[k] = balances[balances[k]]; }
  requires \forall uint i; balances[i] == 0;
  ensures balances[k] == 17;
  function guarded(uint k) { balances[k] = 0; }
}

def followClaim : Fml Follower [] := cspec[Follower]{follow}
def followReduction : TraceReduction followClaim := declaration_trace_reduce[followClaim]
def followCounterstate : { σ : State Follower [] // ¬ holds σ followClaim } :=
  (followReduction.countermodelFromTrace? (State.init Follower)
    [.uint (PrimTy.ofLit .uint 3 rfl)] values).get (by decide +kernel)

/-- Actual program normalization and declaration certificates retain the
original universally quantified function claim in the refutation. -/
theorem follow_invalid : ¬ Valid followClaim :=
  fun h => followCounterstate.property (h followCounterstate.val)

example : followCounterstate.val.storage.find
    ((SRef.ofRoot (C := Follower) "balances" rfl).index .map (PrimTy.ofLit .uint 3 rfl)) =
      some (.prim (PrimTy.ofLit .uint 4 rfl)) := by decide +kernel

example : followCounterstate.val.storage.find
    ((SRef.ofRoot (C := Follower) "balances" rfl).index .map (PrimTy.ofLit .uint 4 rfl)) =
      some (.prim (PrimTy.ofLit .uint 19 rfl)) := by decide +kernel

def guardedDeclaration := declaration_reduce[cspec[Follower]{guarded}]

/-- A quantified user requirement stays present under the hidden parameter
binder; it cannot be treated as a certified declaration range. -/
example : (DeclarationReduction.trace? guardedDeclaration).isNone = true := by decide +kernel

def mixedQuery : Query Bank (Bool × Int × Int × Int) :=
  (Query.get paused).bind fun b => (Query.get debt).bind fun d =>
    (Query.get three).bind fun k => (Query.get (balance k)).bind fun v =>
      .pure (b, d.val, k.val, v.val)

def mixedValues : ReadValues := ReadValues.ofList
  [.bool true, .int (PrimTy.ofLit .int (-2) rfl),
    .uint (PrimTy.ofLit .uint 4 rfl), .uint (PrimTy.ofLit .uint 19 rfl)]

/-- info: (true, -2, 4, 19) -/
#guard_msgs in #eval (Query.replay mixedValues 0 mixedQuery).1

/-- The same mixed values are the query's actual interpreter observations. -/
example : mixedQuery.runStorage (Query.replay mixedValues 0 mixedQuery).2.realize =
    (true, -2, 4, 19) :=
  (mixedQuery.replay_realize mixedValues 0
    ((Assignment.consistentB_iff _).mp (by decide +kernel))).trans (by decide +kernel)

def conditionalPrefix : Query Bank PrimTy.int.Denote :=
  (Query.get paused).bind fun b => if b = true then Query.get debt else .pure (PrimTy.dflt .int)

def conditionalQuery : Query Bank PrimTy.uint.Denote := conditionalPrefix.bind fun _ => Query.get three
def conditionalValues : ReadValues :=
  ReadValues.ofList [.bool false, .uint (PrimTy.ofLit .uint 19 rfl)]

/-- The skipped signed read consumes no occurrence: the continuation uses
position one, rather than the prefix's conservative bound of two. -/
example : (Query.replay conditionalValues 0 conditionalQuery).1.val = 19 := by decide +kernel
example : (Query.replay conditionalValues 0 conditionalQuery).2.length = 2 := by decide +kernel

def aliasQuery : Query Bank Bool :=
  (Query.get three).bind fun k => (Query.get (balance k)).bind fun v =>
    .pure (decide (k.val = 3 → v.val = 3))

def conflictingValues (i : Nat) : (p : PrimTy) → p.Denote
  | .uint => if i = 0 then PrimTy.ofLit .uint 3 rfl else PrimTy.ofLit .uint 19 rfl
  | .int => PrimTy.dflt .int
  | .bool => false

example : (Query.replay conflictingValues 0 aliasQuery).1 = false := by decide +kernel
example : (Query.replay conflictingValues 0 aliasQuery).2.consistentB = false := by decide +kernel
example : (aliasQuery.countermodelFromTrace? conflictingValues).isNone = true := by decide +kernel

def selfAliasValues : ReadValues := ReadValues.ofList
  [.uint (PrimTy.ofLit .uint 3 rfl), .uint (PrimTy.ofLit .uint 3 rfl)]

/-- The source query selects `balances[3]` twice. Equal occurrence values
are realizable; conflicting values must be rejected before transport. -/
def selfAliasCounterstate : { σ : State Bank [] // ¬ holds σ claim } :=
  (reduction.countermodelFromTrace? (State.init Bank) [] selfAliasValues).get (by decide +kernel)

example : (three.read selfAliasCounterstate.val.storage).val = 3 := by decide +kernel
example : (reduction.countermodelFromTrace? (State.init Bank) [] conflictingValues).isNone = true := by decide +kernel

/-- Every actual state has a consistent occurrence witness for this query. -/
example (st : Storage Bank) : ∃ a : Assignment Bank,
    (Query.replay a.values 0 aliasQuery).1 = aliasQuery.runStorage st ∧
      (Query.replay a.values 0 aliasQuery).2.Consistent :=
  aliasQuery.replay_storage_exists st

example (st : Storage Bank) : ∃ a : Assignment Bank,
    a.length ≤ reduction.sentence.readBound ∧
    (Query.replay a.values 0 (reduction.sentence.query (State.init Bank) AEnv.dflt [])).1 =
      (reduction.sentence.query (State.init Bank) AEnv.dflt []).runStorage st ∧
    (Query.replay a.values 0 (reduction.sentence.query (State.init Bank) AEnv.dflt [])).2.Consistent :=
  Query.replay_storage_exists_bounded _ st (reduction.sentence.query_within _ _ _)

/-- info: 'Solidity.ReadRealization.Query.replay_realizable_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Query.replay_realizable_iff

/-- info: 'Solidity.Decide.TraceReduction.valid_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms TraceReduction.valid_iff

end Solidity.Examples.ReadTrace
