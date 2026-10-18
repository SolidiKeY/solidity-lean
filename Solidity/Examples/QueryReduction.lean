import Solidity.Calculus.QueryReduction
import Solidity.Examples.ReadRealization

/-!
# Read-dependent mapping keys

Reconstruction must preserve the inner read before selecting the outer
mapping location. These examples go through the original formula's exact
reduction and return a counterstate to that formula.
-/

namespace Solidity.Examples.QueryReduction

open Solidity.Decide Solidity.ReadRealization
open Solidity.Semantics
open Solidity.Examples.ReadRealization (Bank balance three four)
open scoped Solidity.Scoped

local instance : InContract := ⟨Bank⟩

def claim : Fml Bank [] := dl!{ balances[balances[3]] == 7 }
def reduction : ExactReduction claim := (exactReduction? claim).get (by decide +kernel)
def recognized : ReadFormula reduction.leaf.elim :=
  (ReadFormula.ofFormula? reduction.leaf.elim).get (by decide +kernel)

def requests : Assignment Bank :=
  [⟨three, PrimTy.ofLit .uint 4 rfl⟩, ⟨four, PrimTy.ofLit .uint 9 rfl⟩]

def valuation (r : Ref Bank) : r.Value := Assignment.lookup requests r

example : (recognized.query (State.init Bank) AEnv.dflt).run valuation = false := by
  decide +kernel

def counterstate : { σ : State Bank [] // ¬ σ ⊧ claim } :=
  reduction.countermodelFromReads recognized (State.init Bank) valuation (by decide +kernel)

example : counterstate.val.storage.find three.ref = some (.prim (PrimTy.ofLit .uint 4 rfl)) := by
  decide +kernel

example : counterstate.val.storage.find four.ref = some (.prim (PrimTy.ofLit .uint 9 rfl)) := by
  decide +kernel

def parameterClaim : Fml Bank [] :=
  dl!{ ∀ uint a; ∀ int d; ∀ bool b;
    b == true ∧ d + 2 == 0 → balances[balances[a]] == 7 }

def parameterReduction : ReadReduction parameterClaim :=
  (readReduction? parameterClaim).get (by decide +kernel)

def args : List CallValue :=
  [.uint (PrimTy.ofLit .uint 3 rfl), .int (PrimTy.ofLit .int (-2) rfl), .bool true]

/-- The body is false at this typed instance, so the entire universally
quantified original formula has a concrete storage counterstate. -/
def parameterCounterstate : { σ : State Bank [] // ¬ σ ⊧ parameterClaim } :=
  (parameterReduction.countermodel? (State.init Bank) args requests).get (by decide +kernel)

/-- A proposal with conflicting aliased occurrences is rejected before
query evaluation, rather than silently keeping its first occurrence. -/
example : (parameterReduction.countermodel? (State.init Bank) args
    [⟨three, PrimTy.ofLit .uint 4 rfl⟩, ⟨three, PrimTy.ofLit .uint 9 rfl⟩]).isNone = true := by
  decide +kernel

/-- Supplying a boolean at the unsigned position selects the unsigned
default. It cannot bypass the original typed quantifier. -/
example : ReadSentence.argument .uint [.bool true] = PrimTy.dflt .uint := by decide +kernel

example : parameterCounterstate.val.storage.find four.ref = some (.prim (PrimTy.ofLit .uint 9 rfl)) := by
  decide +kernel

/-- Equal failed computations are not defined equality. -/
example : ReadFormula.equal (p := .uint) none none = false := rfl

def shortCircuit : Fml Bank [] := dl!{ false ∧ balances[balances[3]] == 9 → false }
def shortCircuitReduction : ReadReduction shortCircuit :=
  (readReduction? shortCircuit).get (by decide +kernel)

example : (shortCircuitReduction.countermodel? (State.init Bank) [] requests).isNone = true := by
  decide +kernel

/-- Array lengths, memory and quantified hypotheses remain outside this
initial read-query fragment. Recognizer failure makes no negative claim. -/
example : (readReduction? (dl!{ (∀ uint k; balances[k] == 0) → balances[3] == 0 })).isNone = true := by
  decide +kernel

example : (ReadExpr.ofTerm? (LTm.obsL (C := Bank) (E := .prim .uint) (.err))).isNone = true := by
  decide +kernel

example : (ReadExpr.ofTerm? (LTm.app0 (C := Bank) .memory)).isNone = true := by
  decide +kernel

example : (ReadExpr.ofTerm? (LTm.app1 (C := Bank) .net (.app0 (.lit (PrimTy.dflt .uint))))).isNone = true := by
  decide +kernel

section Nested

def Nested : Contract := contract!{ mapping(int => mapping(bool => Person)) people; }
local instance : InContract := ⟨Nested⟩

def nestedClaim : Fml Nested [] := dl!{ ∀ int k; ∀ bool b; people[k][b].age == 7 }
def nestedReduction : ReadReduction nestedClaim :=
  (readReduction? nestedClaim).get (by decide +kernel)

def nestedValuation (r : Ref Nested) : r.Value :=
  PrimTy.casesOn (motive := fun p => p.Denote) r.prim true
    (PrimTy.ofLit .uint 9 rfl) (PrimTy.ofLit .int (-2) rfl)

def nestedCounterstate : { σ : State Nested [] // ¬ σ ⊧ nestedClaim } :=
  nestedReduction.reduction.countermodelFromInstance nestedReduction.sentence (State.init Nested)
    [.int (PrimTy.ofLit .int (-2) rfl), .bool true] nestedValuation (by decide +kernel)

/-- A struct field under signed and boolean mapping keys really contains
the assigned value in the reconstructed interpreter storage. -/
example : nestedCounterstate.val.storage.find
    ((((SRef.ofRoot "people" (C := Nested) rfl).index .map (PrimTy.ofLit .int (-2) rfl)).index .map true).field
      (f := "age") rfl) = some (.prim (PrimTy.ofLit .uint 9 rfl)) := by
  decide +kernel

end Nested

/-- info: 'Solidity.Decide.ExactReduction.countermodelFromReads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExactReduction.countermodelFromReads

/-- info: 'Solidity.Decide.ReadReduction.valid_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ReadReduction.valid_iff

end Solidity.Examples.QueryReduction
