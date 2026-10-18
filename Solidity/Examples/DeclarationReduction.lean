import Solidity.Calculus.DeclarationReduction
import Solidity.Examples.QueryReduction

/-!
# Declaration premises are removed exactly

The original formula retains its generated quantified ranges. The
normalization certificate proves that they can be removed before the
exact read-query recognizer, while ordinary requirements stay in place.
-/

namespace Solidity.Examples.DeclarationReduction

open Solidity.Decide Solidity.ReadRealization
open Solidity.Examples.ReadRealization (Bank three four)
open Solidity.Examples.QueryReduction (claim parameterClaim args requests)
open scoped Solidity.Scoped

local instance : InContract := ⟨Bank⟩

def facts : Fml Bank [] := declaration_facts[Bank]
def withDeclarations : Fml Bank [] := .imp facts claim

def reduced : DeclarationReadReduction withDeclarations :=
  declaration_read_reduce[withDeclarations]

def counterstate : { σ : State Bank [] // ¬ σ ⊧ withDeclarations } :=
  (reduced.countermodel? (State.init Bank) [] requests).get (by decide +kernel)

example : counterstate.val.storage.find four.ref = some (.prim (PrimTy.ofLit .uint 9 rfl)) := by
  decide +kernel

def withParameters : Fml Bank [] := .imp facts parameterClaim
def parameterReduced : DeclarationReadReduction withParameters :=
  declaration_read_reduce[withParameters]

example : (parameterReduced.countermodel? (State.init Bank) args requests).isSome = true := by
  decide +kernel

/-- The actual specification shape: a parameter outside the implication,
and a quantified mapping declaration inside its antecedent. -/
def underParameter : Fml Bank [] := dl!{ ∀ uint a;
  (∀ uint k; 0 <= balances[k] ∧ balances[k] <=
    115792089237316195423570985008687907853269984665640564039457584007913129639935)
    ∧ a == 3 → balances[balances[a]] == 7 }
def underParameterReduced : DeclarationReadReduction underParameter :=
  declaration_read_reduce[underParameter]

example : (underParameterReduced.countermodel? (State.init Bank)
    [.uint (PrimTy.ofLit .uint 3 rfl)] requests).isSome = true := by
  decide +kernel

example : (underParameterReduced.countermodel? (State.init Bank)
    [.uint (PrimTy.ofLit .uint 8 rfl)] requests).isNone = true := by
  decide +kernel

def withRequirement : Fml Bank [] :=
  .imp (.and facts (dl!{ balances[3] == 4 })) claim
def requiredReduced : DeclarationReadReduction withRequirement :=
  declaration_read_reduce[withRequirement]

example : (requiredReduced.countermodel? (State.init Bank) [] requests).isSome = true := by
  decide +kernel

def falseRequirement : Fml Bank [] :=
  .imp (.and facts (dl!{ balances[3] == 8 })) claim
def falseRequiredReduced : DeclarationReadReduction falseRequirement :=
  declaration_read_reduce[falseRequirement]

/-- A false user requirement remains an antecedent. It is not silently
replaced by truth alongside the generated declaration facts. -/
example : (falseRequiredReduced.countermodel? (State.init Bank) [] requests).isNone = true := by
  decide +kernel

def falseQuantifiedPremise : Fml Bank [] :=
  dl!{ (∀ uint k; balances[k] == 1) → balances[3] == 0 }

example : True := by
  fail_if_success
    have _ : DeclarationReadReduction falseQuantifiedPremise :=
      declaration_read_reduce[falseQuantifiedPremise]
  trivial

/-- info: 'Solidity.DeclarationReadReduction.valid_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms DeclarationReadReduction.valid_iff

end Solidity.Examples.DeclarationReduction
