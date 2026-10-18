import Solidity.Calculus.DeclarationStaticReduction
import Solidity.Examples.ReadRealization

/-!
# Guaranteed counterstates from original storage formulas

Recognition, exact reduction, scalar domains, complete arithmetic decision
and actual storage reconstruction compose here without supplied candidate
values. Unsupported source forms receive no verdict.
-/

namespace Solidity.Examples.StaticLinear

open Solidity.Decide Solidity.ReadRealization
open Solidity.Examples.ReadRealization (Bank three four debt paused)
open scoped Solidity.Scoped

local instance : InContract := ⟨Bank⟩

def claim : Fml Bank [] := dl!{ ¬(balances[3] == 17) }
def reduction : StaticReduction claim := (staticReduction? claim).get (by decide +kernel)

/-- info: some 17 -/
#guard_msgs in
#eval match reduction.verify with
  | .inl _ => none
  | .inr cm => some (three.read cm.val.storage).val

def aliasClaim : Fml Bank [] := dl!{ balances[3] == balances[3] }
def aliasReduction : StaticReduction aliasClaim := (staticReduction? aliasClaim).get (by decide +kernel)

/-- Repeated actual locations get one variable, so no false alias model can
be constructed by assigning two occurrences different values. -/
example : aliasReduction.refs.length = 1 := by decide +kernel

/-- info: true -/
#guard_msgs in #eval aliasReduction.verify.isLeft

def mixedClaim : Fml Bank [] := dl!{ ¬(paused == true ∧ debt == (0 - 2) ∧ balances[3] == 17) }
def mixedReduction : StaticReduction mixedClaim := (staticReduction? mixedClaim).get (by decide +kernel)

/-- info: some (true, -2, 17) -/
#guard_msgs in
#eval match mixedReduction.verify with
  | .inl _ => none
  | .inr cm => some (paused.read cm.val.storage, (debt.read cm.val.storage).val,
      (three.read cm.val.storage).val)

def independentClaim : Fml Bank [] := dl!{ balances[3] == 17 → balances[4] == 17 }
def independentReduction : StaticReduction independentClaim :=
  (staticReduction? independentClaim).get (by decide +kernel)

/-- info: some (17, true) -/
#guard_msgs in
#eval match independentReduction.verify with
  | .inl _ => none
  | .inr cm => some ((three.read cm.val.storage).val, decide ((four.read cm.val.storage).val ≠ 17))

def boolClaim : Fml Bank [] := dl!{ paused == false }
def boolReduction : StaticReduction boolClaim := (staticReduction? boolClaim).get (by decide +kernel)

def boolCounterstate : { σ : State Bank [] // ¬ σ ⊧ boolClaim } :=
  boolReduction.countermodel (by decide +kernel)

/-- Generated quantified mapping ranges remain in the certified conclusion. -/
def withDeclarations : Fml Bank [] := .imp (declaration_facts[Bank]) boolClaim
def declaredReduction : StaticReduction withDeclarations :=
  declaration_static_reduce[withDeclarations]
def declaredCounterstate : { σ : State Bank [] // ¬ σ ⊧ withDeclarations } :=
  declaredReduction.countermodel (by decide +kernel)

example : paused.read declaredCounterstate.val.storage = true := by decide +kernel

/-- User requirements remain premises of the exact decision. -/
def userRequirement : Fml Bank [] := dl!{ paused == false → paused == false }
def requiredReduction : StaticReduction userRequirement :=
  declaration_static_reduce[userRequirement]
example : Valid userRequirement := requiredReduction.valid_of_decide (by decide +kernel)

example : True := by
  fail_if_success
    have _ : StaticReduction (dl!{ (∀ uint k; balances[k] == 1) → balances[3] == 0 }) :=
      declaration_static_reduce[dl!{ (∀ uint k; balances[k] == 1) → balances[3] == 0 }]
  trivial

example : paused.read boolCounterstate.val.storage = true := by decide +kernel

example : (staticReduction? (dl!{ balances[balances[3]] == 7 })).isNone = true := by decide +kernel
/-- Checked failure in a closed unsigned expression is not a default literal. -/
example : (staticReduction? (dl!{ 0 - 1 == 0 })).isNone = true := by decide +kernel
example : (staticReduction? (dl!{ balances[3] + 1 == 7 })).isNone = true := by decide +kernel
example : (staticReduction? (dl!{ ∀ uint k; balances[k] == 0 })).isNone = true := by decide +kernel
example : (staticReduction? (dl!{ [balances[3] = 7;] balances[3] == 7 })).isNone = true := by decide +kernel

section Nested

def Nested : Contract := contract!{ mapping(int => mapping(bool => Person)) people; }
local instance : InContract := ⟨Nested⟩

def nestedClaim : Fml Nested [] := dl!{ ¬(people[2][true].age == 17) }
def nestedReduction : StaticReduction nestedClaim := (staticReduction? nestedClaim).get (by decide +kernel)

def age : Ref Nested :=
  ⟨.uint, (((SRef.ofRoot "people" (C := Nested) rfl).index .map (PrimTy.ofLit .int 2 rfl)).index .map true).field
    (f := "age") rfl, by
      simp only [SRef.Declared, SRef.field, SRef.index, SRef.append, SRef.ofRoot,
        Path.index_map, Path.append_nil, Path.append_key]
      exact .key _ (.key _ (.field (s := "Person") (f := "age") rfl .nil))⟩

/-- info: some 17 -/
#guard_msgs in
#eval match nestedReduction.verify with
  | .inl _ => none
  | .inr cm => some (age.read cm.val.storage).val

end Nested

/-- info: 'Solidity.Decide.StaticReduction.verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms StaticReduction.verify

end Solidity.Examples.StaticLinear
