import Solidity.Calculus.DecisionSourceInstance
import Solidity.Examples.DecisionArrayGaps

/-! # Actual pre-translation array-instance certificates
Global verdicts and original gap pins remain unchanged.
-/
namespace Solidity.Examples.DecisionSourceInstance
open Solidity.Decide Solidity.Examples.DecisionArrayGaps
set_option Elab.async false

local instance sourceInstanceContract : InContract := ⟨Probe⟩

def zeroCells : SVal ((Probe.rootType "cells").getD Ty.uint) :=
  .array
    (.cons (.struct (.cons (.prim (uintOfNat 0)) .nil))
      (.cons (.struct (.cons (.prim (uintOfNat 0)) .nil))
        (.cons (.struct (.cons (.prim (uintOfNat 0)) .nil)) .nil)))
    .nil (by decide)

def inhabitedStructState : State Probe [] :=
  (State.init Probe).withStorage ((Storage.init Probe).set
    (f := "cells") (T := (Probe.rootType "cells").getD Ty.uint) (by rfl) zeroCells)

def structAntecedent : Fml Probe [] := dl[Probe]{ ∀ uint i; i < 3 → cells[i].v = 0 }

theorem struct_antecedent_original : ∃ rhs : Fml Probe [],
    arrayStruct = .imp structAntecedent rhs := ⟨_, rfl⟩

/-- The array-of-struct antecedent really holds at a constructed three-cell root. -/
theorem struct_antecedent_inhabited : holds inhabitedStructState structAntecedent := by
  intro i hi
  change (some (decide (i.1 < 3)) : Option Bool) = some true at hi
  have hi3 : i.1 < 3 := of_decide_eq_true (Option.some.inj hi)
  have hn : 0 ≤ i.1 := PrimTy.uint_nonneg i
  have he : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 := by omega
  rcases he with h0 | h1 | h2
  · have hx : i = uintOfNat 0 := Subtype.ext h0
    subst i
    apply (holds_eq_of_eval (x := uintOfNat 0) (y := uintOfNat 0)
      (by decide +kernel) (by decide +kernel)).mpr
    rfl
  · have hx : i = uintOfNat 1 := Subtype.ext h1
    subst i
    apply (holds_eq_of_eval (x := uintOfNat 0) (y := uintOfNat 0)
      (by decide +kernel) (by decide +kernel)).mpr
    rfl
  · have hx : i = uintOfNat 2 := Subtype.ext h2
    subst i
    apply (holds_eq_of_eval (x := uintOfNat 0) (y := uintOfNat 0)
      (by decide +kernel) (by decide +kernel)).mpr
    rfl

def structWitness : SourceUIntLiteralChain (uintOfNat 3) (uintOfNat 1) arrayStruct :=
  (sourceUIntLiteralChain? arrayStruct (uintOfNat 3) (uintOfNat 1)).get (by decide +kernel)
def nestedWitness : SourceUIntLiteralChain (uintOfNat 3) (uintOfNat 1) arrayArray :=
  (sourceUIntLiteralChain? arrayArray (uintOfNat 3) (uintOfNat 1)).get (by decide +kernel)
def keyWitness : SourceUIntLiteralChain (uintOfNat 3) (uintOfNat 1) belowKey :=
  (sourceUIntLiteralChain? belowKey (uintOfNat 3) (uintOfNat 1)).get (by decide +kernel)
def fixedKeyWitness : SourceUIntLiteralChain (uintOfNat 3) (uintOfNat 1) fixedBelowKey :=
  (sourceUIntLiteralChain? fixedBelowKey (uintOfNat 3) (uintOfNat 1)).get (by decide +kernel)
def fieldWitness : SourceUIntLiteralChain (uintOfNat 3) (uintOfNat 1) belowField :=
  (sourceUIntLiteralChain? belowField (uintOfNat 3) (uintOfNat 1)).get (by decide +kernel)

theorem actual_source_certificates : Fml.ValidH arrayStruct ∧ Fml.ValidH arrayArray ∧
    Fml.ValidH belowKey ∧ Fml.ValidH fixedBelowKey ∧ Fml.ValidH belowField :=
  ⟨structWitness.validH (by decide +kernel), nestedWitness.validH (by decide +kernel),
    keyWitness.validH (by decide +kernel), fixedKeyWitness.validH (by decide +kernel),
    fieldWitness.validH (by decide +kernel)⟩

/-- The new certificates reach a source whose current leaf translation refuses. -/
theorem before_leaf_translation : leafOf? arrayStruct = none ∧ leafOf? arrayArray = none := by
  constructor <;> rfl

theorem mismatched_instance_refused :
    (sourceUIntLiteralChain? fixedBad (uintOfNat 2) (uintOfNat 1)).isSome = false := by
  decide +kernel

theorem outside_guard_refused :
    (sourceUIntLiteralChain? fixedBad (uintOfNat 2) (uintOfNat 2)).isSome = false := by
  decide +kernel

/-- This refusal is supported by the existing actual false fixed-array model. -/
theorem false_source_not_certifiable :
    ¬ Nonempty (SourceUIntLiteralChain (uintOfNat 2) (uintOfNat 1) fixedBad) := by
  intro ⟨w⟩
  exact fixedBad_notValid w.valid

theorem preserved_global_unknowns : decideGoal arrayStruct = .unknown ∧
    decideGoal arrayArray = .unknown ∧ decideGoal belowKey = .unknown ∧
    decideGoal fixedBelowKey = .unknown ∧ decideGoal belowField = .unknown :=
  ⟨arrayStruct_unknown, arrayArray_unknown, belowKey_unknown, fixedBelowKey_unknown,
    belowField_unknown⟩

end Solidity.Examples.DecisionSourceInstance
