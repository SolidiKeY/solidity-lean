import Solidity.Calculus.DecisionGivenHeapFixedBoundary
import Solidity.Examples.DecisionGapData

/-! # Fixed-array given-heap certificates and intrinsic controls
The zero-length control concerns intrinsic leaves, not Solidity-source acceptance.
All reads use the actual fixed object; no dynamic candidate is reinterpreted.
-/
namespace Solidity.Examples.DecisionGivenHeapFixed
open Solidity.Decide Solidity.Decide.ResidueReason Solidity.Examples.Decision

def lit {Γ : Ctx} (k : Nat) : Tm Gaps Γ (.val .uint) := .app0 (.lit (uintOfNat k))
def source (n : Nat) (key : Tm Gaps [.mem (.fixed (.prim .uint) n)] (.val .uint)) : Fml Gaps [] :=
  .bind .box (.user "s") (.mem (.fixed (.prim .uint) n))
    (.eq (fixedHeapUIntRead n key) (fixedHeapUIntRead n key))
abbrev A : RefTy := .fixed (.prim .uint) 3

def literalSource : Fml Gaps [] := source 3 (lit 1)
def computedSource : Fml Gaps [] := source 3 (.app2 (.binop .add rfl) (lit 0) (lit 1))
def partialSource : Fml Gaps [] := source 3 (.app2 (.binop .sub rfl) (lit 0) (lit 1))
def boundsSource : Fml Gaps [] := source 3 (lit 3)
def zeroSource : Fml Gaps [] := source 0 (lit 0)

def literalWitness : GivenHeapFixedReadReflexive literalSource :=
  (givenHeapFixedRead? literalSource).get (by decide +kernel)
def computedWitness : GivenHeapFixedReadReflexive computedSource :=
  (givenHeapFixedRead? computedSource).get (by decide +kernel)
def partialWitness : GivenHeapFixedReadReflexive partialSource :=
  (givenHeapFixedRead? partialSource).get (by decide +kernel)
def boundsWitness : GivenHeapFixedReadReflexive boundsSource :=
  (givenHeapFixedRead? boundsSource).get (by decide +kernel)
def zeroWitness : GivenHeapFixedReadReflexive zeroSource :=
  (givenHeapFixedRead? zeroSource).get (by decide +kernel)

theorem length_preserved : literalWitness.length = 3 := by rfl

theorem actual_targets (waivers : Waivers) : literalSource.inTarget waivers = true ∧
    computedSource.inTarget waivers = true ∧ partialSource.inTarget waivers = true ∧
    boundsSource.inTarget waivers = true ∧ zeroSource.inTarget waivers = true :=
  ⟨literalWitness.target waivers, computedWitness.target waivers, partialWitness.target waivers,
    boundsWitness.target waivers, zeroWitness.target waivers⟩

theorem actual_coverage : literalSource.Covered = true ∧ computedSource.Covered = true ∧
    partialSource.Covered = true ∧ boundsSource.Covered = true ∧ zeroSource.Covered = true :=
  ⟨literalWitness.covered, computedWitness.covered, partialWitness.covered,
    boundsWitness.covered, zeroWitness.covered⟩

theorem actual_verdicts : decideGoal literalSource = .proved ∧ decideGoal computedSource = .proved ∧
    decideGoal partialSource = .proved ∧ decideGoal boundsSource = .proved ∧
    decideGoal zeroSource = .proved :=
  ⟨literalWitness.proved, computedWitness.proved, partialWitness.proved,
    boundsWitness.proved, zeroWitness.proved⟩

def words : MObj [] A := ⟨[uintOfNat 1, uintOfNat 2, uintOfNat 3], rfl⟩
def allocated : (σ : State Gaps []) × HRef σ.H A := (State.init Gaps).alloc words
def heapState : State Gaps [] := allocated.1
def present : State Gaps [.mem A] := heapState.push (some allocated.2)
def unset : State Gaps [.mem A] := (State.init Gaps).push (t := .mem A) none

theorem inhabited_states : holds (State.init Gaps) literalSource ∧
    holds heapState literalSource := ⟨literalWitness.valid _, literalWitness.valid _⟩

theorem read_observations :
    (fixedHeapUIntRead 3 (lit 0)).eval present = some (uintOfNat 1) ∧
    (fixedHeapUIntRead 3 (lit 1)).eval present = some (uintOfNat 2) ∧
    (fixedHeapUIntRead 3 (lit 3)).eval present = none ∧
    (fixedHeapUIntRead 3 (.app2 (.binop .sub rfl) (lit 0) (lit 1))).eval present = none ∧
    (fixedHeapUIntRead 3 (lit 0)).eval unset = none := by
  decide +kernel

def differentReads : Fml Gaps [] := .bind .box (.user "s") (.mem A)
  (.eq (fixedHeapUIntRead 3 (lit 0)) (fixedHeapUIntRead 3 (lit 1)))

theorem unequal_read_countermodel : ¬ holds heapState differentReads := by
  intro h
  have he : uintOfNat 1 = uintOfNat 2 :=
    (holds_eq_of_eval read_observations.1 read_observations.2.1).mp (h (some allocated.2))
  exact (by decide +kernel : uintOfNat 1 ≠ uintOfNat 2) he

def programBody : Fml Gaps [.mem A] :=
  .eq (.app2 (.binop .eqB rfl) (fixedHeapUIntRead 3 (lit 0))
    (fixedHeapUIntRead 3 (lit 0))) (.app0 (.lit true))
def programEquality : Fml Gaps [] := .bind .box (.user "s") (.mem A) programBody

theorem program_equality_countermodel : ¬ holds (State.init Gaps) programEquality := by
  intro h
  have hc : holds unset programBody := h none
  change (none : Option Bool) = some true at hc
  cases hc

def actualDiamond : Fml Gaps [] := .bind .diamond (.user "s") (.mem A)
  (.eq (fixedHeapUIntRead 3 (lit 0)) (fixedHeapUIntRead 3 (lit 0)))
def actualFresh : Fml Gaps [] := .allocAll (.user "s") A
  (.eq (fixedHeapUIntRead 3 (lit 0)) (fixedHeapUIntRead 3 (lit 0)))
def dynamicSource : Fml Gaps [] := .bind .box (.user "s") (.mem (.array (.prim .uint)))
  (.eq (computedHeapUIntRead (lit 0)) (computedHeapUIntRead (lit 0)))
def nonRead : Fml Gaps [] := .bind .box (.user "s") (.mem A) (.eq (lit 0) (lit 0))

theorem exact_refusals : ([differentReads, programEquality, actualDiamond,
    actualFresh, dynamicSource, nonRead].map Fml.givenHeapFixedReadReflexive).any id = false := by
  decide +kernel

def localKey : Tm Gaps [.mem A, .val .uint] (.val .uint) := .pvV (.there .here)
def contextualSource : Fml Gaps [.val .uint] := .bind .box (.user "s") (.mem A)
  (.eq (fixedHeapUIntRead 3 localKey) (fixedHeapUIntRead 3 localKey))
def nonlinearSource : Fml Gaps [.val .uint] := .bind .box (.user "s") (.mem A)
  (.eq (fixedHeapUIntRead 3 (.app2 (.binop .mul rfl) localKey localKey))
    (fixedHeapUIntRead 3 (.app2 (.binop .mul rfl) localKey localKey)))

theorem contextual_classified : contextualSource.givenHeapFixedReadReflexive = true := by
  decide +kernel

theorem nonlinear_refused : nonlinearSource.givenHeapFixedReadReflexive = false := by
  decide +kernel

theorem nonlinear_still_valid : ∀ σ : State Gaps [.val .uint], holds σ nonlinearSource := by
  intro σ v
  rfl

def outerRead : Tm Gaps [.mem A, .mem A] (.val .uint) :=
  .app2 .read (.app0 .memory) (.app2 (.mat .fixed) (.pvI (.there .here)) (lit 0))
def outerSource : Fml Gaps [.mem A] := .bind .box (.user "s") (.mem A) (.eq outerRead outerRead)

theorem other_pointer_refused : outerSource.givenHeapFixedReadReflexive = false := by
  decide +kernel

def otherLengthRead : Tm Gaps [.mem A, .mem (.fixed (.prim .uint) 4)] (.val .uint) :=
  .app2 .read (.app0 .memory) (.app2 (.mat .fixed) (.pvI (.there .here)) (lit 0))
def otherLengthSource : Fml Gaps [.mem (.fixed (.prim .uint) 4)] :=
  .bind .box (.user "s") (.mem A) (.eq otherLengthRead otherLengthRead)

theorem other_length_pointer_refused : otherLengthSource.givenHeapFixedReadReflexive = false := by
  decide +kernel

end Solidity.Examples.DecisionGivenHeapFixed
