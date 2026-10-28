import Solidity.Calculus.MemInst
import Solidity.Examples.DecisionMemory

/-!
# Scoped memory-block instantiation controls

These are Lean intrinsic/kernel controls, not source/compiler/EVM tests.
The original closer gap remains unknown. Successful recognition and an
instantiation certificate alone are not a whole-leaf reduction certificate.
-/

namespace Solidity.Examples.MemoryInstantiation

open Solidity.Decide Solidity.Examples.Decision

abbrev MΓ : Ctx := [.mem UA]

def body : Fml Gaps (.val .uint :: MΓ) := mxRangeBody .here (uintOfNat 0)
def points : List (MxPoint Gaps MΓ) := mxBlockPoints .here
  [MxPoint.ix .read (litU 0) rfl] [MxPoint.ix .guard (litU 3) rfl]

def prepared : MxInstPrep Gaps MΓ (.user "i") body :=
  ⟨points, mxRangeInstances .here (uintOfNat 0) points,
    mxRangeInstances_checked (.user "i") .here (uintOfNat 0) points⟩

#guard (mxRangeBody? body).isSome
#guard points.length == 5
#guard prepared.instances.length == 5

/-- Both sides of the removed value binder are retained at their own
positions: the outer value becomes here, not the substituted literal. -/
theorem capture_preserved :
    Fml.instTm (C := Gaps) (.user "i") .uint
      (.eq (.pvV .here) (.pvV (.there .here)) : Fml Gaps [.val .uint, .val .uint])
      (litU 7) = some (.eq (litU 7) (.pvV .here)) := rfl

/-- The unsupported nested value binder is explicitly refused. -/
def nested : Fml Gaps (.val .uint :: MΓ) :=
  .all (.user "j") .uint
    (.eq (.pvV .here) (.pvV (.there .here)))

#guard !(mxRangeBody? nested).isSome

theorem nested_refused :
    Fml.instTm (.user "i") .uint nested (litU 0) = none := rfl

/-- No empty request can bypass the public factory's binder refusal. -/
theorem empty_request_refused : mxInstPrep? (.user "i") nested [] = none := rfl

/-- Recognition and its typed proof also work for primitive bool arrays. -/
def boolBody : Fml Gaps [.val .uint, .mem (.array (.prim .bool))] :=
  mxRangeBody .here true

#guard (mxRangeBody? boolBody).isSome

theorem supported_recognized : (mxRangeBody? body).isSome = true := by decide +kernel

theorem nested_unrecognized : (mxRangeBody? nested).isSome = false := by decide +kernel

/-- A guard on one local does not license a read through another local. -/
def wrongArray : Fml Gaps [.val .uint, .mem UA, .mem UA] :=
  .imp (isT (gtB (mlenG (.there .here)) (.pvV .here)))
    (.eq (mrdG .dyn (.there (.there .here)) (.pvV .here)) (litU 0))

#guard !(mxRangeBody? wrongArray).isSome

/-- A supported second-array body still recognizes its own identity. -/
def secondArray : Fml Gaps [.val .uint, .mem UA, .mem UA] :=
  mxRangeBody (.there .here) (uintOfNat 0)

#guard (mxRangeBody? secondArray).isSome

/-- A halting point remains present in the output as a guarded instance. -/
def failedPoint : MxPoint Gaps MΓ := MxPoint.ix .read (mxHalt .uint) rfl

def failedPrepared : MxInstPrep Gaps MΓ (.user "i") body :=
  ⟨[failedPoint], mxRangeInstances .here (uintOfNat 0) [failedPoint],
    mxRangeInstances_checked (.user "i") .here (uintOfNat 0) [failedPoint]⟩

theorem failed_point_vacuous (σ : State Gaps MΓ) : holds σ failedPrepared.body := by
  apply (failedPrepared.holds_iff σ).2
  intro pt hpt u hu
  have he : pt = failedPoint := List.mem_singleton.1 hpt
  subst pt
  have hn : failedPoint.tm.eval σ = none := mxHalt_eval σ .uint
  rw [hn] at hu
  cases hu

/-- A failed successor at uint's maximum cannot wrap to a zero instance. -/
def topSuccessor : MxPoint Gaps [] :=
  (MxPoint.ix .guard (litU (2 ^ 256 - 1)) rfl).succ

#guard !(topSuccessor.tm.eval (State.init Gaps)).isSome

theorem top_successor_halts : topSuccessor.tm.eval (State.init Gaps) = none := by
  decide +kernel

/-- Empty allocation makes the original block and all its checked
instances vacuous, while its exterior zero read still halts. -/
def empty {H : HTy} : MObj H UA := ⟨[], by change 0 < 2 ^ 256; decide⟩

theorem empty_block (σ : State Gaps []) :
    holds (σ.allocPush empty) (.all (.user "i") .uint body) := by
  unfold body
  rw [mxRangeBlock_holds]
  intro k hk
  have hn : k < 0 := by simpa only [MObj.elems_dyn, empty, List.length_nil] using hk
  omega

theorem empty_prepared (σ : State Gaps []) : holds (σ.allocPush empty) prepared.body :=
  prepared.sound (σ.allocPush empty) (empty_block σ)

theorem empty_exterior_halts (σ : State Gaps []) :
    (mrdG .dyn .here (litU 0)).eval (σ.allocPush empty) = none := by
  simpa only [Tm.wk_app0, MObj.elems_dyn, empty, List.getElem?_nil,
    Option.bind_eq_bind, Option.bind_some] using
    (mxReadNew_eval σ (empty : MObj σ.H UA) .dyn (litU 0) rfl rfl)

/-- Reconstructed allocation preserves both repeated and distinct local
identity comparisons. No arbitrary given heap is rebuilt. -/
theorem alias_preserved (σ : State Gaps [.mem UA]) (o : MObj σ.H UA) (B : List Int) :
    ((σ.allocPush (mxFloorRebuild .dyn (by trivial) o B)).getV (.here : Idx [.mem UA, .mem UA] (.mem UA)) =
      (σ.allocPush (mxFloorRebuild .dyn (by trivial) o B)).getV (.there .here)) ↔
    ((σ.allocPush o).getV (.here : Idx [.mem UA, .mem UA] (.mem UA)) =
      (σ.allocPush o).getV (.there .here)) :=
  mxFloorRebuild_alloc_alias σ o B .here (.there .here)

/-- Retained failed attempt: using raw memory-length points directly as
indices does not yet give the unchanged memory cut a supported leaf. -/
def rawPreparedLeaf : Fml Gaps [] :=
  .allocAll (.user "s") UA
    (.imp prepared.body (.eq (mrdG .dyn .here (litU 0)) (litU 0)))

#guard !(rawPreparedLeaf.mxTop).isSome
/-- The original bound index cannot be pulled before its array binder. -/
theorem bound_index_not_ground : body.mxIdx (.drop (.drop .refl)) 1 = [] := rfl

/-- The same correct array position does collect a ground read. Thus the
negative control above actually tests the binder-dependent index. -/
theorem ground_index_collected :
    (mxRangeInstance (C := Gaps) (Γ := [.val .uint, .mem UA]) (.there .here)
      (uintOfNat 0) (litU 0)).mxIdx (.drop (.drop .refl)) 1 = [litU 0] := rfl

#print axioms capture_preserved
#print axioms nested_refused
#print axioms empty_request_refused
#print axioms supported_recognized
#print axioms nested_unrecognized
#print axioms failed_point_vacuous
#print axioms top_successor_halts
#print axioms empty_block
#print axioms empty_prepared
#print axioms empty_exterior_halts
#print axioms alias_preserved

end Solidity.Examples.MemoryInstantiation
