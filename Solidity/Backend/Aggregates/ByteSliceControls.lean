import Solidity.Backend.Aggregates.ByteSlices
import Solidity.Backend.Aggregates.ByteParameterControls

/-! Inhabited local-expression clients; not a deployed external-call or EVM
simulation. The unused global functions are explicit fixture parameters. -/
namespace Solidity.Backend.Aggregates.ByteSliceControls
open Solidity ByteParameters ByteSlices ByteParameterControls

def program : Source.Program E where
  body _ := none
  consts _ := none
  inits _ := []
  ctor _ := none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := []

def fixed : Roadmap.Fixed where
  evm := { keccak := fun _ => 0, keccak_lt := fun _ => by decide, precompile := fun _ _ => none, precompileGas := fun _ _ => 0 }
  ledger := fun balance _ address => balance address
  regionLen := 1
  rootSlots := 1

def G : Source.Glob E :=
  ⟨program,.legacy,fixed,fun _ => ⟨0,by decide⟩,fun _ _ => false,
    fun _ => .answer (.success []),⟨0,by decide⟩⟩

def goodBefore := (ByteSlices.locals sourceLocals 68 3 1 3 (by decide) (by decide),sourceState)
def capacity := slice_capacity frame entry 1 3 (by decide)
def imported := lower aliasTarget frame 69 2 capacity

theorem client :
    (Source.evalE G frame 2 ByteSlices.expr).run goodBefore =
      (.ok (.val (.cdRef rfl 69 2)),goodBefore) ∧
    RefRelated (D := E.layout) frame (.cdRef rfl 69 2) imported.heap
      (aliasTarget.alloc (bytesObj aliasTarget.H (ByteParameters.payload frame 69 2) capacity)).2 ∧
    (ByteParameters.payload frame 69 2).length = 2 :=
  import_slice G frame selector data rfl rfl entry 1 3 (by decide) (by decide)
    sourceLocals sourceState aliasTarget 0

theorem eval_good : (Source.evalE G frame 2 ByteSlices.expr).run goodBefore =
    (.ok (.val (.cdRef rfl 69 2)),goodBefore) := client.1

theorem source_aliases :
    goodBefore.1.get (.there (.there (.there .here))) =
      goodBefore.1.get (.there (.there (.there (.there .here)))) := rfl

theorem target_aliases : TEnv.get (.there .here) imported.env =
    TEnv.get (.there (.there .here)) imported.env := rfl

theorem target_contents : MObj.elems ArrTy.dyn (imported.heap.get
    (aliasTarget.alloc (bytesObj aliasTarget.H (ByteParameters.payload frame 69 2) capacity)).2) =
    [8,9].map byteWord := ByteParameters.target_contents aliasTarget frame 69 2 capacity

def reversedBefore := (ByteSlices.locals sourceLocals 68 3 3 1 (by decide) (by decide),sourceState)
theorem reversed_eval : (Source.evalE G frame 2 ByteSlices.expr).run reversedBefore =
    (.error (.revert []),reversedBefore) := by
  unfold reversedBefore
  rw [eval_expr]
  rfl

def pastBefore := (ByteSlices.locals sourceLocals 68 3 0 4 (by decide) (by decide),sourceState)
theorem past_end_eval : (Source.evalE G frame 2 ByteSlices.expr).run pastBefore =
    (.error (.revert []),pastBefore) := by
  unfold pastBefore
  rw [eval_expr]
  rfl

def emptyBefore := (ByteSlices.locals sourceLocals 68 3 3 3 (by decide) (by decide),sourceState)
theorem empty_eval : (Source.evalE G frame 2 ByteSlices.expr).run emptyBefore =
    (.ok (.val (.cdRef rfl 71 0)),emptyBefore) := by
  unfold emptyBefore
  rw [eval_expr]
  rfl

theorem no_source_allocation :
    ((Source.evalE G frame 2 ByteSlices.expr).run goodBefore).2.2.heap.next = 2 := by
  rw [eval_good]
  rfl

theorem wrong_source_allocation :
    ((Source.evalE G frame 2 ByteSlices.expr).run goodBefore).2.2.heap.next ≠ 3 := by
  rw [no_source_allocation]
  decide

theorem wrong_halt : ((Source.evalE G frame 2 ByteSlices.expr).run pastBefore).1 ≠
    .error (.revert [7]) := by
  rw [past_end_eval]
  intro impossible
  cases impossible

theorem omitted_slice_origin : ByteParameters.payload frame 68 2 ≠
    ByteParameters.payload frame 69 2 := by decide

end Solidity.Backend.Aggregates.ByteSliceControls
