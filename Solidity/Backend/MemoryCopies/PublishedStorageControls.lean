import Solidity.Backend.MemoryCopies.PublishedStorage
import Solidity.Backend.MemoryCopies.PrimitiveArray
import Solidity.Backend.StorageOps.ProducerInterfaceControls
import Solidity.Evm.MemoryObjectArrayExamples

/-! Actual memory allocation followed by the published scalar SSTORE endpoint.
This is a mixed-location word-model witness, not five-location adequacy. -/
namespace Solidity.Backend.MemoryCopies.PublishedStorageControls
open Evm Evm.Memory
private structure Input where
  H : HTy
  heap : Heap H
  base : Nat → Fin W
  machine : Machine
  allocator : Objects.AllocatorRepr heap base 8 (wmod 40) machine
private def input : Input := ⟨_,_,_,_,ObjectArrayExamples.initial_allocator⟩
private def values : List PrimTy.uint.Denote := [indexValue (wmod 11),indexValue (wmod 23)]
private def words : List Word := [w[11],w[23]]
private def first : Machine := arrayWordsMachine (wmod 40) 1 words (allocateMachine input.machine (wmod 40) (wmod 2))
private def middle : Machine := first.push w[40]
private def after : Machine :=
  {middle with store := WordStore.write middle.store (.root 0) (StorageOps.TargetOperations.encodeWord StorageOps.ProducerInterfaceControls.word).val}
private theorem representation : PrimitiveWords .uint values words := by
  refine ⟨rfl,?_⟩
  intro index value selected
  cases index with
  | zero => cases selected; exact ⟨w[11],rfl,ReprV.uint_of rfl⟩
  | succ index => cases index with
    | zero => cases selected; exact ⟨w[23],rfl,ReprV.uint_of rfl⟩
    | succ index => cases selected
private def endpoint : StorageOps.ProducerInterface.ReachedEndpoint (N:=8) (L:=1) (R:=1)
    StorageOps.ProducerInterfaceControls.root StorageOps.ProducerInterfaceControls.queries StorageOps.ProducerInterfaceControls.base StorageOps.ProducerInterfaceControls.hash [] StorageOps.ProducerInterfaceControls.locations StorageOps.ProducerInterfaceControls.symbolic StorageOps.ProducerInterfaceControls.numeric StorageOps.ProducerInterfaceControls.code middle after where
  state := published_storage_same_store StorageOps.ProducerInterfaceControls.state_endpoint after rfl
  execution := StorageOps.TargetOperations.run_write (.root 0) StorageOps.ProducerInterfaceControls.word middle
private theorem memory_run : run (primitiveArrayCode words) input.machine = .ok middle 0 :=
  primitive_array_run words input.machine (wmod 40) (by decide) input.allocator.free.cell (by decide)

theorem published_master_inhabited : PublishedStorageConsumer StorageOps.ProducerInterfaceControls.reached_endpoint := publishedStorageConsumer StorageOps.ProducerInterfaceControls.reached_endpoint

theorem mixed_endpoint_inhabited : PublishedStorageConsumer endpoint := publishedStorageConsumer endpoint

theorem memory_ownership :
    Objects.AllocatorRepr (input.heap.alloc (primitiveArrayObject .uint values (by decide))).1
      (upd input.base input.H.length (wmod 40)) 8 (wmod 43) first :=
  primitive_array_allocator input.heap .uint values (by decide) words representation input.base 8 (wmod 40)
    input.machine input.allocator (by decide)

theorem reached_ownership :
    Objects.AllocatorRepr (input.heap.alloc (primitiveArrayObject .uint values (by decide))).1
      (upd input.base input.H.length (wmod 40)) 8 (wmod 43) after := memory_ownership.mem_eq rfl

theorem mixed_run : run (primitiveArrayCode words ++ StorageOps.ProducerInterfaceControls.code) input.machine = .ok after 0 ∧
    after.mem 0 = w[43] ∧ after.mem 40 = w[2] ∧ after.mem 41 = w[11] ∧ after.mem 42 = w[23] ∧
    after.mem 17 = w[7] ∧ after.store (.root 0) = 1 ∧ after.stack = [w[40],w[77]] := by
  constructor
  · exact (mixed_endpoint_inhabited.compose (primitiveArrayCode words) input.machine ⟨memory_run⟩).execution
  · decide +kernel

theorem skipped_store_rejected : ¬ LocationStepPremise (primitiveArrayCode words ++ StorageOps.ProducerInterfaceControls.code) input.machine middle := by
  intro proposed
  have reached : after = middle := by
    have execution : run (primitiveArrayCode words ++ StorageOps.ProducerInterfaceControls.code) input.machine = .ok after 0 := mixed_run.1
    rw [proposed.execution] at execution
    exact (Out.ok.inj execution).1.symm
  have wrong : after.store (.root 0) = middle.store (.root 0) := congrArg (fun machine => machine.store (.root 0)) reached
  change (1 : Nat) = 0 at wrong
  cases wrong

#print axioms published_master_inhabited
#print axioms mixed_endpoint_inhabited
#print axioms memory_ownership
#print axioms reached_ownership
#print axioms mixed_run
#print axioms skipped_store_rejected
end Solidity.Backend.MemoryCopies.PublishedStorageControls
