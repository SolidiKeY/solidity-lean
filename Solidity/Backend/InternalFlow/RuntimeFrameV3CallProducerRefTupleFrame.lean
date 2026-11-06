import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRefTuple

/-! Ownership and retained-context transport for the ascending tuple result
copies. No returned-prefix representation or full tuple-call producer is
asserted here. All actual copy runs preserve the live heap, aliases through its
unchanged object map, allocation cursor and zeroed free region. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.Tuple
open Evm Evm.Memory

/-- Each real copy writes strictly inside the reserved frame. Heap separation,
all live object representations and the free tail therefore survive. -/
theorem copy_allocator {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W}
    (count source destination : Nat) (before after : Machine)
    (ownership : StructAllocatorRepr hp base frame cursor before)
    (positive : 0 < destination) (room : destination + count ≤ frame)
    (evaluated : Evm.run (copyCode source destination count) before = .ok after 0) :
    StructAllocatorRepr hp base frame cursor after := by
  induction count generalizing source destination before with
  | zero =>
    change Evm.Out.ok before 0 = Evm.Out.ok after 0 at evaluated
    have same : before = after := (Evm.Out.ok.inj evaluated).1
    exact same ▸ ownership
  | succ count ih =>
    let first := writeMachine before destination (before.mem source)
    have firstRun : Evm.run [.mload source, .mstore destination] before = .ok first 0 := rfl
    have remaining : Evm.run (copyCode (source+1) (destination+1) count) first =
        .ok after 0 := by
      change Evm.run ([.mload source, .mstore destination] ++
        copyCode (source+1) (destination+1) count) before = _ at evaluated
      rw [Evm.run_append_ok firstRun] at evaluated
      exact evaluated
    exact ih (source+1) (destination+1) first
      (ownership.localWrite destination positive (by omega) (before.mem source))
      (by omega) (by omega) remaining

/-- A tuple copy above the caller leaves the caller's complete representation
in the reached heap, including storage aliases, memory pointers and references.
This is not rollback of the post-body globals or heap. -/
theorem copy_retained {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
    {post : State C Γ} {base : Nat → Fin W} {before after : Machine}
    (count source destination : Nat) (ordered : destination ≤ source)
    (above : b + Γ.length ≤ destination) (room : destination + count ≤ frame)
    (represented : StateRepr L b frame F post base before)
    (evaluated : Evm.run (copyCode source destination count) before = .ok after 0) :
    StateRepr L b frame F post base after := by
  obtain ⟨actual, executed, stack, values, outside, fields⟩ :=
    copy_run count source destination before ordered
  have same : actual = after := (Evm.Out.ok.inj (executed.symm.trans evaluated)).1
  subst actual
  have changed := Restored.memory_transport represented after.mem
    (fun index _ => outside (cellOf b index) (.inl (by
      have bound := lvl_lt b index
      change lvl b index < destination
      omega)))
    (fun address bound => outside address (.inr (by omega)))
  have shape := congrArg (fun m : Machine => {m with mem := after.mem}) fields
  change {after with stack := before.stack} = {before with mem := after.mem} at shape
  rw [← stack] at shape
  have target : {before with mem := after.mem} = after := by
    calc
      {before with mem := after.mem} = {before with mem := after.mem, stack := after.stack} := by rw [stack]
      _ = after := shape.symm
  exact target ▸ changed

#print axioms copy_allocator
#print axioms copy_retained
end Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.Tuple
