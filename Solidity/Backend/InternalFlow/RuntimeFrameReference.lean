import Solidity.Backend.InternalFlow.RuntimeFrameResult

/-! Export a reached memory reference into an old caller binding. Pointer
identity is derived from the actual reached representation, not guessed from
an allocation frontier. The heap and all post-body fields survive scope drop;
no preservation of pre-call heap contents or fragile storage liveness follows.
-/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.Reference
open Evm Evm.Memory
variable {C : Contract} {Γ Δ : Ctx} {R : RefTy}

def code (b : Nat) (scope : Ext Γ Δ) (destination : Idx Γ (.mem R))
    (result : Idx Δ (.mem R)) : List Instr :=
 [.mload (cellOf b result), .mstore (cellOf b (destination.ext scope))]

/-- Logical scope exit writes the evaluated reference into exactly the old
caller destination. This uses the published generic typed environment law. -/
theorem source_export (scope : Ext Γ Δ) (destination : Idx Γ (.mem R))
    (result : Idx Δ (.mem R)) (σ : State C Δ) :
 (σ.setLocal (destination.ext scope) (TEnv.get result σ.env)).drop scope =
 (σ.drop scope).setLocal destination (TEnv.get result σ.env) := by
 simp only [State.drop, State.setLocal, CallResultRestore.env_drop_set]

/-- Read the actual represented pointer, export it, and drop the private
logical prefix. Full StateRepr transports the reached heap, all other caller
aliases and current storage-slot evidence without asserting Heap.Keeps. -/
theorem export_reference {L b frame : Nat} {F : Frag Δ}
    {σ : State C Δ} {base : Nat → Fin W} {m : Machine}
    (represented : StateRepr L b frame F σ base m)
    (scope : Ext Γ Δ) (destination : Idx Γ (.mem R)) (result : Idx Δ (.mem R)) :
 ∃ reference : HRef σ.H R,
 TEnv.get result σ.env = some reference ∧
 m.mem (cellOf b result) = .val (base reference.id) ∧
 Evm.run (code b scope destination result) m =
   .ok (writeMachine m (cellOf b destination) (.val (base reference.id))) 0 ∧
 StateRepr L b frame (F.restrict Γ)
   ((σ.setLocal (destination.ext scope) (TEnv.get result σ.env)).drop scope)
   base (writeMachine m (cellOf b destination) (.val (base reference.id))) := by
 obtain ⟨reference, value, pointer⟩ := represented.pointers result
 refine ⟨reference,value,pointer,?_,?_⟩
 · simp only [code,cellOf,lvl_ext]
   change Evm.run [.mload (cellOf b result),.mstore (cellOf b destination)] m = _
   simp only [Evm.run,exec_cons_zero,Instr.step,Machine.next,Out.ok_bind,exec_nil,pointer]
   rfl
 · rw [value]
   simpa only [cellOf,lvl_ext] using (represented.setMem (destination.ext scope) reference).drop scope

/-- Export is a bounded caller-cell write, with exact zero allocator cost.
This consumes real allocator ownership; source success never manufactures it. -/
theorem allocator {L b frame : Nat} {F : Frag Δ}
    {σ : State C Δ} {base : Nat → Fin W} {m : Machine}
    (represented : StateRepr L b frame F σ base m)
    (scope : Ext Γ Δ) (destination : Idx Γ (.mem R)) (result : Idx Δ (.mem R)) :
 GrowsAllocator b frame 0 σ base m
   ((σ.setLocal (destination.ext scope) (TEnv.get result σ.env)).drop scope) base
   (writeMachine m (cellOf b destination) (m.mem (cellOf b result))) := by
 intro cursor positive allocation space
 have lower : 0 < cellOf b destination :=
   Nat.lt_of_lt_of_le positive (le_lvl b destination)
 have upper : cellOf b destination < frame := by
   have h := lvl_lt b (destination.ext scope)
   have hn := represented.locals
   simp only [lvl_ext] at h
   exact Nat.lt_of_lt_of_le h hn
 simpa only [Nat.add_zero] using
   allocation.localWrite (cellOf b destination) lower upper (m.mem (cellOf b result))

/-- The result escapes at the next genuine caller level, after private
logical binders have been removed. This emits no new heap allocation. -/
def headCode (b : Nat) (Γ : Ctx) (result : Idx Δ (.mem R)) : List Instr :=
 [.mload (cellOf b result), .mstore (b + Γ.length)]

theorem export_head {L b frame : Nat} {F : Frag Δ}
    {σ : State C Δ} {base : Nat → Fin W} {m : Machine}
    (represented : StateRepr L b frame F σ base m)
    (scope : Ext Γ Δ) (result : Idx Δ (.mem R))
    (room : b + (Γ.length + 1) ≤ frame) :
 ∃ reference : HRef σ.H R,
 TEnv.get result σ.env = some reference ∧
 m.mem (cellOf b result) = .val (base reference.id) ∧
 Evm.run (headCode b Γ result) m =
   .ok (writeMachine m (b + Γ.length) (.val (base reference.id))) 0 ∧
 StateRepr L b frame ((F.restrict Γ).push (.mem R) .ok)
   ((σ.drop scope).push (t := .mem R) (TEnv.get result σ.env))
   base (writeMachine m (b + Γ.length) (.val (base reference.id))) := by
 obtain ⟨reference,value,pointer⟩ := represented.pointers result
 refine ⟨reference,value,pointer,?_,?_⟩
 · simp only [headCode,Evm.run,exec_cons_zero,Instr.step,Machine.next,Out.ok_bind,exec_nil,pointer]
   rfl
 · rw [value]
   exact (represented.drop scope).consMem reference room

/-- Exact intrinsic memory-return environment. The ordinary CallRet admission
premises remain unchanged; no frontend/call-body agreement is assumed here. -/
theorem leave_memory (scope : Ext Γ Δ) (result : Idx Δ (.mem R))
    (σ : State C Δ) (name : Var) (defaultOk : (Ty.ref R).defaultOkS = true)
    (mapFree : (Ty.ref R).mapFree = true) :
 CallRet.leaveT (σ.drop scope).env (.mem R name defaultOk mapFree)
   (TEnv.get result σ.env, ()) =
 ((σ.drop scope).push (t := .mem R) (TEnv.get result σ.env)).env := rfl

end Solidity.Backend.InternalFlow.RuntimeFrame.Reference
