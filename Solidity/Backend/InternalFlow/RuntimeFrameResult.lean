import Solidity.Evm.MemoryScope
import Solidity.Evm.MemoryCapture
import Solidity.Calculus.CallResultRestore

/-! Primitive result export from a reached typed private frame. The emitted
load/store reads the actual result cell, retains all other physical cells and
all post-body fields, and drops only the logical private prefix. This is not a
recursive dispatcher, caller-word rollback or a call-body compiler. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.Result
open Evm Evm.Memory
variable {C : Contract} {Γ Δ : Ctx} {p : PrimTy}

def code (b : Nat) (scope : Ext Γ Δ) (destination : Idx Γ (.val p))
    (result : Idx Δ (.val p)) : List Instr :=
 [.mload (cellOf b result), .mstore (cellOf b (destination.ext scope))]

/-- The real reached result is read before its private binder is dropped.
Full representation includes the mutated heap, current fragile-slot evidence,
all caller pointers and post-body world fields. No old-heap preservation is
required or inferred. The input is the producer's reached StateRepr. -/
theorem export_result {L b frame : Nat} {F : Frag Δ}
    {σ : State C Δ} {base : Nat → Fin W} {m : Machine}
    (represented : StateRepr L b frame F σ base m)
    (scope : Ext Γ Δ) (destination : Idx Γ (.val p)) (result : Idx Δ (.val p)) :
 Evm.run (code b scope destination result) m =
   .ok (writeMachine m (cellOf b destination) (m.mem (cellOf b result))) 0 ∧
 StateRepr L b frame (F.restrict Γ)
   ((σ.setLocal (destination.ext scope) (TEnv.get result σ.env)).drop scope)
   base (writeMachine m (cellOf b destination) (m.mem (cellOf b result))) := by
 have value : ReprV p (TEnv.get result σ.env) (m.mem (cellOf b result)) :=
   represented.core.vals result
 have written := represented.setVal (destination.ext scope) _ _ value
 have dropped := written.drop scope
 rw [CallResultRestore.state_drop_set] at dropped
 refine ⟨?_, ?_⟩
 · simp only [code, cellOf, lvl_ext]
   rfl
 · rw [CallResultRestore.state_drop_set]
   simpa only [cellOf, lvl_ext] using dropped

/-- Logical scope exit writes precisely the retained caller destination. -/
theorem source_export (scope : Ext Γ Δ) (destination : Idx Γ (.val p))
    (result : Idx Δ (.val p)) (σ : State C Δ) :
 (σ.setLocal (destination.ext scope) (TEnv.get result σ.env)).drop scope =
 (σ.drop scope).setLocal destination (TEnv.get result σ.env) :=
 CallResultRestore.state_drop_set scope destination _ σ

/-- Private physical cells remain present; scope exit is not memory erasure. -/
theorem outside (m : Machine) (b : Nat)
    (destination : Idx Γ (.val p)) (result : Idx Δ (.val p)) (address : Nat)
    (different : address ≠ cellOf b destination) :
 (writeMachine m (cellOf b destination) (m.mem (cellOf b result))).mem address =
 m.mem address := by
 simp only [writeMachine, upd, if_neg different]

/-- Result export allocates no object and preserves the genuine reached
allocator, with its exact zero-cost cursor. Positive frame origin is retained
from the existing allocator interface, not inferred from source success. -/
theorem allocator {L b frame : Nat} {F : Frag Δ}
    {σ : State C Δ} {base : Nat → Fin W} {m : Machine}
    (represented : StateRepr L b frame F σ base m)
    (scope : Ext Γ Δ) (destination : Idx Γ (.val p)) (result : Idx Δ (.val p)) :
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
 have preserved := allocation.localWrite (cellOf b destination) lower upper
   (m.mem (cellOf b result))
 simpa only [Nat.add_zero] using preserved

end Solidity.Backend.InternalFlow.RuntimeFrame.Result
