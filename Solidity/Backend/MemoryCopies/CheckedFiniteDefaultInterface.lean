import Solidity.Backend.MemoryCopies.CheckedDefault
import Solidity.Backend.MemoryCopies.DefaultDemand
import Solidity.Evm.MemoryStructDefaultSource

/-! Total capacity contracts for the existing finite default plans. The guard
checks once before allocation; all successful plan fields and root offsets stay
intact. Source panic, physical adequacy and plan availability remain separate. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def checkedFiniteDefaultCode {R : RefTy} (plan : DefaultPlan R) (suffix : List Instr) : List Instr :=
  defaultCapacityGuard plan.cost ++ (plan.code ++ suffix)

def FiniteDefaultSuccess {C : Contract} {Γ : Ctx} {R : RefTy} (plan : DefaultPlan R)
    {L b frame : Nat} {F : Frag Γ} (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (memory : (Ty.ref R).mapFree = true)
    (fits : cursor.val + plan.cost < W) : Prop :=
  let grown := state.heap.allocDefault R memory
  ∃ (base' : Nat → Fin W) (mem : Nat → Word),
    StateRepr L b frame F (state.adopt grown).1 base' {machine with mem := mem} ∧
    StructAllocatorRepr grown.heap base' frame ⟨cursor.val + plan.cost, fits⟩ {machine with mem := mem} ∧
    BaseExtends state.H base base' ∧
    base' grown.val.id = wmod (cursor.val + plan.root) ∧
    run (checkedFiniteDefaultCode plan []) machine =
      .ok (({machine with mem := mem} : Machine).push (.val (wmod (cursor.val + plan.root)))) 0 ∧
    heapWords grown.heap = heapWords state.heap + plan.cost

structure CheckedFiniteDefaultCertificate : Prop where
  execute : ∀ {C : Contract} {Γ : Ctx} {R : RefTy} (plan : DefaultPlan R)
    {L b frame : Nat} {F : Frag Γ} (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (memory : (Ty.ref R).mapFree = true),
    StateRepr L b frame F state base machine →
    StructAllocatorRepr state.heap base frame cursor machine → 0 < b →
    (∃ fits, FiniteDefaultSuccess (L := L) (b := b) (frame := frame) (F := F)
      plan state base cursor machine memory fits) ∨
    (¬ cursor.val + plan.cost < W ∧ run (checkedFiniteDefaultCode plan []) machine = .revert)
  declaration : ∀ {C : Contract} {Γ : Ctx} {R : RefTy} (plan : DefaultPlan R)
    {L b frame : Nat} {F : Frag Γ} (state : State C Γ) (base : Nat → Fin W)
    (cursor : Fin W) (machine : Machine) (memory : (Ty.ref R).mapFree = true),
    StateRepr L b frame F state base machine →
    StructAllocatorRepr state.heap base frame cursor machine → 0 < b →
    b + (Γ.length + 1) ≤ frame →
    GrowingResult L b frame plan.cost (F.push (.mem R) .ok) state base machine
      (TRun.declMem R none memory state)
      (run (checkedFiniteDefaultCode plan [.mstore (cell (b + Γ.length))]) machine) ∨
    (¬ cursor.val + plan.cost < W ∧
      run (checkedFiniteDefaultCode plan [.mstore (cell (b + Γ.length))]) machine = .revert)

end Solidity.Backend.MemoryCopies
