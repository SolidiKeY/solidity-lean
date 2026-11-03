import Solidity.Backend.InternalFlow.RuntimeFrameCapturedProgram
import Solidity.Backend.InternalFlow.RuntimeFrameCallAgreement
import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV3

/-! Typed ordinary-call forms: `Form` classifies the memory-return and tuple
`CallRet` constructors. A proof certificate for existing constructors, not a
new AST, value, evaluator or admission policy. Tuple emission and concrete
allocating reference witnesses are open; nothing here inhabits a producer. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef
open Evm Evm.Memory

inductive Form (Γ : Ctx) : {rs Δ : Ctx} → CallRet Γ rs Δ → Ext Γ Δ → Prop where
 | memory (R : RefTy) (name : Var) (hd : (Ty.ref R).defaultOkS=true)
     (hm : (Ty.ref R).mapFree=true) :
     Form Γ (.mem R name hd hm) (.push .refl)
 | tuple {rs : Ctx} (binders : RetBinders rs) :
     Form Γ (.rets binders) (Ext.append Γ rs)

variable {C : Contract} {Γ Δ ps rs Γf : Ctx} {b : Nat} {F : Frag Γ}
 {f : Name} {args : Args C Γ ps} {ret : CallRet Γ rs Δ}
 {body : Prog C (rs ++ ps) Γf} {scope : Ext Γ Δ}

def plan (selected : Composition.Program b F (.cons (.call f args ret body) .nil))
 (lo pointer : Nat) : InterfaceV1.Emission C Γ Δ :=
 ⟨Restore.saveCells pointer (Restore.contextCells b Γ) ++ selected.checked.code ++
   Restore.restoreCells pointer (Restore.contextCells b Γ),
 selected.checked.frag,max selected.checked.need (max Γ.length Δ.length),lo,pointer,
 (fun _ => Γ.length+1),selected.checked.cost⟩

/-- Physical resource domain; agreement with approved remains an external
hypothesis. These fields mirror the Entry resource conditions (no coverage
theorem is proved here). -/
def admitted (selected : Composition.Program b F (.cons (.call f args ret body) .nil))
 (lo pointer : Nat) : InterfaceV3.Admission C Γ := fun L frame caller base machine start =>
 StateRepr L b frame F caller base machine ∧
 b+max selected.checked.need (max Γ.length Δ.length)≤lo ∧
 lo≤pointer ∧ pointer<frame ∧ lo≤start ∧ start+(Γ.length+1)≤frame ∧
 (pointer<start ∨ start+(Γ.length+1)≤pointer) ∧ start+(Γ.length+1)<W ∧
 machine.mem pointer=.val (wmod start) ∧
 AllocationInput b frame (selected.checked.cost caller) caller base machine

/-- Remaining producer target; no inhabitant is asserted by this type. Its own
`plan` field is free: it is not pinned to `plan selected lo pointer`. -/
abbrev ProducerGoal (selected : Composition.Program b F (.cons (.call f args ret body) .nil))
 (lo pointer : Nat) (approved : InterfaceV3.Admission C Γ) :=
 InterfaceV3.PendingCallProducer b F approved (admitted selected lo pointer) f args ret body

end Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef
