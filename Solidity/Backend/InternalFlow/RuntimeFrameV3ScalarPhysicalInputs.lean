import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarDemand
import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV3

/-! Physical input requirements for the count-demand scalar image. They are
independent of Entry, source-call outcomes, quotation indices and any approved
source profile. The count expression is evaluated only by the existing reserve
function. Agreement with an approved original profile is NOT supplied. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPhysicalInputs
open Evm Evm.Memory

structure Input {C : Contract} {Γ : Ctx} (b c pointer : Nat) (F : Frag Γ)
 (count : Val C Γ .uint) (L frame : Nat) (caller : State C Γ)
 (base : Nat → Fin W) (machine : Machine) (start : Nat) : Prop where
 represented : StateRepr L b frame F caller base machine
 locals : b+Γ.length≤pointer
 workspace : b+(c+3-b)≤pointer
 pointerBelow : pointer<frame
 payloadAbove : pointer≤start
 reserve : start+ScalarDemand.reserve count caller≤frame
 separate : pointer<start ∨ start+ScalarDemand.reserve count caller≤pointer
 noWrap : start+ScalarDemand.reserve count caller<W
 cursor : machine.mem pointer=.val (wmod start)

def domain {C : Contract} {Γ : Ctx} (b c pointer : Nat) (F : Frag Γ)
 (count : Val C Γ .uint) : Nat → InterfaceV3.Admission C Γ :=
 fun _ => Input b c pointer F count

/-- Coverage is derived for every caller and every index. Zero heap cost and
control-space follow from this actual plan, rather than extra input premises. -/
theorem coverage {C : Contract} {Γ : Ctx} {R : RefTy} {b c frame pointer bottom : Nat}
 {F : Frag Γ} {count : Val C Γ .uint}
 (emitted : ScalarEmitter.Emission b c frame pointer bottom F count)
 (reference : Idx Γ (.mem R)) (destination : Idx Γ (.val .uint)) :
 InterfaceV3.FamilyEntryCoverage b F (domain b c pointer F count)
   (ScalarDemand.plan emitted reference destination) := by
 intro depth L capacity caller base machine start input
 exact ⟨input.represented,input.locals,input.locals,input.workspace,Nat.le_refl _,input.pointerBelow,
   input.payloadAbove,input.reserve,Nat.le_max_left _ _,input.separate,input.noWrap,input.cursor,.inl rfl⟩

/-- Conversely, each checked Entry supplies precisely these physical facts.
This theorem does not establish that an original source case is in the domain. -/
theorem of_entry {C : Contract} {Γ : Ctx} {R : RefTy} {b c selectedFrame pointer bottom : Nat}
 {F : Frag Γ} {count : Val C Γ .uint}
 (emitted : ScalarEmitter.Emission b c selectedFrame pointer bottom F count)
 (reference : Idx Γ (.mem R)) (destination : Idx Γ (.val .uint))
 {depth L frame : Nat} {caller : State C Γ} {base : Nat → Fin W} {machine : Machine} {start : Nat}
 (entry : InterfaceV1.Entry ((ScalarDemand.plan emitted reference destination).at depth)
   L b frame F caller base machine start) :
 Input b c pointer F count L frame caller base machine start :=
 ⟨entry.represented,entry.callerBound,entry.workspace,entry.pointerBelow,entry.payloadAbove,
  entry.reserve,entry.separate,entry.noWrap,entry.cursor⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPhysicalInputs
