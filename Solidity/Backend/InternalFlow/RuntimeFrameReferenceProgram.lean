import Solidity.Backend.InternalFlow.RuntimeFrameReference
import Solidity.Evm.MemoryCalls

/-! Composition of actual checked program execution with reached reference
export. Certificates are the published checked Calls.Program constructors, not desired
simulation premises. Failed runs supply no final source or target state. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.Reference.Program
open Evm Evm.Memory
variable {C : Contract} {Ξ Δ Γ : Ctx} {R : RefTy}

/-- The actual checked program produces the reached reference and machine;
export then preserves its full post-body relation, exact cost and stack. -/
theorem after_reference {b L frame : Nat} {F : Frag Ξ} {P : Prog C Ξ Δ}
 (checked : Calls.Program b F P) {σ : State C Ξ} {base : Nat → Fin W} {m : Machine}
 (represented : StateRepr L b frame F σ base m)
 (room : b + checked.need ≤ frame)
 (capacity : AllocationInput b frame (checked.cost σ) σ base m)
 (out : Solidity.Out C σ.H Δ) (source : P.run σ = .ok out)
 (scope : Ext Γ Δ) (destination : Idx Γ (.mem R)) (result : Idx Δ (.mem R)) :
 ∃ (middle last : Machine) (addresses : Nat → Fin W) (reference : HRef out.st.H R),
 Evm.run checked.code m = .ok middle 0 ∧
 TEnv.get result out.st.env = some reference ∧
 middle.mem (cellOf b result) = .val (addresses reference.id) ∧
 last = writeMachine middle (cellOf b destination) (.val (addresses reference.id)) ∧
 Evm.run (checked.code ++ Reference.code b scope destination result) m = .ok last 0 ∧
 StateRepr L b frame (checked.frag.restrict Γ)
   ((out.st.setLocal (destination.ext scope) (TEnv.get result out.st.env)).drop scope)
   addresses last ∧
 last.stack = m.stack ∧ BaseExtends σ.H base addresses ∧
 GrowsAllocator b frame (checked.cost σ) σ base m
   ((out.st.setLocal (destination.ext scope) (TEnv.get result out.st.env)).drop scope)
   addresses last := by
 rcases checked.sound represented room capacity with
   ⟨actual,middle,addresses,hs,ht,hr,hk,he,hg⟩ | ⟨hs,ht⟩
 · have same := Except.ok.inj (hs.symm.trans source)
   subst actual
   obtain ⟨reference,value,pointer,exported,full⟩ := Reference.export_reference hr scope destination result
   let last := writeMachine middle (cellOf b destination) (.val (addresses reference.id))
   have preserved := Reference.allocator hr scope destination result
   rw [pointer] at preserved
   refine ⟨middle,last,addresses,reference,ht,value,pointer,rfl,?_,full,hk,he,?_⟩
   · rw [Evm.run_append_ok ht]
     exact exported
   · simpa only [Nat.add_zero] using hg.comp preserved
 · rw [source] at hs
   contradiction

/-- Exact bare revert from the supported checked fragment absorbs the export
suffix. No failed State, pointer frontier or world rollback is reconstructed. -/
theorem revert_absorbs {b L frame : Nat} {F : Frag Ξ} {P : Prog C Ξ Δ}
 (checked : Calls.Program b F P) {σ : State C Ξ} {base : Nat → Fin W} {m : Machine}
 (represented : StateRepr L b frame F σ base m)
 (room : b + checked.need ≤ frame)
 (capacity : AllocationInput b frame (checked.cost σ) σ base m)
 (source : P.run σ = .error .revert) (suffix : List Instr) :
 Evm.run (checked.code ++ suffix) m = .revert := by
 rcases checked.sound represented room capacity with
   ⟨actual,middle,addresses,hs,ht,hr,hk,he,hg⟩ | ⟨hs,ht⟩
 · rw [source] at hs
   contradiction
 · exact Evm.run_append_revert ht
/-- A following checked caller program uses the actual exported relation
and allocation input. Total room/cost is genuine, not a supplied midpoint. -/
theorem after_reference_then {b L frame : Nat} {F : Frag Ξ} {P : Prog C Ξ Δ}
 (checked : Calls.Program b F P) {σ : State C Ξ} {base : Nat → Fin W} {m : Machine}
 (represented : StateRepr L b frame F σ base m)
 (room : b + checked.need ≤ frame)
 (out : Solidity.Out C σ.H Δ) (source : P.run σ = .ok out)
 (scope : Ext Γ Δ) (destination : Idx Γ (.mem R)) (result : Idx Δ (.mem R))
 {Ω : Ctx} {tail : Prog C Γ Ω}
 (next : Calls.Program b (checked.frag.restrict Γ) tail)
 (nextRoom : b + next.need ≤ frame)
 (capacity : AllocationInput b frame (checked.cost σ + next.cost
   ((out.st.setLocal (destination.ext scope) (TEnv.get result out.st.env)).drop scope)) σ base m)
 (final : Solidity.Out C out.st.H Ω)
 (nextSource : tail.run ((out.st.setLocal (destination.ext scope) (TEnv.get result out.st.env)).drop scope) = .ok final) :
 ∃ last addresses,
 Evm.run ((checked.code ++ Reference.code b scope destination result) ++ next.code) m = .ok last 0 ∧
 StateRepr L b frame next.frag final.st addresses last ∧ last.stack = m.stack ∧
 BaseExtends σ.H base addresses ∧
 GrowsAllocator b frame (checked.cost σ + next.cost
   ((out.st.setLocal (destination.ext scope) (TEnv.get result out.st.env)).drop scope))
   σ base m final.st addresses last := by
 obtain ⟨middle,exported,firstBase,reference,run,value,pointer,written,whole,hr,hk,he,hg⟩ :=
   after_reference checked represented room (capacity.of_le (Nat.le_add_right _ _)) out source scope destination result
 have nextInput := hg.nextInput capacity
 rcases next.sound hr nextRoom nextInput with
   ⟨actual,last,addresses,hs,ht,hfinal,hstack,extended,growth⟩ | ⟨hs,ht⟩
 · have same := Except.ok.inj (hs.symm.trans nextSource)
   subst actual
   refine ⟨last,addresses,?_,hfinal,hstack.trans hk,he.trans out.ext extended,hg.comp growth⟩
   rw [Evm.run_append_ok whole]
   exact ht
 · rw [nextSource] at hs
   contradiction
end Solidity.Backend.InternalFlow.RuntimeFrame.Reference.Program
