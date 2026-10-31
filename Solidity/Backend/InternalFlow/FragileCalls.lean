import Solidity.Backend.InternalFlow.FragileFrames
import Solidity.Backend.InternalFlow.StorageCalls

/-! Export the actual live indexed reference with its fragile classification.
The reached live witness is extracted from StateRepr, never assumed for a body. -/
namespace Solidity.Backend.InternalFlow.FragileCalls
open Evm Evm.Memory
variable {C : Contract}

private theorem ok_of_state {H : HTy} {Γ : Ctx} {res : TRes (Solidity.Out C H Γ)}
    {τ : State C Γ} (h : res.map (·.st) = .ok τ) : ∃ o, res = .ok o ∧ o.st = τ := by
  cases res with
  | error e => cases h
  | ok o => exact ⟨o,rfl,Except.ok.inj h⟩

private theorem error_of_state {H : HTy} {Γ : Ctx} {res : TRes (Solidity.Out C H Γ)}
    (h : res.map (·.st) = .error .revert) : res = .error .revert := by
  cases res with
  | error e => exact congrArg Except.error (Except.error.inj h)
  | ok o => cases h

def storageReturnFragile {b : Nat} {Γ ps Γf : Ctx} {F : Frag Γ} (f : Name)
    (args : Args C Γ ps) (R : RefTy) (name : Var) (body : Prog C (.alias R :: ps) Γf)
    (hq : Calls.Program b F (StorageCalls.expand args R name body))
    (fragile : hq.frag.get .here = .fragile) : Calls.Statement b F (.call f args (.storage R name) body) where
  frag := (hq.frag.restrict Γ).push (.alias R) .fragile
  code := hq.code ++ Calls.returnPointerCode b Γ ps
  need := hq.need
  cost := hq.cost
  allocates := hq.allocates
  zeroCost := hq.zeroCost
  sound := by
    intro L frame σ base m h room capacity
    rcases hq.sound h room capacity with ⟨o,m₁,base',ho,hc,hm,hk,he,ha⟩ | ⟨ho,hc⟩
    · obtain ⟨ref,slot,href,hslot,hpath,hlive⟩ := hm.core.fragile .here fragile
      let τ := o.st.thin (.keep (Thin.ofExt (Ext.append Γ ps)))
      have hτ : τ = (o.st.drop (Ext.append Γ (.alias R :: ps))).push (t := .alias R) (some ref) := by
        unfold τ State.thin State.drop State.push State.withEnv
        simp only [TEnv.thin,TEnv.thin_ofExt]
        have href' : o.st.env.1 = some ref := href
        rw [href']
        rfl
      have hs : ((Stmt.call f args (.storage R name) body).run σ).map (·.st) = .ok τ := by
        change (Stmt.call f args (.storage R name) body).runSt σ = _
        rw [← StorageCalls.expand_runSt f args R name body σ]
        show (((StorageCalls.expand args R name body).run σ).map (·.st)).map _ = _
        rw [ho]
        rfl
      obtain ⟨out,hout,ht⟩ := ok_of_state hs
      have hroom : b + (Γ.length + 1) ≤ frame := by
        have hh := hm.locals
        simp only [List.length_cons,List.length_append] at hh
        omega
      have hrepr := FragileFrames.pushFragile (hm.drop (Ext.append Γ (.alias R :: ps))) hpath hlive hroom
      have hcode : run (Calls.returnPointerCode b Γ ps) m₁ =
          .ok (writeMachine m₁ (cell (b + Γ.length)) (.slot slot)) 0 := by
        have hp : m₁.mem (cell (b + Γ.length + ps.length)) = .slot slot := by
          simpa only [Machine.memAt,cellOf,lvl_here,List.length_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hslot
        simp only [Calls.returnPointerCode,run,exec_cons_zero,Instr.step,Machine.next,hp,
          Out.ok_bind,exec_nil,writeMachine]
      refine .inl ⟨out,writeMachine m₁ (cell (b + Γ.length)) (.slot slot),base',hout,?_,?_,hk,he,?_⟩
      · rw [run_append_ok hc]
        exact hcode
      · rw [ht,hτ]
        exact hrepr
      · intro cursor hb alloc space
        rw [ht,hτ]
        exact (ha cursor hb alloc space).localWrite _ (by dsimp [cell]; omega) (by dsimp [cell]; omega) _
    · have hs : ((Stmt.call f args (.storage R name) body).run σ).map (·.st) = .error .revert := by
        change (Stmt.call f args (.storage R name) body).runSt σ = _
        rw [← StorageCalls.expand_runSt f args R name body σ]
        show (((StorageCalls.expand args R name body).run σ).map (·.st)).map _ = _
        rw [ho]
        rfl
      exact .inr ⟨error_of_state hs,run_append_revert hc⟩

end Solidity.Backend.InternalFlow.FragileCalls
