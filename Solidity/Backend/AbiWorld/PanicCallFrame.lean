import Solidity.Backend.AbiWorld.PanicReadWindow
import Solidity.Semantics.Run

/-! Typed call/catch consumers of actual arbitrary full-word Panic packets.
No external world or compiler/call-frame simulation is assumed. -/
namespace Solidity.Backend.AbiWorld.PanicCallFrame
open Semantics PanicReadWindow
variable {C : Contract} {Γ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx}

def callee (d : List UInt8) : Prog C [] [] := .cons (.revertData [.bytes d]) .nil

theorem call_data (σ : State C Γ) (d : List UInt8) :
    TRun.call Args.nil (.rets .nil) (callee (C:=C) d).ext (callee d).runR σ = .error (THalt.ofData d) := by
  simp only [TRun.call,callee,Prog.runR,TRun.seq,TRun.revertData,RevPart.evalT,
    List.mapM_cons,List.mapM_nil,List.flatten_cons,List.flatten_nil,List.append_nil,
    Args.evalT,bind,Except.bind,pure,Except.pure]

/-- The literal callee really runs; no desired failed-call premise remains.
Error precedes Panic, the exact code binder is supplied, and clause locals drop. -/
theorem selected (σ : State C Γ) (c : ExtCall C Γ)
    (hnz : (c.addr.evalT σ).1 ≠ 0)
    (hself : (c.addr.evalT σ).1 = σ.tx.selfAddress.1)
    (n : Nat) (hn : n < 2^256) (suffix : List UInt8)
    (ok : Prog C Γ Γ₁) (err : Prog C Γ Γ₂) (code : CodeBinder κ)
    (pnc : Prog C (κ ++ Γ) Γ₃) (other : Prog C Γ Γ₄) :
    TRun.tryCall c .nil ok.ext ok.runR err.ext err.runR code pnc.ext pnc.runR
      other.ext other.runR Args.nil (callee (C:=C) (encodePanic n ++ suffix)).ext
      (callee (encodePanic n ++ suffix)).runR true σ =
      (pnc.runR (σ.withEnv (TEnv.append κ (code.decodeT (H:=σ.H) (word n hn)) σ.env))).map
        (fun o => ⟨o.st.drop ((Ext.append Γ κ).trans pnc.ext),o.ext⟩) := by
  have hc : decide ((c.addr.evalT σ).1 = σ.tx.selfAddress.1) = true := by
    simp only [hself,decide_true]
  have actual : TRun.call Args.nil (.rets .nil) (callee (C:=C) (encodePanic n ++ suffix)).ext
      (callee (encodePanic n ++ suffix)).runR σ = .error (.revertWith (encodePanic n ++ suffix)) := by
    simpa only [encodePanic,panicSelector,List.cons_append,THalt.ofData] using call_data σ (encodePanic n ++ suffix)
  simp only [TRun.tryCall,if_neg hnz,hc,Bool.and_self,ite_true,Binders.toRet,actual,error_reject,PanicReadWindow.decode n hn suffix]
end Solidity.Backend.AbiWorld.PanicCallFrame
#print axioms Solidity.Backend.AbiWorld.PanicCallFrame.call_data
#print axioms Solidity.Backend.AbiWorld.PanicCallFrame.selected
