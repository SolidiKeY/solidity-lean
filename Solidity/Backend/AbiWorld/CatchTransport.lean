import Solidity.Semantics.RevertMemory
import Solidity.Semantics.AllocBytes
import Solidity.Backend.AbiWorld.PublishedLayout

/-! Consumers of the published intrinsic call/catch execution. These laws keep
actual callee execution as a premise; concrete typed programs discharge it in
`CatchControls`. They claim neither target compilation nor whole-world rollback. -/
namespace Solidity.Backend.AbiWorld.CatchTransport
variable {C : Contract} {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx}

/-- Error decoding precedes Panic decoding, and all clause locals are popped.
The code binder and its frame are exactly those of the published execution. -/
theorem try_revertWith (c : ExtCall C Γ) (rets : Binders ρ)
    (ok : Prog C (ρ ++ Γ) Γ₁) (err : Prog C Γ Γ₂) (code : CodeBinder κ)
    (pnc : Prog C (κ ++ Γ) Γ₃) (other : Prog C Γ Γ₄)
    (args : Args C Γ ps) (callee : Prog C (ρ ++ ps) Γf)
    (σ : State C Γ) (d : List UInt8)
    (hnz : (c.addr.evalT σ).1 ≠ 0)
    (hself : (c.addr.evalT σ).1 = σ.tx.selfAddress.1)
    (hcall : TRun.call args (.rets rets) callee.ext callee.runR σ =
      .error (.revertWith d)) :
    TRun.tryCall c rets ok.ext ok.runR err.ext err.runR code pnc.ext pnc.runR
        other.ext other.runR args callee.ext callee.runR true σ =
      match Semantics.decodeError d with
      | some _ => (err.runR σ).map (fun o => ⟨o.st.drop err.ext, o.ext⟩)
      | none => match Semantics.decodePanic d with
        | some n => (pnc.runR (σ.withEnv
            (TEnv.append κ (code.decodeT (H := σ.H) n) σ.env))).map
            (fun o => ⟨o.st.drop ((Ext.append Γ κ).trans pnc.ext), o.ext⟩)
        | none => (other.runR σ).map (fun o => ⟨o.st.drop other.ext, o.ext⟩) := by
  have hc : decide ((c.addr.evalT σ).1 = σ.tx.selfAddress.1) = true :=
    by simp only [hself, decide_true]
  simp only [TRun.tryCall, if_neg hnz, hc, Bool.and_self,
    ite_true, hcall]
  cases Semantics.decodeError d <;> cases Semantics.decodePanic d <;> rfl

/-- Failure bytes are extracted by `catchBytes`, decoded by the existing codec,
allocated as a fresh object, consumed by the clause, then popped with its locals.
Only the heap-extension certificate is erased; no desired frame preservation is assumed. -/
theorem catch_allocated {Γb : Ctx} (c : ExtCall C Γ) (rets : Binders ρ)
    (args : Args C Γ ps) (callee : Prog C (ρ ++ ps) Γf)
    (kind : CatchKind) (body : Prog C (.mem bytesR :: Γ) Γb)
    (σ : State C Γ) (d bs : List UInt8)
    (hnz : (c.addr.evalT σ).1 ≠ 0)
    (hself : (c.addr.evalT σ).1 = σ.tx.selfAddress.1)
    (hcall : TRun.call args (.rets rets) callee.ext callee.runR σ =
      .error (THalt.ofData d)) (hdecode : kind.decode d = some bs) :
    (TRun.catchData c rets args callee.ext callee.runR true kind body.ext body.runR σ).map
        (·.st) =
      (body.runR (σ.allocPush (bytesObj σ.H bs (kind.decode_lt hdecode)))).map
        (fun o => o.st.drop ((Ext.push .refl).trans body.ext)) := by
  rw [TRun.catchData_self_data c rets args callee.ext callee.runR kind body.ext
    body.runR σ d bs hnz hself hcall hdecode]
  have ha := TRun.litBytesT_alloc σ bs (kind.decode_lt hdecode) body.runR
  cases hl : TRun.litBytesT bs body.runR σ with
  | error e =>
    rw [hl] at ha
    cases hb : body.runR (σ.allocPush (bytesObj σ.H bs (kind.decode_lt hdecode))) with
    | error e' => rw [hb] at ha; cases ha; rfl
    | ok o => rw [hb] at ha; cases ha
  | ok o =>
    rw [hl] at ha
    cases hb : body.runR (σ.allocPush (bytesObj σ.H bs (kind.decode_lt hdecode))) with
    | error e => rw [hb] at ha; cases ha
    | ok o' => rw [hb] at ha; exact congrArg (fun s => Except.ok
        (s.drop ((Ext.push .refl).trans body.ext))) (Except.ok.inj ha)

/-- info: 'Solidity.Backend.AbiWorld.CatchTransport.try_revertWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms try_revertWith
/-- info: 'Solidity.Backend.AbiWorld.CatchTransport.catch_allocated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms catch_allocated
end Solidity.Backend.AbiWorld.CatchTransport
