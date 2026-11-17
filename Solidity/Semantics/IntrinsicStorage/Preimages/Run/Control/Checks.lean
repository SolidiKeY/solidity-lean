import Solidity.Semantics.IntrinsicStorage.Preimages.Run.Control

/-! Regressions for the observed control-flow steps under sequencing: a
continuation sees exactly the actual typed result, and a failing actual run
skips the continuation and keeps the inputs observed up to the failure. -/
namespace Solidity.Semantics.IntrinsicStorage.Observe.Run.Control.Checks

open Solidity.Storage
open Solidity.Semantics.IntrinsicStorage.Observe.Run
variable {C : Contract} {Γ : Ctx}

section Continuation
variable {β : Type} (σ : State C Γ) (f : Out C σ.H Γ → Audit β)

-- A conditional hands the continuation the actual branch output.
example {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (h₁ : Ext Γ Γ₁) (thn : Step C Γ Γ₁)
    (h₂ : Ext Γ Γ₂) (els : Step C Γ Γ₂) :
    (ite c h₁ thn h₂ els σ >>= f).result =
      (TRun.ite c h₁ (project thn) h₂ (project els) σ >>= fun o => (f o).result) := by
  simp only [Audit.result_bind, ite_result]

-- A bounded loop and a block, run with the actual loop fuel.
example {Γ₁ : Ctx} (n : Nat) (c : Val C Γ .bool) (h : Ext Γ Γ₁) (body : Step C Γ Γ₁) :
    (loop n c h body σ >>= f).result =
      (TRun.loopF n c h (project body) σ >>= fun o => (f o).result) ∧
    (block h body σ >>= f).result =
      (TRun.block h (project body) σ >>= fun o => (f o).result) := by
  simp only [Audit.result_bind, loop_result, block_result, and_self]

-- An internal call, alone and followed by a receiver operation or push.
example {ps rs Γf Γv : Ctx} {E : Ty} (a : Args C Γ ps) (ret : CallRet Γ rs Γ)
    (hb : Ext (rs ++ ps) Γf) (body : Step C (rs ++ ps) Γf) (r : Var)
    (hr : Ext ([.alias (.array E)] ++ ps) Γf) (rbody : Step C ([.alias (.array E)] ++ ps) Γf)
    (op : ReceiverOp C Γ E) (he : Ext Γ Γv) (code : Step C Γ Γv) (v : Src C Γv E) :
    (call a ret hb body σ >>= f).result =
      (TRun.call a ret hb (project body) σ >>= fun o => (f o).result) ∧
    (callReceiver a r hr rbody op σ >>= f).result =
      (TRun.callReceiver a r hr (project rbody) op σ >>= fun o => (f o).result) ∧
    (callReceiverPush a r hr rbody he code v σ >>= f).result =
      (TRun.callReceiverPush a r hr (project rbody) he (project code) v σ >>=
        fun o => (f o).result) := by
  simp only [Audit.result_bind, call_result, callReceiver_result, callReceiverPush_result,
    and_self]

-- `try` over every handler, and the reverting catch clause with its data.
example {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf Γc : Ctx} (ec : ExtCall C Γ) (rets : Binders ρ)
    (h₁ : Ext (ρ ++ Γ) Γ₁) (ok : Step C (ρ ++ Γ) Γ₁) (h₂ : Ext Γ Γ₂) (err : Step C Γ Γ₂)
    (code : CodeBinder κ) (h₃ : Ext (κ ++ Γ) Γ₃) (pnc : Step C (κ ++ Γ) Γ₃)
    (h₄ : Ext Γ Γ₄) (other : Step C Γ Γ₄) (sargs : Args C Γ ps) (hs : Ext (ρ ++ ps) Γf)
    (sbody : Step C (ρ ++ ps) Γf) (self : Bool) (kind : CatchKind)
    (hc : Ext (.mem bytesR :: Γ) Γc) (cbody : Step C (.mem bytesR :: Γ) Γc) :
    (tryCall ec rets h₁ ok h₂ err code h₃ pnc h₄ other sargs hs sbody self σ >>= f).result =
      (TRun.tryCall ec rets h₁ (project ok) h₂ (project err) code h₃ (project pnc) h₄
        (project other) sargs hs (project sbody) self σ >>= fun o => (f o).result) ∧
    (catchData ec rets sargs hs sbody self kind hc cbody σ >>= f).result =
      (TRun.catchData ec rets sargs hs (project sbody) self kind hc (project cbody) σ >>=
        fun o => (f o).result) := by
  simp only [Audit.result_bind, tryCall_result, catchData_result, and_self]

-- Sequencing and the empty program.
example (s p : Step C Γ Γ) :
    (seq s p σ >>= f).result = (TRun.seq (project s) (project p) σ >>= fun o => (f o).result) ∧
    (nil σ >>= f).result = (TRun.nil σ >>= fun o => (f o).result) := by
  simp only [Audit.result_bind, seq_result, nil_result, and_self]

-- A conditional whose condition fails keeps the inputs the condition hashed.
example {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (h₁ : Ext Γ Γ₁) (thn : Step C Γ Γ₁)
    (h₂ : Ext Γ Γ₂) (els : Step C Γ Γ₂) (e : THalt) (h : (value σ c).result = .error e) :
    (ite c h₁ thn h₂ els σ).inputs = (value σ c).inputs :=
  Audit.failed_bind _ _ h

-- A failed `try` skips the continuation with the actual halt and keeps its inputs.
example {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} (ec : ExtCall C Γ) (rets : Binders ρ)
    (h₁ : Ext (ρ ++ Γ) Γ₁) (ok : Step C (ρ ++ Γ) Γ₁) (h₂ : Ext Γ Γ₂) (err : Step C Γ Γ₂)
    (code : CodeBinder κ) (h₃ : Ext (κ ++ Γ) Γ₃) (pnc : Step C (κ ++ Γ) Γ₃)
    (h₄ : Ext Γ Γ₄) (other : Step C Γ Γ₄) (sargs : Args C Γ ps) (hs : Ext (ρ ++ ps) Γf)
    (sbody : Step C (ρ ++ ps) Γf) (self : Bool) (e : THalt)
    (h : TRun.tryCall ec rets h₁ (project ok) h₂ (project err) code h₃ (project pnc) h₄
      (project other) sargs hs (project sbody) self σ = .error e) :
    (tryCall ec rets h₁ ok h₂ err code h₃ pnc h₄ other sargs hs sbody self σ >>= f).result =
      .error e ∧
    (tryCall ec rets h₁ ok h₂ err code h₃ pnc h₄ other sargs hs sbody self σ >>= f).inputs =
      (tryCall ec rets h₁ ok h₂ err code h₃ pnc h₄ other sargs hs sbody self σ).inputs :=
  ⟨by rw [Audit.result_bind, tryCall_result, h]; rfl,
   Audit.failed_bind _ f ((tryCall_result ..).trans h)⟩

-- A failed call skips the continuation and keeps the inputs of the call.
example {ps rs Γf : Ctx} (a : Args C Γ ps) (ret : CallRet Γ rs Γ) (hb : Ext (rs ++ ps) Γf)
    (body : Step C (rs ++ ps) Γf) (e : THalt)
    (h : TRun.call a ret hb (project body) σ = .error e) :
    (call a ret hb body σ >>= f).inputs = (call a ret hb body σ).inputs :=
  Audit.failed_bind _ f ((call_result ..).trans h)

-- A loop out of fuel diverges, and revert data halts with the data it evaluates.
example (c : Val C Γ .bool) (body : Step C Γ Γ) (d : List (RevPart C Γ)) :
    (loop 0 c .refl body σ).result = .error .diverge ∧
    (revertData d σ >>= f).result = (TRun.revertData d σ >>= fun o => (f o).result) := by
  simp only [Audit.result_bind, revertData_result, and_true]; rfl

-- A receiver operation alone, and the catch bytes a reverting `try` hands its clause.
example {ρ ps Γf : Ctx} {T : Ty} (op : ReceiverOp C Γ T) (b : SPath C Γ (.array T))
    (ec : ExtCall C Γ) (rets : Binders ρ) (sargs : Args C Γ ps) (hs : Ext (ρ ++ ps) Γf)
    (sbody : Step C (ρ ++ ps) Γf) (self : Bool) (g : List UInt8 → Audit β) :
    (receiverOp op b σ >>= f).result = (TRun.receiverOp op b σ >>= fun o => (f o).result) ∧
    (catchBytes ec rets sargs hs sbody self σ >>= g).result =
      (TRun.catchBytes ec rets sargs hs (project sbody) self σ >>= fun d => (g d).result) := by
  simp only [Audit.result_bind, receiverOp_result, catchBytes_result, and_self]

end Continuation

-- Literal revert bytes are written in order before the catch body runs.
example {Γ₁ : Ctx} (bs : List UInt8) (k : Step C (.mem bytesR :: Γ) Γ₁) (σ : State C Γ) :
    (litBytes bs k σ).result = TRun.litBytesT bs (project k) σ := litBytes_result bs k σ

end Solidity.Semantics.IntrinsicStorage.Observe.Run.Control.Checks
