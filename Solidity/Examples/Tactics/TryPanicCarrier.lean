import Solidity.Evm.TryPanicCarrier
import Solidity.Examples.Tactics.TryPanicProducer

/-! Nonvacuous constructed-call controls. No source or target adequacy claim. -/
namespace Solidity.Examples.Tactics.TryPanicCarrier
open Evm.TryByteImage Evm.TryPanicProducer Evm.TryPanicCarrier
variable {C : Contract}

/-- Both tags retain a live object aliased by two real caller locals. -/
theorem live_both (C : Contract) : ∀ _p : Pipeline,
    TRun.catchBytes selfCall .nil args36 .refl carrier36.runR true
      (TryPanicProducer.aliasCaller C) = .ok computed36 := by
  intro _
  apply catch_halt
  change (7 : Int) ≠ 0
  decide

/-- Actual empty-return entry retains arbitrary heap and the entire global frame. -/
theorem entry_frame {Γ : Ctx} (σ : State C Γ) :
    let τ := (CallRet.enterT (CallRet.rets (Γ := Γ) .nil)
      (σ.withEnv (Δ := Input) (size36, ()))).st
    τ.H = σ.H ∧ τ.storage = σ.storage ∧ τ.tx = σ.tx ∧
      τ.net = σ.net ∧ τ.selfBalance = σ.selfBalance := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Same-shaped contexts do not identify the caller return with the f parameter. -/
theorem entry_parameter_not_caller_return (σ : State C Input) :
    TEnv.get sizeSlot (σ.withEnv (Δ := Input) (size36, ())).env = size36 := rfl

/-- A constant constructed body also runs at6: no false operational refusal. -/
theorem other_argument (C : Contract) (_p : Pipeline) :
    TRun.call (argsAt ⟨6, rfl⟩) (.rets .nil) .refl carrier36.runR
      (TryPanicProducer.aliasCaller C) = .error (THalt.ofData computed36) := by
  exact call_at_halt _ _

/-- A mismatched result cannot pass the actual catch observation. -/
theorem wrong_bytes {Γ : Ctx} (σ : State C Γ) (hnz : σ.tx.selfAddress.val ≠ 0)
    (bs : List UInt8) (hwrong : bs ≠ computed36) :
    TRun.catchBytes selfCall .nil args36 .refl carrier36.runR true σ ≠ .ok bs := by
  rw [catch_halt σ hnz]
  intro h
  exact hwrong (Except.ok.inj h).symm

/-- New catch allocation remains fresh; original caller aliases keep identity0. -/
theorem live_capture_ids (C : Contract) :
    let σ := TryPanicProducer.aliasCaller C
    let τ := σ.allocPush (bytesObj σ.H computed36 (by rw [computed36_length]; decide))
    (σ.alloc (bytesObj σ.H computed36 (by rw [computed36_length]; decide))).2.id = 1 ∧
      TEnv.get (.there .here) τ.env = TEnv.get (.there (.there .here)) τ.env := ⟨rfl, rfl⟩

/-- The data handler scope/Ext equation uses the derived call, not a premise. -/
theorem live_data_scope (C : Contract) :
    let σ := TryPanicProducer.aliasCaller C
    TRun.catchData selfCall .nil args36 .refl carrier36.runR true .raw .refl TRun.nil σ =
      (TRun.litBytesT computed36 TRun.nil σ).map
        (fun o => ⟨o.st.drop ((Ext.push .refl).trans .refl), o.ext⟩) := by
  apply data_transport
  change (7 : Int) ≠ 0
  decide

/-- A selected constructed Panic handler writes a distinct caller slot. -/
def normalTry {Γ : Ctx} (i : Idx Γ (.val .uint)) : TStep C Γ Γ :=
  TRun.tryCall selfCall .nil .refl TryPanicProducer.failClause
    .refl TryPanicProducer.failClause (.some (.user "c"))
    .refl (TRun.assignLocal (.there i) (.simple (.local .here)))
    .refl TryPanicProducer.failClause args36 .refl carrier36.runR true

theorem normal_return {Γ : Ctx} (i : Idx Γ (.val .uint)) (σ : State C Γ)
    (hnz : σ.tx.selfAddress.val ≠ 0) :
    normalTry i σ = .ok ⟨σ.setLocal i codeWord, List.prefix_refl _⟩ := by
  have hc := call_halt σ
  rw [TryPanicProducer.raw_halt] at hc
  have hs : (selfCall.addr.evalT σ).val = σ.tx.selfAddress.val := rfl
  simp only [normalTry, TRun.tryCall, hs, decide_true, Bool.true_and, hc,
    TryPanicProducer.no_error_decode, computed36_decode, if_neg hnz, if_true]
  rfl

/-- Live two-alias callers also have an inhabited selected-normal-return witness
in both tags; the callee's ghost allocation is rolled back, handler scope dropped. -/
theorem live_normal_both (C : Contract) :
    let σ := (TryPanicProducer.aliasCaller C).push (t := .val .uint) (⟨0, rfl⟩)
    ∀ _p : Pipeline, normalTry .here σ = .ok ⟨σ.setLocal .here codeWord, List.prefix_refl _⟩ := by
  dsimp only
  intro _
  apply normal_return
  change (7 : Int) ≠ 0
  decide

end Solidity.Examples.Tactics.TryPanicCarrier
