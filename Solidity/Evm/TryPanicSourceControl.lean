import Solidity.Frontend.SolcJson.TryPanicSourceCaller

/-! Concrete intrinsic normalization of c#105 control and Return94. The callee
is a parameter: this module neither replaces f#7 by a constant carrier nor
claims that an assembly body has been lowered. No H16 source semantics change. -/
namespace Solidity.Evm.TryPanicSourceControl
open TryPanicProducer TryPanicCarrier

abbrev Caller := Solidity.Frontend.TryPanicSourceCaller.CallerCtx
abbrev Handler := LTy.val .uint :: Caller
variable {C : Contract}

/-- Return94 assigns binder87 to the existing return slot74. This normalization
is specific to the terminal catch body; it is not a general early-return rule. -/
def return94 : Stmt C Handler Handler :=
  .assignLocal (.there .here) (.simple (.local .here))

def returnOut (σ : State C Handler) : Out C σ.H Handler :=
  ⟨σ.setLocal (.there .here) (TEnv.get .here σ.env), List.prefix_refl _⟩

theorem return94_run (σ : State C Handler) :
    Stmt.run σ return94 = .ok (returnOut σ) := rfl

/-- Both rejecting clauses remain real assert(false) programs. -/
def reject : Prog C Caller Caller :=
  .cons (.assert (.simple (.bool false))) .nil

def panicBody : Prog C Handler Handler :=
  .cons (.assert (.simple (.bool true))) (.cons return94 .nil)

def caller (body : Prog C Input Input) : Stmt C Caller Caller :=
  .tryCall selfCall .nil reject reject (.some (.user "c")) panicBody reject args36 body true

/-- Exact existing primitive, retaining its self/external, successful, raw
failure, decoded Error/Panic, depth and exhaustion alternatives. -/
def form (body : Prog C Input Input) : TStep C Caller Caller :=
  TRun.tryCall selfCall .nil
    .refl (TRun.assert (.simple (.bool false)))
    .refl (TRun.assert (.simple (.bool false))) (.some (.user "c"))
    .refl (TRun.seq (TRun.assert (.simple (.bool true))) return94.runR)
    .refl (TRun.assert (.simple (.bool false))) args36 .refl body.runR true

theorem caller_runR (body : Prog C Input Input) :
    (caller body).runR = form body := by
  rfl

/-- Arbitrary binder, arbitrary caller heap and transaction. -/
theorem returned_slot (σ : State C Handler) :
    TEnv.get (.there .here) (returnOut σ).st.env = TEnv.get .here σ.env := rfl

theorem return_frame (σ : State C Handler) :
    (returnOut σ).st.storage = σ.storage ∧
    (returnOut σ).st.tx = σ.tx ∧
    (returnOut σ).st.heap = σ.heap := by
  exact ⟨rfl, rfl, rfl⟩

/-- A zero receiver is rejected before the supplied body is invoked. -/
theorem zero_receiver (body : Prog C Input Input) (σ : State C Caller)
    (hz : σ.tx.selfAddress.val = 0) :
    Stmt.run σ (caller body) = .error .revert := by
  change form body σ = _
  simp only [form, TRun.tryCall, show (selfCall.addr.evalT σ).val = 0 from hz, if_pos]

/-- Generic finite-image realization, retaining the original local length.
This is the remaining body producer obligation, not an inhabitant or a chosen
child outcome. It cannot be replaced by the fixed carrier36. -/
def BodyRealizes (body : Prog C Input Input) : Prop :=
  ∀ (σ : State C Input) (key : TryByteImage.FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K)
    (fits : (TEnv.get sizeSlot σ.env).val.toNat ≤ K),
    body.runR σ = .error (THalt.ofData
      (TryPanicSourceFrame.dataK σ key K aligned large fits))

/-- No independently supplied final image or reply is needed: completion
inversion and uniqueness connect the producer to the SAME finite entry. -/
theorem body_completed (body : Prog C Input Input) (realizes : BodyRealizes body)
    (σ : State C Input) (key : TryByteImage.FrameKey) (K : Nat)
    (aligned : ∃ k, K = k*32) (large : 96 ≤ K)
    (μ final : TryByteImage.FrameMem C Input) (bytes : List UInt8)
    (entry : TryPanicSourceFrame.FiniteEntry σ key K aligned large μ)
    (completed : TryPanicSourcePlan.BodyCompletedAt TryPanicSourcePlan.originalOps μ final bytes) :
    body.runR σ = .error (THalt.ofData bytes) := by
  subst μ
  obtain ⟨_, fits, _, _⟩ := TryPanicSourceDeterminism.completed_exact completed
  have same : bytes = TryPanicSourceFrame.dataK σ key K aligned large fits :=
    (TryPanicSourceDeterminism.completion_unique completed
      (TryPanicSourceFrame.completed_generic σ key K aligned large fits)).2
  rw [same]
  exact realizes σ key K aligned large fits

/-- Generic realization supplies the actual argument36 invocation as a
consequence. Installation and the compiled-EVM frame are not claimed. -/
theorem body_at36 (body : Prog C Input Input) (realizes : BodyRealizes body)
    (σ : State C Input) (key : TryByteImage.FrameKey)
    (size : TEnv.get sizeSlot σ.env = size36) :
    body.runR σ = .error (THalt.ofData computed36) := by
  have fits : (TEnv.get sizeSlot σ.env).val.toNat ≤ 96 := by
    rw [size]
    decide
  have result : body.runR σ = .error (THalt.ofData
      (TryPanicSourceFrame.dataK σ key 96 ⟨3, rfl⟩ (by decide) fits)) :=
    realizes σ key 96 ⟨3, rfl⟩ (by decide) fits
  rw [TryPanicSourceFrame.data36_computed σ key 96 ⟨3, rfl⟩ (by decide) size fits] at result
  exact result

/-- SAME-call raw Panic branch. The byte/child-run conditions are explicitly
branch inputs here, not original f execution or installation certificates. -/
theorem panic_return (body : Prog C Input Input) (σ : State C Caller)
    (data : List UInt8) (code : Semantics.Word) (nonzero : σ.tx.selfAddress.val ≠ 0)
    (called : TRun.call args36 (.rets .nil) .refl body.runR σ =
      .error (.revertWith data))
    (notError : Semantics.decodeError data = none)
    (panic : Semantics.decodePanic data = some code) :
    Stmt.run σ (caller body) =
      .ok ⟨σ.setLocal .here code, List.prefix_refl _⟩ := by
  change form body σ = _
  have own : (selfCall.addr.evalT σ).val = σ.tx.selfAddress.val := rfl
  simp only [form, TRun.tryCall, own, if_neg nonzero, decide_true, Bool.true_and,
    if_true, Binders.toRet, called, notError, panic]
  rfl

/-- Generic assembly realization, not a raw reply hypothesis, suffices to
supply the argument36 call branch consumed by panic_return. -/
theorem call_at36 (body : Prog C Input Input) (realizes : BodyRealizes body)
    (σ : State C Caller) (key : TryByteImage.FrameKey) :
    TRun.call args36 (.rets .nil) .refl body.runR σ =
      .error (THalt.ofData computed36) := by
  unfold TRun.call
  rw [args36_eval]
  change (body.runR (σ.withEnv (size36, ()))).map _ = _
  rw [body_at36 body realizes (σ.withEnv (size36, ())) key rfl]
  rfl

/-- Concrete caller client: Return94 and caller control are discharged, while
the generic body realization and actual nonzero receiver remain explicit.
No separate chosen raw reply or successful caller-run premise is used. -/
theorem caller_at36 (body : Prog C Input Input) (realizes : BodyRealizes body)
    (σ : State C Caller) (key : TryByteImage.FrameKey)
    (nonzero : σ.tx.selfAddress.val ≠ 0) :
    Stmt.run σ (caller body) =
      .ok ⟨σ.setLocal .here codeWord, List.prefix_refl _⟩ := by
  apply panic_return body σ computed36 codeWord nonzero
  · have call : TRun.call args36 (.rets .nil) .refl body.runR σ =
        .error (THalt.ofData computed36) := call_at36 body realizes σ key
    have raw : THalt.ofData computed36 = .revertWith computed36 := by
      rw [computed36_panic]
      rfl
    rw [raw] at call
    exact call
  · decide +kernel
  · exact computed36_decode

/-- Nonvacuous constructed-control client, using the already checked fixed
carrier. This does NOT instantiate BodyRealizes or identify the original f. -/
theorem carrier_control (σ : State C Caller) (nonzero : σ.tx.selfAddress.val ≠ 0) :
    Stmt.run σ (caller carrier36) =
      .ok ⟨σ.setLocal .here codeWord, List.prefix_refl _⟩ := by
  apply panic_return carrier36 σ computed36 codeWord nonzero
  · have call : TRun.call args36 (.rets .nil) .refl carrier36.runR σ =
        .error (THalt.ofData computed36) := TryPanicCarrier.call_halt σ
    have raw : THalt.ofData computed36 = .revertWith computed36 := by
      rw [computed36_panic]
      rfl
    rw [raw] at call
    exact call
  · decide +kernel
  · exact computed36_decode

end Solidity.Evm.TryPanicSourceControl
