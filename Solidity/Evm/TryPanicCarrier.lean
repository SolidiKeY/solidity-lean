import Solidity.Evm.TryPanicProducer

/-! Closed intrinsic constructed-call carrier. No original-source construction,
bytecode adequacy, callback change or source admission is asserted. -/
namespace Solidity.Evm.TryPanicCarrier
open TryByteImage TryPanicProducer
variable {C : Contract} {Γ : Ctx}

private theorem map_error_inv {α β ε : Type} (a : Except ε α) (f : α → β) (e : ε)
    (h : a.map f = .error e) : a = .error e := by
  cases a with
  | error x => cases h; rfl
  | ok x => cases h

/-- Existing syntax allocates bytes and immediately reads the actual new object. -/
def rawTail : Prog C (.mem bytesR :: Γ) (.mem bytesR :: Γ) :=
  .cons (.revertData [.mem .raw .here]) .nil

def inner : Prog C Γ (.mem bytesR :: Γ) :=
  litBytes (.user "ghost") computed36 rawTail

/-- The ghost local is scoped; this constant body is not generic source f(uint). -/
def carrier36 : Prog C Input Input := .cons (.block inner) .nil

private theorem allocated_tail (σ : State C Γ) :
    rawTail.runR (σ.allocPush (bytesObj σ.H computed36
      (by rw [computed36_length]; decide))) = .error (THalt.ofData computed36) := by
  rw [Prog.runR_eq]
  change TRun.seq (TRun.revertData [.mem .raw .here]) TRun.nil
    (σ.allocPush (bytesObj σ.H computed36 (by rw [computed36_length]; decide))) = _
  rw [TRun.seq, TRun.revertData_mem (σ.allocPush (bytesObj σ.H computed36
      (by rw [computed36_length]; decide))) .raw .here
      (σ.alloc (bytesObj σ.H computed36 (by rw [computed36_length]; decide))).2 rfl,
    captureBytes_read]

theorem inner_halt (σ : State C Γ) :
    Prog.run σ inner = .error (THalt.ofData computed36) := by
  rw [inner, Prog.run_litBytes]
  apply map_error_inv _ (fun o => o.st)
  have h := TRun.litBytesT_alloc σ computed36
    (by rw [computed36_length]; decide) rawTail.runR
  rw [allocated_tail] at h
  exact h

theorem carrier36_halt (σ : State C Input) :
    Prog.run σ carrier36 = .error (THalt.ofData computed36) := by
  change TRun.seq (TRun.block _ inner.runR) TRun.nil σ = _
  have h : inner.runR σ = .error (THalt.ofData computed36) := inner_halt σ
  simp only [TRun.seq, TRun.block, h, Except.map]

def args36 : Args C Γ Input :=
  .snoc .nil .uint (.user "size") (.simple (.lit 36 rfl))

theorem args36_eval (σ : State C Γ) :
    Args.evalT σ args36 = .ok (size36, ()) := rfl

theorem empty_entry (σ : State C Γ) :
    CallRet.enterT (CallRet.rets (Γ := Γ) .nil) (σ.withEnv (Δ := Input) (size36, ())) =
      ⟨σ.withEnv (Δ := Input) (size36, ()), List.prefix_refl _⟩ := rfl

theorem call_halt (σ : State C Γ) :
    TRun.call args36 (.rets .nil) .refl carrier36.runR σ =
      .error (THalt.ofData computed36) := by
  unfold TRun.call
  rw [args36_eval]
  change (carrier36.runR (σ.withEnv (Δ := Input) (size36, ()))).map _ = _
  rw [show carrier36.runR (σ.withEnv (Δ := Input) (size36, ())) =
      .error (THalt.ofData computed36) from carrier36_halt _]
  rfl

/-- Actual receiver, arbitrary caller heap; no oracle or synthetic address. -/
def selfCall : ExtCall C Γ :=
  ⟨.env .selfAddress rfl, "f", [⟨.uint, .lit 36 rfl⟩]⟩

theorem catch_halt (σ : State C Γ) (hnz : σ.tx.selfAddress.val ≠ 0) :
    TRun.catchBytes selfCall .nil args36 .refl carrier36.runR true σ =
      .ok computed36 := by
  apply TRun.catchBytes_self_data
  · exact hnz
  · rfl
  · exact call_halt σ

/-- Pipeline labels are provenance only, not emitted-byte correctness. -/
theorem both_tags (σ : State C Γ) (hnz : σ.tx.selfAddress.val ≠ 0) :
    ∀ _p : Pipeline, TRun.catchBytes selfCall .nil args36 .refl carrier36.runR true σ =
      .ok computed36 := fun _ => catch_halt σ hnz

/-- Same fixed constructed body also runs for other scalar arguments. No refusal
of a source/provenance certificate is promoted to an operational failure. -/
def argsAt (n : U256) : Args C Γ Input :=
  .snoc .nil .uint (.user "size") (.simple (.lit n.val n.property))

theorem call_at_halt (n : U256) (σ : State C Γ) :
    TRun.call (argsAt n) (.rets .nil) .refl carrier36.runR σ =
      .error (THalt.ofData computed36) := by
  unfold TRun.call
  simp only [argsAt, Args.evalT, Val.evalT, Simple.evalT, bind, Except.bind,
    pure, Except.pure]
  rw [show (carrier36 (C := C)).runR =
    (fun _ => .error (THalt.ofData computed36)) from funext carrier36_halt]

theorem zero_receiver (σ : State C Γ) (hz : σ.tx.selfAddress.val = 0) :
    TRun.catchBytes selfCall .nil args36 .refl carrier36.runR true σ = .error .revert := by
  have h : (selfCall.addr.evalT σ).val = 0 := hz
  simp only [TRun.catchBytes, h, if_pos]

theorem external_empty (σ : State C Γ) (hnz : σ.tx.selfAddress.val ≠ 0)
    (he : σ.tx.ext = []) :
    TRun.catchBytes selfCall .nil args36 .refl carrier36.runR false σ = .error .revert := by
  have h : (selfCall.addr.evalT σ).val ≠ 0 := hnz
  simp only [TRun.catchBytes, if_neg h, Bool.false_and, Bool.false_eq_true,
    he, Semantics.lookupBy, if_false]

/-- Reuse actual catch-data allocation/scope/Ext transport, with hcall derived. -/
theorem data_transport {Γ₁ : Ctx} (h : Ext (.mem bytesR :: Γ) Γ₁)
    (body : TStep C (.mem bytesR :: Γ) Γ₁) (σ : State C Γ)
    (hnz : σ.tx.selfAddress.val ≠ 0) :
    TRun.catchData selfCall .nil args36 .refl carrier36.runR true .raw h body σ =
      (TRun.litBytesT computed36 body σ).map
        (fun o => ⟨o.st.drop ((Ext.push .refl).trans h), o.ext⟩) := by
  apply TRun.catchData_self_data
  · exact hnz
  · rfl
  · exact call_halt σ
  · rfl

end Solidity.Evm.TryPanicCarrier
