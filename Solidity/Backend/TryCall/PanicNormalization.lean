import Solidity.Evm.TryPanicSourceExecution

/-! Known-self Panic normalization for the checked try-call specialization.
The two primitive proofs reuse the owned source checkpoint 2ae124d153a2;
master still exposes them as parameters. No H16 source module is edited.
This is a source equation, not a compiled-code or deployment association. -/
namespace Solidity.Backend.TryCall.PanicNormalization
open Evm Evm.TryByteImage Evm.TryPanicProducer Evm.TryPanicSourceBody
variable {C : Contract}

theorem put_then : PutThen (C := C) := by
  intro σ o i b k length
  simp only [TRun.seq, put_run σ o i b length]
  cases k (σ.allocPush (if i.val < o.1.length
    then MObj.setElem .dyn o i.val (byteWord b) else o)) <;> rfl

theorem allocate_run : AllocateRun (C := C) := by
  intro σ
  let n : Nat := (TEnv.get sizeSlot σ.env).val.toNat
  have bound : n < 2^256 := input_bound σ
  have nonneg : 0 ≤ (TEnv.get sizeSlot σ.env).val := by
    have range : PrimTy.uint.inRange (TEnv.get sizeSlot σ.env).val = true :=
      (TEnv.get sizeSlot σ.env).property
    simp only [PrimTy.inRange, decide_eq_true_eq] at range
    exact range.1
  have input : TEnv.get sizeSlot σ.env =
      PrimTy.ofLit .uint (n : Int) (PrimTy.inRange_uint_of_lt bound) := by
    apply Subtype.ext
    change (TEnv.get sizeSlot σ.env).val = (n : Int)
    dsimp only [n]
    omega
  have same : TRun.declMem bytesR (some (.newArr (.local sizeSlot) rfl)) rfl σ =
      TRun.declMem bytesR
        (some (.newArr (.lit (n : Int) (PrimTy.inRange_uint_of_lt bound)) rfl)) rfl σ := by
    exact congrArg (fun v : PrimTy.uint.Denote =>
      let g := σ.copyStToMG (newArrT bytesR v rfl) rfl
      (Except.ok ⟨g.st.push (t := .mem bytesR) (some g.val), g.ext⟩ :
        TRes (Out C σ.H Buffer))) input
  exact same.trans (TRun.declMem_newArr_bytes σ n bound)

/-- The actual generic body, not a selected reply, supplies the catch result. -/
theorem nonzero (σ : State C Evm.TryPanicSourceControl.Caller) (key : FrameKey)
    (active : σ.tx.selfAddress.val ≠ 0) :
    Stmt.run σ (Evm.TryPanicSourceControl.caller body) =
      .ok ⟨σ.setLocal .here codeWord, List.prefix_refl _⟩ :=
  Evm.TryPanicSourceExecution.caller_return put_then allocate_run σ key active

/-- Zero receiver remains a real bare revert before the generic body. -/
theorem zero (σ : State C Evm.TryPanicSourceControl.Caller)
    (inactive : σ.tx.selfAddress.val = 0) :
    Stmt.run σ (Evm.TryPanicSourceControl.caller body) = .error .revert :=
  Evm.TryPanicSourceControl.zero_receiver body σ inactive

/-- All source outcomes are classified without a successful-run premise. -/
theorem all_outcomes (σ : State C Evm.TryPanicSourceControl.Caller) (key : FrameKey) :
    Stmt.run σ (Evm.TryPanicSourceControl.caller body) =
      if σ.tx.selfAddress.val = 0 then .error .revert
      else .ok ⟨σ.setLocal .here codeWord, List.prefix_refl _⟩ := by
  by_cases active : σ.tx.selfAddress.val = 0
  · rw [if_pos active]
    exact zero σ active
  · rw [if_neg active]
    exact nonzero σ key active

end Solidity.Backend.TryCall.PanicNormalization
