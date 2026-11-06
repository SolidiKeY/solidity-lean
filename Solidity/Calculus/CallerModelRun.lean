import Solidity.Calculus.CallerModel

/-!
# The runs under a caller model

`ExecSM M J` (`Calculus/CallerModel.lean`) against `ExecS J`
(`Semantics/Callback.lean`), proved once per constructor:

* **weakening of the attacker** (`ExecSM.mono`, `ExecPM.mono`,
  `ExecFM.mono`): a run under a model is one under any model allowing more;
* **`any` is today's reading** (`ExecSM.toExecS` and `ExecS.ofExecSM`, for
  programs and frames too): a run under any model is a callback run, and a
  callback run is one under `any`;
* **the deterministic run is a run under every model** (`Stmt.execM_run`,
  `Prog.execM_run`, `Frames.execM_run`), as `Prog.exec_run` is for `ExecS`:
  its callees change nothing, which every model allows
  (`CallerModel.allows_refl`).

The proofs follow `Semantics/Callback.lean`'s constructor by constructor
(`Prog.exec_run`'s is its copy, a resumption given `allows_refl`).
-/

namespace Solidity

open Semantics (Word lookupBy)
open Solidity (Modality)

variable {C : Contract}

section Mono

variable {M M' : CallerModel C} {J : StateInv C}

mutual

/-- **A run under `M` is a run under any `M'` allowing more.** -/
theorem ExecSM.mono (hA : ∀ {Γ : Ctx} (σ : State C Γ) st nt sb, M.Allows J σ st nt sb → M'.Allows J σ st nt sb) : {Γ Γ' : Ctx} → {σ : State C Γ} → {s : Stmt C Γ Γ'} →
    {o : COut C σ.H Γ'} → ExecSM M J σ s o → ExecSM M' J σ s o
  | _, _, _, _, _, .det a0 => .det a0
  | _, _, _, _, _, .transferHalt a0 a1 => .transferHalt a0 a1
  | _, _, _, _, _, .transferViolated a0 a1 a2 => .transferViolated a0 a1 a2
  | _, _, _, _, _, .transferResume a0 a1 a2 a3 a4 => .transferResume a0 a1 a2 a3 (hA _ _ _ _ a4)
  | _, _, _, _, _, .sendHalt a0 a1 => .sendHalt a0 a1
  | _, _, _, _, _, .sendFailed a0 a1 => .sendFailed a0 a1
  | _, _, _, _, _, .sendRefused a0 a1 => .sendRefused a0 a1
  | _, _, _, _, _, .sendViolated a0 a1 a2 => .sendViolated a0 a1 a2
  | _, _, _, _, _, .sendResume a0 a1 a2 a3 a4 => .sendResume a0 a1 a2 a3 (hA _ _ _ _ a4)
  | _, _, _, _, _, .iteHalt a0 => .iteHalt a0
  | _, _, _, _, _, .iteThen a0 a1 => .iteThen a0 (ExecPM.mono hA a1)
  | _, _, _, _, _, .iteElse a0 a1 => .iteElse a0 (ExecPM.mono hA a1)
  | _, _, _, _, _, .callArgs a0 => .callArgs a0
  | _, _, _, _, _, .callBody a0 a1 => .callBody a0 (ExecPM.mono hA a1)
  | _, _, _, _, _, .callRec a0 => .callRec (ExecSM.mono hA a0)
  | _, _, _, _, _, .callReceiver a0 => .callReceiver (ExecSM.mono hA a0)
  | _, _, _, _, _, .callReceiverPush a0 a1 a2 => .callReceiverPush (ExecSM.mono hA a0) a1 (ExecPM.mono hA a2)
  | _, _, _, _, _, .callReceiverPushUnset a0 a1 => .callReceiverPushUnset (ExecSM.mono hA a0) a1
  | _, _, _, _, _, .callReceiverPushHalt a0 => .callReceiverPushHalt (ExecSM.mono hA a0)
  | _, _, _, _, _, .callReceiverPushViolated a0 => .callReceiverPushViolated (ExecSM.mono hA a0)
  | _, _, _, _, _, .tryRevert => .tryRevert
  | _, _, _, _, _, .tryDecode a0 => .tryDecode a0
  | _, _, _, _, _, .tryViolated a0 => .tryViolated a0
  | _, _, _, _, _, .tryOk a0 a1 a2 a3 a4 a5 => .tryOk a0 a1 (hA _ _ _ _ a2) a3 (ExecPM.mono hA a4) a5
  | _, _, _, _, _, .tryError a0 a1 => .tryError a0 (ExecPM.mono hA a1)
  | _, _, _, _, _, .tryPanic a0 a1 => .tryPanic a0 (ExecPM.mono hA a1)
  | _, _, _, _, _, .tryOther a0 a1 => .tryOther a0 (ExecPM.mono hA a1)
  | _, _, _, _, _, .trySelfOk a0 a1 a2 a3 => .trySelfOk a0 a1 (ExecSM.mono hA a2) (ExecPM.mono hA a3)
  | _, _, _, _, _, .trySelfHalt a0 a1 a2 a3 a4 a5 => .trySelfHalt a0 a1 (ExecSM.mono hA a2) a3 a4 a5
  | _, _, _, _, _, .trySelfError a0 a1 a2 a3 => .trySelfError a0 a1 (ExecSM.mono hA a2) (ExecPM.mono hA a3)
  | _, _, _, _, _, .trySelfOther a0 a1 a2 a3 a4 => .trySelfOther a0 a1 (ExecSM.mono hA a2) a3 (ExecPM.mono hA a4)
  | _, _, _, _, _, .trySelfPanic a0 a1 a2 a3 a4 => .trySelfPanic a0 a1 (ExecSM.mono hA a2) a3 (ExecPM.mono hA a4)
  | _, _, _, _, _, .trySelfViolated a0 a1 a2 => .trySelfViolated a0 a1 (ExecSM.mono hA a2)
  | _, _, _, _, _, .loopHalt a0 a1 => .loopHalt a0 a1
  | _, _, _, _, _, .loopExit a0 a1 => .loopExit a0 a1
  | _, _, _, _, _, .loopIter a0 a1 a2 a3 => .loopIter a0 a1 (ExecPM.mono hA a2) (ExecSM.mono hA a3)
  | _, _, _, _, _, .loopStop a0 a1 a2 a3 => .loopStop a0 a1 (ExecPM.mono hA a2) a3
  | _, _, _, _, _, .loopDiverge a0 => .loopDiverge a0
  | _, _, _, _, _, .block a0 a1 => .block a0 (ExecPM.mono hA a1)
  | _, _, _, _, _, .catchDataHalt a0 a1 => .catchDataHalt a0 a1
  | _, _, _, _, _, .catchDataBody a0 a1 a2 => .catchDataBody a0 a1 (ExecPM.mono hA a2)
  termination_by structural _ _ _ _ _ h => h

/-- The same, for a sequence. -/
theorem ExecPM.mono (hA : ∀ {Γ : Ctx} (σ : State C Γ) st nt sb, M.Allows J σ st nt sb → M'.Allows J σ st nt sb) : {Γ Γ' : Ctx} → {σ : State C Γ} → {P : Prog C Γ Γ'} →
    {o : COut C σ.H Γ'} → ExecPM M J σ P o → ExecPM M' J σ P o
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .cons a0 a1 => .cons (ExecSM.mono hA a0) (ExecPM.mono hA a1)
  | _, _, _, _, _, .halt a0 => .halt (ExecSM.mono hA a0)
  | _, _, _, _, _, .violated a0 => .violated (ExecSM.mono hA a0)
  termination_by structural _ _ _ _ _ h => h

end

/-- The same, for the frames. -/
theorem ExecFM.mono (hA : ∀ {Γ : Ctx} (σ : State C Γ) st nt sb, M.Allows J σ st nt sb → M'.Allows J σ st nt sb) {Γ₀ : Ctx} : {Γ : Ctx} → {σ : State C Γ} → {κ : Frames C Γ Γ₀} →
    {o : COut C σ.H Γ₀} → ExecFM M J (Γ₀ := Γ₀) σ κ o → ExecFM M' J (Γ₀ := Γ₀) σ κ o
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .seq a0 a1 => .seq (ExecPM.mono hA a0) (ExecFM.mono hA a1)
  | _, _, _, _, .seqHalt a0 => .seqHalt (ExecPM.mono hA a0)
  | _, _, _, _, .seqViolated a0 => .seqViolated (ExecPM.mono hA a0)
  | _, _, _, _, .pop a0 => .pop (ExecFM.mono hA a0)
  | _, _, _, _, .drop a0 => .drop (ExecFM.mono hA a0)

end Mono

section Any

variable {M : CallerModel C} {J : StateInv C}

mutual

/-- **A run under a caller model is a callback run**: drop what the model
asks of each resumption. -/
theorem ExecSM.toExecS : {Γ Γ' : Ctx} → {σ : State C Γ} → {s : Stmt C Γ Γ'} →
    {o : COut C σ.H Γ'} → ExecSM M J σ s o → ExecS J σ s o
  | _, _, _, _, _, .det a0 => .det a0
  | _, _, _, _, _, .transferHalt a0 a1 => .transferHalt a0 a1
  | _, _, _, _, _, .transferViolated a0 a1 a2 => .transferViolated a0 a1 a2
  | _, _, _, _, _, .transferResume a0 a1 a2 a3 _ => .transferResume a0 a1 a2 a3
  | _, _, _, _, _, .sendHalt a0 a1 => .sendHalt a0 a1
  | _, _, _, _, _, .sendFailed a0 a1 => .sendFailed a0 a1
  | _, _, _, _, _, .sendRefused a0 a1 => .sendRefused a0 a1
  | _, _, _, _, _, .sendViolated a0 a1 a2 => .sendViolated a0 a1 a2
  | _, _, _, _, _, .sendResume a0 a1 a2 a3 _ => .sendResume a0 a1 a2 a3
  | _, _, _, _, _, .iteHalt a0 => .iteHalt a0
  | _, _, _, _, _, .iteThen a0 a1 => .iteThen a0 (ExecPM.toExecP a1)
  | _, _, _, _, _, .iteElse a0 a1 => .iteElse a0 (ExecPM.toExecP a1)
  | _, _, _, _, _, .callArgs a0 => .callArgs a0
  | _, _, _, _, _, .callBody a0 a1 => .callBody a0 (ExecPM.toExecP a1)
  | _, _, _, _, _, .callRec a0 => .callRec (ExecSM.toExecS a0)
  | _, _, _, _, _, .callReceiver a0 => .callReceiver (ExecSM.toExecS a0)
  | _, _, _, _, _, .callReceiverPush a0 a1 a2 => .callReceiverPush (ExecSM.toExecS a0) a1 (ExecPM.toExecP a2)
  | _, _, _, _, _, .callReceiverPushUnset a0 a1 => .callReceiverPushUnset (ExecSM.toExecS a0) a1
  | _, _, _, _, _, .callReceiverPushHalt a0 => .callReceiverPushHalt (ExecSM.toExecS a0)
  | _, _, _, _, _, .callReceiverPushViolated a0 => .callReceiverPushViolated (ExecSM.toExecS a0)
  | _, _, _, _, _, .tryRevert => .tryRevert
  | _, _, _, _, _, .tryDecode a0 => .tryDecode a0
  | _, _, _, _, _, .tryViolated a0 => .tryViolated a0
  | _, _, _, _, _, .tryOk a0 a1 _ a3 a4 a5 => .tryOk a0 a1 a3 (ExecPM.toExecP a4) a5
  | _, _, _, _, _, .tryError a0 a1 => .tryError a0 (ExecPM.toExecP a1)
  | _, _, _, _, _, .tryPanic a0 a1 => .tryPanic a0 (ExecPM.toExecP a1)
  | _, _, _, _, _, .tryOther a0 a1 => .tryOther a0 (ExecPM.toExecP a1)
  | _, _, _, _, _, .trySelfOk a0 a1 a2 a3 => .trySelfOk a0 a1 (ExecSM.toExecS a2) (ExecPM.toExecP a3)
  | _, _, _, _, _, .trySelfHalt a0 a1 a2 a3 a4 a5 => .trySelfHalt a0 a1 (ExecSM.toExecS a2) a3 a4 a5
  | _, _, _, _, _, .trySelfError a0 a1 a2 a3 => .trySelfError a0 a1 (ExecSM.toExecS a2) (ExecPM.toExecP a3)
  | _, _, _, _, _, .trySelfOther a0 a1 a2 a3 a4 => .trySelfOther a0 a1 (ExecSM.toExecS a2) a3 (ExecPM.toExecP a4)
  | _, _, _, _, _, .trySelfPanic a0 a1 a2 a3 a4 => .trySelfPanic a0 a1 (ExecSM.toExecS a2) a3 (ExecPM.toExecP a4)
  | _, _, _, _, _, .trySelfViolated a0 a1 a2 => .trySelfViolated a0 a1 (ExecSM.toExecS a2)
  | _, _, _, _, _, .loopHalt a0 a1 => .loopHalt a0 a1
  | _, _, _, _, _, .loopExit a0 a1 => .loopExit a0 a1
  | _, _, _, _, _, .loopIter a0 a1 a2 a3 => .loopIter a0 a1 (ExecPM.toExecP a2) (ExecSM.toExecS a3)
  | _, _, _, _, _, .loopStop a0 a1 a2 a3 => .loopStop a0 a1 (ExecPM.toExecP a2) a3
  | _, _, _, _, _, .loopDiverge a0 => .loopDiverge a0
  | _, _, _, _, _, .block a0 a1 => .block a0 (ExecPM.toExecP a1)
  | _, _, _, _, _, .catchDataHalt a0 a1 => .catchDataHalt a0 a1
  | _, _, _, _, _, .catchDataBody a0 a1 a2 => .catchDataBody a0 a1 (ExecPM.toExecP a2)
  termination_by structural _ _ _ _ _ h => h

/-- The same, for a sequence. -/
theorem ExecPM.toExecP : {Γ Γ' : Ctx} → {σ : State C Γ} → {P : Prog C Γ Γ'} →
    {o : COut C σ.H Γ'} → ExecPM M J σ P o → ExecP J σ P o
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .cons a0 a1 => .cons (ExecSM.toExecS a0) (ExecPM.toExecP a1)
  | _, _, _, _, _, .halt a0 => .halt (ExecSM.toExecS a0)
  | _, _, _, _, _, .violated a0 => .violated (ExecSM.toExecS a0)
  termination_by structural _ _ _ _ _ h => h

end

/-- The same, for the frames. -/
theorem ExecFM.toExecF {Γ₀ : Ctx} : {Γ : Ctx} → {σ : State C Γ} → {κ : Frames C Γ Γ₀} →
    {o : COut C σ.H Γ₀} → ExecFM M J (Γ₀ := Γ₀) σ κ o → ExecF J (Γ₀ := Γ₀) σ κ o
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .seq a0 a1 => .seq (ExecPM.toExecP a0) (ExecFM.toExecF a1)
  | _, _, _, _, .seqHalt a0 => .seqHalt (ExecPM.toExecP a0)
  | _, _, _, _, .seqViolated a0 => .seqViolated (ExecPM.toExecP a0)
  | _, _, _, _, .pop a0 => .pop (ExecFM.toExecF a0)
  | _, _, _, _, .drop a0 => .drop (ExecFM.toExecF a0)

mutual

/-- **A callback run is a run under `any`.** -/
theorem ExecS.ofExecSM : {Γ Γ' : Ctx} → {σ : State C Γ} → {s : Stmt C Γ Γ'} →
    {o : COut C σ.H Γ'} → ExecS J σ s o → ExecSM .any J σ s o
  | _, _, _, _, _, .det a0 => .det a0
  | _, _, _, _, _, .transferHalt a0 a1 => .transferHalt a0 a1
  | _, _, _, _, _, .transferViolated a0 a1 a2 => .transferViolated a0 a1 a2
  | _, _, _, _, _, .transferResume a0 a1 a2 a3 => .transferResume a0 a1 a2 a3 trivial
  | _, _, _, _, _, .sendHalt a0 a1 => .sendHalt a0 a1
  | _, _, _, _, _, .sendFailed a0 a1 => .sendFailed a0 a1
  | _, _, _, _, _, .sendRefused a0 a1 => .sendRefused a0 a1
  | _, _, _, _, _, .sendViolated a0 a1 a2 => .sendViolated a0 a1 a2
  | _, _, _, _, _, .sendResume a0 a1 a2 a3 => .sendResume a0 a1 a2 a3 trivial
  | _, _, _, _, _, .iteHalt a0 => .iteHalt a0
  | _, _, _, _, _, .iteThen a0 a1 => .iteThen a0 (ExecP.ofExecPM a1)
  | _, _, _, _, _, .iteElse a0 a1 => .iteElse a0 (ExecP.ofExecPM a1)
  | _, _, _, _, _, .callArgs a0 => .callArgs a0
  | _, _, _, _, _, .callBody a0 a1 => .callBody a0 (ExecP.ofExecPM a1)
  | _, _, _, _, _, .callRec a0 => .callRec (ExecS.ofExecSM a0)
  | _, _, _, _, _, .callReceiver a0 => .callReceiver (ExecS.ofExecSM a0)
  | _, _, _, _, _, .callReceiverPush a0 a1 a2 => .callReceiverPush (ExecS.ofExecSM a0) a1 (ExecP.ofExecPM a2)
  | _, _, _, _, _, .callReceiverPushUnset a0 a1 => .callReceiverPushUnset (ExecS.ofExecSM a0) a1
  | _, _, _, _, _, .callReceiverPushHalt a0 => .callReceiverPushHalt (ExecS.ofExecSM a0)
  | _, _, _, _, _, .callReceiverPushViolated a0 => .callReceiverPushViolated (ExecS.ofExecSM a0)
  | _, _, _, _, _, .tryRevert => .tryRevert
  | _, _, _, _, _, .tryDecode a0 => .tryDecode a0
  | _, _, _, _, _, .tryViolated a0 => .tryViolated a0
  | _, _, _, _, _, .tryOk a0 a1 a3 a4 a5 => .tryOk a0 a1 trivial a3 (ExecP.ofExecPM a4) a5
  | _, _, _, _, _, .tryError a0 a1 => .tryError a0 (ExecP.ofExecPM a1)
  | _, _, _, _, _, .tryPanic a0 a1 => .tryPanic a0 (ExecP.ofExecPM a1)
  | _, _, _, _, _, .tryOther a0 a1 => .tryOther a0 (ExecP.ofExecPM a1)
  | _, _, _, _, _, .trySelfOk a0 a1 a2 a3 => .trySelfOk a0 a1 (ExecS.ofExecSM a2) (ExecP.ofExecPM a3)
  | _, _, _, _, _, .trySelfHalt a0 a1 a2 a3 a4 a5 => .trySelfHalt a0 a1 (ExecS.ofExecSM a2) a3 a4 a5
  | _, _, _, _, _, .trySelfError a0 a1 a2 a3 => .trySelfError a0 a1 (ExecS.ofExecSM a2) (ExecP.ofExecPM a3)
  | _, _, _, _, _, .trySelfOther a0 a1 a2 a3 a4 => .trySelfOther a0 a1 (ExecS.ofExecSM a2) a3 (ExecP.ofExecPM a4)
  | _, _, _, _, _, .trySelfPanic a0 a1 a2 a3 a4 => .trySelfPanic a0 a1 (ExecS.ofExecSM a2) a3 (ExecP.ofExecPM a4)
  | _, _, _, _, _, .trySelfViolated a0 a1 a2 => .trySelfViolated a0 a1 (ExecS.ofExecSM a2)
  | _, _, _, _, _, .loopHalt a0 a1 => .loopHalt a0 a1
  | _, _, _, _, _, .loopExit a0 a1 => .loopExit a0 a1
  | _, _, _, _, _, .loopIter a0 a1 a2 a3 => .loopIter a0 a1 (ExecP.ofExecPM a2) (ExecS.ofExecSM a3)
  | _, _, _, _, _, .loopStop a0 a1 a2 a3 => .loopStop a0 a1 (ExecP.ofExecPM a2) a3
  | _, _, _, _, _, .loopDiverge a0 => .loopDiverge a0
  | _, _, _, _, _, .block a0 a1 => .block a0 (ExecP.ofExecPM a1)
  | _, _, _, _, _, .catchDataHalt a0 a1 => .catchDataHalt a0 a1
  | _, _, _, _, _, .catchDataBody a0 a1 a2 => .catchDataBody a0 a1 (ExecP.ofExecPM a2)
  termination_by structural _ _ _ _ _ h => h

/-- The same, for a sequence. -/
theorem ExecP.ofExecPM : {Γ Γ' : Ctx} → {σ : State C Γ} → {P : Prog C Γ Γ'} →
    {o : COut C σ.H Γ'} → ExecP J σ P o → ExecPM .any J σ P o
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .cons a0 a1 => .cons (ExecS.ofExecSM a0) (ExecP.ofExecPM a1)
  | _, _, _, _, _, .halt a0 => .halt (ExecS.ofExecSM a0)
  | _, _, _, _, _, .violated a0 => .violated (ExecS.ofExecSM a0)
  termination_by structural _ _ _ _ _ h => h

end

/-- The same, for the frames. -/
theorem ExecF.ofExecFM {Γ₀ : Ctx} : {Γ : Ctx} → {σ : State C Γ} → {κ : Frames C Γ Γ₀} →
    {o : COut C σ.H Γ₀} → ExecF J (Γ₀ := Γ₀) σ κ o → ExecFM .any J (Γ₀ := Γ₀) σ κ o
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .seq a0 a1 => .seq (ExecP.ofExecPM a0) (ExecF.ofExecFM a1)
  | _, _, _, _, .seqHalt a0 => .seqHalt (ExecP.ofExecPM a0)
  | _, _, _, _, .seqViolated a0 => .seqViolated (ExecP.ofExecPM a0)
  | _, _, _, _, .pop a0 => .pop (ExecF.ofExecFM a0)
  | _, _, _, _, .drop a0 => .drop (ExecF.ofExecFM a0)

end Any

/-! ## The deterministic run under every model -/

section Det

variable {Γ : Ctx}

mutual

/-- **The run `Stmt.run` makes is a callback run**, the callee changing
nothing, unless it leaves `J` broken on the way. -/
theorem Stmt.execM_run (M : CallerModel C) (J : StateInv C) : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → ∀ σ : State C Γ,
    ExecSM M J σ s (.ofRes (s.run σ)) ∨ ExecSM M J σ s .violated
  | _, _, .transfer r a, σ => by
    cases hp : J.pay with
    | false => exact .inl (.det hp)
    | true =>
      show ExecSM M J σ _ (.ofRes (TRun.transfer r a σ)) ∨ _
      cases h : TRun.transfer r a σ with
      | error e => exact .inl (.transferHalt hp h)
      | ok o₁ =>
        by_cases hI : J.at o₁.st
        · exact .inl (ExecSM.transferResume (st := o₁.st.storage) (nt := o₁.st.net) (sb := o₁.st.selfBalance) hp h hI hI (M.allows_refl J _))
        · exact .inr (.transferViolated hp h hI)
  | _, _, .send pv r a full, σ => by
    cases hp : (J.pay || full) with
    | false => exact .inl (.det hp)
    | true =>
      show ExecSM M J σ _ (.ofRes (TRun.send pv r a σ)) ∨ _
      rcases TRun.send_cases pv r a σ with ⟨e, hs⟩ | ⟨o₁, ht, hs⟩ | hs
      · rw [hs]; exact .inl (.sendHalt hp hs)
      · rw [hs]
        by_cases hI : J.at o₁.st
        · exact .inl (ExecSM.sendResume (st := o₁.st.storage) (nt := o₁.st.net) (sb := o₁.st.selfBalance) hp ht hI hI (M.allows_refl J _))
        · exact .inr (.sendViolated hp ht hI)
      · rw [hs]; exact .inl (.sendRefused hp hs)
  | _, _, .ite c thn els, σ => by
    show ExecSM M J σ _ (.ofRes (TRun.ite c thn.ext thn.runR els.ext els.runR σ)) ∨ _
    rw [TRun.ite_eval]
    cases hc : c.evalT σ with
    | error e => exact .inl (.iteHalt hc)
    | ok b =>
      cases b with
      | true =>
        dsimp only
        rw [← COut.map_ofRes]
        rcases Prog.execM_run M J thn σ with h | h
        · exact .inl (.iteThen hc h)
        · exact .inr (.iteThen (o := .violated) hc h)
      | false =>
        dsimp only
        rw [← COut.map_ofRes]
        rcases Prog.execM_run M J els σ with h | h
        · exact .inl (.iteElse hc h)
        · exact .inr (.iteElse (o := .violated) hc h)
  | _, _, .call f args ret body, σ => by
    show ExecSM M J σ _ (.ofRes (TRun.call args ret body.ext body.runR σ)) ∨ _
    rw [TRun.call_eq]
    cases ha : args.evalT σ with
    | error e => exact .inl (.callArgs ha)
    | ok a =>
      show ExecSM M J σ _
        (.ofRes (TRun.callFrom ret body.ext body.runR σ (ret.enterT (σ.withEnv a)))) ∨ _
      rw [TRun.callFrom_eq, ← COut.map_ofRes]
      rcases Prog.execM_run M J body (ret.enterT (σ.withEnv a)).st with h | h
      · exact .inl (ExecSM.callBody (f := f) ha h)
      · exact .inr (ExecSM.callBody (f := f) (o := .violated) ha h)
  | _, _, .callRec f d args ret body, σ => by
    show ExecSM M J σ _ (.ofRes (TRun.call args ret (body ()).ext (body ()).runR σ)) ∨ _
    rw [TRun.call_eq]
    cases ha : args.evalT σ with
    | error e => exact .inl (.callRec (.callArgs ha))
    | ok a =>
      show ExecSM M J σ _
        (.ofRes (TRun.callFrom ret (body ()).ext (body ()).runR σ (ret.enterT (σ.withEnv a)))) ∨ _
      rw [TRun.callFrom_eq, ← COut.map_ofRes]
      rcases Prog.execM_run M J (body ()) (ret.enterT (σ.withEnv a)).st with h | h
      · exact .inl (.callRec (ExecSM.callBody (f := f) ha h))
      · exact .inr (.callRec (ExecSM.callBody (f := f) (o := .violated) ha h))
  | _, _, .callReceiver f args r body op, σ => by
    have hc : ExecSM M J σ (.call f args (.storage _ r) body)
        (.ofRes (TRun.call args (.storage _ r) body.ext body.runR σ)) ∨
        ExecSM M J σ (.call f args (.storage _ r) body) .violated := by
      rw [TRun.call_eq]
      cases ha : args.evalT σ with
      | error e => exact .inl (.callArgs ha)
      | ok a =>
        change ExecSM M J σ _ (.ofRes (TRun.callFrom (.storage _ r) body.ext body.runR σ
          ⟨σ.withEnv (none, a), List.prefix_refl _⟩)) ∨ _
        rw [TRun.callFrom_eq, ← COut.map_ofRes]
        rcases Prog.execM_run M J body (σ.withEnv (none, a)) with h | h
        · exact .inl (ExecSM.callBody (f := f) ha h)
        · exact .inr (ExecSM.callBody (f := f) (o := .violated) ha h)
    rcases hc with h | h
    · exact .inl (by
        simpa only [COut.receiverOp_of_call] using (ExecSM.callReceiver (op := op) h))
    · exact .inr (ExecSM.callReceiver (op := op) h)
  | _, _, .callReceiverPush f args r body code value, σ => by
    change ExecSM M J σ _ (.ofRes (TRun.callReceiverPush args r body.ext body.runR
      code.ext code.runR value σ)) ∨ _
    have hc : ExecSM M J σ (.call f args (.storage _ r) body)
        (.ofRes (TRun.call args (.storage _ r) body.ext body.runR σ)) ∨
        ExecSM M J σ (.call f args (.storage _ r) body) .violated := by
      rw [TRun.call_eq]
      cases ha : args.evalT σ with
      | error e => exact .inl (.callArgs ha)
      | ok a =>
        change ExecSM M J σ _ (.ofRes (TRun.callFrom (.storage _ r) body.ext body.runR σ
          ⟨σ.withEnv (none, a), List.prefix_refl _⟩)) ∨ _
        rw [TRun.callFrom_eq, ← COut.map_ofRes]
        rcases Prog.execM_run M J body (σ.withEnv (none, a)) with h | h
        · exact .inl (ExecSM.callBody (f := f) ha h)
        · exact .inr (ExecSM.callBody (f := f) (o := .violated) ha h)
    rcases hc with h | h
    · cases hg : TRun.call args (.storage _ r) body.ext body.runR σ with
      | error err =>
        rw [hg] at h
        exact .inl (by
          simpa only [TRun.callReceiverPush, hg, bind, Except.bind,
            COut.ofRes] using (ExecSM.callReceiverPushHalt (code := code) (value := value) h))
      | ok a =>
        rw [hg] at h
        cases hp : a.st.env.1 with
        | none =>
          exact .inl (by
            simpa only [TRun.callReceiverPush, hg,
              TRun.afterReceiverPrefix, SPath.resolveT, TEnv.get, hp, bind, Except.bind,
              Except.map, COut.ofRes] using
              (ExecSM.callReceiverPushUnset (code := code) (value := value) h hp))
        | some ref =>
          rcases Prog.execM_run M J code (a.st.drop (.push .refl)) with hu | hu
          · exact .inl (by
              simpa only [TRun.callReceiverPush, hg,
                TRun.afterReceiverPrefix, SPath.resolveT, TEnv.get, hp, bind, Except.bind,
                COut.pushPrefix_ofRes, Prog.run, COut.map_ofRes] using
                (ExecSM.callReceiverPush (value := value) h hp hu))
          · exact .inr (ExecSM.callReceiverPush (value := value) h hp hu)
    · exact .inr (ExecSM.callReceiverPushViolated (code := code) (value := value) h)
  | _, _, .tryCall call rets ok err code pnc other sargs sbody self, σ => by
    show ExecSM M J σ _ (.ofRes (TRun.tryCall call rets ok.ext ok.runR err.ext err.runR code
      pnc.ext pnc.runR other.ext other.runR sargs sbody.ext sbody.runR self σ)) ∨ _
    have hErr : (self = true → (call.addr.evalT σ).1 ≠ σ.tx.selfAddress.1) →
        ExecSM M J σ (.tryCall call rets ok err code pnc other sargs sbody self)
        (.ofRes ((err.runR σ).map fun o => ⟨o.st.drop err.ext, o.ext⟩)) ∨
        ExecSM M J σ (.tryCall call rets ok err code pnc other sargs sbody self) .violated := by
      intro hsf
      rw [← COut.map_ofRes]
      rcases Prog.execM_run M J err σ with h | h
      · exact .inl (.tryError hsf h)
      · exact .inr (.tryError (o := .violated) hsf h)
    have hOth : (self = true → (call.addr.evalT σ).1 ≠ σ.tx.selfAddress.1) →
        ExecSM M J σ (.tryCall call rets ok err code pnc other sargs sbody self)
        (.ofRes ((other.runR σ).map fun o => ⟨o.st.drop other.ext, o.ext⟩)) ∨
        ExecSM M J σ (.tryCall call rets ok err code pnc other sargs sbody self) .violated := by
      intro hsf
      rw [← COut.map_ofRes]
      rcases Prog.execM_run M J other σ with h | h
      · exact .inl (.tryOther hsf h)
      · exact .inr (.tryOther (o := .violated) hsf h)
    have hPnc : (self = true → (call.addr.evalT σ).1 ≠ σ.tx.selfAddress.1) →
        ∀ v, ExecSM M J σ (.tryCall call rets ok err code pnc other sargs sbody self)
        (.ofRes ((pnc.runR (σ.withEnv (TEnv.append _ (code.decodeT v) σ.env))).map
          fun o => ⟨o.st.drop ((Ext.append _ _).trans pnc.ext), o.ext⟩)) ∨
        ExecSM M J σ (.tryCall call rets ok err code pnc other sargs sbody self) .violated := by
      intro hsf v
      rw [← COut.map_ofRes]
      rcases Prog.execM_run M J pnc (σ.withEnv (TEnv.append _ (code.decodeT v) σ.env)) with h | h
      · exact .inl (.tryPanic hsf h)
      · exact .inr (.tryPanic (o := .violated) hsf h)
    unfold TRun.tryCall
    split
    · exact .inl .tryRevert
    rename_i hz
    split
    · rename_i hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨rfl, hs⟩ := hs
      have hc : ExecSM M J σ (.call call.fn sargs (.rets rets.toRet) sbody)
          (.ofRes (TRun.call sargs (.rets rets.toRet) sbody.ext sbody.runR σ)) ∨
          ExecSM M J σ (.call call.fn sargs (.rets rets.toRet) sbody) .violated := by
        rw [TRun.call_eq]
        cases ha : sargs.evalT σ with
        | error e => exact .inl (.callArgs ha)
        | ok a =>
          show ExecSM M J σ _ (.ofRes (TRun.callFrom (.rets rets.toRet) sbody.ext sbody.runR σ
            ((CallRet.rets rets.toRet).enterT (σ.withEnv a)))) ∨ _
          rw [TRun.callFrom_eq, ← COut.map_ofRes]
          rcases Prog.execM_run M J sbody ((CallRet.rets rets.toRet).enterT (σ.withEnv a)).st with h | h
          · exact .inl (ExecSM.callBody (f := call.fn) ha h)
          · exact .inr (ExecSM.callBody (f := call.fn) (o := .violated) ha h)
      rcases hc with hc | hc
      · revert hc
        cases TRun.call sargs (.rets rets.toRet) sbody.ext sbody.runR σ with
        | ok o₁ =>
          intro hc
          dsimp only
          rw [← COut.map_ofRes]
          rcases Prog.execM_run M J ok o₁.st with h | h
          · exact .inl (ExecSM.trySelfOk hz hs hc h)
          · exact .inr (ExecSM.trySelfOk (o := .violated) hz hs hc h)
        | error e =>
          intro hc
          cases e with
          | revert =>
            dsimp only
            rw [← COut.map_ofRes]
            rcases Prog.execM_run M J other σ with h | h
            · exact .inl (.trySelfOther hz hs hc (.inl rfl) h)
            · exact .inr (.trySelfOther (o := .violated) hz hs hc (.inl rfl) h)
          | revertWith d =>
            dsimp only
            split
            · rw [← COut.map_ofRes]
              rcases Prog.execM_run M J err σ with h | h
              · exact .inl (.trySelfError hz hs hc h)
              · exact .inr (.trySelfError (o := .violated) hz hs hc h)
            · split
              · rename_i v hv
                rw [← COut.map_ofRes]
                rcases Prog.execM_run M J pnc
                  (σ.withEnv (TEnv.append _ (code.decodeT v) σ.env)) with h | h
                · exact .inl (.trySelfPanic hz hs hc (.inr ⟨d, rfl, hv⟩) h)
                · exact .inr (.trySelfPanic (o := .violated) hz hs hc (.inr ⟨d, rfl, hv⟩) h)
              · rw [← COut.map_ofRes]
                rcases Prog.execM_run M J other σ with h | h
                · exact .inl (.trySelfOther hz hs hc (.inr ⟨d, rfl⟩) h)
                · exact .inr (.trySelfOther (o := .violated) hz hs hc (.inr ⟨d, rfl⟩) h)
          | panic =>
            rw [← COut.map_ofRes]
            rcases Prog.execM_run M J pnc
              (σ.withEnv (TEnv.append _ (code.decodeT (TRun.selfPanicCode call σ)) σ.env)) with h | h
            · exact .inl (.trySelfPanic hz hs hc (.inl rfl) h)
            · exact .inr (.trySelfPanic (o := .violated) hz hs hc (.inl rfl) h)
          | diverge => exact .inl (ExecSM.trySelfHalt hz hs hc (by decide) (by decide) nofun)
          | exhausted => exact .inl (ExecSM.trySelfHalt hz hs hc (by decide) (by decide) nofun)
      · exact .inr (ExecSM.trySelfViolated hz hs hc)
    rename_i hns
    have hg : self = true → (call.addr.evalT σ).1 ≠ 0 ∧
        (call.addr.evalT σ).1 ≠ σ.tx.selfAddress.1 := fun hself =>
      ⟨hz, fun he => hns (by simp only [hself, he, decide_true, Bool.and_self])⟩
    rcases lookupBy (call.keyT σ) σ.tx.ext with _ | (vs | _ | v | _)
    · exact .inl .tryRevert
    · dsimp only
      cases hd : rets.decodeT (C := C) (H := σ.H) vs with
      | error e => exact .inl (.tryDecode hd)
      | ok p =>
        obtain ⟨r, rest⟩ := p
        simp only [bind, Except.bind]
        by_cases hI : J.at σ
        · rw [← COut.map_ofRes]
          rcases Prog.execM_run M J ok (σ.withEnv (TEnv.append _ r σ.env)) with h | h
          · exact .inl (ExecSM.tryOk (st := σ.storage) (nt := σ.net) (sb := σ.selfBalance) hI hI (M.allows_refl J _) hd h hg)
          · exact .inr (ExecSM.tryOk (st := σ.storage) (nt := σ.net) (sb := σ.selfBalance) (o := .violated) hI hI (M.allows_refl J _) hd h hg)
        · exact .inr (.tryViolated hI)
    · exact hErr fun h => (hg h).2
    · exact hPnc (fun h => (hg h).2) v
    · exact hOth fun h => (hg h).2
  | Γ, _, .loop a c body, σ => by
    cases ht : Prog.callsBack J.pay body with
    | false => exact .inl (.det (by simp only [Stmt.forksIn, ht]))
    | true =>
      show ExecSM M J σ _ (.ofRes (TRun.loop c body.ext body.runR σ)) ∨ _
      rw [TRun.loop_eq]
      have key : ∀ (n : Nat) (τ : State C Γ) (r : TRes (Out C τ.H Γ)),
          TLoop.iterN (TRun.loopBody body.ext body.runR τ.H) (fun o => c.evalT o.st) n
              ⟨τ, List.prefix_refl _⟩ = .inr r →
            ExecSM M J τ (.loop a c body) (.ofRes r) ∨ ExecSM M J τ (.loop a c body) .violated := by
        intro n
        induction n with
        | zero => intro τ r hn; simp only [TLoop.iterN, reduceCtorEq] at hn
        | succ n ih =>
          intro τ r hn
          simp only [TLoop.iterN, TLoop.step] at hn
          cases hc : c.evalT τ with
          | error e =>
            rw [hc] at hn; cases hn
            exact .inl (.loopHalt ht hc)
          | ok b =>
            cases b with
            | false =>
              rw [hc] at hn; cases hn
              exact .inl (.loopExit ht hc)
            | true =>
              rw [hc] at hn
              simp only [TRun.loopBody] at hn
              rcases Prog.execM_run M J body τ with h | h
              · change ExecPM M J τ body (.ofRes (body.runR τ)) at h
                cases hr : body.runR τ with
                | error e =>
                  rw [hr] at hn h
                  cases hn
                  exact .inl (.loopStop (o := .halt e) ht hc h rfl)
                | ok o' =>
                  rw [hr] at hn h
                  have hn' : TLoop.iterN (TRun.loopBody body.ext body.runR τ.H)
                      (fun o => c.evalT o.st) n (Out.drop body.ext o') = .inr r := hn
                  rw [TRun.loop_iterN_cat c body.ext body.runR (Out.drop body.ext o') n] at hn'
                  cases hi : TLoop.iterN
                      (TRun.loopBody body.ext body.runR (Out.drop body.ext o').st.H)
                      (fun o => c.evalT o.st) n ⟨(Out.drop body.ext o').st, List.prefix_refl _⟩ with
                  | inl => rw [hi] at hn'; cases hn'
                  | inr r'' =>
                    rw [hi] at hn'
                    cases hn'
                    rw [← COut.map_ofRes]
                    rcases ih _ r'' hi with h' | h'
                    · exact .inl (.loopIter ht hc h h')
                    · exact .inr (.loopIter (o := .violated) ht hc h h')
              · exact .inr (.loopStop (o := .violated) ht hc h rfl)
      by_cases hex : ∃ r n, TLoop.iterN (TRun.loopBody body.ext body.runR σ.H)
          (fun o => c.evalT o.st) n ⟨σ, List.prefix_refl _⟩ = .inr r
      · obtain ⟨r, n, hn⟩ := hex
        rw [TLoop.run_of_iterN hn]
        exact key n σ r hn
      · have : TLoop.run (TRun.loopBody body.ext body.runR σ.H) (fun o => c.evalT o.st)
            ⟨σ, List.prefix_refl _⟩ = .error .diverge := by
          simp only [TLoop.run, hex, dite_false]
        rw [this]
        exact .inl (.loopDiverge ht)
  | _, _, .block body, σ => by
    cases ht : Prog.callsBack J.pay body with
    | false => exact .inl (.det (by simp only [Stmt.forksIn, ht]))
    | true =>
      show ExecSM M J σ _ (.ofRes ((body.runR σ).map (Out.drop body.ext))) ∨ _
      rw [← COut.map_ofRes]
      rcases Prog.execM_run M J body σ with h | h
      · exact .inl (.block ht h)
      · exact .inr (.block (o := .violated) ht h)
  | Γ, _, @Stmt.catchData _ _ _ _ _ Γ₁ c rets sargs sbody self kind x body, σ => by
    cases hf : (Stmt.catchData c rets sargs sbody self kind x body).forksIn J.pay with
    | false => exact .inl (.det hf)
    | true =>
      show ExecSM M J σ _ (.ofRes (TRun.catchData c rets sargs sbody.ext sbody.runR self kind
        body.ext body.runR σ)) ∨ _
      unfold TRun.catchData
      cases hb : TRun.catchBytes c rets sargs sbody.ext sbody.runR self σ with
      | error e => exact .inl (.catchDataHalt hf (TRun.catchBytes_ne_panic hb))
      | ok d =>
        simp only [bind, Except.bind]
        cases kind.decode d with
        | none => exact .inl (.catchDataHalt hf nofun)
        | some bs =>
          dsimp only
          rw [TRun.litBytesT_seq]
          unfold TRun.seq
          cases hl : TRun.litBytesT bs TRun.nil σ with
          | error e =>
            refine .inl (.catchDataHalt hf fun hp => ?_)
            subst hp
            exact TRun.litBytesT_noPanic (k := TRun.nil) (fun _ => TRes.NoPanic.ok _) bs σ hl
          | ok o₁ =>
            dsimp only
            have hm : ∀ r : TRes (Out C o₁.st.H Γ₁),
                (COut.ofRes ((r.map fun o' => (⟨o'.st, o₁.ext.trans o'.ext⟩ : Out C σ.H Γ₁)).map
                  fun o => (⟨o.st.drop ((Ext.push .refl).trans body.ext), o.ext⟩ : Out C σ.H Γ))) =
                (COut.ofRes r).map fun o' =>
                  ⟨o'.st.drop ((Ext.push .refl).trans body.ext), o₁.ext.trans o'.ext⟩ := by
              intro r; cases r <;> rfl
            rw [hm]
            rcases Prog.execM_run M J body o₁.st with h | h
            · exact .inl (.catchDataBody hf hl h)
            · exact .inr (.catchDataBody (o := .violated) hf hl h)
  | _, _, .assign .., _ | _, _, .rebind .., _ | _, _, .assignLocal .., _ | _, _, .declLocal .., _
  | _, _, .declStorage .., _ | _, _, .opAssign .., _ | _, _, .incDec .., _
  | _, _, .assignIncDec .., _ | _, _, .assignLocalPush .., _ | _, _, .push .., _
  | _, _, .pushOpAssign .., _ | _, _, .pushIncDec .., _
  | _, _, .pop .., _ | _, _, .declMem .., _
  | _, _, .rebindMem .., _ | _, _, .assignFromMem .., _ | _, _, .assignMem .., _
  | _, _, .delete .., _ | _, _, .deleteMem .., _ | _, _, .assignNew .., _ | _, _, .require .., _
  | _, _, .assert .., _ | _, _, .revert, _ | _, _, .assumeFalse, _
  | _, _, .revertData .., _ => .inl (.det rfl)

/-- The same, for a sequence. -/
theorem Prog.execM_run (M : CallerModel C) (J : StateInv C) : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → ∀ σ : State C Γ,
    ExecPM M J σ P (.ofRes (Prog.run σ P)) ∨ ExecPM M J σ P .violated
  | _, _, .nil, _ => .inl .nil
  | _, _, .cons s P, σ => by
    rcases Stmt.execM_run M J s σ with h | h
    · cases hs : Stmt.run σ s with
      | error e =>
        rw [hs] at h
        show ExecPM M J σ _ (.ofRes (TRun.seq s.runR P.runR σ)) ∨ _
        unfold TRun.seq
        rw [show s.runR σ = .error e from hs]
        exact .inl (.halt h)
      | ok o₁ =>
        rw [hs] at h
        rw [Prog.run_cons_ok hs, ← COut.map_ofRes]
        rcases Prog.execM_run M J P o₁.st with h' | h'
        · exact .inl (.cons h h')
        · exact .inr (.cons (o := .violated) h h')
    · exact .inr (.violated h)

end

/-- The same, for the frames after a program. -/
theorem Frames.execM_run (M : CallerModel C) (J : StateInv C) {Γ₀ : Ctx} : {Γ : Ctx} → (κ : Frames C Γ Γ₀) →
    ∀ σ : State C Γ, ExecFM M J σ κ (.ofRes (κ.run σ)) ∨ ExecFM M J σ κ .violated
  | _, .nil, _ => .inl .nil
  | _, .seq ω κ, σ => by
    show ExecFM M J σ _ (.ofRes (TRun.seq (fun τ => Prog.run τ ω) (fun τ => Frames.run τ κ) σ)) ∨ _
    unfold TRun.seq
    dsimp only
    rcases Prog.execM_run M J ω σ with h | h
    · cases hs : Prog.run σ ω with
      | error e => rw [hs] at h; exact .inl (.seqHalt h)
      | ok o₁ =>
        rw [hs] at h
        dsimp only
        rw [← COut.map_ofRes]
        rcases Frames.execM_run M J κ o₁.st with h' | h'
        · exact .inl (.seq h h')
        · exact .inr (.seq (o := .violated) h h')
    · exact .inr (.seqViolated h)
  | _, .pop _ h κ, σ => (Frames.execM_run M J κ (σ.drop h)).imp .pop .pop
  | _, .drop h κ, σ => (Frames.execM_run M J κ (σ.thin h)).imp .drop .drop



end Det

end Solidity
