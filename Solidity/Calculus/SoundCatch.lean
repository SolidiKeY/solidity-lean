import Solidity.Calculus.SoundCalls
import Solidity.Calculus.DataIn

/-!
# The rule of a `catch` clause that binds the data is sound

`catchDataStep` (`Calculus/Blocks.lean`) against `TRun.catchData`
(`docs/semantic-gaps.md`, "Revert data").  The clause binds what the call
reverts with, read from the state the `try` started in.  For a self-call the
callee's run gives it: its data is one its body lists (`Prog.run_dataS`,
`Calculus/DataIn.lean`), so one of the rule's goals is the clause after
that datum's allocation (`Prog.run_litBytes`); with `raw`, the body has no
`assert` (`Prog.asserts_of_revertDatas`), so the callee does not panic and
no `Panic` data, the transaction's, is bound.  At another receiver the rule's
goal is `false` (`assert(false);` after the `require`s), so nothing is to
show there.
-/

namespace Solidity

open Solidity (Modality)

variable {C : Contract} {Γ : Ctx}

/-- `Panic` data has `Panic`'s selector: no `Error` reason decodes from it. -/
theorem Semantics.decodeError_encodePanic (c : Nat) :
    Semantics.decodeError (Semantics.encodePanic c) = none := by
  simp only [Semantics.decodeError, Semantics.encodePanic, Semantics.panicSelector,
    Semantics.errorSelector, List.cons_append, List.take_succ_cons,
    List.take_zero, List.nil_append]
  rfl

/-- The data a self-call's callee reverts with, where a clause of `kind`
binds something of it, is one `kind.datas` lists. -/
theorem catchBytes_self_mem {ρ ps Γf : Ctx} (call : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf) (kind : CatchKind) (σ : State C Γ)
    {ds : List (List UInt8)} (hd : kind.datas sbody = some ds) {d bs : List UInt8}
    (hb : (match TRun.call sargs (.rets rets) sbody.ext sbody.runR σ with
      | .ok _ => .error .revert
      | .error .revert => .ok []
      | .error (.revertWith d) => .ok d
      | .error .panic => .ok (Semantics.encodePanic (TRun.selfPanicCode call σ).1.toNat)
      | .error e => .error e : TRes (List UInt8)) = .ok d)
    (hk : kind.decode d = some bs) : d ∈ ds := by
  cases kind with
  | reason =>
    have hS : sbody.revertDatas false = some ds := hd
    have hk' : Semantics.decodeError d = some bs := hk
    revert hb
    cases hc : TRun.call sargs (.rets rets) sbody.ext sbody.runR σ with
    | ok => intro hb; cases hb
    | error e =>
      cases e with
      | revert => intro hb; cases hb; exact absurd hk' (by simp [Semantics.decodeError])
      | revertWith d' =>
        intro hb; cases hb
        exact TRun.call_dataS sargs (.rets rets) _ _ (Prog.run_dataS false sbody hS) σ d hc
      | panic =>
        intro hb; cases hb
        rw [Semantics.decodeError_encodePanic] at hk'
        cases hk'
      | diverge | exhausted => intro hb; cases hb
  | raw =>
    have hd' : ((sbody.revertDatas true).map ([] :: ·)) = some ds := hd
    simp only [Option.map_eq_some_iff] at hd'
    obtain ⟨S, hS, rfl⟩ := hd'
    revert hb
    cases hc : TRun.call sargs (.rets rets) sbody.ext sbody.runR σ with
    | ok => intro hb; cases hb
    | error e =>
      cases e with
      | revert => intro hb; cases hb; exact List.mem_cons_self
      | revertWith d' =>
        intro hb; cases hb
        exact List.mem_cons_of_mem _
          (TRun.call_dataS sargs (.rets rets) _ _ (Prog.run_dataS true sbody hS) σ d hc)
      | panic =>
        intro _
        exact absurd hc (TRun.call_noPanic sargs (.rets rets) _ _
          (Prog.run_noPanic sbody (Prog.asserts_of_revertDatas sbody hS)) σ)
      | diverge | exhausted => intro hb; cases hb

/-- **`catchDataBox`** (Lean): for a self-call whose callee's data are known,
the clause after the allocation of each datum it may bind; another
receiver's goal is `false`; otherwise the rule is `false`. -/
theorem Premise.sound_catchDataBox {ρ ps Γf Γ₁ : Ctx} (call : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf) (self : Bool) (kind : CatchKind) (x : Var)
    (body : Prog C (.mem bytesR :: Γ) Γ₁) (σ : State C Γ) :
    Premise.Sound .box (.catchData call rets sargs sbody self kind x body)
      (catchDataStep .box call sbody self kind x body) σ := by
  intro _ _ ω κ φ h
  cases self with
  | false => exact absurd trivial h
  | true =>
  cases hd : kind.datas sbody with
  | none =>
    have h' : holds σ (Fml.ff : Fml C Γ) := by
      unfold catchDataStep at h; rw [hd] at h; exact h
    exact absurd trivial h'
  | some ds =>
  have h' := h
  unfold catchDataStep at h'
  rw [hd] at h'
  have hall := (holds_conj _).1 h'
  rw [holds_modal_iff, runSt_cons_frames]
  show Modality.afterRunTR .box _ (((TRun.catchData call rets sargs sbody.ext sbody.runR true kind
    body.ext body.runR σ).map (·.st)).bind _)
  unfold TRun.catchData
  cases hb : TRun.catchBytes call rets sargs sbody.ext sbody.runR true σ with
  | error e =>
    exact afterRunTR_box_error (TRun.catchBytes_ne_panic hb)
  | ok d =>
    rw [ok_bind]
    cases hk : kind.decode d with
    | none => exact afterRunTR_box_error nofun
    | some bs =>
      dsimp only
      unfold TRun.catchBytes at hb
      split at hb
      · cases hb
      rename_i hz
      have hc : call.hasCode.evalT σ = .ok true := by
        rw [ExtCall.hasCode_evalT]; simp only [hz, decide_false, Bool.not_false]
      split at hb
      · rename_i hs
        simp only [Bool.true_and, decide_eq_true_eq] at hs
        have hi : call.isSelf.evalT σ = .ok true := by
          rw [ExtCall.isSelf_evalT]; simp only [hs, decide_true]
        have hbs := catchBytes_self_mem call rets sargs sbody kind σ hd hb hk
        have hψ : holds σ (Fml.modalK .box (.cons (.require call.hasCode)
            (.cons (.require call.isSelf) (catchLit x kind d body)))
            (.pop .block ((Ext.append Γ []).trans (Prog.cons (.require call.hasCode)
              (.cons (.require call.isSelf) (catchLit x kind d body))).ext) (.seq ω κ)) φ) :=
          hall _ (List.mem_map.2 ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨d, hbs, rfl⟩), rfl⟩)
        have hl : catchLit x kind d body = litBytes x bs body := by
          unfold catchLit; rw [hk]
        have h0 := holds_modalK_pop σ _ _ ω κ φ hψ
        rw [Prog.runSt_require_true hc, Prog.runSt_require_true hi, hl] at h0
        have e : Prog.runSt σ (litBytes x bs body) = (TRun.litBytesT bs body.runR σ).map (·.st) := by
          show (Prog.run σ (litBytes x bs body)).map (·.st) = _
          rw [Prog.run_litBytes]
        rw [e, show (Ext.append Γ []).trans (Prog.cons (.require call.hasCode)
          (.cons (.require call.isSelf) (litBytes x bs body))).ext =
          (Ext.push .refl).trans body.ext from Subsingleton.elim _ _] at h0
        rw [TRes.map_st _ _ (State.drop ((Ext.push .refl).trans body.ext)) fun _ => rfl]
        exact h0
      · rename_i hs
        simp only [Bool.true_and, decide_eq_true_eq] at hs
        have hn : call.notSelf.evalT σ = .ok true := by
          rw [ExtCall.notSelf_evalT]; simp only [hs, decide_false, Bool.not_false]
        let P1 : Prog C Γ Γ := .cons (.require call.hasCode) (.cons (.require call.notSelf)
          (.cons (.assert (.simple (.bool false))) .nil))
        have hψ : holds σ (Fml.modalK .box P1
            (.pop .block ((Ext.append Γ []).trans P1.ext) (.seq ω κ)) φ) :=
          hall _ (List.mem_map.2 ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩)
        have h0 := holds_modalK_pop σ _ _ ω κ φ hψ
        rw [Prog.runSt_require_true hc, Prog.runSt_require_true hn] at h0
        exact absurd h0 fun h0 => h0.2 rfl

/-- **The rule of a `catch` clause binding the data is sound**: `catchDataBox`
under the box, `false` under the diamond. -/
theorem Stmt.sound_catchData (k : Nat) (m : Modality) {ρ ps Γf Γ₁ : Ctx} (call : ExtCall C Γ)
    (rets : Binders ρ) (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf) (self : Bool)
    (kind : CatchKind) (x : Var) (body : Prog C (.mem bytesR :: Γ) Γ₁) (σ : State C Γ)
    (pr : Premise C Γ Γ)
    (hp : Stmt.step k m (.catchData call rets sargs sbody self kind x body) = pr) :
    Premise.Runs m (.catchData call rets sargs sbody self kind x body) pr σ := by
  change catchDataStep m call sbody self kind x body = pr at hp
  cases m with
  | box =>
    cases hp
    have hs : Premise.Sound .box (.catchData call rets sargs sbody self kind x body)
        (catchDataStep .box call sbody self kind x body) σ :=
      Premise.sound_catchDataBox call rets sargs sbody self kind x body σ
    revert hs
    unfold catchDataStep
    split <;> exact id
  | diamond => cases hp; exact Premise.sound_done σ false nofun

end Solidity
