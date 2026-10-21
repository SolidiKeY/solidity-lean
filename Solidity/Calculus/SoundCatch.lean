import Solidity.Calculus.SoundCalls
import Solidity.Calculus.DataIn
import Solidity.Semantics.AllocBytes

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
    have hk' : Semantics.decodeError d = some bs := CatchKind.decode_reason hk
    revert hb
    cases hc : TRun.call sargs (.rets rets) sbody.ext sbody.runR σ with
    | ok => intro hb; cases hb
    | error e =>
      cases e with
      | revert => intro hb; cases hb; exact absurd hk' (by simp [Semantics.decodeError])
      | revertWith d' =>
        intro hb; cases hb
        exact TRun.call_dataS sargs (.rets rets) _ _ (Prog.run_dataS false sbody hS) σ d hc
          (.inr (by rw [hk']; rfl))
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
          (TRun.call_dataS sargs (.rets rets) _ _ (Prog.run_dataS true sbody hS) σ d hc (.inl rfl))
      | panic =>
        intro _
        exact absurd hc (TRun.call_noPanic sargs (.rets rets) _ _
          (Prog.run_noPanic sbody (Prog.asserts_of_revertDatas sbody hS)) σ)
      | diverge | exhausted => intro hb; cases hb

/-- The goal for data of any contents (`Premise.allocBranches`): past the
`require`s `Q`, which pass, the clause for every fresh `bytes` gives the
clause after the allocation of the bytes `bs` (`TRun.litBytesT_alloc`). -/
theorem catch_alloc_sound {Γ₁ Γ₂ Γ₀ : Ctx} (σ : State C Γ) (Q : Prog C Γ Γ)
    (hQ : Prog.runSt σ Q = .ok σ) (x : Var) (body : Prog C (.mem bytesR :: Γ) Γ₁)
    (ω : Prog C Γ Γ₂) (κ : Frames C Γ₂ Γ₀) (φ : Fml C Γ₀) (bs : List UInt8)
    (hn : bs.length < 2 ^ 256)
    (h : holds σ (.modal .box Q .nil (.allocAll x bytesR
      (.modalK .box body (.pop .block ((Ext.push .refl).trans body.ext) (.seq ω κ)) φ)))) :
    Modality.afterRunTR .box (holds · φ)
      ((((TRun.litBytesT bs body.runR σ).map fun o =>
          (⟨o.st.drop ((Ext.push .refl).trans body.ext), o.ext⟩ : Out C σ.H Γ)).map (·.st)).bind
        fun υ => (Prog.runSt υ ω).bind (Frames.runSt · κ)) := by
  rw [holds_modal_iff, hQ] at h
  have ha : holds σ (.allocAll x bytesR
      (.modalK .box body (.pop .block ((Ext.push .refl).trans body.ext) (.seq ω κ)) φ)) := h.1
  have h0 := holds_modalK_pop _ _ _ ω κ φ (ha (bytesObj σ.H bs hn))
  rw [TRes.map_st _ _ (State.drop ((Ext.push .refl).trans body.ext)) fun _ => rfl,
    TRun.litBytesT_alloc σ bs hn]
  exact h0

/-- **`catchDataBox`** (Lean): for a self-call whose callee's data are known,
the clause after the allocation of each datum it may bind; at another
receiver, or where the data are not known, the clause after the allocation
of any bytes (`catch_alloc_sound`). -/
theorem Premise.sound_catchDataBox {ρ ps Γf Γ₁ : Ctx} (call : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf) (self : Bool) (kind : CatchKind) (x : Var)
    (body : Prog C (.mem bytesR :: Γ) Γ₁) (σ : State C Γ) :
    Premise.Sound .box (.catchData call rets sargs sbody self kind x body)
      (catchDataStep .box call sbody self kind x body) σ := by
  intro _ _ ω κ φ h
  rw [holds_modal_iff, runSt_cons_frames]
  show Modality.afterRunTR .box _ (((TRun.catchData call rets sargs sbody.ext sbody.runR self kind
    body.ext body.runR σ).map (·.st)).bind _)
  unfold TRun.catchData
  cases hb : TRun.catchBytes call rets sargs sbody.ext sbody.runR self σ with
  | error e =>
    exact afterRunTR_box_error (TRun.catchBytes_ne_panic hb)
  | ok d =>
  rw [ok_bind]
  cases hk : kind.decode d with
  | none => exact afterRunTR_box_error nofun
  | some bs =>
  dsimp only
  have hn : bs.length < 2 ^ 256 := CatchKind.decode_lt hk
  have hz : ¬ (call.addr.evalT σ).1 = 0 := by
    intro hz
    unfold TRun.catchBytes at hb
    rw [if_pos hz] at hb
    cases hb
  have hc : call.hasCode.evalT σ = .ok true := by
    rw [ExtCall.hasCode_evalT]; simp only [hz, decide_false, Bool.not_false]
  have hQ : Prog.runSt σ (.cons (.require call.hasCode) .nil) = .ok σ := by
    rw [Prog.runSt_require_true hc]; rfl
  cases self with
  | false =>
    exact catch_alloc_sound σ _ hQ x body ω κ φ bs hn (by unfold catchDataStep at h; exact h)
  | true =>
  cases hd : kind.datas sbody with
  | none =>
    exact catch_alloc_sound σ _ hQ x body ω κ φ bs hn
      (by unfold catchDataStep at h; rw [hd] at h; exact h)
  | some ds =>
  have h' := h
  unfold catchDataStep at h'
  rw [hd] at h'
  have hall := (holds_conj _).1 h'
  unfold TRun.catchBytes at hb
  rw [if_neg hz] at hb
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
      hall _ (List.mem_append_left _ (List.mem_map.2 ⟨_, List.mem_map.2 ⟨d, hbs, rfl⟩, rfl⟩))
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
    have hn' : call.notSelf.evalT σ = .ok true := by
      rw [ExtCall.notSelf_evalT]; simp only [hs, decide_false, Bool.not_false]
    exact catch_alloc_sound σ _ (by rw [Prog.runSt_require_true hc, Prog.runSt_require_true hn']; rfl)
      x body ω κ φ bs hn (hall _ (List.mem_append_right _ (List.mem_singleton_self _)))

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
