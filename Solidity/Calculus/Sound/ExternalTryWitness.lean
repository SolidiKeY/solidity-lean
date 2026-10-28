import Solidity.Calculus.SoundKit
import Solidity.Semantics.ExternalTryWitness
import Solidity.Semantics.AllocBytes

/-!
# Deterministic, state-indexed external try witnesses

A normal execution is evidence only at its actual starting state. The helpers
below read the existing deterministic `holds`; they do not conclude validity,
callback soundness, or a taclet. Continuations and scope frames run unchanged.
Payload binding reuses `catchBytes`, `CatchKind.decode`, and `litBytesT_alloc`.
-/

namespace Solidity

variable {C : Contract} {Γ Γ₁ Γ₀ : Ctx}

/-- A bounded helper: check the postcondition at the exact witnessed final state.
There is no search, oracle synthesis, or change of logical reading. -/
theorem holds_diamond_of_normal {σ : State C Γ} {P : Prog C Γ Γ₁}
    {κ : Frames C Γ₁ Γ₀} {τ : State C Γ₀} {φ : Fml C Γ₀}
    (hw : Prog.runFrames σ P κ = .ok τ) (hp : holds τ φ) :
    holds σ (.modal .diamond P κ φ) := by
  change Modality.afterRunTR .diamond (holds · φ) _
  rw [hw]
  exact ⟨hp, by intro h; cases h⟩

/-- Exact transport from a statement's typed outcome through its remaining
program and scope frames. Instantiate `hs` with an `externalTry_*_returns`
lemma; its oracle, decoder and selected-clause premises remain proof obligations. -/
theorem holds_diamond_cons_normal_iff {σ : State C Γ} {s : Stmt C Γ Γ₁}
    {out : Out C σ.H Γ₁} (hs : s.run σ = .ok out)
    {Γ₂ : Ctx} (ω : Prog C Γ₁ Γ₂) (κ : Frames C Γ₂ Γ₀)
    {τ : State C Γ₀}
    (hk : (Prog.runSt out.st ω).bind (Frames.runSt · κ) = .ok τ)
    (φ : Fml C Γ₀) :
    holds σ (.modal .diamond (.cons s ω) κ φ) ↔ holds τ φ := by
  rw [holds_modal_iff, runSt_cons_frames]
  simp only [Stmt.runSt, hs, Except.map]
  change Modality.afterRunTR .diamond (holds · φ)
    ((Prog.runSt out.st ω).bind (Frames.runSt · κ)) ↔ holds τ φ
  rw [hk]
  change (holds τ φ ∧ (Except.ok τ : TRes (State C Γ₀)) ≠ .error .panic) ↔ holds τ φ
  exact ⟨And.left, fun h => ⟨h, by intro bad; cases bad⟩⟩

/-- State projection transport also covers allocation witnesses whose heap typing
has grown. No state is rebuilt or erased when the continuation is run. -/
theorem holds_diamond_cons_state_normal_iff {σ : State C Γ} {s : Stmt C Γ Γ₁}
    {υ : State C Γ₁} (hs : Stmt.runSt σ s = .ok υ)
    {Γ₂ : Ctx} (ω : Prog C Γ₁ Γ₂) (κ : Frames C Γ₂ Γ₀)
    {τ : State C Γ₀}
    (hk : (Prog.runSt υ ω).bind (Frames.runSt · κ) = .ok τ)
    (φ : Fml C Γ₀) :
    holds σ (.modal .diamond (.cons s ω) κ φ) ↔ holds τ φ := by
  rw [holds_modal_iff, runSt_cons_frames, hs]
  change Modality.afterRunTR .diamond (holds · φ)
    ((Prog.runSt υ ω).bind (Frames.runSt · κ)) ↔ holds τ φ
  rw [hk]
  change (holds τ φ ∧ (Except.ok τ : TRes (State C Γ₀)) ≠ .error .panic) ↔ holds τ φ
  exact ⟨And.left, fun h => ⟨h, by intro bad; cases bad⟩⟩

section Try
variable {ρ κ ps Γf Δ₁ Δ₂ Δ₃ Δ₄ Γ₂ : Ctx}
    (call : ExtCall C Γ) (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Δ₁)
    (err : Prog C Γ Δ₂) (code : CodeBinder κ) (pnc : Prog C (κ ++ Γ) Δ₃)
    (other : Prog C Γ Δ₄) (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf)
    (σ : State C Γ) (ω : Prog C Γ Γ₂) (frames : Frames C Γ₂ Γ₀)
    (τ : State C Γ₀) (φ : Fml C Γ₀)

/-- The actual ok clause's normal witness gives exactly its deterministic
formula at `σ`, including the unchanged continuation and frames. -/
theorem externalTry_ok_formula (vs rest : List Semantics.Word) (r : TEnv C σ.H ρ)
    (hd : rets.decodeT vs = .ok (r, rest))
    (hz : (call.addr.evalT σ).1 ≠ 0)
    (he : Semantics.lookupBy (call.keyT σ) σ.tx.ext = some (.ok vs))
    (out : Out C σ.H Δ₁) (hc : ok.runR (σ.withEnv (TEnv.append ρ r σ.env)) = .ok out)
    (hk : (Prog.runSt (out.st.drop ((Ext.append Γ ρ).trans ok.ext)) ω).bind (Frames.runSt · frames) = .ok τ) :
    holds σ (.modal .diamond
      (.cons (.tryCall call rets ok err code pnc other sargs sbody false) ω) frames φ) ↔
      holds τ φ := by
  exact holds_diamond_cons_normal_iff
    (σ := σ) (s := .tryCall call rets ok err code pnc other sargs sbody false)
    (TRun.externalTry_ok_returns call rets ok err code pnc other sargs sbody σ vs rest r hd hz he out hc)
    ω frames hk φ

/-- The actual error clause's normal witness gives exactly its deterministic
formula at `σ`, including the unchanged continuation and frames. -/
theorem externalTry_error_formula (data : List UInt8)

    (hz : (call.addr.evalT σ).1 ≠ 0)
    (he : Semantics.lookupBy (call.keyT σ) σ.tx.ext = some (.error data))
    (out : Out C σ.H Δ₂) (hc : err.runR σ = .ok out)
    (hk : (Prog.runSt (out.st.drop err.ext) ω).bind (Frames.runSt · frames) = .ok τ) :
    holds σ (.modal .diamond
      (.cons (.tryCall call rets ok err code pnc other sargs sbody false) ω) frames φ) ↔
      holds τ φ := by
  exact holds_diamond_cons_normal_iff
    (σ := σ) (s := .tryCall call rets ok err code pnc other sargs sbody false)
    (TRun.externalTry_error_returns call rets ok err code pnc other sargs sbody σ data hz he out hc)
    ω frames hk φ

/-- The actual panic clause's normal witness gives exactly its deterministic
formula at `σ`, including the unchanged continuation and frames. -/
theorem externalTry_panic_formula (v : Semantics.Word)

    (hz : (call.addr.evalT σ).1 ≠ 0)
    (he : Semantics.lookupBy (call.keyT σ) σ.tx.ext = some (.panic v))
    (out : Out C σ.H Δ₃) (hc : pnc.runR (σ.withEnv (TEnv.append κ (code.decodeT (H := σ.H) v) σ.env)) = .ok out)
    (hk : (Prog.runSt (out.st.drop ((Ext.append Γ κ).trans pnc.ext)) ω).bind (Frames.runSt · frames) = .ok τ) :
    holds σ (.modal .diamond
      (.cons (.tryCall call rets ok err code pnc other sargs sbody false) ω) frames φ) ↔
      holds τ φ := by
  exact holds_diamond_cons_normal_iff
    (σ := σ) (s := .tryCall call rets ok err code pnc other sargs sbody false)
    (TRun.externalTry_panic_returns call rets ok err code pnc other sargs sbody σ v hz he out hc)
    ω frames hk φ

/-- The actual other clause's normal witness gives exactly its deterministic
formula at `σ`, including the unchanged continuation and frames. -/
theorem externalTry_other_formula (data : List UInt8)

    (hz : (call.addr.evalT σ).1 ≠ 0)
    (he : Semantics.lookupBy (call.keyT σ) σ.tx.ext = some (.other data))
    (out : Out C σ.H Δ₄) (hc : other.runR σ = .ok out)
    (hk : (Prog.runSt (out.st.drop other.ext) ω).bind (Frames.runSt · frames) = .ok τ) :
    holds σ (.modal .diamond
      (.cons (.tryCall call rets ok err code pnc other sargs sbody false) ω) frames φ) ↔
      holds τ φ := by
  exact holds_diamond_cons_normal_iff
    (σ := σ) (s := .tryCall call rets ok err code pnc other sargs sbody false)
    (TRun.externalTry_other_returns call rets ok err code pnc other sargs sbody σ data hz he out hc)
    ω frames hk φ

end Try

/-- A caller revert cannot serve as a normal deterministic witness, whatever
postcondition, continuation or frames were proposed. -/
theorem holds_diamond_cons_revert {σ : State C Γ} {s : Stmt C Γ Γ₁}
    (hs : s.run σ = .error .revert) {Γ₂ : Ctx}
    (ω : Prog C Γ₁ Γ₂) (κ : Frames C Γ₂ Γ₀) (φ : Fml C Γ₀) :
    ¬ holds σ (.modal .diamond (.cons s ω) κ φ) := by
  rw [holds_modal_iff, runSt_cons_frames]
  simp only [Stmt.runSt, hs, Except.map, Except.bind,
    Modality.afterRunTR, Modality.onTHalt]
  intro h
  cases h.1

namespace TRun
variable {ρ ps Γf Δ : Ctx}

/-- External catch data come from the actual oracle entry, never a fabricated
payload. Error and Panic entries are ABI encoded by the existing semantics. -/
theorem externalCatchBytes (call : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf) (σ : State C Γ)
    (r : Semantics.ExtResult) (d : List UInt8)
    (hz : (call.addr.evalT σ).1 ≠ 0)
    (he : Semantics.lookupBy (call.keyT σ) σ.tx.ext = some r)
    (hd : (match r with
      | .error bs => .ok (Semantics.encodeError bs)
      | .panic v => .ok (Semantics.encodePanic v.1.toNat)
      | .other bs => .ok bs
      | .ok _ => .error .revert : TRes (List UInt8)) = .ok d) :
    catchBytes call rets sargs sbody.ext sbody.runR false σ = .ok d := by
  simp only [catchBytes, hz, if_false, Bool.false_and, Bool.false_eq_true, he]
  cases r <;> exact hd

/-- Reuse the existing allocation theorem: the decoded payload is fresh, the
body starts from the original caller state plus that object, and exactly its
local scope is popped. The heap extension is retained in the typed run. -/
theorem catchData_normal (call : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf) (self : Bool)
    (kind : CatchKind) (body : Prog C (.mem bytesR :: Γ) Δ) (σ : State C Γ)
    (d bs : List UInt8)
    (hb : catchBytes call rets sargs sbody.ext sbody.runR self σ = .ok d)
    (hd : kind.decode d = some bs)
    (out : Out C (σ.allocPush (bytesObj σ.H bs (CatchKind.decode_lt hd))).H Δ)
    (hc : body.runR (σ.allocPush (bytesObj σ.H bs (CatchKind.decode_lt hd))) = .ok out) :
    (catchData call rets sargs sbody.ext sbody.runR self kind body.ext body.runR σ).map (·.st) =
      .ok (out.st.drop ((Ext.push .refl).trans body.ext)) := by
  simp only [catchData, hb, ok_bind, hd]
  rw [TRes.map_st _ _ (State.drop ((Ext.push .refl).trans body.ext)) (fun _ => rfl)]
  change ((litBytesT bs body.runR σ).map (·.st)).map _ = _
  rw [litBytesT_alloc σ bs (CatchKind.decode_lt hd), hc]
  rfl

/-- A payload that fails the existing catch decoder cannot complete normally. -/
theorem catchData_decode_refused (call : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf) (self : Bool)
    (kind : CatchKind) (body : Prog C (.mem bytesR :: Γ) Δ) (σ : State C Γ)
    (d : List UInt8)
    (hb : catchBytes call rets sargs sbody.ext sbody.runR self σ = .ok d)
    (hd : kind.decode d = none) :
    catchData call rets sargs sbody.ext sbody.runR self kind body.ext body.runR σ = .error .revert := by
  simp only [catchData, hb, ok_bind, hd]

end TRun

/-- A decoded data-binding catch's normal witness transports its exact allocated
state and popped scope through the continuation and frames, for `holds` only. -/
theorem catchData_normal_formula {ρ ps Γf Δ Γ₂ : Ctx}
    (call : ExtCall C Γ) (rets : Binders ρ) (sargs : Args C Γ ps)
    (sbody : Prog C (ρ ++ ps) Γf) (self : Bool) (kind : CatchKind) (x : Var)
    (body : Prog C (.mem bytesR :: Γ) Δ) (σ : State C Γ) (d bs : List UInt8)
    (hb : TRun.catchBytes call rets sargs sbody.ext sbody.runR self σ = .ok d)
    (hd : kind.decode d = some bs)
    (out : Out C (σ.allocPush (bytesObj σ.H bs (CatchKind.decode_lt hd))).H Δ)
    (hc : body.runR (σ.allocPush (bytesObj σ.H bs (CatchKind.decode_lt hd))) = .ok out)
    (ω : Prog C Γ Γ₂) (frames : Frames C Γ₂ Γ₀) (τ : State C Γ₀)
    (hk : (Prog.runSt (out.st.drop ((Ext.push .refl).trans body.ext)) ω).bind
      (Frames.runSt · frames) = .ok τ) (φ : Fml C Γ₀) :
    holds σ (.modal .diamond
      (.cons (.catchData call rets sargs sbody self kind x body) ω) frames φ) ↔ holds τ φ := by
  exact holds_diamond_cons_state_normal_iff
    (σ := σ) (s := .catchData call rets sargs sbody self kind x body)
    (TRun.catchData_normal call rets sargs sbody self kind body σ d bs hb hd out hc)
    ω frames hk φ

/-- info: 'Solidity.holds_diamond_of_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms holds_diamond_of_normal

/-- info: 'Solidity.catchData_normal_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms catchData_normal_formula

end Solidity
