import Solidity.Semantics.Run

/-!
# Oracle-backed external try execution witnesses

These equations select a clause only from actual oracle and ABI-decoding
evidence. They preserve the full typed outcome, including the heap extension,
rollback to the caller state on catches and the binding/pop of return locals.
They concern the deterministic run, not universal callback diamonds.
-/

namespace Solidity.TRun

variable {C : Contract} {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx}
    (call : ExtCall C Γ) (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁)
    (err : Prog C Γ Γ₂) (code : CodeBinder κ) (pnc : Prog C (κ ++ Γ) Γ₃)
    (other : Prog C Γ Γ₄) (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf)
    (σ : State C Γ)

/-- The actual external oracle selects this clause; catches start from `σ`. -/
theorem externalTry_ok (vs rest : List Semantics.Word) (r : TEnv C σ.H ρ)
    (hd : rets.decodeT vs = .ok (r, rest))
    (hz : (call.addr.evalT σ).1 ≠ 0)
    (he : Semantics.lookupBy (call.keyT σ) σ.tx.ext = some (.ok vs)) :
    tryCall call rets ok.ext ok.runR err.ext err.runR code pnc.ext pnc.runR
      other.ext other.runR sargs sbody.ext sbody.runR false σ =
    (ok.runR (σ.withEnv (TEnv.append ρ r σ.env))).map
      (fun o => ⟨o.st.drop ((Ext.append Γ ρ).trans ok.ext), o.ext⟩) := by
  simp only [tryCall, hz, if_false, Bool.false_and, Bool.false_eq_true, he, hd]
  rfl

/-- The actual external oracle selects this clause; catches start from `σ`. -/
theorem externalTry_error (data : List UInt8)
    (hz : (call.addr.evalT σ).1 ≠ 0)
    (he : Semantics.lookupBy (call.keyT σ) σ.tx.ext = some (.error data)) :
    tryCall call rets ok.ext ok.runR err.ext err.runR code pnc.ext pnc.runR
      other.ext other.runR sargs sbody.ext sbody.runR false σ =
    (err.runR σ).map (fun o => ⟨o.st.drop err.ext, o.ext⟩) := by
  simp only [tryCall, hz, if_false, Bool.false_and, Bool.false_eq_true, he]

/-- The actual external oracle selects this clause; catches start from `σ`. -/
theorem externalTry_panic (v : Semantics.Word)
    (hz : (call.addr.evalT σ).1 ≠ 0)
    (he : Semantics.lookupBy (call.keyT σ) σ.tx.ext = some (.panic v)) :
    tryCall call rets ok.ext ok.runR err.ext err.runR code pnc.ext pnc.runR
      other.ext other.runR sargs sbody.ext sbody.runR false σ =
    (pnc.runR (σ.withEnv (TEnv.append κ (code.decodeT (H := σ.H) v) σ.env))).map
      (fun o => ⟨o.st.drop ((Ext.append Γ κ).trans pnc.ext), o.ext⟩) := by
  simp only [tryCall, hz, if_false, Bool.false_and, Bool.false_eq_true, he]

/-- The actual external oracle selects this clause; catches start from `σ`. -/
theorem externalTry_other (data : List UInt8)
    (hz : (call.addr.evalT σ).1 ≠ 0)
    (he : Semantics.lookupBy (call.keyT σ) σ.tx.ext = some (.other data)) :
    tryCall call rets ok.ext ok.runR err.ext err.runR code pnc.ext pnc.runR
      other.ext other.runR sargs sbody.ext sbody.runR false σ =
    (other.runR σ).map (fun o => ⟨o.st.drop other.ext, o.ext⟩) := by
  simp only [tryCall, hz, if_false, Bool.false_and, Bool.false_eq_true, he]

/-- A caller-side failure never enters any catch clause. -/
theorem externalTry_zero
    (hz : (call.addr.evalT σ).1 = 0) :
    tryCall call rets ok.ext ok.runR err.ext err.runR code pnc.ext pnc.runR
      other.ext other.runR sargs sbody.ext sbody.runR false σ = .error .revert := by
  simp only [tryCall, hz, if_true]

/-- A caller-side failure never enters any catch clause. -/
theorem externalTry_missing
    (hz : (call.addr.evalT σ).1 ≠ 0)
    (he : Semantics.lookupBy (call.keyT σ) σ.tx.ext = none) :
    tryCall call rets ok.ext ok.runR err.ext err.runR code pnc.ext pnc.runR
      other.ext other.runR sargs sbody.ext sbody.runR false σ = .error .revert := by
  simp only [tryCall, hz, if_false, Bool.false_and, Bool.false_eq_true, he]

/-- A caller-side failure never enters any catch clause. -/
theorem externalTry_decode_error (vs : List Semantics.Word) (e : THalt)
    (hz : (call.addr.evalT σ).1 ≠ 0)
    (he : Semantics.lookupBy (call.keyT σ) σ.tx.ext = some (.ok vs))
    (hd : rets.decodeT (C := C) (H := σ.H) vs = .error e) :
    tryCall call rets ok.ext ok.runR err.ext err.runR code pnc.ext pnc.runR
      other.ext other.runR sargs sbody.ext sbody.runR false σ = .error e := by
  simp only [tryCall, hz, if_false, Bool.false_and, Bool.false_eq_true, he, hd]
  rfl

/-- A normally completed selected clause is a genuine normal external try witness. -/
theorem externalTry_ok_returns (vs rest : List Semantics.Word) (r : TEnv C σ.H ρ)
    (hd : rets.decodeT vs = .ok (r, rest))
    (hz : (call.addr.evalT σ).1 ≠ 0)
    (he : Semantics.lookupBy (call.keyT σ) σ.tx.ext = some (.ok vs))
    (out : Out C σ.H Γ₁) (hc : ok.runR (σ.withEnv (TEnv.append ρ r σ.env)) = .ok out) :
    tryCall call rets ok.ext ok.runR err.ext err.runR code pnc.ext pnc.runR
      other.ext other.runR sargs sbody.ext sbody.runR false σ = .ok ⟨out.st.drop ((Ext.append Γ ρ).trans ok.ext), out.ext⟩ := by
  rw [externalTry_ok call rets ok err code pnc other sargs sbody σ vs rest r hd hz he, hc]
  rfl

/-- A normally completed selected clause is a genuine normal external try witness. -/
theorem externalTry_error_returns (data : List UInt8)
    (hz : (call.addr.evalT σ).1 ≠ 0)
    (he : Semantics.lookupBy (call.keyT σ) σ.tx.ext = some (.error data))
    (out : Out C σ.H Γ₂) (hc : err.runR σ = .ok out) :
    tryCall call rets ok.ext ok.runR err.ext err.runR code pnc.ext pnc.runR
      other.ext other.runR sargs sbody.ext sbody.runR false σ = .ok ⟨out.st.drop err.ext, out.ext⟩ := by
  rw [externalTry_error call rets ok err code pnc other sargs sbody σ data hz he, hc]
  rfl

/-- A normally completed selected clause is a genuine normal external try witness. -/
theorem externalTry_panic_returns (v : Semantics.Word)
    (hz : (call.addr.evalT σ).1 ≠ 0)
    (he : Semantics.lookupBy (call.keyT σ) σ.tx.ext = some (.panic v))
    (out : Out C σ.H Γ₃) (hc : pnc.runR (σ.withEnv (TEnv.append κ (code.decodeT (H := σ.H) v) σ.env)) = .ok out) :
    tryCall call rets ok.ext ok.runR err.ext err.runR code pnc.ext pnc.runR
      other.ext other.runR sargs sbody.ext sbody.runR false σ = .ok ⟨out.st.drop ((Ext.append Γ κ).trans pnc.ext), out.ext⟩ := by
  rw [externalTry_panic call rets ok err code pnc other sargs sbody σ v hz he, hc]
  rfl

/-- A normally completed selected clause is a genuine normal external try witness. -/
theorem externalTry_other_returns (data : List UInt8)
    (hz : (call.addr.evalT σ).1 ≠ 0)
    (he : Semantics.lookupBy (call.keyT σ) σ.tx.ext = some (.other data))
    (out : Out C σ.H Γ₄) (hc : other.runR σ = .ok out) :
    tryCall call rets ok.ext ok.runR err.ext err.runR code pnc.ext pnc.runR
      other.ext other.runR sargs sbody.ext sbody.runR false σ = .ok ⟨out.st.drop other.ext, out.ext⟩ := by
  rw [externalTry_other call rets ok err code pnc other sargs sbody σ data hz he, hc]
  rfl

end Solidity.TRun
