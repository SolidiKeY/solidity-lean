import Solidity.Semantics.ExternalTryWitness

/-!
# Exact typed conditions for every try outcome

This predicate is a specification by actual receiver, callee/oracle, decoder
and selected-clause outcomes. It calls no try evaluator, changes no admissible
state, and includes all clause halts, not just normal completion. Scope drops
and composed heap extensions are exactly the run's. Caller failures remain
outside the catch boundary. The callback judgement is not involved.
-/
namespace Solidity.TRun
variable {C : Contract} {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx}
    (call : ExtCall C Γ) (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁)
    (err : Prog C Γ Γ₂) (code : CodeBinder κ) (pnc : Prog C (κ ++ Γ) Γ₃)
    (other : Prog C Γ Γ₄) (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf)
    (self : Bool) (σ : State C Γ)

/-- Necessary and sufficient conditions, indexed by the *full* typed result.
An `.ok` index demands a normal selected clause; an `.error` index retains
its exact halt, including a failure in the success/catch body itself. -/
def tryCondition (result : TRes (Out C σ.H Γ)) : Prop :=
  if (call.addr.evalT σ).1 = 0 then result = .error .revert else
  if self && decide ((call.addr.evalT σ).1 = σ.tx.selfAddress.1) then
    match TRun.call sargs (.rets rets) sbody.ext sbody.runR σ with
    | .ok o => result = (ok.runR o.st).map fun o' =>
        ⟨o'.st.drop ((Ext.append Γ ρ).trans ok.ext), o.ext.trans o'.ext⟩
    | .error .revert => result = (other.runR σ).map fun o => ⟨o.st.drop other.ext, o.ext⟩
    | .error (.revertWith d) =>
      match Semantics.decodeError d with
      | some _ => result = (err.runR σ).map fun o => ⟨o.st.drop err.ext, o.ext⟩
      | none => match Semantics.decodePanic d with
        | some c => result = (pnc.runR (σ.withEnv (TEnv.append κ (code.decodeT (H := σ.H) c) σ.env))).map
            fun o => ⟨o.st.drop ((Ext.append Γ κ).trans pnc.ext), o.ext⟩
        | none => result = (other.runR σ).map fun o => ⟨o.st.drop other.ext, o.ext⟩
    | .error .panic =>
      result = (pnc.runR (σ.withEnv (TEnv.append κ (code.decodeT (H := σ.H) (selfPanicCode call σ)) σ.env))).map
        fun o => ⟨o.st.drop ((Ext.append Γ κ).trans pnc.ext), o.ext⟩
    | .error e => result = .error e
  else match Semantics.lookupBy (call.keyT σ) σ.tx.ext with
  | none => result = .error .revert
  | some (.ok vs) => match rets.decodeT (C := C) (H := σ.H) vs with
    | .error e => result = .error e
    | .ok (r, _) => result = (ok.runR (σ.withEnv (TEnv.append ρ r σ.env))).map
        fun o => ⟨o.st.drop ((Ext.append Γ ρ).trans ok.ext), o.ext⟩
  | some (.error _) => result = (err.runR σ).map fun o => ⟨o.st.drop err.ext, o.ext⟩
  | some (.panic c) =>
    result = (pnc.runR (σ.withEnv (TEnv.append κ (code.decodeT (H := σ.H) c) σ.env))).map
      fun o => ⟨o.st.drop ((Ext.append Γ κ).trans pnc.ext), o.ext⟩
  | some (.other _) => result = (other.runR σ).map fun o => ⟨o.st.drop other.ext, o.ext⟩

/-- The condition is exact in both directions for arbitrary normal or halting
outcomes, under either self-dispatch flag, without adding any global premise. -/
theorem tryCall_eq_iff (result : TRes (Out C σ.H Γ)) :
    tryCall call rets ok.ext ok.runR err.ext err.runR code pnc.ext pnc.runR
      other.ext other.runR sargs sbody.ext sbody.runR self σ = result ↔
    tryCondition call rets ok err code pnc other sargs sbody self σ result := by
  unfold tryCall tryCondition
  simp only [bind, Except.bind]
  repeat' first
    | exact ⟨Eq.symm, Eq.symm⟩
    | (split <;> try simp only [*])

/-- Data-binding clauses are likewise conditional on actual catch bytes,
decoding, allocation, and the entire typed body outcome. -/
def catchCondition (kind : CatchKind) (body : Prog C (.mem bytesR :: Γ) Γ₁)
    (result : TRes (Out C σ.H Γ)) : Prop :=
  match catchBytes call rets sargs sbody.ext sbody.runR self σ with
  | .error e => result = .error e
  | .ok d => match kind.decode d with
    | none => result = .error .revert
    | some bs => result = (litBytesT bs body.runR σ).map
        fun o => ⟨o.st.drop ((Ext.push .refl).trans body.ext), o.ext⟩

/-- Includes absent/malformed data and failures after allocating the payload;
none can be silently promoted into successful clause completion. -/
theorem catchData_eq_iff (kind : CatchKind) (body : Prog C (.mem bytesR :: Γ) Γ₁)
    (result : TRes (Out C σ.H Γ)) :
    catchData call rets sargs sbody.ext sbody.runR self kind body.ext body.runR σ = result ↔
    catchCondition call rets sargs sbody self σ kind body result := by
  unfold catchData catchCondition
  simp only [bind, Except.bind]
  repeat' first
    | exact ⟨Eq.symm, Eq.symm⟩
    | (split <;> try simp only [*])

/-- A failing receiver/argument capture prefix never enters its following try.
Every halt is forwarded unchanged; this does not catch argument failures. -/
theorem try_prefix_failure {Δ Ω : Ctx} (firstStep : TStep C Γ Δ) (rest : TStep C Δ Ω)
    (e : THalt) (h : firstStep σ = .error e) : seq firstStep rest σ = .error e := by
  simp only [seq, h]

/-- A successful capture prefix supplies its exact typed state and heap
extension to the try, rather than re-evaluating operands in the old state. -/
theorem try_prefix_success {Δ Ω : Ctx} (firstStep : TStep C Γ Δ) (rest : TStep C Δ Ω)
    (out : Out C σ.H Δ) (h : firstStep σ = .ok out) :
    seq firstStep rest σ = (rest out.st).map fun o => ⟨o.st, out.ext.trans o.ext⟩ := by
  simp only [seq, h]

/-- info: 'Solidity.TRun.tryCall_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tryCall_eq_iff

end Solidity.TRun
