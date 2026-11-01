import Solidity.Semantics.RunFuel

/-! Exact single-memory-return capture used by the entry serializer. The
witnesses are actual argument/entry/body results; no bytes or outcomes are
injected. Failure, caller locals, heap extension and reference identity remain
those of the existing run. -/
namespace Solidity.EntryReturn
variable {C : Contract} {Γ ps Γf : Ctx} {R : RefTy}

/-- An actual normal source/serializer body exports its actual memory local,
with the precise grown heap and caller environment. -/
theorem call_returns (args : Args C Γ ps) (name : Var)
    (hd : (Ty.ref R).defaultOkS = true) (hm : (Ty.ref R).mapFree = true)
    (scope : Ext ([LTy.mem R] ++ ps) Γf) (body : TStep C ([LTy.mem R] ++ ps) Γf)
    (σ : State C Γ) (a : TEnv C σ.H ps) (ha : args.evalT σ = .ok a)
    (entry : Out C σ.H ([LTy.mem R] ++ ps))
    (he : (CallRet.mem (Γ := Γ) R name hd hm).enterT (σ.withEnv (Δ := ps) a) = entry)
    (out : Out C entry.st.H Γf) (hb : body entry.st = .ok out) :
    TRun.call args (.mem R name hd hm) scope body σ =
      .ok ⟨out.st.withEnv (Δ := .mem R :: Γ)
        ((TEnv.drop scope out.st.env).1, TEnv.wk (entry.ext.trans out.ext) Γ σ.env),
        entry.ext.trans out.ext⟩ := by
  cases he
  simp only [TRun.call, ha, bind, Except.bind, hb, CallRet.leaveT, TEnv.take]
  rfl

/-- Compose an actual source-frame witness and an actual serializer witness.
The encoder receives exactly the source result, including its live aliases;
the outer capture exports the actual encoded object without copying it. -/
theorem call_serializes {Γs : Ctx} (args : Args C Γ ps) (name : Var)
    (hd : (Ty.ref R).defaultOkS = true) (hm : (Ty.ref R).mapFree = true)
    (sourceScope : Ext ([LTy.mem R] ++ ps) Γs) (encodeScope : Ext Γs Γf)
    (source : TStep C ([LTy.mem R] ++ ps) Γs) (encode : TStep C Γs Γf)
    (σ : State C Γ) (a : TEnv C σ.H ps) (ha : args.evalT σ = .ok a)
    (entry : Out C σ.H ([LTy.mem R] ++ ps))
    (he : (CallRet.mem (Γ := Γ) R name hd hm).enterT (σ.withEnv (Δ := ps) a) = entry)
    (sourceOut : Out C entry.st.H Γs) (hs : source entry.st = .ok sourceOut)
    (encodedOut : Out C sourceOut.st.H Γf) (hc : encode sourceOut.st = .ok encodedOut) :
    TRun.call args (.mem R name hd hm) (sourceScope.trans encodeScope)
      (TRun.seq source encode) σ =
      .ok ⟨encodedOut.st.withEnv (Δ := .mem R :: Γ)
        ((TEnv.drop (sourceScope.trans encodeScope) encodedOut.st.env).1,
          TEnv.wk (entry.ext.trans (sourceOut.ext.trans encodedOut.ext)) Γ σ.env),
        entry.ext.trans (sourceOut.ext.trans encodedOut.ext)⟩ := by
  have hr : TRun.seq source encode entry.st =
      .ok (⟨encodedOut.st, sourceOut.ext.trans encodedOut.ext⟩ : Out C entry.st.H Γf) := by
    simp only [TRun.seq, hs, hc]
    rfl
  exact call_returns args name hd hm (sourceScope.trans encodeScope)
    (TRun.seq source encode) σ a ha entry he _ hr

/-- A checked non-divergent bounded execution is the existing ordinary run,
by the repository's fuel approximation theorem. No fuel allowance is changed. -/
theorem bounded_exact {Δ : Ctx} (P : Prog C Γ Δ) (σ : State C Γ) (n : Nat)
    (h : (P.runF n σ).halt? = none) : P.runR σ = P.runF n σ := by
  rcases Prog.runF_approx n P σ with hd | same
  · rw [hd] at h
    cases h
  · exact same.symm

/-- Earlier argument failure cannot execute the source body or serializer. -/
theorem call_argument_failure (args : Args C Γ ps) (name : Var)
    (hd : (Ty.ref R).defaultOkS = true) (hm : (Ty.ref R).mapFree = true)
    (scope : Ext ([LTy.mem R] ++ ps) Γf) (body : TStep C ([LTy.mem R] ++ ps) Γf)
    (σ : State C Γ) (e : THalt) (h : args.evalT σ = .error e) :
    TRun.call args (.mem R name hd hm) scope body σ = .error e := by
  simp only [TRun.call, h, bind, Except.bind]

/-- Actual body failure, including an uncaught revert with bytes, propagates
without a serialization result. This statement includes every existing halt. -/
theorem call_body_failure (args : Args C Γ ps) (name : Var)
    (hd : (Ty.ref R).defaultOkS = true) (hm : (Ty.ref R).mapFree = true)
    (scope : Ext ([LTy.mem R] ++ ps) Γf) (body : TStep C ([LTy.mem R] ++ ps) Γf)
    (σ : State C Γ) (a : TEnv C σ.H ps) (ha : args.evalT σ = .ok a)
    (entry : Out C σ.H ([LTy.mem R] ++ ps))
    (he : (CallRet.mem (Γ := Γ) R name hd hm).enterT (σ.withEnv (Δ := ps) a) = entry)
    (e : THalt) (hb : body entry.st = .error e) :
    TRun.call args (.mem R name hd hm) scope body σ = .error e := by
  cases he
  simp only [TRun.call, ha, bind, Except.bind, hb]

/-- Capture is the same heap reference, not a copy or a re-decoded surrogate. -/
theorem capture_identity {H : HTy} (caller : TEnv C H Γ) (name : Var)
    (hd : (Ty.ref R).defaultOkS = true) (hm : (Ty.ref R).mapFree = true)
    (r : Option (HRef H R)) :
    TEnv.get .here ((CallRet.mem R name hd hm).leaveT caller (r, ())) = r := rfl

/-- Dropping only the exported local restores exactly the caller's locals. -/
theorem capture_caller {H : HTy} (caller : TEnv C H Γ) (name : Var)
    (hd : (Ty.ref R).defaultOkS = true) (hm : (Ty.ref R).mapFree = true)
    (r : Option (HRef H R)) :
    TEnv.drop (.push .refl) ((CallRet.mem R name hd hm).leaveT caller (r, ())) = caller := rfl

/-- Growing the heap changes only the proof carried by an alias, not identity. -/
theorem alias_identity {H H' : HTy} (ext : H <+: H') (r : HRef H R) :
    (r.wk ext).id = r.id := rfl

/-- A capture/return projection keeps the primitive tuple's full typed order. -/
theorem primitive_order {H : HTy} {ρ : Ctx} (bs : Binders ρ)
    (caller : TEnv C H Γ) (returns : TEnv C H ρ) :
    (CallRet.rets bs).leaveT caller returns = TEnv.append ρ returns caller := rfl

end Solidity.EntryReturn
