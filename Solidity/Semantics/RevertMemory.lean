import Solidity.Semantics.RunFuel

/-!
# Revert data read from typed memory

A memory operand reads the current object, including writes through aliases.
The result is an immutable byte list which survives callee heap rollback.
Finite execution certificates describe the unbounded run when they halt
without exhausting their loop fuel.
-/

namespace Solidity

variable {C : Contract} {Γ : Ctx}

/-- A set memory local reverts with its current bytes, encoded for its kind. -/
theorem RevPart.evalT_mem (σ : State C Γ) (kind : CatchKind)
    (src : Idx Γ (.mem bytesR)) (r : HRef σ.H bytesR)
    (h : TEnv.get src σ.env = some r) :
    (RevPart.mem kind src).evalT σ = .ok
      (let bs := (σ.heap.get r).1.map (fun v => UInt8.ofNat v.val.toNat)
       match kind with | .raw => bs | .reason => Semantics.encodeError bs) := by
  cases kind <;> simp only [RevPart.evalT, MPath.mvalT, h, bind, Except.bind, pure, Except.pure]

/-- A finite non-divergent halt is the exact halt of the unbounded run. -/
theorem TRes.Approx.halt_eq {α : Type} {a b : TRes α} (hab : TRes.Approx a b)
    {e : THalt} (he : e ≠ .diverge) (h : a.halt? = some e) : b.halt? = some e := by
  apply Eq.trans (congrArg TRes.halt? (hab.eq ?_).symm) h
  intro hd
  rw [hd] at h
  exact he (Option.some.inj h).symm

/-- A sole memory operand produces exactly these bytes, with the empty raw
buffer represented by the ordinary empty-data revert. -/
theorem TRun.revertData_mem (σ : State C Γ) (kind : CatchKind)
    (src : Idx Γ (.mem bytesR)) (r : HRef σ.H bytesR)
    (h : TEnv.get src σ.env = some r) :
    TRun.revertData [.mem kind src] σ = .error
      (THalt.ofData (let bs := (σ.heap.get r).1.map (fun v => UInt8.ofNat v.val.toNat)
       match kind with | .raw => bs | .reason => Semantics.encodeError bs)) := by
  simp only [TRun.revertData, List.mapM_cons, RevPart.evalT_mem σ kind src r h,
    List.mapM_nil, bind, Except.bind, pure, Except.pure, List.flatten_cons,
    List.flatten_nil, List.append_nil]

/-- An unset memory source fails before producing any data. -/
theorem RevPart.evalT_mem_unset (σ : State C Γ) (kind : CatchKind)
    (src : Idx Γ (.mem bytesR)) (h : TEnv.get src σ.env = none) :
    (RevPart.mem kind src).evalT σ = .error .revert := by
  simp only [RevPart.evalT, MPath.mvalT, h, bind, Except.bind]

/-- The loop bound is absent from the certified execution conclusion. -/
theorem Prog.run_halt_of_runF {Γ' : Ctx} (P : Prog C Γ Γ') (σ : State C Γ)
    (fuel : Nat) {e : THalt} (he : e ≠ .diverge)
    (h : (P.runF fuel σ).halt? = some e) : (Prog.run σ P).halt? = some e :=
  (P.runF_approx fuel σ).halt_eq he h

/-- A successful bounded run also certifies successful unbounded execution. -/
theorem TRes.Approx.returned {α : Type} {a b : TRes α} (hab : TRes.Approx a b)
    (h : a.toOption.isSome = true) : b.toOption.isSome = true := by
  rcases hab with hd | rfl
  · rw [hd] at h; cases h
  · exact h

/-- Exact data produced by a failing self-call, including an empty buffer,
is transported without consulting the transaction's external-response oracle.
The address hypotheses are necessary: zero-address calls fail in the caller. -/
theorem TRun.catchBytes_self_data {ρ ps Γf : Ctx} (c : ExtCall C Γ)
    (rets : Binders ρ) (sargs : Args C Γ ps) (hs : Ext (ρ ++ ps) Γf)
    (sbody : TStep C (ρ ++ ps) Γf) (σ : State C Γ) (d : List UInt8)
    (hnz : (c.addr.evalT σ).1 ≠ 0)
    (hself : (c.addr.evalT σ).1 = σ.tx.selfAddress.1)
    (hcall : TRun.call sargs (.rets rets) hs sbody σ = .error (THalt.ofData d)) :
    TRun.catchBytes c rets sargs hs sbody true σ = .ok d := by
  have hc : decide ((c.addr.evalT σ).1 = σ.tx.selfAddress.1) = true := by
    simp only [hself, decide_true]
  simp only [TRun.catchBytes, if_neg hnz, hc, Bool.and_self, Bool.true_eq, ↓reduceIte, hcall]
  cases d <;> rfl

/-- A self-call catch clause starts from the caller's original state and
allocates the exact decoded bytes of the callee's halt. The conclusion keeps
the allocation and its typed heap extension explicit, so no rollback or
symbolic-data connection is replaced by an arbitrary bytes assumption. -/
theorem TRun.catchData_self_data {ρ ps Γf Γ₁ : Ctx} (c : ExtCall C Γ)
    (rets : Binders ρ) (sargs : Args C Γ ps) (hs : Ext (ρ ++ ps) Γf)
    (sbody : TStep C (ρ ++ ps) Γf) (kind : CatchKind)
    (h₁ : Ext (.mem bytesR :: Γ) Γ₁) (body : TStep C (.mem bytesR :: Γ) Γ₁)
    (σ : State C Γ) (d bs : List UInt8)
    (hnz : (c.addr.evalT σ).1 ≠ 0)
    (hself : (c.addr.evalT σ).1 = σ.tx.selfAddress.1)
    (hcall : TRun.call sargs (.rets rets) hs sbody σ = .error (THalt.ofData d))
    (hdecode : kind.decode d = some bs) :
    TRun.catchData c rets sargs hs sbody true kind h₁ body σ =
      (TRun.litBytesT bs body σ).map
        (fun o => ⟨o.st.drop ((Ext.push .refl).trans h₁), o.ext⟩) := by
  simp only [TRun.catchData,
    TRun.catchBytes_self_data c rets sargs hs sbody σ d hnz hself hcall,
    bind, Except.bind, hdecode]

end Solidity
