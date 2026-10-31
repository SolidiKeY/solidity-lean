import Solidity.Backend.InternalFlow.StorageFrames

/-! Finite single storage-reference result export. Plain paths are exported as
actual symbolic storage slots; no conversion into a memory-object pointer. -/
namespace Solidity.Backend.InternalFlow.StorageCalls
open Evm Evm.Memory
variable {C : Contract}

def expand {Γ ps Γf : Ctx} (args : Args C Γ ps) (R : RefTy) (name : Var)
    (body : Prog C (.alias R :: ps) Γf) : Prog C Γ (.alias R :: (ps ++ Γ)) :=
  args.declsThen (.cons (.declStorage R name none)
    (.cons (.block (body.wk (Thin.atop (.alias R :: ps) Γ)).2.2) .nil))

/-- Exact expansion used by published Premise.sound_callStorage, as a run
identity rather than only a logical premise soundness consequence. -/
theorem expand_runSt {Γ ps Γf : Ctx} (f : Name) (args : Args C Γ ps)
    (R : RefTy) (name : Var) (body : Prog C (.alias R :: ps) Γf) (σ : State C Γ) :
    ((expand args R name body).runSt σ).map
      (State.thin (.keep (Thin.ofExt (Ext.append Γ ps)))) =
      (Stmt.call f args (.storage R name) body).runSt σ := by
  rw [expand, Args.runSt_declsThen]
  change _ = (TRun.call args (.storage R name) body.ext body.runR σ).map (·.st)
  rw [TRun.call_eq]
  cases args.evalT σ with
  | error => rfl
  | ok a =>
    simp only [TRes.ok_bind, ok_bind, Prog.runSt_cons, Stmt.runSt_declStorage_none]
    rw [show (σ.withEnv (TEnv.append ps a σ.env)).push (t := .alias R) none =
      σ.withEnv (TEnv.append (.alias R :: ps) (none,a) σ.env) from rfl,
      State.withEnv_append_lift, Stmt.runSt, Stmt.run_block_wk]
    unfold TRun.callFrom Prog.run CallRet.enterT
    dsimp only
    change _ = Except.map (fun o : Solidity.Out C σ.H (.alias R :: Γ) => o.st)
      ((body.runR (σ.withEnv (Δ := .alias R :: ps) (none,a))).bind fun o =>
        .ok ⟨o.st.withEnv (Δ := .alias R :: Γ)
          ((TEnv.drop body.ext o.st.env).1,TEnv.wk o.ext Γ σ.env),o.ext⟩)
    cases body.runR (σ.withEnv (Δ := .alias R :: ps) (none,a)) with
    | error => rfl
    | ok o =>
      apply congrArg Except.ok
      simp only [Solidity.Out.drop, Solidity.Out.lift, State.lift, State.drop, State.thin, State.withEnv]
      erw [TEnv.thin_put_keepAllAtop (rs := [.alias R]) (r := (none,()))]
      rfl

private theorem state_injective {H : HTy} {Γ : Ctx}
    {a b : TRes (Solidity.Out C H Γ)} (h : a.map (·.st) = b.map (·.st)) : a = b := by
  cases a with
  | error e => cases b with
    | error f => exact congrArg Except.error (Except.error.inj h)
    | ok o => cases h
  | ok o => cases b with
    | error f => cases h
    | ok o' =>
      have hs : o.st = o'.st := Except.ok.inj h
      have ho : o = o' := by cases o; cases o'; cases hs; rfl
      exact congrArg Except.ok ho

/-- The transported heap extension is the actual expansion's Out.ext. -/
theorem expand_runR {Γ ps Γf : Ctx} (f : Name) (args : Args C Γ ps)
    (R : RefTy) (name : Var) (body : Prog C (.alias R :: ps) Γf) (σ : State C Γ) :
    ((expand args R name body).run σ).map (fun o =>
      (⟨o.st.thin (.keep (Thin.ofExt (Ext.append Γ ps))),o.ext⟩ :
        Solidity.Out C σ.H (.alias R :: Γ))) =
      (Stmt.call f args (.storage R name) body).run σ := by
  apply state_injective
  have h := expand_runSt f args R name body σ
  cases hx : (expand args R name body).run σ with
  | error e => simpa only [Prog.runSt,hx,Except.map] using h
  | ok o => simpa only [Prog.runSt,hx,Except.map] using h

private theorem ok_of_state {H : HTy} {Γ : Ctx} {res : TRes (Solidity.Out C H Γ)}
    {τ : State C Γ} (h : res.map (·.st) = .ok τ) : ∃ o, res = .ok o ∧ o.st = τ := by
  cases res with
  | error e => cases h
  | ok o => exact ⟨o,rfl,Except.ok.inj h⟩

private theorem error_of_state {H : HTy} {Γ : Ctx} {res : TRes (Solidity.Out C H Γ)}
    (h : res.map (·.st) = .error .revert) : res = .error .revert := by
  cases res with
  | error e => exact congrArg Except.error (Except.error.inj h)
  | ok o => cases h

/-- Export a statically plain storage alias. The actual source reference and
PathSlot witness come from StateRepr, not a supplied desired alias equation. -/
def storageReturn {b : Nat} {Γ ps Γf : Ctx} {F : Frag Γ} (f : Name)
    (args : Args C Γ ps) (R : RefTy) (name : Var) (body : Prog C (.alias R :: ps) Γf)
    (hq : Calls.Program b F (expand args R name body))
    (plain : hq.frag.get .here = .ok) : Calls.Statement b F (.call f args (.storage R name) body) where
  frag := (hq.frag.restrict Γ).push (.alias R) .ok
  code := hq.code ++ Calls.returnPointerCode b Γ ps
  need := hq.need
  cost := hq.cost
  allocates := hq.allocates
  zeroCost := hq.zeroCost
  sound := by
    intro L frame σ base m h room capacity
    rcases hq.sound h room capacity with ⟨o,m₁,base',ho,hc,hm,hk,he,ha⟩ | ⟨ho,hc⟩
    · obtain ⟨ref,slot,href,hslot,hpath⟩ := hm.core.aliases .here plain
      let τ := o.st.thin (.keep (Thin.ofExt (Ext.append Γ ps)))
      have hτ : τ = (o.st.drop (Ext.append Γ (.alias R :: ps))).push (t := .alias R) (some ref) := by
        unfold τ State.thin State.drop State.push State.withEnv
        simp only [TEnv.thin,TEnv.thin_ofExt]
        have href' : o.st.env.1 = some ref := href
        rw [href']
        rfl
      have hs : ((Stmt.call f args (.storage R name) body).run σ).map (·.st) = .ok τ := by
        change (Stmt.call f args (.storage R name) body).runSt σ = _
        rw [← expand_runSt f args R name body σ]
        show (((expand args R name body).run σ).map (·.st)).map _ = _
        rw [ho]
        rfl
      obtain ⟨out,hout,ht⟩ := ok_of_state hs
      have hroom : b + (Γ.length + 1) ≤ frame := by
        have hh := hm.locals
        simp only [List.length_cons,List.length_append] at hh
        omega
      have hrepr := StorageFrames.pushAlias (hm.drop (Ext.append Γ (.alias R :: ps))) hpath hroom
      have hcode : run (Calls.returnPointerCode b Γ ps) m₁ =
          .ok (writeMachine m₁ (cell (b + Γ.length)) (.slot slot)) 0 := by
        have hp : m₁.mem (cell (b + Γ.length + ps.length)) = .slot slot := by
          simpa only [Machine.memAt,cellOf,lvl_here,List.length_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hslot
        simp only [Calls.returnPointerCode,run,exec_cons_zero,Instr.step,Machine.next,hp,
          Out.ok_bind,exec_nil,writeMachine]
      refine .inl ⟨out,writeMachine m₁ (cell (b + Γ.length)) (.slot slot),base',hout,?_,?_,hk,he,?_⟩
      · rw [run_append_ok hc]
        exact hcode
      · rw [ht,hτ]
        exact hrepr
      · intro cursor hb alloc space
        rw [ht,hτ]
        exact (ha cursor hb alloc space).localWrite _ (by dsimp [cell]; omega) (by dsimp [cell]; omega) _
    · have hs : ((Stmt.call f args (.storage R name) body).run σ).map (·.st) = .error .revert := by
        change (Stmt.call f args (.storage R name) body).runSt σ = _
        rw [← expand_runSt f args R name body σ]
        show (((expand args R name body).run σ).map (·.st)).map _ = _
        rw [ho]
        rfl
      exact .inr ⟨error_of_state hs,run_append_revert hc⟩

end Solidity.Backend.InternalFlow.StorageCalls
