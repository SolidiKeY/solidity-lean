import Solidity.Backend.InternalFlow.CallerFrame
import Solidity.Calculus.RunFrameMem
/-! Captured caller views through a direct call and its checked scoped tail.
Only the tail uses the published frame guard; callee writes remain arbitrary.
No new evaluator, admission rule or heap-content frame is introduced. -/
namespace Solidity.Backend.InternalFlow.CallerTail
variable {C : Contract}

/-- Whole selected-environment consequence of the published local frame law.
The syntactic guard and write exclusion remain explicit and unchanged. -/
theorem program_environment {Γ Δ Ξ : Ctx} {P : Prog C Γ Δ} (h : Thin Ξ Γ)
    (within : Prog.withinM .nonpayable P = true)
    (unwritten : ∀ (t : LTy) (i : Idx Ξ t),
      (t,(i.wk h).toNat) ∉ Prog.writesAt 0 P)
    {σ : State C Γ} {out : Out C σ.H Δ} (executed : P.run σ = .ok out) :
    TEnv.thin h (TEnv.drop P.ext out.st.env) =
      TEnv.wk out.ext Ξ (TEnv.thin h σ.env) := by
  have localFrame := (Prog.run_frameM P within 0 executed).2
  apply TEnv.ext
  intro t i
  rw [CallerFrame.read_thin,TEnv.get_wk,CallerFrame.read_thin]
  exact localFrame t (i.wk h) (Nat.zero_le _) (by
    simpa only [Nat.sub_zero] using unwritten t i)

/-- The tail's real mutability guard and static local-write exclusion frame
captured caller locals. The callee itself may mutate older heap contents. -/
theorem environment {Γ Δ Ε Ξ rs ps Γf : Ctx}
    {f : Name} {args : Args C Γ ps} {ret : CallRet Γ rs Δ}
    {body : Prog C (rs ++ ps) Γf} {tail : Prog C Δ Ε}
    (h : Thin Ξ Γ) (separate : CallerFrame.Disjoint h ret)
    (within : Prog.withinM .nonpayable tail = true)
    (unwritten : ∀ (t : LTy) (i : Idx Ξ t),
      (t,((i.wk h).ext ret.ext).toNat) ∉ Prog.writesAt 0 tail)
    {σ : State C Γ} {out : Out C σ.H Ε}
    (executed : (Prog.cons (.call f args ret body) tail).run σ = .ok out) :
    TEnv.thin h (TEnv.drop (ret.ext.trans tail.ext) out.st.env) =
      TEnv.wk out.ext Ξ (TEnv.thin h σ.env) := by
  change (Prog.cons (.call f args ret body) tail).runR σ = _ at executed
  rw [Prog.runR_eq] at executed
  change TRun.seq (TRun.call args ret body.ext body.runC) tail.runC σ = _ at executed
  unfold TRun.seq at executed
  split at executed
  · rename_i first firstRun
    obtain ⟨last,lastRun,exported⟩ := tmap_ok_inv executed
    cases exported
    have callFrame := CallerFrame.call_environment h args ret body.ext body.runC separate firstRun
    have tailRun : tail.run first.st = .ok last := by
      change tail.runR first.st = _
      rw [Prog.runR_eq]
      exact lastRun
    have localFrame := (Prog.run_frameM tail within 0 tailRun).2
    apply TEnv.ext
    intro t i
    rw [CallerFrame.read_thin,TEnv.drop_trans,TEnv.get_wk,CallerFrame.read_thin]
    rw [← TEnv.get_ext_drop (i.wk h) ret.ext]
    have kept := localFrame t ((i.wk h).ext ret.ext) (Nat.zero_le _) (by
      simpa only [Nat.sub_zero] using unwritten t i)
    rw [kept,TEnv.get_ext_drop]
    have captured := congrArg (TEnv.get i) callFrame
    rw [CallerFrame.read_thin,TEnv.get_wk,CallerFrame.read_thin] at captured
    rw [captured,LTy.TDenote.wk_wk]
  · cases executed

theorem alias {Γ Δ Ε Ξ rs ps Γf : Ctx}
    {f : Name} {args : Args C Γ ps} {ret : CallRet Γ rs Δ}
    {body : Prog C (rs ++ ps) Γf} {tail : Prog C Δ Ε}
    (h : Thin Ξ Γ) (separate : CallerFrame.Disjoint h ret)
    (within : Prog.withinM .nonpayable tail = true)
    (unwritten : ∀ (t : LTy) (i : Idx Ξ t),
      (t,((i.wk h).ext ret.ext).toNat) ∉ Prog.writesAt 0 tail)
    {σ : State C Γ} {out : Out C σ.H Ε}
    (executed : (Prog.cons (.call f args ret body) tail).run σ = .ok out)
    {R : RefTy} (i : Idx Ξ (.mem R)) (r : HRef σ.H R)
    (old : TEnv.get (i.wk h) σ.env = some r) :
    TEnv.get (i.wk h) (TEnv.drop (ret.ext.trans tail.ext) out.st.env) =
      some (r.wk out.ext) := by
  have captured := congrArg (TEnv.get i) (environment h separate within unwritten executed)
  rw [CallerFrame.read_thin,TEnv.get_wk,CallerFrame.read_thin,old] at captured
  exact captured

/-- Target transport for an actual selected call-plus-tail candidate. Only
its checked tail is framed; callee heap mutation remains unrestricted. -/
theorem selected_target {b L frame : Nat} {Γ Δ Ε Ξ rs ps Γf : Ctx}
    {f : Name} {args : Args C Γ ps} {ret : CallRet Γ rs Δ} {F : Evm.Frag Γ}
    {body : Prog C (rs ++ ps) Γf} {tail : Prog C Δ Ε}
    (h : Thin Ξ Γ) (separate : CallerFrame.Disjoint h ret)
    (within : Prog.withinM .nonpayable tail = true)
    (unwritten : ∀ (t : LTy) (i : Idx Ξ t),
      (t,((i.wk h).ext ret.ext).toNat) ∉ Prog.writesAt 0 tail)
    (condition : Val C Γ .bool) (pre post : List (DispatchArm C Γ)) (fail : Stmt C Γ Γ)
    (compiled : Evm.Memory.Calls.Statement b F
      (DispatchArm.chain (pre ++ ⟨condition,.cons (.call f args ret body) tail⟩ :: post) fail))
    (σ : State C Γ) (miss : ∀ a ∈ pre, a.cond.evalT σ = .ok false)
    (hit : condition.evalT σ = .ok true) (out : Out C σ.H Ε)
    (executed : (Prog.cons (.call f args ret body) tail).run σ = .ok out)
    {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (repr : Evm.Memory.StateRepr L b frame F σ base m)
    (room : b + compiled.need ≤ frame)
    (capacity : Evm.Memory.AllocationInput b frame (compiled.cost σ) σ base m) :
    ∃ m' base', Evm.run compiled.code m = .ok m' 0 ∧
      Evm.Memory.StateRepr L b frame compiled.frag
        (out.st.drop (ret.ext.trans tail.ext)) base' m' ∧
      m'.stack = m.stack ∧ Evm.Memory.BaseExtends σ.H base base' ∧
      Evm.Memory.GrowsAllocator b frame (compiled.cost σ) σ base m
        (out.st.drop (ret.ext.trans tail.ext)) base' m' ∧
      TEnv.thin h (TEnv.drop (ret.ext.trans tail.ext) out.st.env) =
        TEnv.wk out.ext Ξ (TEnv.thin h σ.env) ∧
      ∀ (R : RefTy) (i : Idx Ξ (.mem R)) (r : HRef σ.H R),
        TEnv.get (i.wk h) σ.env = some r →
          m'.mem (Evm.cellOf b (i.wk h)) = .val (base r.id) := by
  obtain ⟨m',base',target,represented,stack,addresses,growth⟩ :=
    FiniteDispatch.selected_endpoint pre ⟨condition,.cons (.call f args ret body) tail⟩ post
      fail compiled σ miss hit out executed repr room capacity
  refine ⟨m',base',target,represented,stack,addresses,growth,
    environment h separate within unwritten executed,?_⟩
  intro R i r old
  exact PublishedDirectCalls.old_alias_at_entry_address
    (⟨out.st.drop (ret.ext.trans tail.ext),out.ext⟩ : Out C σ.H Γ)
    represented addresses r (i.wk h) (alias h separate within unwritten executed i r old)

/-- info: 'Solidity.Backend.InternalFlow.CallerTail.program_environment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms program_environment

/-- info: 'Solidity.Backend.InternalFlow.CallerTail.environment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms environment

/-- info: 'Solidity.Backend.InternalFlow.CallerTail.alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms alias

/-- info: 'Solidity.Backend.InternalFlow.CallerTail.selected_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms selected_target

end Solidity.Backend.InternalFlow.CallerTail
