import Solidity.Backend.InternalFlow.FiniteDispatch
/-! Captured caller subframes through actual intrinsic returns and finite
selected direct-call targets. Body heap mutation is permitted; this transports
locals/reference identity, not heap contents, rollback or general dispatch. -/
namespace Solidity.Backend.InternalFlow.CallerFrame
variable {C : Contract}

/-- Static destination separation only. This is not a simulation premise or
an extension of a source/compiler admission predicate. -/
def Disjoint {Γ Ξ : Ctx} (h : Thin Ξ Γ) : {rs Δ : Ctx} → CallRet Γ rs Δ → Prop
  | _, _, .val _ _ (some destination) =>
      ∀ (t : LTy) (i : Idx Ξ t), destination.toNat ≠ (i.wk h).toNat
  | _, _, _ => True

theorem read_thin {H : HTy} {Γ Δ : Ctx} {t : LTy}
    (h : Thin Γ Δ) (i : Idx Γ t) (env : TEnv C H Δ) :
    TEnv.get i (TEnv.thin h env) = TEnv.get (i.wk h) env := by
  have selected := TEnv.get_put h i (TEnv.thin h env) env
  rw [TEnv.put_thin] at selected
  exact selected.symm

/-- All return forms preserve the selected caller subenvironment after their
exported result prefix is removed; a scalar destination must be disjoint. -/
theorem export_environment {H : HTy} {Γ Δ Ξ rs : Ctx}
    (h : Thin Ξ Γ) (ret : CallRet Γ rs Δ) (separate : Disjoint h ret)
    (caller : TEnv C H Γ) (result : TEnv C H rs) :
    TEnv.thin h (TEnv.drop ret.ext (ret.leaveT caller result)) = TEnv.thin h caller := by
  cases ret with
  | none => rfl
  | val p name destination =>
    cases destination with
    | none => rfl
    | some destination =>
      change TEnv.thin h (TEnv.set destination result.1 caller) = TEnv.thin h caller
      apply TEnv.ext
      intro t i
      rw [read_thin,read_thin]
      exact TEnv.get_set_ne destination (i.wk h) result.1 caller (separate t i)
  | rets bs => exact congrArg (TEnv.thin h) (tuple_result_tail bs caller result)
  | mem R name hd hm => rfl
  | storage R name => rfl

/-- Actual successful calls transport the complete selected caller frame
along their real composed heap extension. Arbitrary body heap writes are not
claimed to preserve contents; only captured caller locals/results are framed. -/
theorem call_environment {Γ Δ Ξ rs ps Γf : Ctx}
    (h : Thin Ξ Γ) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (scope : Ext (rs ++ ps) Γf) (body : TStep C (rs ++ ps) Γf)
    (separate : Disjoint h ret) {σ : State C Γ} {out : Out C σ.H Δ}
    (executed : TRun.call args ret scope body σ = .ok out) :
    TEnv.thin h (TEnv.drop ret.ext out.st.env) =
      TEnv.wk out.ext Ξ (TEnv.thin h σ.env) := by
  unfold TRun.call at executed
  obtain ⟨arguments,ha,executed⟩ := tbind_ok_inv executed
  obtain ⟨produced,hb,exported⟩ := tbind_ok_inv executed
  cases Except.ok.inj exported
  exact (export_environment h ret separate _ _).trans (TEnv.thin_wk _ h σ.env)

/-- A one-call candidate uses the same actual call run; nil adds no work. -/
theorem single_call_environment {Γ Δ Ξ rs ps Γf : Ctx}
    {f : Name} {args : Args C Γ ps} {ret : CallRet Γ rs Δ}
    {body : Prog C (rs ++ ps) Γf} (h : Thin Ξ Γ) (separate : Disjoint h ret)
    {σ : State C Γ} {out : Out C σ.H Δ}
    (executed : (Prog.cons (.call f args ret body) .nil).run σ = .ok out) :
    TEnv.thin h (TEnv.drop ret.ext out.st.env) =
      TEnv.wk out.ext Ξ (TEnv.thin h σ.env) := by
  have single : (Prog.cons (.call f args ret body) .nil).run σ =
      TRun.call args ret body.ext body.runR σ := by
    change (Prog.cons (.call f args ret body) .nil).runR σ = _
    rw [Prog.runR_eq,Prog.runR_eq]
    change TRun.seq (TRun.call args ret body.ext body.runC) TRun.nil σ = _
    unfold TRun.seq
    cases TRun.call args ret body.ext body.runC σ <;> rfl
  rw [single] at executed
  exact call_environment h args ret body.ext body.runR separate executed

/-- Concrete old-reference identity follows from the whole captured frame;
there is deliberately no old-content equality for a mutating callee. -/
theorem single_call_alias {Γ Δ Ξ rs ps Γf : Ctx}
    {f : Name} {args : Args C Γ ps} {ret : CallRet Γ rs Δ}
    {body : Prog C (rs ++ ps) Γf} (h : Thin Ξ Γ) (separate : Disjoint h ret)
    {σ : State C Γ} {out : Out C σ.H Δ}
    (executed : (Prog.cons (.call f args ret body) .nil).run σ = .ok out)
    {R : RefTy} (i : Idx Ξ (.mem R)) (r : HRef σ.H R)
    (old : TEnv.get (i.wk h) σ.env = some r) :
    TEnv.get (i.wk h) (TEnv.drop ret.ext out.st.env) = some (r.wk out.ext) := by
  have framed := congrArg (TEnv.get i) (single_call_environment h separate executed)
  rw [read_thin,TEnv.get_wk,read_thin,old] at framed
  exact framed

/-- Finite selected direct-call transport consumes the actual public target
certificate and real input/cost/frame premises. Every old protected alias is
derived from call capture, not supplied as an output representation oracle. -/
theorem selected_target {b L frame : Nat} {Γ Δ Ξ rs ps Γf : Ctx}
    {f : Name} {args : Args C Γ ps} {ret : CallRet Γ rs Δ} {F : Evm.Frag Γ}
    {body : Prog C (rs ++ ps) Γf} (h : Thin Ξ Γ) (separate : Disjoint h ret)
    (condition : Val C Γ .bool) (pre post : List (DispatchArm C Γ))
    (fail : Stmt C Γ Γ)
    (compiled : Evm.Memory.Calls.Statement b F
      (DispatchArm.chain (pre ++ ⟨condition,.cons (.call f args ret body) .nil⟩ :: post) fail))
    (σ : State C Γ) (miss : ∀ a ∈ pre, a.cond.evalT σ = .ok false)
    (hit : condition.evalT σ = .ok true) (out : Out C σ.H Δ)
    (executed : (Prog.cons (.call f args ret body) .nil).run σ = .ok out)
    {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (repr : Evm.Memory.StateRepr L b frame F σ base m)
    (room : b + compiled.need ≤ frame)
    (capacity : Evm.Memory.AllocationInput b frame (compiled.cost σ) σ base m) :
    ∃ m' base', Evm.run compiled.code m = .ok m' 0 ∧
      Evm.Memory.StateRepr L b frame compiled.frag (out.st.drop ret.ext) base' m' ∧
      m'.stack = m.stack ∧ Evm.Memory.BaseExtends σ.H base base' ∧
      Evm.Memory.GrowsAllocator b frame (compiled.cost σ) σ base m
        (out.st.drop ret.ext) base' m' ∧
      TEnv.thin h (TEnv.drop ret.ext out.st.env) =
        TEnv.wk out.ext Ξ (TEnv.thin h σ.env) ∧
      ∀ (R : RefTy) (i : Idx Ξ (.mem R)) (r : HRef σ.H R),
        TEnv.get (i.wk h) σ.env = some r →
          m'.mem (Evm.cellOf b (i.wk h)) = .val (base r.id) := by
  obtain ⟨m',base',target,represented,stack,addresses,growth⟩ :=
    FiniteDispatch.selected_endpoint pre ⟨condition,.cons (.call f args ret body) .nil⟩ post
      fail compiled σ miss hit out executed repr room capacity
  refine ⟨m',base',target,represented,stack,addresses,growth,
    single_call_environment h separate executed,?_⟩
  intro R i r old
  exact PublishedDirectCalls.old_alias_at_entry_address
    (⟨out.st.drop ret.ext,out.ext⟩ : Out C σ.H Γ) represented addresses r (i.wk h)
    (single_call_alias h separate executed i r old)

/-- Selecting a live scalar destination as protected is rejected by the
static guard, not by an invented runtime failure. -/
theorem overlapping_destination {Γ : Ctx} {p : PrimTy} (name : Var)
    (destination : Idx Γ (.val p)) :
    ¬ Disjoint (Thin.refl : Thin Γ Γ) (.val p name (some destination)) := by
  intro separate
  exact separate (.val p) destination rfl

/-- info: 'Solidity.Backend.InternalFlow.CallerFrame.read_thin' depends on axioms: [propext] -/
#guard_msgs in #print axioms read_thin

/-- info: 'Solidity.Backend.InternalFlow.CallerFrame.export_environment' depends on axioms: [propext] -/
#guard_msgs in #print axioms export_environment

/-- info: 'Solidity.Backend.InternalFlow.CallerFrame.call_environment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms call_environment

/-- info: 'Solidity.Backend.InternalFlow.CallerFrame.single_call_environment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms single_call_environment

/-- info: 'Solidity.Backend.InternalFlow.CallerFrame.single_call_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms single_call_alias

/-- info: 'Solidity.Backend.InternalFlow.CallerFrame.selected_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms selected_target

/-- info: 'Solidity.Backend.InternalFlow.CallerFrame.overlapping_destination' depends on axioms: [propext] -/
#guard_msgs in #print axioms overlapping_destination

end Solidity.Backend.InternalFlow.CallerFrame
