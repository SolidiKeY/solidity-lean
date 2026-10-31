import Solidity.Semantics.RunFrame

/-!
# Independent laws for the published intrinsic call frames

These theorems consume CallRet, TEnv and TRun.call unchanged. They do not
provide the missing backend memory-frame representation or source lowering.
-/
namespace Solidity.Backend.InternalFlow

variable {C : Contract} {H : HTy} {Γ Δ rs ps Γf : Ctx}

/-- An exported storage result retains the exact reference and caller tail. -/
theorem storage_result (R : RefTy) (name : Var) (caller : TEnv C H Γ)
    (result : TEnv C H [.alias R]) :
    (CallRet.storage R name).leaveT caller result = (result.1, caller) := rfl

/-- Memory results retain the reference, including its heap-typing proof. -/
theorem memory_result (R : RefTy) (name : Var)
    (hd : (Ty.ref R).defaultOkS = true) (hm : (Ty.ref R).mapFree = true)
    (caller : TEnv C H Γ) (result : TEnv C H [.mem R]) :
    (CallRet.mem R name hd hm).leaveT caller result = (result.1, caller) := rfl

/-- A scalar result only changes its specified destination. -/
theorem scalar_result_other {p : PrimTy} {t : LTy}
    (destination : Idx Γ (.val p)) (other : Idx Γ t)
    (hne : destination.toNat ≠ other.toNat) (name : Var)
    (caller : TEnv C H Γ) (result : TEnv C H [.val p]) :
    TEnv.get other ((CallRet.val p name (some destination)).leaveT caller result) =
      TEnv.get other caller :=
  TEnv.get_set_ne destination other result.1 caller hne

/-- Tuple export preserves the complete pre-existing caller tail. -/
theorem tuple_result_tail (binders : Binders rs)
    (caller : TEnv C H Γ) (result : TEnv C H rs) :
    TEnv.drop (Ext.append Γ rs) ((CallRet.rets binders).leaveT caller result) = caller :=
  TEnv.drop_append rs result caller

/-- Storage-reference identity survives two successive heap extensions. -/
theorem alias_heap_transport {H' H'' : HTy} (e : H <+: H') (f : H' <+: H'')
    (R : RefTy) (a : Option (SRef C (.ref R))) :
    LTy.TDenote.wk f (.alias R) (LTy.TDenote.wk e (.alias R) a) = a := rfl

/-- Memory-reference identity survives two independently supplied extensions. -/
theorem memory_heap_identity {H' H'' : HTy} (e : H <+: H') (f : H' <+: H'')
    (R : RefTy) (a : HRef H R) : ((a.wk e).wk f).id = a.id := rfl

/-- Exact intrinsic call return equation, including the body's heap growth.
The premises are actual argument evaluation and an actual body execution;
neither is a backend simulation premise or counted as discharged here. -/
theorem call_return (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (scope : Ext (rs ++ ps) Γf) (body : TStep C (rs ++ ps) Γf)
    (caller : State C Γ) (arguments : TEnv C caller.H ps)
    (ha : args.evalT caller = .ok arguments)
    (out : Out C (ret.enterT (caller.withEnv arguments)).st.H Γf)
    (hb : body (ret.enterT (caller.withEnv arguments)).st = .ok out) :
    TRun.call args ret scope body caller =
      .ok ⟨out.st.withEnv
        (ret.leaveT
          (TEnv.wk ((ret.enterT (caller.withEnv arguments)).ext.trans out.ext) Γ caller.env)
          (TEnv.take rs (TEnv.drop scope out.st.env))),
        (ret.enterT (caller.withEnv arguments)).ext.trans out.ext⟩ := by
  simp only [TRun.call, ha, ok_bind, hb]
  rfl

/-- A body failure is propagated with its original class and exact bytes.
TRes carries no failed state: this is not a rollback theorem. -/
theorem call_body_failure (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (scope : Ext (rs ++ ps) Γf) (body : TStep C (rs ++ ps) Γf)
    (caller : State C Γ) (arguments : TEnv C caller.H ps)
    (ha : args.evalT caller = .ok arguments) (failure : THalt)
    (hb : body (ret.enterT (caller.withEnv arguments)).st = .error failure) :
    TRun.call args ret scope body caller = .error failure := by
  simp only [TRun.call, ha, ok_bind, hb, error_bind]
  <;> rfl

/-- Renaming of result export consumes the published dependent-signature law. -/
theorem result_renaming (h : Thin Γ Δ) (caller : TEnv C H Γ)
    (background : TEnv C H Δ) (ret : CallRet Γ rs Γf) (result : TEnv C H rs) :
    ∃ background', TEnv.off (ret.wk h).2.1 background' = TEnv.off h background ∧
      (ret.wk h).2.2.leaveT (TEnv.put h caller background) result =
      TEnv.put (ret.wk h).2.1 (ret.leaveT caller result) background' :=
  CallRet.leaveT_wk h caller background ret result

end Solidity.Backend.InternalFlow
