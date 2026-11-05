import Solidity.Backend.InternalFlow.RuntimeFrameCallAgreement

/-! Caller bindings after actual successful primitive-return calls. Heap
extension is retained in every transported value. No heap-content preservation,
alias liveness, target compiler or general recursive adequacy is assumed. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame
variable {C : Contract} {Γ ps Γf : Ctx} {p : PrimTy}

theorem assigned_env (f : Name) (args : Args C Γ ps) (name : Var)
 (destination : Idx Γ (.val p)) (body : Prog C (.val p :: ps) Γf)
 (caller : State C Γ) (out : Solidity.Out C caller.H Γ)
 (actual : (.call f args (.val p name (some destination)) body : Stmt C Γ Γ).run caller=.ok out) :
 ∃ value : p.Denote, out.st.env=TEnv.set destination value (TEnv.wk out.ext Γ caller.env) := by
 obtain ⟨arguments,bodyOut,evaluated,executed,rfl⟩ :=
  CallAgreement.output_of_call f args (.val p name (some destination)) body caller out actual
 refine ⟨(TEnv.take [.val p] (TEnv.drop body.ext bodyOut.st.env)).1,?_⟩
 rfl

theorem assigned_slot (f : Name) (args : Args C Γ ps) (name : Var)
 (destination : Idx Γ (.val p)) (body : Prog C (.val p :: ps) Γf)
 (caller : State C Γ) (out : Solidity.Out C caller.H Γ)
 (actual : (.call f args (.val p name (some destination)) body : Stmt C Γ Γ).run caller=.ok out)
 {t : LTy} (index : Idx Γ t) (different : index.toNat≠destination.toNat) :
 TEnv.get index out.st.env=LTy.TDenote.wk out.ext t (TEnv.get index caller.env) := by
 obtain ⟨value,restored⟩ := assigned_env f args name destination body caller out actual
 rw [restored]
 exact (TEnv.get_set_ne destination index value (TEnv.wk out.ext Γ caller.env) (Ne.symm different)).trans
  (TEnv.get_wk out.ext index caller.env)

theorem discarded_env (f : Name) (args : Args C Γ ps) (name : Var)
 (body : Prog C (.val p :: ps) Γf) (caller : State C Γ) (out : Solidity.Out C caller.H Γ)
 (actual : (.call f args (.val p name none) body : Stmt C Γ Γ).run caller=.ok out) :
 out.st.env=TEnv.wk out.ext Γ caller.env := by
 obtain ⟨arguments,bodyOut,evaluated,executed,rfl⟩ :=
  CallAgreement.output_of_call f args (.val p name none) body caller out actual
 rfl

theorem discarded_slot (f : Name) (args : Args C Γ ps) (name : Var)
 (body : Prog C (.val p :: ps) Γf) (caller : State C Γ) (out : Solidity.Out C caller.H Γ)
 (actual : (.call f args (.val p name none) body : Stmt C Γ Γ).run caller=.ok out)
 {t : LTy} (index : Idx Γ t) :
 TEnv.get index out.st.env=LTy.TDenote.wk out.ext t (TEnv.get index caller.env) := by
 rw [discarded_env f args name body caller out actual]
 exact TEnv.get_wk out.ext index caller.env

end Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.assigned_env' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.assigned_env

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.assigned_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.assigned_slot

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.discarded_env' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.discarded_env

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.discarded_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.discarded_slot
