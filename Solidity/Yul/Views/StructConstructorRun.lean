import Solidity.Yul.Views.LocalConstructorArguments

namespace Solidity.Yul.Views

/-- The actual constructor operands determine its typed field data. This cast
uses the real owner declaration certificate, not a supplied layout agreement. -/
def structConstructorData {E : Source.Env} {name : Source.DeclName} {ps : List Source.STy}
    (typed : (E.structFields name .memory).map (List.map Prod.snd)=some ps)
    (values : Source.Vals E.layout ps) : Source.Data E.layout (.struct .memory name) :=
  .struct ((structConstructor_types E name ps typed).symm ▸ constructorFields ps values)

/-- Actual evalE/argument/fields/allocation composition, with complete source
state equality. Only recognized identity-local operands are claimed here. -/
theorem structConstructor_run {E Γ name ps} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ)
    (typed : (E.structFields name .memory).map (List.map Prod.snd)=some ps)
    (args : Source.RConvArgs E Γ ps) (values : Source.Vals E.layout ps)
    (step : localConstructorValues s.1 ps args=some values) :
    (Source.evalE G F (n+ps.length+2) (.structNew typed args)).run s=
      (.ok (.val (Source.Val.memRef rfl s.2.heap.next)),
        objectAllocatedState s (structConstructorData typed values)) := by
  have fields := structConstructor_types E name ps typed
  have argsRun := localConstructorValues_run G F n s ps args values step
  change (Source.evalE G F ((n+ps.length+1)+1) (.structNew typed args)).run s= _
  rw [Source.evalE,Source.Hoare.run_bind,argsRun]
  simp only []
  subst ps
  rw [Source.Hoare.run_bind,constructorFields_run]
  simp only []
  rw [Source.Hoare.run_bind,objectAllocRef_run _ _ rfl]
  rfl

/-- Constructor data validity is derived from the actual extracted local
operands and owner locals typing, including aliased child ownership. -/
theorem structConstructorData_valid {E Γ name ps} (H : Source.HeapTy)
    (locals : Source.Locals E.layout Γ)
    (typed : (E.structFields name .memory).map (List.map Prod.snd)=some ps)
    (args : Source.RConvArgs E Γ ps) (values : Source.Vals E.layout ps)
    (step : localConstructorValues locals ps args=some values)
    (ok : Source.LocalsOK E H locals) :
    Source.DataOK E H (structConstructorData typed values) := by
  have valid := constructorFields_valid H values (localConstructorValues_valid H locals ok ps args values step)
  have fields := structConstructor_types E name ps typed
  subst ps
  exact .struct valid

theorem structConstructorData_inner {E name ps}
    (typed : (E.structFields name .memory).map (List.map Prod.snd)=some ps)
    (values : Source.Vals E.layout ps) : Source.Data.Inner (E := E) (structConstructorData typed values) := by
  have fields := structConstructor_types E name ps typed
  subst ps
  exact constructorFields_inner values

/-- Actual constructor state and every-ORIGINAL-H owner MemOK. Data validity
is derived from initial MemOK, rather than assumed as a result-view premise. -/
theorem structConstructor_MemOK {E Γ name ps} (H : Source.HeapTy)
    (s : Source.EMState E Γ)
    (typed : (E.structFields name .memory).map (List.map Prod.snd)=some ps)
    (args : Source.RConvArgs E Γ ps) (values : Source.Vals E.layout ps)
    (step : localConstructorValues s.1 ps args=some values) (ok : Source.MemOK E H s) :
    Source.MemOK E H (objectAllocatedState s (structConstructorData typed values)) ∧
      (Source.Val.memRef (τ := Source.STy.struct .memory name) rfl s.2.heap.next).RefOK E
        (objectAllocatedState s (structConstructorData typed values)).2.heap.ty := by
  exact objectAllocRef_MemOK H s _ rfl True.intro (structConstructorData_inner typed values)
    (structConstructorData_valid _ s.1 typed args values step ok.1.2) ok

/-- Reuse bridge to the concrete physical allocation API. Its complete map,
retained-capacity and unchanged-writeback theorems now describe this actual
evalE producer, without a second evaluator or assumed correspondence. -/
theorem structConstructor_eval_alloc {E Γ name ps} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ)
    (typed : (E.structFields name .memory).map (List.map Prod.snd)=some ps)
    (args : Source.RConvArgs E Γ ps) (values : Source.Vals E.layout ps)
    (step : localConstructorValues s.1 ps args=some values) :
    (Source.evalE G F (n+ps.length+2) (.structNew typed args)).run s=
      (do let value ← Source.allocRef (structConstructorData typed values)
          pure (Source.RVal.val value)).run s := by
  rw [structConstructor_run G F n s typed args values step,Source.Hoare.run_bind,objectAllocRef_run _ _ rfl]
  rfl

/-- Any ACTUAL argument failure, including effects already made by earlier
arguments, is passed through unchanged. This does not claim that the local
collector instruments arbitrary argument intermediates. -/
theorem structConstructor_args_halt {E Γ name ps} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s after : Source.EMState E Γ) (reason : Source.Halt)
    (typed : (E.structFields name .memory).map (List.map Prod.snd)=some ps)
    (args : Source.RConvArgs E Γ ps)
    (failed : (Source.evalConvArgs G F n args).run s=(.error reason,after)) :
    (Source.evalE G F (n+1) (.structNew typed args)).run s=(.error reason,after) := by
  rw [Source.evalE,Source.Hoare.run_bind,failed]

end Solidity.Yul.Views
