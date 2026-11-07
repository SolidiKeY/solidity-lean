import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarSource

/-! Shared native allocation/primitive-return constructors. Child execution
is the actual intrinsic run; concrete one/two-turn clients discharge it using
source_zero. No desired simulation or target state is assumed. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

theorem return_turn {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (σ : State C (Frame R)) (depth n : Nat) (bound : n+1<W) (ref : HRef σ.H R)
 (counter : TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env=countValue (n+1) bound)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame R) (.mem R)) σ.env=some ref)
 (out : Solidity.Out C (allocated σ).H (Frame R))
 (child : (body R hm depth).run (entered (allocated σ) n (by omega) (ref.wk (extension σ)))=.ok out)
 (value : TEnv.get (.here : Idx (Frame R) (.val .uint)) out.st.env=countValue n (by omega)) :
 let arguments : TEnv C (allocated σ).H (Parameters R) := (countValue n (by omega),(some (ref.wk (extension σ)),()))
 let returned := exported (result R) Ext.refl (allocated σ) arguments out
 (body R hm (depth+1)).run σ=.ok
  ⟨finished returned.st (n+1) bound,(extension σ).trans returned.ext⟩ := by
 dsimp only
 let parent := allocated σ
 let arguments : TEnv C parent.H (Parameters R) := (countValue n (by omega),(some (ref.wk (extension σ)),()))
 let returned := exported (result R) Ext.refl parent arguments out
 have parameters := allocated_parameters σ n bound ref counter alias
 have args := next_eval hm parent n bound (ref.wk (extension σ)) parameters.1 parameters.2
 have native := call_return (next R hm) (result R) Ext.refl (body R hm depth).runR parent arguments args out child
 have called : (.callRec "allocatingScalar" depth (next R hm) (result R) (fun _ => body R hm depth) :
  Stmt C (Frame R) (Frame R)).run parent=.ok returned := by
  change TRun.call (next R hm) (result R) (body R hm depth).ext (body R hm depth).runR parent=_
  have scope : (body (C:=C) R hm depth).ext=Ext.refl := Subsingleton.elim _ _
  rw [scope]
  exact native
 have live : TEnv.get (.here : Idx (Frame R) (.val .uint)) returned.st.env=countValue n (by omega) := by
  change TEnv.get .here (TEnv.set .here (TEnv.get (.here : Idx (Frame R) (.val .uint)) out.st.env)
   (TEnv.wk returned.ext (Frame R) parent.env))=_
  rw [TEnv.get_set,value]
 have advanced := increment_run returned.st n bound live
 have continued : (continuation R hm depth (fun _ => body R hm depth)).run parent=
  .ok ⟨finished returned.st (n+1) bound,returned.ext⟩ := by
  rw [continuation,Prog.run_cons_ok called,Prog.run_cons_ok advanced,Prog.run_nil]
  rfl
 rw [source_positive hm σ depth n bound counter,continued]
 rfl

theorem one_return {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (σ : State C (Frame R)) (depth : Nat) (ref : HRef σ.H R)
 (counter : TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env=countValue 1 (by decide))
 (alias : TEnv.get (.there (.there .here) : Idx (Frame R) (.mem R)) σ.env=some ref) :
 (body R hm (depth+2)).run σ=.ok ⟨finished (allocated σ) 1 (by decide),extension σ⟩ := by
 let child := entered (allocated σ) 0 W_pos (ref.wk (extension σ))
 have zero := source_zero hm child depth rfl
 have actual := return_turn hm σ (depth+1) 0 (by decide) ref counter alias
  ⟨finished child 0 W_pos,List.prefix_refl _⟩ zero rfl
 apply actual.trans
 apply congrArg Except.ok
 apply Solidity.Out.eq_of_st
 change (allocated σ).withEnv (Δ:=Frame R)
   (countValue 1 (by decide),(TEnv.wk (List.prefix_refl _) (Frame R) (allocated σ).env).2)=
  finished (allocated σ) 1 (by decide)
 rw [TEnv.wk_self]
 rfl

theorem two_return {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (σ : State C (Frame R)) (depth : Nat) (ref : HRef σ.H R)
 (counter : TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env=countValue 2 (by decide))
 (alias : TEnv.get (.there (.there .here) : Idx (Frame R) (.mem R)) σ.env=some ref) :
 (body R hm (depth+3)).run σ=.ok
  ⟨finished (allocated (allocated σ)) 2 (by decide),(extension σ).trans (extension (allocated σ))⟩ := by
 let child := entered (allocated σ) 1 (by decide) (ref.wk (extension σ))
 have nested := one_return hm child depth (ref.wk (extension σ)) rfl rfl
 have actual := return_turn hm σ (depth+2) 1 (by decide) ref counter alias
  ⟨finished (allocated child) 1 (by decide),extension child⟩ nested rfl
 apply actual.trans
 apply congrArg Except.ok
 apply Solidity.Out.eq_of_st
 change (allocated (allocated σ)).withEnv (Δ:=Frame R)
   (countValue 2 (by decide),(TEnv.wk (extension (allocated σ)) (Frame R) (allocated σ).env).2)=
  finished (allocated (allocated σ)) 2 (by decide)
 rfl

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.return_turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.return_turn

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.one_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.one_return

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.two_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarSource.two_return
