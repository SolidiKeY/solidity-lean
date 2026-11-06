import Solidity.Evm.MemoryMixedLoopCompile
import Solidity.Evm.MemoryMixedLoopFinite
import Solidity.Evm.MemoryLoopScopeBudget
import Solidity.Evm.MemoryAllocSourceExamples

namespace Solidity.Evm.Memory.MixedLoops.AllocationControls
private def C : Contract := contract!{}
private def Γ : Ctx := [.val .uint]
private def R : RefTy := .array (.prim .uint)
private def Δ : Ctx := .mem R :: Γ
private def state : State C Γ := (State.init C).push (t:=.val .uint) (indexValue ⟨2,by decide⟩)
private def bases : Nat → Fin W := fun _=>⟨0,W_pos⟩
private def machine : Machine := {Machine.init with mem:=fun a=>if a=0 then w[16] else if a=1 then w[2] else if a=5 then w[99] else w[0]}
private theorem initial : StateRepr 1 1 6 (Frag.init Γ) state bases machine ∧
    StructAllocatorRepr state.heap bases 6 (wmod 16) machine := AllocSourceExamples.initial_repr
private def condition : Val C Γ .bool := .binop .gt rfl rfl (.simple (.local .here)) (.simple (.lit 0 rfl))
private def allocate : Stmt C Γ Δ := .declMem R (.user "fresh") (some (.newArr (.lit 0 rfl) rfl)) rfl rfl
private def reset : Stmt C Δ Δ := .assignLocal (.there .here) (.simple (.lit 0 rfl))
private def skipped : Stmt C Δ Δ := .loop .auto (.simple (.bool false)) (.nil : Prog C Δ Δ)
private def body : Prog C Γ Δ := .cons allocate (.cons reset (.cons skipped .nil))
private def compiled : Compiled 1 (Frag.init Γ) condition body :=
  (compile 1 (Frag.init Γ) condition body).get (by decide +kernel)
attribute [irreducible] compiled

private theorem skipped_run (σ : State C Δ) : skipped.run σ=.ok ⟨σ,List.prefix_refl _⟩ := by
  rw [show skipped=Stmt.loop .auto (.simple (.bool false)) (.nil : Prog C Δ Δ) from rfl,Stmt.run_loop]
  exact TLoop.run_of_iterN (n:=1) rfl

private theorem body_stops (σ : State C Γ) (out : Solidity.Out C σ.H Δ)
    (run : body.run σ=.ok out) : condition.evalT (out.st.drop body.ext)=.ok false := by
  have allocated : allocate.run σ=.ok ⟨σ.allocPush (defaultArray .uint ⟨0,W_pos⟩),List.prefix_append _ _⟩ :=
    newArray_decl σ .uint (.lit 0 rfl) ⟨0,W_pos⟩ rfl
  have resetRun : reset.run (σ.allocPush (defaultArray .uint ⟨0,W_pos⟩))=
      .ok ⟨(σ.allocPush (defaultArray .uint ⟨0,W_pos⟩)).setLocal (.there .here) (indexValue ⟨0,W_pos⟩),List.prefix_refl _⟩ := rfl
  change (Prog.cons allocate (.cons reset (.cons skipped .nil))).run σ=.ok out at run
  rw [Prog.run_cons_ok allocated,Prog.run_cons_ok resetRun,Prog.run_cons_ok (skipped_run _)] at run
  cases run
  rfl

private theorem actual_room : Room compiled.cert 6 state bases machine := by
  apply room_one_turn compiled.cert state bases machine body_stops
  apply LoopScopes.room_of_prefixBudget compiled.cert.bodyCert
    (show LoopScopes.prefixBudget compiled.cert.bodyCert state=some 1 by unfold compiled;decide +kernel)
  exact .inr ⟨by decide,wmod 16,initial.2,by decide +kernel⟩

theorem every_horizon (n : Nat) : Horizon compiled.cert 1 6 state bases machine
    (TLoop.iterN (horizonBody body) (fun o=>condition.evalT o.st) n ⟨state,List.prefix_refl _⟩)
    (loopIterN (fun m=>exec compiled.cond 0 m) (fun m=>exec compiled.code 0 m) n machine) :=
  compiled.cert.correct_horizon initial.1 (by unfold compiled;decide +kernel) actual_room n

theorem full_allocation : LoopScopes.Result 1 1 6 (Frag.init Γ) state bases machine
    (fun o cost=>Prefix compiled.cert state o cost)
    ((Stmt.loop .auto condition body).run state) (run [.loop compiled.cond compiled.code] machine) :=
  compiled.cert.correct .auto initial.1 (by unfold compiled;decide +kernel) actual_room

private def sourceObserve (r : TRes (Solidity.Out C [] Γ)) : Option (Int × Nat) := do
  let out ← r.toOption
  pure ((TEnv.get (.here : Idx Γ (.val .uint)) out.st.env).val,out.st.H.length)
private def targetObserve (r : Out) : Option (List Nat) := do
  match r with
  | .ok out _ => [out.mem 0,out.mem 1,out.mem 2,out.mem 5,out.mem 16].mapM fun word=>
      match word with | .val w=>some w.val | _=>none
  | _=>none
/-- info: (some (0, 1), some [17, 0, 16, 99, 0]) -/
#guard_msgs in
#eval (sourceObserve ((Stmt.loop .auto condition body).run state),targetObserve (run [.loop compiled.cond compiled.code] machine))

theorem finite_only (n : Nat) : CountedHorizon compiled.cert 1 6 state bases machine n
    (TLoop.iterN (horizonBody body) (fun o=>condition.evalT o.st) n ⟨state,List.prefix_refl _⟩)
    (loopIterN (fun m=>exec compiled.cond 0 m) (fun m=>exec compiled.code 0 m) n machine) :=
  compiled.cert.correct_finite_horizon n initial.1 (by unfold compiled;decide +kernel) (actual_room.finite n)

theorem zero_without_future_room : CountedHorizon compiled.cert 1 6 state bases machine 0
    (TLoop.iterN (horizonBody body) (fun o=>condition.evalT o.st) 0 ⟨state,List.prefix_refl _⟩)
    (loopIterN (fun m=>exec compiled.cond 0 m) (fun m=>exec compiled.code 0 m) 0 machine) :=
  compiled.cert.correct_finite_horizon 0 initial.1 (by unfold compiled;decide +kernel) (finiteRoom_zero compiled.cert state bases machine)

end Solidity.Evm.Memory.MixedLoops.AllocationControls
