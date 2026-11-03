import Solidity.Evm.MemoryRecursiveRoom
import Solidity.Evm.MemoryAllocSourceExamples
namespace Solidity.Evm.Memory.Recursive.AllocationControls
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
private def skippedBody : Nat → Prog C Δ Δ
  | 0=>.nil
  | n+1=>.cons (.loop .auto (.simple (.bool false)) (skippedBody n)) .nil
private def skipped : Stmt C Δ Δ := .loop .auto (.simple (.bool false)) (skippedBody 3)
private def body : Prog C Γ Δ := .cons allocate (.cons reset (.cons skipped .nil))
private def program : Prog C Γ Γ := .cons (.loop .auto condition body) .nil
private def compiled : CompiledProg 1 (Frag.init Γ) program :=
  (compileProg 1 program (Frag.init Γ)).get (by decide +kernel)
attribute [irreducible] compiled

/-- The recursive compiler records the actual allocating leaf rather than
silently using the nonallocating shortcut. The full input still requires
reached allocator bounds; frame capacity alone is not allocation room. -/
theorem allocating : compiled.cert.allocates=true := by unfold compiled;decide +kernel

theorem frame_need : 1+compiled.cert.need≤6 := by unfold compiled;decide +kernel

/-- Closed certificate correctness includes actual allocator growth. The
allocation input is explicit here; the observations below are runtime controls,
not a proof that capacity alone supplies that input. -/
theorem correct (room : Room compiled.cert 6 state bases machine) :
    LoopScopes.Result 1 1 6 compiled.frag state bases machine
      (fun out amount=>Cost compiled.cert state out amount)
      (program.run state) (run compiled.code machine) :=
  compiled.correct ⟨initial.1,frame_need,room⟩

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
#eval (sourceObserve (program.run state),targetObserve (run compiled.code machine))


end Solidity.Evm.Memory.Recursive.AllocationControls
