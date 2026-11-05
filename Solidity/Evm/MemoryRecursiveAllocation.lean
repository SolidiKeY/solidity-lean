import Solidity.Evm.MemoryRecursiveRoom
import Solidity.Evm.MemoryRecursiveDemandBounds
import Solidity.Evm.MemoryAllocSourceExamples

/-! Allocating recursive-loop controls over the existing intrinsic source.
The body stops after its first successful turn. Computed recursive demands are
bounded by one word, and an actual allocator input discharges Room. The original
conditional correctness API is preserved alongside that concrete proof. -/
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

private theorem skipped_run (σ : State C Δ) : skipped.run σ=.ok ⟨σ,List.prefix_refl _⟩ := by
  rw [show skipped=Stmt.loop .auto (.simple (.bool false)) (skippedBody 3) from rfl,Stmt.run_loop]
  exact TLoop.run_of_iterN (n:=1) rfl

/-- The actual allocating/resetting body stops for every successful source run,
including its recursively nested but unentered false loops. -/
theorem body_stops (σ : State C Γ) (out : Solidity.Out C σ.H Δ)
    (run : body.run σ=.ok out) : condition.evalT (out.st.drop body.ext)=.ok false := by
  have allocated : allocate.run σ=.ok ⟨σ.allocPush (defaultArray .uint ⟨0,W_pos⟩),List.prefix_append _ _⟩ :=
    newArray_decl σ .uint (.lit 0 rfl) ⟨0,W_pos⟩ rfl
  have resetRun : reset.run (σ.allocPush (defaultArray .uint ⟨0,W_pos⟩))=
      .ok ⟨(σ.allocPush (defaultArray .uint ⟨0,W_pos⟩)).setLocal (.there .here) (indexValue ⟨0,W_pos⟩),List.prefix_refl _⟩ := rfl
  change (Prog.cons allocate (.cons reset (.cons skipped .nil))).run σ=.ok out at run
  rw [Prog.run_cons_ok allocated,Prog.run_cons_ok resetRun,Prog.run_cons_ok (skipped_run _)] at run
  cases run
  rfl

/-- Actual source allocator representation and cursor room for one word.
Availability is separate from the source demand bound below. -/
theorem one_word_input : AllocationInput 1 6 1 state bases machine := by
  exact .inr ⟨by decide,wmod 16,initial.2,by decide +kernel⟩

/-- Every actual reached demand of the computed recursive certificate consumes
at most its one allocating word, including completed and partial loop prefixes. -/
theorem demand_bound (amount : Nat) (demand : Demand compiled.cert state amount) : amount≤1 := by
  unfold compiled at demand
  apply demand_cons_nil_le _ state 1 ?_ demand
  intro amount inner
  apply stmtDemand_loop_one_turn_le _ _ _ _ state 1 body_stops ?_ ?_ inner
  · intro amount later
    apply demand_cons_base_nonallocating_le _ _ state 1 ?_ ?_ later
    · decide +kernel
    · decide +kernel
  · intro out amount cost
    apply cost_cons_base_nonallocating_le _ _ state 1 ?_ ?_ cost
    · decide +kernel
    · decide +kernel

/-- Concrete allocator room derived from the demand bound and represented cursor,
not from frame capacity or an assumed execution agreement. -/
theorem actual_room : Room compiled.cert 6 state bases machine := by
  intro amount demand
  exact one_word_input.of_le (demand_bound amount demand)

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
