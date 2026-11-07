import Solidity.Evm.MemoryLoopHorizonObjectAllocatingTarget
import Solidity.Evm.MemoryLoopHorizonObjectHeapKeeps

/-! Initialization of newly appended uint arrays in the actual allocating
loop. Owner allocation splitting identifies each reference as old or fresh;
genuine prefixes retain zero lengths for all objects appended after the
initial heap. The reached complete representation then fixes their target
header words to zero under the existing strong capacity premises. -/
namespace Solidity.Evm.Memory.HorizonObjectAllocating
variable {C : Contract} {Γ : Ctx}

theorem body_ref_cases {state : State C Γ}
    {out : Solidity.Out C state.H (.mem (.array (.prim .uint))::Γ)}
    (step : body.run state = .ok out) (r : HRef out.st.H (.array (.prim .uint))) :
    (∃ old : HRef state.H (.array (.prim .uint)), old.wk out.ext = r) ∨
      (r.id = state.H.length ∧ out.st.heap.len r .dyn = 0) := by
  change TRun.declMem (.array (.prim .uint)) none rfl state = .ok out at step
  rw [Objects.defaultEmpty_decl] at step
  cases step
  rcases Objects.allocRef_split state.heap (Objects.emptyArray (.prim .uint)) r with
    ⟨old,rfl⟩ | ⟨same,identity⟩
  · exact .inl ⟨old,rfl⟩
  · cases same
    cases identity
    refine .inr ⟨rfl,?_⟩
    change (state.heap.alloc (Objects.emptyArray (.prim .uint))).1.len
      (state.heap.alloc (Objects.emptyArray (.prim .uint))).2 .dyn = 0
    simp only [Heap.len, Heap.get_alloc, MObj.elems_wk, List.length_map, MObj.elems_dyn, Objects.emptyArray, List.length_nil]

theorem prefix_new_empty {state : State C Γ} {out : Solidity.Out C state.H Γ} {cost count : Nat}
    (hp : Construction.CountedLoopPrefix (.simple (.bool true)) body state out cost count)
    (r : HRef out.st.H (.array (.prim .uint))) (fresh : state.H.length ≤ r.id) :
    out.st.heap.len r .dyn = 0 := by
  induction hp with
  | start =>
    have bound : r.id < state.H.length := r.id_lt
    omega
  | next hp condition step ih =>
    rcases body_ref_cases step r with ⟨old,same⟩ | ⟨identity,empty⟩
    · subst r
      have kept : Heap.Keeps _ _ _ := body_keeps_heap step
      have length : _ = _ := congrArg (fun object => (MObj.elems .dyn object).length) (kept old)
      simp only [MObj.elems_wk, List.length_map] at length
      exact length.trans (ih old fresh)
    · exact empty

theorem target_new_array_headers {L b frame : Nat}
    (compiled : Construction.CompiledLoop b (Frag.init Γ) (.simple (.bool true) : Val C Γ .bool) body)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine} (n : Nat)
    (repr : Objects.StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b + frameNeedProg (body : Prog C Γ _) ≤ frame)
    (demand : Objects.AllocationInput b frame n state base machine) :
    ∃ (out : Solidity.Out C state.H Γ) (nextBase : Nat → Fin W) (reached : Machine),
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        n machine = .inl reached ∧
      Construction.CountedLoopPrefix (.simple (.bool true)) body state out n n ∧
      (∀ r : HRef out.st.H (.array (.prim .uint)), state.H.length ≤ r.id →
        reached.mem (nextBase r.id).val = w[0]) := by
  obtain ⟨out,nextBase,reached,target,source,hp,current,stack,bases,grows⟩ :=
    target_pending compiled n repr capacity demand
  refine ⟨out,nextBase,reached,target,hp,?_⟩
  intro r fresh
  have empty := prefix_new_empty hp r fresh
  have length := (current.heap.arrays .dyn r).length rfl
  simpa only [empty] using length

end Solidity.Evm.Memory.HorizonObjectAllocating
