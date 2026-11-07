import Solidity.Evm.MemoryLoopHorizonObjectLocalAlias
import Solidity.Evm.MemoryObjectArrayExamples

/-! Inhabited stored-local aliases across genuine allocating-loop execution.
The public populated fixed-parent fixture supplies three objects, two actual
initialized locals sharing a uint-array reference, and complete cursor40 input.
The owner-composed loop certificate transports the actual declaration code;
both bindings and their pointer24 local cells survive every bounded horizon.
The only premise is word-space 40+n<W; no generic input relation is assumed. -/
namespace Solidity.Evm.Memory.HorizonObjectLocalAliasControls

theorem populated_aliases (n : Nat) (space : 40 + n < W) :
    ∃ (C : Contract) (Γ : Ctx) (state : State C Γ) (initial : Machine)
      (compiled : Construction.CompiledLoop 1 (Frag.init Γ) (.simple (.bool true) : Val C Γ .bool)
        (HorizonObjectAllocating.body : Prog C Γ (.mem (.array (.prim .uint))::Γ)))
      (out : Solidity.Out C state.H Γ) (reached : Machine)
      (i j : Idx Γ (.mem (.array (.prim .uint)))) (r : HRef state.H (.array (.prim .uint))),
      state.H.length = 3 ∧ i ≠ j ∧
      TEnv.get i state.env = some r ∧ TEnv.get j state.env = some r ∧
      loopIterN (fun m => exec compiled.conditionCode 0 m) (fun m => exec compiled.bodyCode 0 m)
        n initial = .inl reached ∧
      Construction.CountedLoopPrefix (.simple (.bool true)) HorizonObjectAllocating.body state out n n ∧
      TEnv.get i out.st.env = some (r.wk out.ext) ∧
      TEnv.get j out.st.env = some (r.wk out.ext) ∧
      reached.mem (cellOf 1 i) = w[24] ∧ reached.mem (cellOf 1 j) = w[24] := by
  obtain ⟨out,nextBase,reached,target,hp,locals⟩ :=
    HorizonObjectAllocating.target_local_aliases
      ⟨_,_,HorizonObjectAllocating.cert 1 (by decide)⟩ n
      ObjectArrayExamples.initial_repr (by change 1 + 4 ≤ 8; omega)
      (.inr ⟨by decide,_,ObjectArrayExamples.initial_allocator,space⟩)
  obtain ⟨r,binding,word⟩ := ObjectArrayExamples.initial_repr.pointers (.there .here)
  have first := locals (.there .here) r binding
  have second := locals (.there (.there .here)) r binding
  refine ⟨_,_,_,_,_,out,reached,.there .here,.there (.there .here),r,rfl,?_,binding,binding,
    target,hp,first.1,second.1,?_,?_⟩
  · intro same
    cases same
  · exact first.2.2
  · exact second.2.2

end Solidity.Evm.Memory.HorizonObjectLocalAliasControls
