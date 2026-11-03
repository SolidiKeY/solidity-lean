import Solidity.Backend.Passes.CapturedValueStability
namespace Solidity.Backend.Passes.CapturedValueStability
open Evm Evm.Memory Evm.Compiler
variable {C : Contract} {Γ : Ctx} {p q : PrimTy}

theorem joined_readback {b L frame : Nat} {F : Frag Γ}
    (x : Var) (e : Val C Γ p) (first : CompiledVal b F e)
    (dst : Idx Γ (.val q)) (update : Val C (.val p :: Γ) q)
    (second : CompiledVal b (F.push (.val p) .ok) update)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (capacity : b+(Γ.length+1) ≤ frame)
    (v : p.Denote) (u : q.Denote)
    (hv : e.evalT state = .ok v)
    (hu : update.evalT (state.push (t := .val p) v) = .ok u) :
    ∃ captured updated, ReprV p v captured ∧ ReprV q u updated ∧ ∀ tail,
      let cm := writeMachine {machine with stack := tail}
        (cell (b+Γ.length)) captured
      let em := writeMachine cm (cellOf b (.there (u := .val p) dst)) updated
      run ((compiled x e first dst update second).code ++
        [.mload (cell (b+Γ.length))]) {machine with stack := tail} =
        .ok (em.push captured) 0 := by
  obtain ⟨captured,updated,hc,hu,runs⟩ := execution x e first dst update second represented capacity v u hv hu
  refine ⟨captured,updated,hc,hu,?_⟩
  intro tail
  have h := runs tail
  rw [run_append_ok h.2.2.2.2.1]
  exact h.2.2.2.2.2

end Solidity.Backend.Passes.CapturedValueStability
