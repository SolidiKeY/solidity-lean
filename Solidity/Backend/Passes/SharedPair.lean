import Solidity.Backend.Passes.TripleSequence

/-! Shared actual outputs for two typed compiled stages. This retains both
physical Inputs and full map relations; success alone justifies stack transport. -/
namespace Solidity.Backend.Passes
open Evm Evm.Compiler

theorem compilation_pair_shared
    {C : Contract} {b L frame : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ}
    {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}
    (left : Compilation b F P) (right : Compilation b left.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : left.Input L frame base σ m) (empty : m.stack = [])
    (link : MappedBoundaryLink left right L frame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o)
    {u : Solidity.Out C o.st.H Ξ} (hu : Q.run o.st = .ok u) :
    ∃ (mb nb : Nat → Fin W) (mid final : Machine),
      (P.join Q).run σ = .ok ⟨u.st,o.ext.trans u.ext⟩ ∧
      mid.stack = [] ∧ final.stack = [] ∧ ∀ tail,
        left.Input L frame base σ {m with stack := tail} ∧
        run left.code {m with stack := tail} = .ok {mid with stack := tail} 0 ∧
        right.Input (L + Evm.Prog.pushes P) frame mb o.st {mid with stack := tail} ∧
        run right.code {mid with stack := tail} = .ok {final with stack := tail} 0 ∧
        run (left.code ++ right.code) {m with stack := tail} = .ok {final with stack := tail} 0 ∧
        MappedOutput left (L + Evm.Prog.pushes P) frame base σ {m with stack := tail}
          o.st {mid with stack := tail} mb ∧
        MappedOutput right ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q)
          frame mb o.st {mid with stack := tail} u.st {final with stack := tail} nb := by
  obtain ⟨mb,nb,mid,final,hsource,hm,hwhole,hstack,ml,mr⟩ :=
    compilation_mapped_success left right hi link hp hq hs hu
  have hir := link o mid mb hs hm ml
  have hr : run right.code mid = .ok final 0 := by
    rw [run_append_ok hm] at hwhole
    exact hwhole
  obtain ⟨actual, ha, hstackLeft, _⟩ := compilation_success left hi hp hs
  have equal : actual = mid := (Evm.Out.ok.inj (ha.symm.trans hm)).1
  have sm : mid.stack = [] := by cases equal; exact hstackLeft.trans empty
  have sf : final.stack = [] := hstack.trans empty
  refine ⟨mb,nb,mid,final,hsource,sm,sf,?_⟩
  intro tail
  have transport (code : List Instr) (x y : Machine)
      (hx : x.stack = []) (hy : y.stack = []) (h : run code x = .ok y 0) :
      run code {x with stack := tail} = .ok {y with stack := tail} 0 := by
    have hh := run_tail code x tail (by rw [h]; intro bad; cases bad)
    simpa only [h,appendOut,appendTail,hx,hy,List.nil_append] using hh
  exact ⟨compilation_input_stack left hi tail,transport _ _ _ empty sm hm,
    compilation_input_stack right hir tail,transport _ _ _ sm sf hr,
    transport _ _ _ empty sf (by rw [run_append_ok hm]; exact hr),
    mapped_output_stack left ml tail tail,mapped_output_stack right mr tail tail⟩

end Solidity.Backend.Passes
