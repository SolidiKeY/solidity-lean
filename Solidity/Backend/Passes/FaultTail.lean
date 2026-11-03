import Solidity.Backend.Passes.FaultReached

/-! Shared successful-prefix maps for a reached typed divergence. The fault
is obtained from its transported Input, never a raw fault-tail theorem. -/
namespace Solidity.Backend.Passes
open Solidity.Evm Solidity.Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ Ξ Ω : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ} {R : Prog C Ξ Ω}

theorem compilation_third_fault_shared
    (a : Compilation b F P) (d : Compilation b a.frag Q) (e : Compilation b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : a.Input L frame base σ m)
    (ad : MappedBoundaryLink a d L frame base σ m)
    (de : ReachedMappedLink a d e L frame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    (hr : Evm.Prog.pays R = false)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o)
    {u : Solidity.Out C o.st.H Ξ} (hu : Q.run o.st = .ok u)
    (he : R.run u.st = .error .diverge) :
    ∃ (mid next : Machine) (mb nb : Nat → Fin W), ∀ tail,
      run a.code {m with stack := tail} = .ok {mid with stack := tail} 0 ∧
      run d.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
      MappedOutput a (L + Evm.Prog.pushes P) frame base σ {m with stack := tail}
        o.st {mid with stack := tail} mb ∧
      d.Input (L + Evm.Prog.pushes P) frame mb o.st {mid with stack := tail} ∧
      MappedOutput d ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q) frame mb o.st
        {mid with stack := tail} u.st {next with stack := tail} nb ∧
      e.Input ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q) frame nb u.st
        {next with stack := tail} ∧
      run e.code {next with stack := tail} = .fault ∧
      run (a.code ++ (d.code ++ e.code)) {m with stack := tail} = .fault ∧
      run ((a.code ++ d.code) ++ e.code) {m with stack := tail} = .fault := by
  obtain ⟨mid, mb, _, _, hall⟩ := compilation_success_shared_mapped a hi hp hs
  have em : {m with stack := m.stack} = m := by cases m; rfl
  have ha := (hall m.stack).1
  have ma := (hall m.stack).2
  rw [em] at ha ma
  have di := ad o _ mb hs ha ma
  obtain ⟨next, nb, _, _, hnext⟩ := compilation_success_shared_mapped d di hq hu
  have hn := (hnext m.stack).1
  have md := (hnext m.stack).2
  have ei := de o _ mb hs ha ma u _ nb hu hn md
  refine ⟨mid, next, mb, nb, ?_⟩
  intro tail
  have dit := compilation_input_stack d di tail
  have eit := compilation_input_stack e ei tail
  have hf := (compilation_fault_iff e eit hr).mpr he
  have ht : run (a.code ++ (d.code ++ e.code)) {m with stack := tail} = .fault := by
    rw [run_append_ok (hall tail).1, run_append_ok (hnext tail).1]
    exact hf
  exact ⟨(hall tail).1, (hnext tail).1, (hall tail).2, dit,
    (hnext tail).2, eit, hf, ht, by simpa only [List.append_assoc] using ht⟩

end Solidity.Backend.Passes
