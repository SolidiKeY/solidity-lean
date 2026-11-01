import Solidity.Roadmap.V16.MemoryCallConsumer

/-! Actual published loop/compiler specification consumers. Room is a reached
prefix obligation; Cost is relational, never legacy allocationCost. Divergence
is retained as source diverge / word-machine fault, not external EVM behavior. -/
namespace Solidity.Roadmap.V16
open Solidity.Evm

theorem loop_result {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (out : Memory.Loops.CompiledProg b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (input : (Compiler.Compilation.memoryLoops out).Input L frame base σ m) :
    Memory.Loops.Result out.cert L frame σ base m (P.run σ) (run out.code m) := by
  exact out.cert.correct input.1 input.2.1 input.2.2

theorem loop_not_exhausted {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (out : Memory.Loops.CompiledProg b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (input : (Compiler.Compilation.memoryLoops out).Input L frame base σ m) :
    P.run σ ≠ .error .exhausted := by
  intro h
  rcases loop_result out input with ⟨o, _, _, _, hs, _⟩ | ⟨hs, _⟩ | ⟨hs, _⟩
  all_goals rw [h] at hs; cases hs

theorem loop_diamond {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (out : Memory.Loops.CompiledProg b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (input : (Compiler.Compilation.memoryLoops out).Input L frame base σ m) {φ : Spec C Δ}
    (diamond : Spec.sat σ (.diamond P φ)) :
    ∃ o m' base' cost, P.run σ = .ok o ∧ run out.code m = .ok m' 0 ∧
      Memory.Loops.Cost out.cert σ o cost ∧
      Memory.StateRepr L b frame out.frag o.st base' m' ∧ m'.stack = m.stack ∧
      Memory.BaseExtends σ.H base base' ∧
      Memory.GrowsAllocator b frame cost σ base m o.st base' m' ∧ Spec.sat o.st φ := by
  obtain ⟨o, source, post⟩ := spec_diamond_success diamond (loop_not_exhausted out input)
  rcases loop_result out input with
    ⟨u, m', base', cost, hs, ht, hc, hr, stack, he, hg⟩ | ⟨hs, _⟩ | ⟨hs, _⟩
  · have eq : u = o := Except.ok.inj (hs.symm.trans source)
    subst u
    exact ⟨o, m', base', cost, source, ht, hc, hr, stack, he, hg, post⟩
  all_goals rw [source] at hs; cases hs

theorem loop_box {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (out : Memory.Loops.CompiledProg b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (input : (Compiler.Compilation.memoryLoops out).Input L frame base σ m) {φ : Spec C Δ}
    (box : Spec.sat σ (.box P φ)) :
    (∃ o m' base' cost, P.run σ = .ok o ∧ run out.code m = .ok m' 0 ∧
      Memory.Loops.Cost out.cert σ o cost ∧
      Memory.StateRepr L b frame out.frag o.st base' m' ∧ m'.stack = m.stack ∧
      Memory.BaseExtends σ.H base base' ∧
      Memory.GrowsAllocator b frame cost σ base m o.st base' m' ∧ Spec.sat o.st φ) ∨
      (P.run σ = .error .revert ∧ run out.code m = .revert) ∨
      (P.run σ = .error .diverge ∧ run out.code m = .fault) := by
  rcases loop_result out input with
    ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg⟩ | h | h
  · exact .inl ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg, spec_box_post box hs⟩
  · exact .inr (.inl h)
  · exact .inr (.inr h)

theorem loop_divergence {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (out : Memory.Loops.CompiledProg b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (input : (Compiler.Compilation.memoryLoops out).Input L frame base σ m) (source : P.run σ = .error .diverge) :
    run out.code m = .fault := by
  rcases loop_result out input with ⟨o, _, _, _, hs, _⟩ | ⟨hs, _⟩ | ⟨_, ht⟩
  · rw [source] at hs; cases hs
  · rw [source] at hs; cases hs
  · exact ht

theorem scoped_loop_result {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (out : Memory.LoopScopes.CompiledProg b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (input : (Compiler.Compilation.memoryLoopScopes out).Input L frame base σ m) :
    Memory.LoopScopes.Result L b frame out.frag σ base m
      (fun o cost => Memory.LoopScopes.Cost out.cert σ o cost) (P.run σ) (run out.code m) := by
  exact out.cert.correct σ base m input.1 input.2.1 input.2.2

theorem scoped_loop_not_exhausted {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (out : Memory.LoopScopes.CompiledProg b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (input : (Compiler.Compilation.memoryLoopScopes out).Input L frame base σ m) :
    P.run σ ≠ .error .exhausted := by
  intro h
  rcases scoped_loop_result out input with ⟨o, _, _, _, hs, _⟩ | ⟨hs, _⟩ | ⟨hs, _⟩
  all_goals rw [h] at hs; cases hs

theorem scoped_loop_diamond {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (out : Memory.LoopScopes.CompiledProg b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (input : (Compiler.Compilation.memoryLoopScopes out).Input L frame base σ m) {φ : Spec C Δ}
    (diamond : Spec.sat σ (.diamond P φ)) :
    ∃ o m' base' cost, P.run σ = .ok o ∧ run out.code m = .ok m' 0 ∧
      Memory.LoopScopes.Cost out.cert σ o cost ∧
      Memory.StateRepr L b frame out.frag o.st base' m' ∧ m'.stack = m.stack ∧
      Memory.BaseExtends σ.H base base' ∧
      Memory.GrowsAllocator b frame cost σ base m o.st base' m' ∧ Spec.sat o.st φ := by
  obtain ⟨o, source, post⟩ := spec_diamond_success diamond (scoped_loop_not_exhausted out input)
  rcases scoped_loop_result out input with
    ⟨u, m', base', cost, hs, ht, hc, hr, stack, he, hg⟩ | ⟨hs, _⟩ | ⟨hs, _⟩
  · have eq : u = o := Except.ok.inj (hs.symm.trans source)
    subst u
    exact ⟨o, m', base', cost, source, ht, hc, hr, stack, he, hg, post⟩
  all_goals rw [source] at hs; cases hs

theorem scoped_loop_box {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (out : Memory.LoopScopes.CompiledProg b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (input : (Compiler.Compilation.memoryLoopScopes out).Input L frame base σ m) {φ : Spec C Δ}
    (box : Spec.sat σ (.box P φ)) :
    (∃ o m' base' cost, P.run σ = .ok o ∧ run out.code m = .ok m' 0 ∧
      Memory.LoopScopes.Cost out.cert σ o cost ∧
      Memory.StateRepr L b frame out.frag o.st base' m' ∧ m'.stack = m.stack ∧
      Memory.BaseExtends σ.H base base' ∧
      Memory.GrowsAllocator b frame cost σ base m o.st base' m' ∧ Spec.sat o.st φ) ∨
      (P.run σ = .error .revert ∧ run out.code m = .revert) ∨
      (P.run σ = .error .diverge ∧ run out.code m = .fault) := by
  rcases scoped_loop_result out input with
    ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg⟩ | h | h
  · exact .inl ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg, spec_box_post box hs⟩
  · exact .inr (.inl h)
  · exact .inr (.inr h)

theorem scoped_loop_divergence {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (out : Memory.LoopScopes.CompiledProg b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (input : (Compiler.Compilation.memoryLoopScopes out).Input L frame base σ m) (source : P.run σ = .error .diverge) :
    run out.code m = .fault := by
  rcases scoped_loop_result out input with ⟨o, _, _, _, hs, _⟩ | ⟨hs, _⟩ | ⟨_, ht⟩
  · rw [source] at hs; cases hs
  · rw [source] at hs; cases hs
  · exact ht



theorem loop_reconstruct {C : Contract} {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (compiled : Compiler.Compilation b F P) (path : compiled.isMemoryLoops = true) :
    Compiler.Compilation.memoryLoops (compiled.memoryLoopsResult path) = compiled := by
  cases compiled with
  | core _ _ => cases path
  | memory _ => cases path
  | referenceArrays _ => cases path
  | objects _ => cases path
  | construction _ => cases path
  | memoryLoops _ => rfl
  | memoryLoopScopes _ => cases path
  | memoryCalls _ _ => cases path

theorem loop_public_diamond {C : Contract} {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (compiled : Compiler.Compilation b F P) (path : compiled.isMemoryLoops = true) {L frame : Nat}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} {φ : Spec C Δ}
    (input : compiled.Input L frame base σ m) (diamond : Spec.sat σ (.diamond P φ)) :
    ∃ o m', P.run σ = .ok o ∧ run compiled.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
      compiled.Rep L frame base σ m o.st m' ∧ Spec.sat o.st φ := by
  cases compiled with
  | core _ _ => cases path
  | memory _ => cases path
  | referenceArrays _ => cases path
  | objects _ => cases path
  | construction _ => cases path
  | memoryLoops out =>
    obtain ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg, hp⟩ :=
      loop_diamond out input diamond
    exact ⟨o, m', hs, ht, stack, ⟨base', cost, o.ext, hc, hr, he, hg⟩, hp⟩
  | memoryLoopScopes _ => cases path
  | memoryCalls _ _ => cases path

theorem scoped_loop_reconstruct {C : Contract} {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (compiled : Compiler.Compilation b F P) (path : compiled.isMemoryLoopScopes = true) :
    Compiler.Compilation.memoryLoopScopes (compiled.memoryLoopScopesResult path) = compiled := by
  cases compiled with
  | core _ _ => cases path
  | memory _ => cases path
  | referenceArrays _ => cases path
  | objects _ => cases path
  | construction _ => cases path
  | memoryLoopScopes _ => rfl
  | memoryLoops _ => cases path
  | memoryCalls _ _ => cases path

theorem scoped_loop_public_diamond {C : Contract} {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (compiled : Compiler.Compilation b F P) (path : compiled.isMemoryLoopScopes = true) {L frame : Nat}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} {φ : Spec C Δ}
    (input : compiled.Input L frame base σ m) (diamond : Spec.sat σ (.diamond P φ)) :
    ∃ o m', P.run σ = .ok o ∧ run compiled.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
      compiled.Rep L frame base σ m o.st m' ∧ Spec.sat o.st φ := by
  cases compiled with
  | core _ _ => cases path
  | memory _ => cases path
  | referenceArrays _ => cases path
  | objects _ => cases path
  | construction _ => cases path
  | memoryLoopScopes out =>
    obtain ⟨o, m', base', cost, hs, ht, hc, hr, stack, he, hg, hp⟩ :=
      scoped_loop_diamond out input diamond
    exact ⟨o, m', hs, ht, stack, ⟨base', cost, o.ext, hc, hr, he, hg⟩, hp⟩
  | memoryLoops _ => cases path
  | memoryCalls _ _ => cases path

end Solidity.Roadmap.V16
