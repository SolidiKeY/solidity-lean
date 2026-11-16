import Solidity.Examples.Roadmap.V16.ConstructionConsumer
/-! Actual published compiler/specification consumers. Panic guards, payment
refusal and divergence remain distinct. Excluding exhaustion is not termination. -/
namespace Solidity.Roadmap.V16
open Solidity.Evm

/-- All actual published compiler alternatives exclude source exhaustion. -/
theorem compiler_not_exhausted {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (input : compiled.Input L frame base σ m) : P.run σ ≠ .error .exhausted := by
  intro h
  rcases compiled.correct input with ⟨_,_,hs,_⟩ | ⟨hs,_⟩ | ⟨_,_,_,_,hs,_⟩ | ⟨hs,_⟩
  · rw [h] at hs; cases hs
  · rcases hs with hs | ⟨_,hs⟩ <;> rw [h] at hs <;> cases hs
  · rw [h] at hs; cases hs
  · rw [h] at hs; cases hs

/-- Genuine diamond consumer. Actual payment refusal remains a separate guarded
alternative with a candidate representation, not a fabricated successful run. -/
theorem compiler_diamond {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} {φ : Spec C Δ}
    (input : compiled.Input L frame base σ m) (diamond : Spec.sat σ (.diamond P φ)) :
    ∃ o, P.run σ = .ok o ∧ Spec.sat o.st φ ∧
      ((∃ m', run compiled.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
        compiled.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m') ∨
       (Evm.Prog.pays P = true ∧ run compiled.code m = .revert ∧
         ∃ candidate, compiled.Rep (L + Evm.Prog.pushes P) frame base σ m o.st candidate)) := by
  obtain ⟨o,source,post⟩ := spec_diamond_success diamond (compiler_not_exhausted compiled input)
  refine ⟨o,source,post,?_⟩
  rcases compiled.correct input with ⟨u,m',hs,ht,stack,rep⟩ | ⟨hs,_⟩ | ⟨pay,ht,u,m',hs,rep⟩ | ⟨hs,_⟩
  · have eq : u = o := Except.ok.inj (hs.symm.trans source)
    subst u
    exact .inl ⟨m',ht,stack,rep⟩
  · rcases hs with hs | ⟨_,hs⟩ <;> rw [source] at hs <;> cases hs
  · have eq : u = o := Except.ok.inj (hs.symm.trans source)
    subst u
    exact .inr ⟨pay,ht,m',rep⟩
  · rw [source] at hs; cases hs

/-- A successful machine run selects only the actual successful agreement arm. -/
theorem compiler_box_target {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m m' : Machine} {φ : Spec C Δ}
    (input : compiled.Input L frame base σ m) (box : Spec.sat σ (.box P φ))
    (target : run compiled.code m = .ok m' 0) :
    ∃ o, P.run σ = .ok o ∧ m'.stack = m.stack ∧
      compiled.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m' ∧ Spec.sat o.st φ := by
  rcases compiled.correct input with ⟨o,n,hs,ht,stack,rep⟩ | ⟨_,ht⟩ | ⟨_,ht,_⟩ | ⟨_,ht⟩
  · have eq : n = m' := by cases ht.symm.trans target; rfl
    subst n
    exact ⟨o,hs,stack,rep,spec_box_post box hs⟩
  · rw [target] at ht; cases ht
  · rw [target] at ht; cases ht
  · rcases ht with ht | ⟨_,ht⟩ <;> rw [target] at ht <;> cases ht

/-- Absence of the actual syntactic payment operation eliminates only payment
refusal; this is a scoped consequence, not full-profile coverage. -/
theorem compiler_nonpaying_diamond {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} {φ : Spec C Δ}
    (input : compiled.Input L frame base σ m) (nonpaying : Evm.Prog.pays P = false)
    (diamond : Spec.sat σ (.diamond P φ)) :
    ∃ o m', P.run σ = .ok o ∧ run compiled.code m = .ok m' 0 ∧
      m'.stack = m.stack ∧ compiled.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m' ∧
      Spec.sat o.st φ := by
  obtain ⟨o,hs,post,result⟩ := compiler_diamond compiled input diamond
  rcases result with ⟨m',ht,stack,rep⟩ | ⟨pays,_⟩
  · exact ⟨o,m',hs,ht,stack,rep,post⟩
  · rw [nonpaying] at pays; cases pays

/-- Source errors retain the published assert guard and divergence/payment
alternatives. Panic is not renamed empty revert at the source. -/
theorem compiler_source_error {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} {e : THalt}
    (input : compiled.Input L frame base σ m) (source : P.run σ = .error e) :
    ((e = .revert ∨ (P.asserts = true ∧ e = .panic)) ∧ run compiled.code m = .revert) ∨
    (e = .diverge ∧ (run compiled.code m = .fault ∨
      (Evm.Prog.pays P = true ∧ run compiled.code m = .revert))) := by
  rcases compiled.correct input with ⟨_,_,hs,_⟩ | ⟨hs,ht⟩ | ⟨_,_,_,_,hs,_⟩ | ⟨hs,ht⟩
  · rw [source] at hs; cases hs
  · refine .inl ⟨?_,ht⟩
    rcases hs with hs | ⟨asserts,hs⟩
    · exact .inl (Except.error.inj (source.symm.trans hs))
    · exact .inr ⟨asserts,Except.error.inj (source.symm.trans hs)⟩
  · rw [source] at hs; cases hs
  · exact .inr ⟨Except.error.inj (source.symm.trans hs),ht⟩
end Solidity.Roadmap.V16
