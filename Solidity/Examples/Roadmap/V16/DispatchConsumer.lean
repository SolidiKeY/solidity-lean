import Solidity.Semantics.Dispatch
import Solidity.Examples.Roadmap.V16.FiniteHeapConsumer

/-! Consume actual intrinsic dispatch selection, not the unproved partial
elaborator/Source links. Guard results and local dropping remain explicit. -/
namespace Solidity.Roadmap.V16
open Solidity.Evm

theorem dispatch_selected_stmt {C : Contract} {Γ : Ctx}
    (pre : List (DispatchArm C Γ)) (a : DispatchArm C Γ) (post : List (DispatchArm C Γ))
    (fail : Stmt C Γ Γ) (σ : State C Γ)
    (before : ∀ b ∈ pre, b.cond.evalT σ = .ok false) (hit : a.cond.evalT σ = .ok true) :
    (DispatchArm.chain (pre ++ a :: post) fail).run σ = (Stmt.block a.body).run σ := by
  change Stmt.runR _ σ = Stmt.runR _ σ
  rw [Stmt.runR_eq,Stmt.runR_eq]
  exact DispatchArm.chain_select pre a post fail σ before hit

theorem dispatch_selected_run {C : Contract} {Γ : Ctx}
    (pre : List (DispatchArm C Γ)) (a : DispatchArm C Γ) (post : List (DispatchArm C Γ))
    (fail : Stmt C Γ Γ) (σ : State C Γ)
    (before : ∀ b ∈ pre, b.cond.evalT σ = .ok false) (hit : a.cond.evalT σ = .ok true) :
    (Prog.cons (DispatchArm.chain (pre ++ a :: post) fail) .nil).run σ =
      (Prog.cons (.block a.body) .nil).run σ := by
  have statement := dispatch_selected_stmt pre a post fail σ before hit
  change TRun.seq (DispatchArm.chain (pre ++ a :: post) fail).runR
      (Prog.nil : Prog C Γ Γ).runR σ =
    TRun.seq (Stmt.block a.body).runR (Prog.nil : Prog C Γ Γ).runR σ
  simp only [TRun.seq,Stmt.run] at statement ⊢
  rw [statement]

theorem dispatch_none_run {C : Contract} {Γ : Ctx}
    (arms : List (DispatchArm C Γ)) (fail : Stmt C Γ Γ) (σ : State C Γ)
    (miss : ∀ b ∈ arms, b.cond.evalT σ = .ok false) :
    (Prog.cons (DispatchArm.chain arms fail) .nil).run σ = (Prog.cons fail .nil).run σ := by
  have statement : (DispatchArm.chain arms fail).run σ = fail.run σ := by
    change Stmt.runR _ σ = Stmt.runR _ σ
    rw [Stmt.runR_eq,Stmt.runR_eq]
    exact DispatchArm.chain_none arms fail σ miss
  change TRun.seq (DispatchArm.chain arms fail).runR (Prog.nil : Prog C Γ Γ).runR σ =
    TRun.seq fail.runR (Prog.nil : Prog C Γ Γ).runR σ
  simp only [TRun.seq,Stmt.run] at statement ⊢
  rw [statement]

theorem dispatch_guard_error {C : Contract} {Γ : Ctx}
    (a : DispatchArm C Γ) (rest : List (DispatchArm C Γ)) (fail : Stmt C Γ Γ)
    (σ : State C Γ) (e : THalt) (error : a.cond.evalT σ = .error e) :
    (DispatchArm.chain (a :: rest) fail).run σ = .error e := by
  change TRun.ite _ _ _ _ _ σ = _
  simp only [TRun.ite,error,bind,Except.bind]

theorem dispatch_box_iff {C : Contract} {Γ : Ctx}
    (pre : List (DispatchArm C Γ)) (a : DispatchArm C Γ) (post : List (DispatchArm C Γ))
    (fail : Stmt C Γ Γ) (σ : State C Γ) (φ : Spec C Γ)
    (before : ∀ b ∈ pre, b.cond.evalT σ = .ok false) (hit : a.cond.evalT σ = .ok true) :
    Spec.sat σ (.box (.cons (DispatchArm.chain (pre ++ a :: post) fail) .nil) φ) ↔
      Spec.sat σ (.box (.cons (.block a.body) .nil) φ) := by
  simp only [Spec.sat,dispatch_selected_run pre a post fail σ before hit]

theorem dispatch_diamond_iff {C : Contract} {Γ : Ctx}
    (pre : List (DispatchArm C Γ)) (a : DispatchArm C Γ) (post : List (DispatchArm C Γ))
    (fail : Stmt C Γ Γ) (σ : State C Γ) (φ : Spec C Γ)
    (before : ∀ b ∈ pre, b.cond.evalT σ = .ok false) (hit : a.cond.evalT σ = .ok true) :
    Spec.sat σ (.diamond (.cons (DispatchArm.chain (pre ++ a :: post) fail) .nil) φ) ↔
      Spec.sat σ (.diamond (.cons (.block a.body) .nil) φ) := by
  simp only [Spec.sat,dispatch_selected_run pre a post fail σ before hit]

/-- Actual finite-heap certificate consumes the selected body's diamond.
No source-success, target-run or no-exhaustion premise is added. -/
theorem dispatch_finite_diamond {C : Contract} {Γ : Ctx} {b L frame : Nat} {F : Frag Γ}
    (pre : List (DispatchArm C Γ)) (a : DispatchArm C Γ) (post : List (DispatchArm C Γ))
    (fail : Stmt C Γ Γ) (σ : State C Γ) (φ : Spec C Γ)
    (before : ∀ x ∈ pre, x.cond.evalT σ = .ok false) (hit : a.cond.evalT σ = .ok true)
    (compiled : Compiler.Compilation b F (.cons (DispatchArm.chain (pre ++ a :: post) fail) .nil))
    (path : compiled.isMemory = true ∨ compiled.isReferenceArray = true ∨ compiled.isObject = true)
    {base : Nat → Fin W} {m : Machine} (input : compiled.Input L frame base σ m)
    (body : Spec.sat σ (.diamond (.cons (.block a.body) .nil) φ)) :
    ∃ o m', (Prog.cons (DispatchArm.chain (pre ++ a :: post) fail) .nil).run σ = .ok o ∧
      run compiled.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
      compiled.Rep L frame base σ m o.st m' ∧ Spec.sat o.st φ :=
  finite_heap_diamond compiled path input
    ((dispatch_diamond_iff pre a post fail σ φ before hit).mpr body)
end Solidity.Roadmap.V16
