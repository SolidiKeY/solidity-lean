import Solidity.Backend.Passes.Stack
import Solidity.Semantics.DeferredSource

/-!
# Typed sequencing across two checked compilation branches

A link is a physical representation obligation at the actual intermediate
typed state. It is not inferred from a core Sim, nor does it assume the
desired preservation theorem. Both original Compilations, their fragments,
and the intermediate heap/base/allocator relations stay in the conclusions.
These terminal lemmas do not supply resource-indexed session prefixes.
-/
namespace Solidity.Backend.Passes

open Solidity.Evm
open Solidity.Evm.Compiler

variable {C : Contract} {b L frame : Nat} {Γ Δ Ξ : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}

/-- The existing coarse machine failure boundary, with panic kept explicit. -/
def TerminalFailure {Γ Δ : Ctx} (P : Prog C Γ Δ) (σ : State C Γ) : Prop :=
  P.run σ = .error .revert ∨ (P.asserts = true ∧ P.run σ = .error .panic)

/-- Per-run transport into the suffix Input. In particular a memory suffix
still requires full ownership and reached capacity, not only a core Sim. -/
def BoundaryLink (left : Compilation b F P) (right : Compilation b left.frag Q)
    (L frame : Nat) (base nextBase : Nat → Fin W) (σ : State C Γ) (m : Machine) : Prop :=
  ∀ (o : Solidity.Out C σ.H Δ) (m' : Machine),
    P.run σ = .ok o → run left.code m = .ok m' 0 →
    left.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m' →
    right.Input (L + Evm.Prog.pushes P) frame nextBase o.st m'

/-- Successful typed sequencing retains both representation witnesses and
uses the actual intrinsic joined program, rather than a target evaluator
as its source semantics. The link is a separate, explicit obligation. -/
theorem compilation_sequence_success
    (left : Compilation b F P) (right : Compilation b left.frag Q)
    {base nextBase : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : left.Input L frame base σ m)
    (link : BoundaryLink left right L frame base nextBase σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o)
    {o' : Solidity.Out C o.st.H Ξ} (hs' : Q.run o.st = .ok o') :
    ∃ m' m'',
      (P.join Q).run σ = .ok ⟨o'.st, o.ext.trans o'.ext⟩ ∧
      run left.code m = .ok m' 0 ∧
      run (left.code ++ right.code) m = .ok m'' 0 ∧
      m''.stack = m.stack ∧
      left.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m' ∧
      right.Rep ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q)
        frame nextBase o.st m' o'.st m'' := by
  obtain ⟨m', ht, hstack, hr⟩ := compilation_success left hi hp hs
  obtain ⟨m'', ht', hstack', hr'⟩ :=
    compilation_success right (link o m' hs ht hr) hq hs'
  refine ⟨m', m'', ?_, ht, ?_, hstack'.trans hstack, hr, hr'⟩
  · rw [DeferredSource.join_run]
    simp only [TRun.seq, hs, hs', Except.map]
  · rw [run_append_ok ht]
    exact ht'

/-- Two-sided *terminal* failure transport for two independently compiled
stages. Left failure short-circuits; right failure is reached only after a
correlated successful left run. This does not identify panic bytes. -/
theorem compilation_sequence_revert_iff
    (left : Compilation b F P) (right : Compilation b left.frag Q)
    {base nextBase : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : left.Input L frame base σ m)
    (link : BoundaryLink left right L frame base nextBase σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false) :
    run (left.code ++ right.code) m = .revert ↔
      TerminalFailure P σ ∨
        ∃ o, P.run σ = .ok o ∧ TerminalFailure Q o.st := by
  constructor
  · intro ht
    rcases compilation_exact left hi hp with
      ⟨o, m', hs, ht', _, hr⟩ | ⟨hs, _⟩ | ⟨_, ht'⟩
    · rw [run_append_ok ht'] at ht
      exact .inr ⟨o, hs,
        (compilation_revert_iff right (link o m' hs ht' hr) hq).mp ht⟩
    · exact .inl hs
    · have hf : run (left.code ++ right.code) m = .fault := run_append_fault ht'
      rw [ht] at hf
      cases hf
  · intro hs
    rcases hs with hs | ⟨o, hs, hfail⟩
    · exact run_append_revert ((compilation_revert_iff left hi hp).mpr hs)
    · obtain ⟨m', ht, _, hr⟩ := compilation_success left hi hp hs
      rw [run_append_ok ht]
      exact (compilation_revert_iff right (link o m' hs ht hr) hq).mpr hfail

/-- Associativity of sequencing at the intrinsic context-indexed program
level, independently of any compiler or recognizer. -/
theorem typed_sequencing_assoc : {Γ Δ Ξ Ω : Ctx} →
    (P : Prog C Γ Δ) → (Q : Prog C Δ Ξ) → (R : Prog C Ξ Ω) →
      (P.join Q).join R = P.join (Q.join R)
  | _, _, _, _, .nil, Q, R => rfl
  | _, _, _, _, .cons stmt P, Q, R => by
    change Prog.cons stmt ((P.join Q).join R) = Prog.cons stmt (P.join (Q.join R))
    rw [typed_sequencing_assoc P Q R]

/-- Both source sequencing and emitted-code sequencing associate. Every
stage retains its actual context and branch-indexed compilation result. -/
theorem compilation_sequence_associative {Ω : Ctx} {R : Prog C Ξ Ω}
    (left : Compilation b F P) (middle : Compilation b left.frag Q)
    (right : Compilation b middle.frag R) (σ : State C Γ) (m : Machine) :
    ((P.join Q).join R).run σ = (P.join (Q.join R)).run σ ∧
      run ((left.code ++ middle.code) ++ right.code) m =
        run (left.code ++ (middle.code ++ right.code)) m := by
  constructor
  · rw [typed_sequencing_assoc]
  · rw [List.append_assoc]

end Solidity.Backend.Passes
