import Solidity.Backend.CompilerEndpoint
import Solidity.Backend.CompilerTotal
import Solidity.Optimizer.Pipeline

/-! The optimizing entry retains the selected program's compilation certificate
and resource interpretation. Its semantic endpoint refers to the original program.
The fallback is taken exactly when compiling the optimized program returns none. -/
namespace Solidity.Backend

open Evm Evm.Compiler

/-- A selected compilation, with semantic equality to the original source. -/
structure OptimizedCompilation {C : Contract} (b : Nat) {Γ Δ : Ctx}
    (F : Frag Γ) (P : Solidity.Prog C Γ Δ) where
  program : Solidity.Prog C Γ Δ
  run_eq : program.runC = P.runC
  result : Compilation b F program

/-- Try the optimized program first, retaining the original compiler as fallback. -/
def compileOptimized {C : Contract} (n b : Nat) {Γ Δ : Ctx}
    (F : Frag Γ) (P : Solidity.Prog C Γ Δ) : Option (OptimizedCompilation b F P) :=
  match Compiler.compile b F (P.optimize n) with
  | some r => some ⟨P.optimize n, P.optimize_runC n, r⟩
  | none => (Compiler.compile b F P).map (fun r => ⟨P, rfl, r⟩)

namespace OptimizedCompilation

/-- Exact agreement with the original source and the selected result's representation.
Resource bounds refer to the program actually compiled, as does its input certificate. -/
def AgreesExact {C : Contract} {b : Nat} {Γ Δ : Ctx} {F : Frag Γ}
    {P : Solidity.Prog C Γ Δ} (r : OptimizedCompilation b F P)
    (L frame : Nat) (base : Nat → Fin W) (σ : State C Γ) (m : Machine) : Prop :=
  (∃ o m', P.run σ = .ok o ∧ Evm.run r.result.code m = .ok m' 0 ∧
    m'.stack = m.stack ∧
    r.result.Rep (L + Evm.Prog.pushes r.program) frame base σ m o.st m') ∨
  ((P.run σ = .error .revert ∨ (P.asserts = true ∧ P.run σ = .error .panic)) ∧
    Evm.run r.result.code m = .revert) ∨
  (P.run σ = .error .diverge ∧ Evm.run r.result.code m = .fault)

end OptimizedCompilation

/-- R1, R2, and exact agreement for every world accepted by the selected result. -/
def CompilerOptimizedEndpoint : Prop :=
  ∀ (n : Nat) {C : Contract} {Γ Δ : Ctx} (b : Nat) (F : Frag Γ)
    (P : Solidity.Prog C Γ Δ),
    compileOptimized n b F P = none ∨
    ∃ r, compileOptimized n b F P = some r ∧
      ∀ L frame : Nat,
        (Passes.WholeProgram.staticRefused r.result L frame = true ∧
          ∀ (base : Nat → Fin W) (σ : State C Γ) (m : Machine),
            ¬ r.result.Input L frame base σ m) ∨
        (Passes.WholeProgram.staticRefused r.result L frame = false ∧
          ∀ (base : Nat → Fin W) (σ : State C Γ) (m : Machine),
            r.result.Input L frame base σ m → r.AgreesExact L frame base σ m)

/-- The original accepted domain still compiles and passes the static check. -/
def CompilerOptimizedTotal : Prop :=
  ∀ (n : Nat) (C : Contract) (Γ Δ : Ctx) (P : Solidity.Prog C Γ Δ),
    AbiWorld.PublicCompilerTotal.ProgOk [] P →
    ∀ (b L frame : Nat), L ≤ Evm.Lmax →
      ∃ r, compileOptimized n b (Frag.init Γ) P = some r ∧
        Passes.WholeProgram.staticRefused r.result L frame = false

/-- Semantic equality transports exact agreement without changing the selected
certificate's representation or resource bounds. -/
theorem OptimizedCompilation.agrees_of_selected {C : Contract} {b : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Solidity.Prog C Γ Δ} (r : OptimizedCompilation b F P)
    {L frame : Nat} {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (h : r.result.AgreesExact L frame base σ m) : r.AgreesExact L frame base σ m := by
  have he : r.program.run σ = P.run σ := by
    simp only [Solidity.Prog.run, Solidity.Prog.runR_eq, r.run_eq]
  unfold Compilation.AgreesExact at h
  rw [he] at h
  rcases h with h | ⟨h | ⟨_, hp⟩, hm⟩ | h
  · exact .inl h
  · exact .inr (.inl ⟨.inl h, hm⟩)
  · refine .inr (.inl ⟨.inr ⟨?_, hp⟩, hm⟩)
    cases ha : P.asserts with
    | false => exact False.elim (Solidity.Prog.run_ne_panic ha σ hp)
    | true => rfl
  · exact .inr (.inr h)

/-- The existing endpoint applied to a particular selected compilation. -/
private theorem selected_endpoint {C : Contract} {b : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Solidity.Prog C Γ Δ} (r : OptimizedCompilation b F P)
    (hc : Compiler.compile b F r.program = some r.result) :
    ∀ L frame : Nat,
      (Passes.WholeProgram.staticRefused r.result L frame = true ∧
        ∀ (base : Nat → Fin W) (σ : State C Γ) (m : Machine),
          ¬ r.result.Input L frame base σ m) ∨
      (Passes.WholeProgram.staticRefused r.result L frame = false ∧
        ∀ (base : Nat → Fin W) (σ : State C Γ) (m : Machine),
          r.result.Input L frame base σ m → r.AgreesExact L frame base σ m) := by
  rcases compiler_endpoint_correct b F r.program with h | ⟨out, h, hs⟩
  · rw [hc] at h
    cases h
  · rw [hc] at h
    cases h
    intro L frame
    rcases hs L frame with h | ⟨h, agrees⟩
    · exact .inl h
    · exact .inr ⟨h, fun base σ m hi => r.agrees_of_selected (agrees base σ m hi)⟩

/-- Optimized code agrees with the original source past the unchanged refusals. -/
theorem compiler_optimized_correct : CompilerOptimizedEndpoint := by
  intro n C Γ Δ b F P
  cases hc : Compiler.compile b F (P.optimize n) with
  | some r =>
    refine .inr ⟨⟨P.optimize n, P.optimize_runC n, r⟩, ?_, ?_⟩
    · simp only [compileOptimized, hc]
    · exact selected_endpoint _ hc
  | none =>
    cases hp : Compiler.compile b F P with
    | none => exact .inl (by simp only [compileOptimized, hc, hp, Option.map_none])
    | some r =>
      refine .inr ⟨⟨P, rfl, r⟩, ?_, ?_⟩
      · simp only [compileOptimized, hc, hp, Option.map_some]
      · exact selected_endpoint _ hp

/-- The fallback never rejects a program accepted by the original compiler. -/
theorem compileOptimized_ne_none {C : Contract} (n b : Nat) {Γ Δ : Ctx}
    (F : Frag Γ) (P : Solidity.Prog C Γ Δ) (h : Compiler.compile b F P ≠ none) :
    compileOptimized n b F P ≠ none := by
  cases hc : Compiler.compile b F (P.optimize n) with
  | some r => simp only [compileOptimized, hc, ne_eq, Option.some_ne_none, not_false_eq_true]
  | none =>
    cases hp : Compiler.compile b F P with
    | none => exact False.elim (h hp)
    | some r => simp only [compileOptimized, hc, hp, Option.map_some, ne_eq,
        Option.some_ne_none, not_false_eq_true]

/-- Every program in the original totality domain is still accepted. This is
acceptance only; the goal separately requires the selected static check to pass. -/
theorem compileOptimized_accepts (n : Nat) (C : Contract) (Γ Δ : Ctx)
    (P : Solidity.Prog C Γ Δ) (hP : AbiWorld.PublicCompilerTotal.ProgOk [] P) (b : Nat) :
    ∃ r, compileOptimized n b (Frag.init Γ) P = some r := by
  obtain ⟨r, hr, _⟩ := compiler_total C Γ Δ P hP b 0 0 (Nat.zero_le _)
  have hn : Compiler.compile b (Frag.init Γ) P ≠ none := by
    rw [hr]
    exact Option.some_ne_none r
  have h := compileOptimized_ne_none n b (Frag.init Γ) P hn
  cases hc : compileOptimized n b (Frag.init Γ) P with
  | none => exact False.elim (h hc)
  | some r => exact ⟨r, rfl⟩

end Solidity.Backend

#print axioms Solidity.Backend.compiler_optimized_correct
#print axioms Solidity.Backend.compileOptimized_ne_none
#print axioms Solidity.Backend.compileOptimized_accepts
