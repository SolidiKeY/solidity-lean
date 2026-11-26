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

end Solidity.Backend
