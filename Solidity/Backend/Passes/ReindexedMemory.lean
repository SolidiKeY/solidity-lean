import Solidity.Backend.Passes.MappedSequence

/-! Equality transport of an existing memory certificate's input fragment.
All predicates and code are retained; this introduces no new compiler/IR. -/
namespace Solidity.Backend.Passes
open Evm Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
  {F G : Frag Γ} {P : Prog C Γ Δ}

def memory_reindex (h : F = G) (out : Memory.CompiledProg b G P) :
    Memory.CompiledProg b F P := h.symm ▸ out

theorem memory_reindex_code (h : F = G) (out : Memory.CompiledProg b G P) :
    (memory_reindex h out).code = out.code := by cases h; rfl

theorem memory_reindex_frag (h : F = G) (out : Memory.CompiledProg b G P) :
    (memory_reindex h out).frag = out.frag := by cases h; rfl

theorem memory_reindex_cost (h : F = G) (out : Memory.CompiledProg b G P) :
    (memory_reindex h out).cert.cost = out.cert.cost := by cases h; rfl

theorem memory_reindex_input_iff (h : F = G) (out : Memory.CompiledProg b G P)
    (base : Nat → Fin W) (σ : State C Γ) (m : Machine) :
    (Compilation.memory (memory_reindex h out)).Input L frame base σ m ↔
      (Compilation.memory out).Input L frame base σ m := by cases h; rfl

theorem memory_reindex_mapped_iff (h : F = G) (out : Memory.CompiledProg b G P)
    (base next : Nat → Fin W) (σ : State C Γ) (m : Machine) (τ : State C Δ) (n : Machine) :
    MappedOutput (.memory (memory_reindex h out)) L frame base σ m τ n next ↔
      MappedOutput (.memory out) L frame base σ m τ n next := by cases h; rfl


theorem memory_reindex_compile (h : F = G) (out : Memory.CompiledProg b G P)
    (hc : Memory.compileProg b G P = some out) :
    Memory.compileProg b F P = some (memory_reindex h out) := by
  cases h
  exact hc

end Solidity.Backend.Passes
