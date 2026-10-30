import Solidity.Evm.Correct
import Solidity.Evm.MemoryLoopScopeCompile

/-!
# The checked compiler entry

One entry selects the existing core compiler when its fragment applies,
otherwise the memory compiler. Its result retains the corresponding fragment
certificate. The common agreement theorem preserves the stronger heap and
pointer relation on the memory path; its input states that relation and the
reserved frame bound explicitly.
-/
namespace Solidity.Evm.Compiler

variable {C : Contract}

inductive Compilation (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) where
  | core (frag : Frag Δ) (cert : inFragP F P = some frag)
  | memory (result : Memory.CompiledProg b F P)
  | memoryLoops (result : Memory.Loops.CompiledProg b F P)
  | memoryLoopScopes (result : Memory.LoopScopes.CompiledProg b F P)

def compile (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) :
    Option (Compilation b F P) :=
  match hc : inFragP F P with
  | some frag => some (.core frag hc)
  | none => match Memory.compileProg b F P with
    | some result => some (.memory result)
    | none => match Memory.Loops.compileProg b F P with
      | some result => some (.memoryLoops result)
      | none => (Memory.LoopScopes.compileProg b P F).map .memoryLoopScopes

namespace Compilation

def code {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ} :
    Compilation b F P → List Instr
  | .core _ _ => Evm.compileProg b P
  | .memory result => result.code
  | .memoryLoops result => result.code
  | .memoryLoopScopes result => result.code

def frag {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ} :
    Compilation b F P → Frag Δ
  | .core out _ => out
  | .memory result => result.frag
  | .memoryLoops result => result.frag
  | .memoryLoopScopes result => result.frag

/-- Identify the legacy finite-memory path; loop memory has `isMemoryLoops`. -/
def isMemory {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ} :
    Compilation b F P → Bool
  | .core _ _ => false
  | .memory _ => true
  | .memoryLoops _ => false
  | .memoryLoopScopes _ => false

/-- Distinguish prefix-capacity loop inputs from legacy finite-memory inputs. -/
def isMemoryLoops {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ} :
    Compilation b F P → Bool
  | .memoryLoops _ => true
  | _ => false

/-- Identify checked loops composed beneath enclosing scopes. -/
def isMemoryLoopScopes {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ} :
    Compilation b F P → Bool
  | .memoryLoopScopes _ => true
  | _ => false

def Input {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) (L frame : Nat) (base : Nat → Fin W)
    (σ : State C Γ) (m : Machine) : Prop :=
  match result with
  | .core _ _ => Sim C L b F σ m ∧ L + Evm.Prog.pushes P ≤ Lmax
  | .memory out => Memory.StateRepr L b frame F σ base m ∧ b + Memory.frameNeedProg P ≤ frame ∧
      Memory.AllocationInput b frame (out.cert.cost σ) σ base m
  | .memoryLoops out => Memory.StateRepr L b frame F σ base m ∧
      b + out.cert.need ≤ frame ∧ Memory.Loops.Room out.cert frame σ base m
  | .memoryLoopScopes out => Memory.StateRepr L b frame F σ base m ∧
      b + out.cert.need ≤ frame ∧ Memory.LoopScopes.Room out.cert frame σ base m

/-- Open the memory premises without reducing the certified compiler result. -/
theorem memory_input {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) (hm : result.isMemory = true) (L frame : Nat)
    (base : Nat → Fin W) (σ : State C Γ) (m : Machine) :
    result.Input L frame base σ m ↔ Memory.StateRepr L b frame F σ base m ∧
      b + Memory.frameNeedProg P ≤ frame ∧
      Memory.AllocationInput b frame (Memory.allocationCostProg P σ) σ base m := by
  cases result with
  | core out cert => cases hm
  | memory out => rfl
  | memoryLoops out => cases hm
  | memoryLoopScopes out => cases hm

def Rep {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) (L frame : Nat) (base : Nat → Fin W)
    (entry : State C Γ) (initial : Machine) (σ : State C Δ) (m : Machine) : Prop :=
  match result with
  | .core out _ => Sim C L b out σ m
  | .memory out => ∃ base', Memory.StateRepr L b frame out.frag σ base' m ∧
      Memory.BaseExtends entry.H base base' ∧
      Memory.GrowsAllocator b frame (out.cert.cost entry) entry base initial σ base' m
  | .memoryLoops out => ∃ base' cost, ∃ e : entry.H <+: σ.H,
      Memory.Loops.Cost out.cert entry ⟨σ, e⟩ cost ∧
      Memory.StateRepr L b frame out.frag σ base' m ∧ Memory.BaseExtends entry.H base base' ∧
      Memory.GrowsAllocator b frame cost entry base initial σ base' m
  | .memoryLoopScopes out => ∃ base' cost, ∃ e : entry.H <+: σ.H,
      Memory.LoopScopes.Cost out.cert entry ⟨σ, e⟩ cost ∧
      Memory.StateRepr L b frame out.frag σ base' m ∧ Memory.BaseExtends entry.H base base' ∧
      Memory.GrowsAllocator b frame cost entry base initial σ base' m

/-- Open the source-prefix capacity premises of the loop path. -/
theorem memoryLoops_input_of {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (out : Memory.Loops.CompiledProg b F P) (L frame : Nat) (base : Nat → Fin W)
    (σ : State C Γ) (m : Machine) :
    (Compilation.memoryLoops out).Input L frame base σ m ↔
      Memory.StateRepr L b frame F σ base m ∧ b + out.cert.need ≤ frame ∧
        Memory.Loops.Room out.cert frame σ base m := Iff.rfl

/-- Recover the loop certificate without unfolding a computed compiler result. -/
def memoryLoopsResult {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) (hm : result.isMemoryLoops = true) : Memory.Loops.CompiledProg b F P :=
  match result with
  | .memoryLoops out => out
  | .core _ _ => False.elim (Bool.noConfusion hm)
  | .memory _ => False.elim (Bool.noConfusion hm)
  | .memoryLoopScopes _ => False.elim (Bool.noConfusion hm)

theorem memoryLoops_input {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) (hm : result.isMemoryLoops = true) (L frame : Nat)
    (base : Nat → Fin W) (σ : State C Γ) (m : Machine) :
    result.Input L frame base σ m ↔ Memory.StateRepr L b frame F σ base m ∧
      b + (result.memoryLoopsResult hm).cert.need ≤ frame ∧
      Memory.Loops.Room (result.memoryLoopsResult hm).cert frame σ base m := by
  cases result with
  | core out cert => cases hm
  | memory out => cases hm
  | memoryLoops out => rfl
  | memoryLoopScopes out => cases hm

/-- Open the source-prefix capacity premises of the loop path. -/
theorem memoryLoopScopes_input_of {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (out : Memory.LoopScopes.CompiledProg b F P) (L frame : Nat) (base : Nat → Fin W)
    (σ : State C Γ) (m : Machine) :
    (Compilation.memoryLoopScopes out).Input L frame base σ m ↔
      Memory.StateRepr L b frame F σ base m ∧ b + out.cert.need ≤ frame ∧
        Memory.LoopScopes.Room out.cert frame σ base m := Iff.rfl

/-- Recover the loop certificate without unfolding a computed compiler result. -/
def memoryLoopScopesResult {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) (hm : result.isMemoryLoopScopes = true) : Memory.LoopScopes.CompiledProg b F P :=
  match result with
  | .memoryLoopScopes out => out
  | .core _ _ => False.elim (Bool.noConfusion hm)
  | .memory _ => False.elim (Bool.noConfusion hm)
  | .memoryLoops _ => False.elim (Bool.noConfusion hm)

theorem memoryLoopScopes_input {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) (hm : result.isMemoryLoopScopes = true) (L frame : Nat)
    (base : Nat → Fin W) (σ : State C Γ) (m : Machine) :
    result.Input L frame base σ m ↔ Memory.StateRepr L b frame F σ base m ∧
      b + (result.memoryLoopScopesResult hm).cert.need ≤ frame ∧
      Memory.LoopScopes.Room (result.memoryLoopScopesResult hm).cert frame σ base m := by
  cases result with
  | core out cert => cases hm
  | memory out => cases hm
  | memoryLoops out => cases hm
  | memoryLoopScopes out => rfl

/-- The compiler preserves typed states and the evaluation stack, or both
executions revert; the existing panic and payment cases retain their guards. -/
def Agrees {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) (L frame : Nat) (base : Nat → Fin W)
    (σ : State C Γ) (m : Machine) : Prop :=
  (∃ o m', P.run σ = .ok o ∧ run result.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
    result.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m') ∨
  ((P.run σ = .error .revert ∨ (P.asserts = true ∧ P.run σ = .error .panic)) ∧
    run result.code m = .revert) ∨
  (Evm.Prog.pays P = true ∧ run result.code m = .revert ∧ ∃ o m',
    P.run σ = .ok o ∧ result.Rep (L + Evm.Prog.pushes P) frame base σ m o.st m') ∨
  (P.run σ = .error .diverge ∧ (run result.code m = .fault ∨
    (Evm.Prog.pays P = true ∧ run result.code m = .revert)))

theorem correct {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (result : Compilation b F P) {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (h : result.Input L frame base σ m) : result.Agrees L frame base σ m := by
  cases result with
  | core out cert => exact Evm.compile_correct cert h.1 h.2
  | memory out =>
    simp only [Agrees, code, Rep, out.cert.pushes_zero, Nat.add_zero]
    rcases out.cert.correct h.1 h.2.1 h.2.2 with
      ⟨o, m', base', ho, hc, hm, hst, he, ha⟩ | ⟨ho, hc⟩
    · exact .inl ⟨o, m', ho, hc, hst, base', hm, he, ha⟩
    · exact .inr (.inl ⟨.inl ho, hc⟩)

  | memoryLoops out =>
    simp only [Agrees, code, Rep, out.cert.pushes_zero, Nat.add_zero]
    rcases out.cert.correct h.1 h.2.1 h.2.2 with
      ⟨o, m', base', cost, ho, hc, hcost, hm, hst, he, ha⟩ | ⟨ho, hc⟩ | ⟨ho, hc⟩
    · exact .inl ⟨o, m', ho, hc, hst, base', cost, o.ext, hcost, hm, he, ha⟩
    · exact .inr (.inl ⟨.inl ho, hc⟩)
    · exact .inr (.inr (.inr ⟨ho, .inl hc⟩))

  | memoryLoopScopes out =>
    simp only [Agrees, code, Rep, out.cert.pushes_zero, Nat.add_zero]
    rcases out.cert.correct σ base m h.1 h.2.1 h.2.2 with
      ⟨o, m', base', cost, ho, hc, hcost, hm, hst, he, ha⟩ | ⟨ho, hc⟩ | ⟨ho, hc⟩
    · exact .inl ⟨o, m', ho, hc, hst, base', cost, o.ext, hcost, hm, he, ha⟩
    · exact .inr (.inl ⟨.inl ho, hc⟩)
    · exact .inr (.inr (.inr ⟨ho, .inl hc⟩))

end Compilation
end Solidity.Evm.Compiler
