import Solidity.Evm.MemoryLoopHorizon
import Solidity.Evm.MemoryCompileExamples

/-! Inhabited finite-horizon interface and horizon-exhaustion negative controls.
These are kernel/source-target controls, not solc/EVM differential evidence. -/
namespace Solidity.Evm.Memory.HorizonControls
open CompileExamples

def stop : Val C Γ .bool := .simple (.bool false)
def spin : Val C Γ .bool := .simple (.bool true)
def body : Prog C Γ Γ := .nil

def cert (c : Bool) : LoopCert 0 (Frag.init Γ)
    (.simple (.bool c) : Val C Γ .bool) body
    (Evm.compileVal 0 (.simple (.bool c) : Val C Γ .bool)) [] :=
  ⟨.core _ rfl, Frag.init Γ, .nil _, rfl⟩

/-- Both terminating and perpetually pending loops instantiate the public
transport against the existing populated, aliased memory fixture. -/
theorem represented (c : Bool) (n : Nat) :
    HorizonRelation 1 0 4 (Frag.init Γ) (.simple (.bool c)) body σ base machine
      (TLoop.iterN (horizonBody body) (fun o => (.simple (.bool c) : Val C Γ .bool).evalT o.st)
        n ⟨σ, List.prefix_refl _⟩)
      (loopIterN (fun m => exec (Evm.compileVal 0 (.simple (.bool c) : Val C Γ .bool)) 0 m) (fun m => exec [] 0 m) n machine) := by
  exact (cert c).correct_horizon fixture_repr (by decide +kernel)
    (loopRoom_nonallocating (.simple (.bool c)) body (by rfl) σ base machine) n

example : TLoop.iterN (horizonBody body) (fun o => stop.evalT o.st) 0
    ⟨σ, List.prefix_refl _⟩ = .inl ⟨σ, List.prefix_refl _⟩ := rfl
example : TLoop.iterN (horizonBody body) (fun o => stop.evalT o.st) 1
    ⟨σ, List.prefix_refl _⟩ = .inr (.ok ⟨σ, List.prefix_refl _⟩) := rfl
example : TLoop.iterN (horizonBody body) (fun o => spin.evalT o.st) 3
    ⟨σ, List.prefix_refl _⟩ = .inl ⟨σ, List.prefix_refl _⟩ := rfl
example : TLoop.iterN (horizonBody body) (fun o => spin.evalT o.st) 3
    ⟨σ, List.prefix_refl _⟩ ≠ .inr (.error .diverge) := by
  intro h
  cases h

/-- A real out-of-bounds memory read in the condition, not the body. -/
private def badCondition : Val C Γ .bool :=
  .binop .eqB rfl rfl
    (.readMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 2 rfl))))
    (.simple (.lit 0 rfl))
private def badCompiled : CompiledVal 0 (Frag.init Γ) badCondition :=
  (Memory.compileVal 0 (Frag.init Γ) badCondition).get (by decide +kernel)
private def badCert : LoopCert 0 (Frag.init Γ) badCondition body badCompiled.code [] :=
  ⟨badCompiled.cert, Frag.init Γ, .nil _, rfl⟩
theorem condition_revert_horizons (n : Nat) :
    HorizonRelation 1 0 4 (Frag.init Γ) badCondition body σ base machine
      (TLoop.iterN (horizonBody body) (fun o => badCondition.evalT o.st) n ⟨σ, List.prefix_refl _⟩)
      (loopIterN (fun m => exec badCompiled.code 0 m) (fun m => exec [] 0 m) n machine) :=
  badCert.correct_horizon fixture_repr (by decide +kernel)
    (loopRoom_nonallocating badCondition body rfl σ base machine) n
private def sourceRevert : Solidity.Out C CompileExamples.H Γ ⊕ TRes (Solidity.Out C CompileExamples.H Γ) → Bool
  | .inr (.error .revert) => true
  | _ => false
private def targetRevert : Machine ⊕ Out → Bool
  | .inr .revert => true
  | _ => false
/-- info: (true, true) -/
#guard_msgs in
#eval (sourceRevert (TLoop.iterN (horizonBody body) (fun o => badCondition.evalT o.st)
    1 ⟨σ, List.prefix_refl _⟩),
  targetRevert (loopIterN (fun m => exec badCompiled.code 0 m) (fun m => exec [] 0 m) 1 machine))

end Solidity.Evm.Memory.HorizonControls
