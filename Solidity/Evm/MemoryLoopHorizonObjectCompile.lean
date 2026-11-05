import Solidity.Evm.MemoryLoopHorizonObjectFinite

/-! Narrow checked loop compilation from the existing complete-object condition
and construction-body compilers. Acceptance checks restored fragment equality
and carries the existing strong LoopCert; no recursive loop-body compiler or
full selection closure is supplied. Finite transport retains explicit frame,
strong representation and reached-capacity premises. -/
namespace Solidity.Evm.Memory.Construction
variable {C : Contract} {Γ Δ : Ctx}

structure CompiledLoop (b : Nat) (F : Frag Γ) (condition : Val C Γ .bool) (body : Prog C Γ Δ) where
  conditionCode : List Instr
  bodyCode : List Instr
  cert : LoopCert b F condition body conditionCode bodyCode

def compileLoop (b : Nat) (F : Frag Γ) (condition : Val C Γ .bool) (body : Prog C Γ Δ) :
    Option (CompiledLoop b F condition body) := do
  let checkedCondition ← Objects.compileVal b F condition
  let checkedBody ← compileProg b F body
  if stable : checkedBody.frag.restrict Γ = F then
    pure ⟨checkedCondition.code, checkedBody.code,
      ⟨checkedCondition.cert, checkedBody.frag, checkedBody.cert, stable⟩⟩
  else none

theorem CompiledLoop.correct_finite_horizon {b L frame : Nat} {F : Frag Γ}
    {condition : Val C Γ .bool} {body : Prog C Γ Δ}
    (compiled : CompiledLoop b F condition body) {state : State C Γ}
    {base : Nat → Fin W} {machine : Machine} (horizon : Nat)
    (repr : Objects.StateRepr L b frame F state base machine)
    (capacity : b + frameNeedProg body ≤ frame)
    (room : FiniteLoopRoom b frame condition body state base machine horizon) :
    CountedHorizonRelation L b frame F condition body state base machine horizon
      (TLoop.iterN (horizonBody body) (fun o => condition.evalT o.st) horizon ⟨state,List.prefix_refl _⟩)
      (loopIterN (fun m => exec compiled.conditionCode 0 m)
        (fun m => exec compiled.bodyCode 0 m) horizon machine) := by
  exact compiled.cert.correct_finite_horizon horizon repr capacity room

theorem compile_nil_inhabited (truth : Bool) :
    (compileLoop 1 (Frag.init []) (.simple (.bool truth) : Val C [] .bool)
      (.nil : Prog C [] [])).isSome = true := by rfl

theorem compile_nested_refused (annotation : LoopAnn C []) (truth : Bool) :
    compileLoop 1 (Frag.init []) (.simple (.bool true) : Val C [] .bool)
      (.cons (.loop annotation (.simple (.bool truth)) (.nil : Prog C [] [])) .nil) = none := by rfl

end Solidity.Evm.Memory.Construction
