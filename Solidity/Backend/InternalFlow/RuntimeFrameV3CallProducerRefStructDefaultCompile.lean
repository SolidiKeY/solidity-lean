import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRefStructDefaultTarget
import Solidity.Backend.InternalFlow.RuntimeFrameComposition
import Solidity.Evm.MemoryStructDefaultSource

/-! Owned finite-struct default leaf for the runtime-frame compiler. It reuses
the actual default selector and typed heap simulation, adding the independently
proved reserved-word footprint. Existing core compilers remain unchanged. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.StructDefault
open Evm Evm.Memory

abbrev DeclarationEmitter : Type :=
  ∀ {C : Contract} {Γ : Ctx} {b : Nat} {R : RefTy} (F : Frag Γ) (name : Var)
    (defaultOk : (Ty.ref R).defaultOkS = true) (mapFree : (Ty.ref R).mapFree = true),
    0 < b → {plan : DefaultPlan R // PlanRuns plan} →
    Composition.Statement (C := C) b F (.declMem R name none defaultOk mapFree)

def declare : DeclarationEmitter := by
  intro C Γ b R F name defaultOk mapFree positive framed
  let plan := framed.val
  refine { checked := {
    frag := F.push (.mem R) .ok
    code := plan.code ++ [.mstore (cell (b + Γ.length))]
    need := Γ.length + 1
    cost := fun _ => plan.cost
    allocates := true
    zeroCost := by intro impossible σ; cases impossible
    sound := ?_ }, safe := ?_ }
  · intro L frame σ base m represented room capacity
    exact plan.declare_correct represented positive mapFree room capacity
  · intro L frame lo σ base m target represented room boundary capacity actual
    change b + (Γ.length + 1) ≤ lo at room
    change AllocationInput b frame plan.cost σ base m at capacity
    rcases capacity with zero | ⟨_, cursor, allocator, space⟩
    · have nonzero := plan.root_lt
      omega
    · obtain ⟨first, executed, cursorWord, kept, stack⟩ := framed.property m frame cursor
        allocator.arrays.free.reserved allocator.arrays.free.above allocator.arrays.free.cell space
      change Evm.run (plan.code ++ [.mstore (cell (b + Γ.length))]) m = _ at actual
      rw [Evm.run_append_ok executed] at actual
      change Evm.Out.ok (writeMachine first (cell (b + Γ.length))
        (.val (wmod (cursor.val + plan.root)))) 0 = .ok target 0 at actual
      have same := (Evm.Out.ok.inj actual).1
      subst target
      exact Footprint.words_trans
        (fun address lower upper => kept address (by omega) upper)
        (Footprint.write_below first (cell (b + Γ.length))
          (.val (wmod (cursor.val + plan.root))) (by change b + Γ.length < lo; omega))

mutual
/-- Extend only the finite struct-default leaf and structurally compose its
sequence/block/branch contexts. All other leaves use the published selector. -/
def compileStatement (b : Nat) {C : Contract} {Γ Δ : Ctx} (F : Frag Γ) :
    (s : Stmt C Γ Δ) → Option (Composition.Statement b F s)
  | .declMem (.struct s) name none defaultOk mapFree => do
    let plan ← select? (.struct s)
    if positive : 0 < b then some (declare F name defaultOk mapFree positive plan) else none
  | .block body => (compileProgram b F body).map Composition.block
  | .ite condition thn els => do
    let cond ← Memory.compileVal b F condition
    let left ← compileProgram b F thn
    let right ← compileProgram b F els
    pure (Composition.branch condition cond left right)
  | other => Composition.compileStatement b F other

def compileProgram (b : Nat) {C : Contract} {Γ Δ : Ctx} (F : Frag Γ) :
    (P : Prog C Γ Δ) → Option (Composition.Program b F P)
  | .nil => some (Composition.nil b F)
  | .cons head tail => do
    let first ← compileStatement b F head
    let rest ← compileProgram b first.checked.frag tail
    pure (Composition.cons first rest)
end

/-- The memory-return entrypoint uses the same existing call expansion and
checked final pointer export; only the finite-default footprint was missing. -/
def compileMemoryCall {C : Contract} {Γ ps Γf : Ctx} (b : Nat) (F : Frag Γ)
    (name : Name) (args : Args C Γ ps) (R : RefTy) (result : Var)
    (defaultOk : (Ty.ref R).defaultOkS = true) (mapFree : (Ty.ref R).mapFree = true)
    (body : Prog C (.mem R :: ps) Γf) :
    Option (Composition.Statement b F (.call name args (.mem R result defaultOk mapFree) body)) := do
  let expanded ← compileProgram b F (Calls.expandMem args R result defaultOk mapFree body)
  if room : (.mem R :: (ps ++ Γ)).length ≤ expanded.checked.need then
    some (Composition.memoryReturn name args R result defaultOk mapFree body expanded room)
  else none

#print axioms declare

end Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.StructDefault
