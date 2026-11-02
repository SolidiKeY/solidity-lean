import Solidity.Backend.Passes.TailLoop
import Solidity.Backend.Passes.Stack

/-!
# Exact saved-tail independence for all eight Compilation constructors

The prior payment-freedom premise is retained. Nonfault target execution
transports suffixes by nested instruction induction; compiler correctness
handles the typed divergence/fault case. Equality never follows merely from
Rep. Each constructor keeps its original Input and complete output relation.
-/
namespace Solidity.Backend.Passes
open Solidity.Evm Solidity.Evm.Compiler

def replaceOutStack (tail : List Word) : Evm.Out → Evm.Out
  | .ok m k => .ok {m with stack := tail} k
  | .revert => .revert
  | .fault => .fault

variable {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ}

/-- Exact outcome and all non-stack fields are independent of the saved tail,
for core, memory, reference arrays, objects, construction and memory calls. -/
theorem compilation_tail_exact (result : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : result.Input L frame base σ m)
    (hp : Evm.Prog.pays P = false) (tail : List Word) :
    run result.code {m with stack := tail} =
      replaceOutStack tail (run result.code {m with stack := []}) := by
  rcases compilation_exact result (compilation_input_stack result hi []) hp with
    ⟨o, canonical, hs, ht, hstack, hr⟩ | ⟨hs, ht⟩ | ⟨hs, ht⟩
  · have he := run_tail result.code {m with stack := []} tail
      (by rw [ht]; intro h; cases h)
    rw [ht]
    simpa only [ht, appendTail, appendOut, replaceOutStack, hstack,
      List.nil_append] using he
  · have he := run_tail result.code {m with stack := []} tail
      (by rw [ht]; intro h; cases h)
    rw [ht]
    simpa only [ht, appendTail, appendOut, replaceOutStack, List.nil_append] using he
  · rw [ht]
    change run result.code {m with stack := tail} = .fault
    rcases compilation_exact result (compilation_input_stack result hi tail) hp with
      ⟨o, out, hs', _, _, _⟩ | ⟨hs' | ⟨_, hs'⟩, _⟩ | ⟨_, ht'⟩
    · rw [hs] at hs'
      cases hs'
    · rw [hs] at hs'
      cases hs'
    · rw [hs] at hs'
      cases hs'
    · exact ht'

/-- One actual canonical machine works for every saved tail, retaining full
branch-specific representation, frame, map and allocator relations per run. -/
theorem compilation_success_shared (result : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : result.Input L frame base σ m)
    (hp : Evm.Prog.pays P = false)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o) :
    ∃ canonical, run result.code {m with stack := []} = .ok canonical 0 ∧
      canonical.stack = [] ∧
      ∀ tail, run result.code {m with stack := tail} =
          .ok {canonical with stack := tail} 0 ∧
        result.Rep (L + Evm.Prog.pushes P) frame base σ {m with stack := tail}
          o.st {canonical with stack := tail} := by
  obtain ⟨canonical, ht, hstack, _⟩ :=
    compilation_success_tail result hi hp hs []
  refine ⟨canonical, ht, hstack, ?_⟩
  intro tail
  have he := compilation_tail_exact result hi hp tail
  rw [ht] at he
  change run result.code {m with stack := tail} =
    .ok {canonical with stack := tail} 0 at he
  obtain ⟨actual, ha, _, hr⟩ := compilation_success_tail result hi hp hs tail
  have hm : actual = {canonical with stack := tail} :=
    (Evm.Out.ok.inj (ha.symm.trans he)).1
  exact ⟨he, hm ▸ hr⟩

/-- Equality after erasing only the returned stack includes all failure
outcomes and every non-stack machine component. -/
theorem compilation_two_tails (result : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : result.Input L frame base σ m)
    (hp : Evm.Prog.pays P = false) (left right : List Word) :
    replaceOutStack [] (run result.code {m with stack := left}) =
      replaceOutStack [] (run result.code {m with stack := right}) := by
  rw [compilation_tail_exact result hi hp left, compilation_tail_exact result hi hp right]
  cases run result.code {m with stack := []} <;> rfl

/-- A fault of arbitrary untyped code cannot be transported as if it were a
typed divergence certificate. This is not a counterexample to the compiler law. -/
theorem raw_fault_counterexample :
    run [.pop] Machine.init = .fault ∧
      run [.pop] {Machine.init with stack := [w[41]]} = .ok Machine.init 0 := by
  constructor <;> rfl

end Solidity.Backend.Passes
