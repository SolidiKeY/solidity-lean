import Solidity.Evm.CoreExamples
import Solidity.Evm.CoreCorrect

/-!
# The scoped interpreter, read off the machine

`Evm/Examples.lean`'s interpreter theorems over the scoped syntax
(`docs/intrinsic.md`, M5): a machine run of `Evm/CoreExamples.lean`, through
`Evm/CoreCorrect.lean`'s headline, is a fact about `Core.Prog.run` from a
fresh contract, without running the interpreter.  The programs are
`scopedOf P`, `P` resolved from no locals; their fragment checks and bounds
run in the kernel (`decide +kernel`), as their runs do.
-/

namespace Solidity.Evm.Core.Examples

open Solidity.Evm.Examples

local instance : InContract := ⟨StandardExample⟩

/-- The fresh contract the interpreter starts from, with no locals. -/
abbrev freshState (C : Contract) (balance : Nat := 0) : Solidity.Core.State C [] :=
  Solidity.Core.State.ofSem (State.fresh C balance)

theorem setAge_frag : (inFragP (Frag.init []) (scopedOf setAge).2).isSome = true := by
  decide +kernel

/-- **`alice.age = 10;` in the interpreter.**  From a fresh contract the
interpreter succeeds, and `alice.age` reads `10`: `compile_storage` ties the
interpreter's read to slot `13`, and the machine run holds `10` there. -/
theorem setAge_interpreter :
    ∃ σ', Solidity.Core.Prog.run (freshState StandardExample) (scopedOf setAge).2 = .ok σ' ∧
      ∀ n, σ'.glob.findLive "alice" [.field "age"] = .ok (.prim (.int n)) → n = 10 := by
  rcases compile_storage (Option.some_get setAge_frag).symm (by decide +kernel) 0 (fresh).bal 0
      W_pos with ⟨σ', m', h1, h2, h3⟩ | ⟨_, h2⟩ | ⟨hp, _⟩
  · refine ⟨σ', h1, fun n hn => ?_⟩
    have hp : PathSlot StandardExample false "alice" [.field "age"] (.prim .uint) (.root 13) :=
      PathSlot.field (segs := []) (PathSlot.root (T := .ref (.struct "Person")) rfl) rfl
    have hs := h3 _ _ _ n hp hn
    have hm := Solidity.Evm.Core.Examples.setAge_run
    unfold slotAfter codeOf at hm
    rw [show run (compileProg 0 (scopedOf setAge).2) fresh = _ from h2] at hm
    simp only [Solidity.Evm.Examples.storeAt, Option.some.injEq] at hm
    omega
  · have := Solidity.Evm.Core.Examples.setAge_run
    unfold slotAfter codeOf at this
    rw [show run (compileProg 0 (scopedOf setAge).2) fresh = _ from h2] at this
    cases this
  · exact absurd hp (by decide +kernel)

theorem overflow_frag : (inFragP (Frag.init []) (scopedOf overflow).2).isSome = true := by
  decide +kernel

/-- **`total += 1;` at `2^256 - 1` reverts in the interpreter**, because it
reverts on the machine: it pays no one and asserts nothing, and
`compile_exact` makes the two revert together. -/
theorem overflow_interpreter :
    Solidity.Core.Prog.run (freshState StandardExample) (scopedOf overflow).2 = .error .revert := by
  rcases compile_exact (Option.some_get overflow_frag).symm
      (Sim.init StandardExample 0 (fresh).bal 0 W_pos) (by decide +kernel) (by decide +kernel) with
    ⟨_, _, _, h, _⟩ | ⟨h | ⟨ha, _⟩, _⟩
  · have := reverted_eq Solidity.Evm.Core.Examples.overflow_run
    unfold codeOf at this
    rw [show run (compileProg 0 (scopedOf overflow).2) fresh = _ from h] at this
    cases this
  · exact h
  · exact absurd ha (by decide +kernel)

theorem payOwner_frag : (inFragP (Frag.init []) (scopedOf payOwner).2).isSome = true := by
  decide +kernel

/-- **`owner.transfer(30);` books `-30` at `5` and nothing at the contract
in the interpreter**, because the machine moved `30` from the contract's
account into `5`'s: `compile_net` reads the interpreter's ledger off the
balances at `5`, and the contract's own entry stays `0`. -/
theorem payOwner_interpreter :
    ∃ σ', Solidity.Core.Prog.run (freshState StandardExample) (scopedOf payOwner).2 = .ok σ' ∧
      σ'.glob.getNet 5 = -30 ∧ σ'.glob.getNet 0 = 0 := by
  have hr := Solidity.Evm.Core.Examples.payOwner_run
  unfold codeOf at hr
  cases h : run (compileProg 0 (scopedOf payOwner).2) (fresh 100) with
  | ok m k =>
    rw [h] at hr
    cases k with
    | zero =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨h0, h5, h00, h50, hs⟩ := hr
      obtain ⟨σ', h1, hnet, hself⟩ := compile_net (Option.some_get payOwner_frag).symm
        (Sim.init StandardExample 0 _ 0 W_pos) (by decide +kernel) h
      refine ⟨σ', h1, ?_⟩
      have h := hnet 5 (by decide) (by rw [hs]; decide)
      rw [h5, h50] at h
      rw [hs] at hself
      exact ⟨h, hself⟩
    | succ => simp only [reduceCtorEq] at hr
  | revert => rw [h] at hr; simp only [reduceCtorEq] at hr
  | fault => rw [h] at hr; simp only [reduceCtorEq] at hr

theorem callTwice_frag : (inFragP (Frag.init []) (scopedOf callTwice).2).isSome = true := by
  decide +kernel

/-- **The call runs in the interpreter too**, and `total` reads `5` after it:
the machine run, through `compile_storage`. -/
theorem callTwice_interpreter :
    ∃ σ', Solidity.Core.Prog.run (freshState CallsExample) (scopedOf callTwice).2 = .ok σ' ∧
      ∀ n, σ'.glob.findLive "total" [] = .ok (.prim (.int n)) → n = 5 := by
  rcases compile_storage (Option.some_get callTwice_frag).symm (by decide +kernel) 0 (fresh).bal 0
      W_pos with ⟨σ', m', h1, h2, h3⟩ | ⟨_, h2⟩ | ⟨hp, _⟩
  · refine ⟨σ', h1, fun n hn => ?_⟩
    have hp : PathSlot CallsExample false "total" [] (.prim .uint) (.root 0) := PathSlot.root rfl
    have hs := h3 _ _ _ n hp hn
    have hm := Solidity.Evm.Core.Examples.callTwice_run
    unfold slotAfter codeOf at hm
    rw [show run (compileProg 0 (scopedOf callTwice).2) fresh = _ from h2] at hm
    simp only [Solidity.Evm.Examples.storeAt, Option.some.injEq] at hm
    rw [show rootSlot CallsExample "total" = .root 0 from rfl] at hm
    omega
  · have := Solidity.Evm.Core.Examples.callTwice_run
    unfold slotAfter codeOf at this
    rw [show run (compileProg 0 (scopedOf callTwice).2) fresh = _ from h2] at this
    cases this
  · exact absurd hp (by decide +kernel)

end Solidity.Evm.Core.Examples
