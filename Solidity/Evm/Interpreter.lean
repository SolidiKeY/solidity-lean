import Solidity.Evm.Examples
import Solidity.Evm.Correct

/-!
# The typed run, read off the machine

The compiler's interpreter theorems over the scoped syntax
(`docs/intrinsic.md`, M5, W1): a machine run of `Evm/Examples.lean`,
through `Evm/Correct.lean`'s headline, is a fact about `Prog.run`
from a fresh contract, without running the interpreter.  The programs are
scoped blocks from no locals; their fragment checks and bounds run in the
kernel (`decide +kernel`), as their runs do.
-/

namespace Solidity.Evm.Examples

open Solidity.Evm.Examples

local instance : InContract := ⟨StandardExample⟩

/-- The fresh contract the typed run starts from, with no locals, no funds,
at address `0`. -/
abbrev freshState (C : Contract) : Solidity.State C [] := freshT C 0 W_pos 0 W_pos

theorem setAge_frag : (inFragP (Frag.init []) setAge).isSome = true := by
  decide +kernel

/-- `alice.age`, typed. -/
def aliceAge : Solidity.SRef StandardExample (.prim .uint) :=
  ⟨"alice", rfl, .field (f := "age") rfl .nil⟩

/-- **`alice.age = 10;` in the typed run.**  From a fresh contract the run
succeeds, and `alice.age` reads `10`: `compile_storage` ties the run's read
to slot `13`, and the machine run holds `10` there. -/
theorem setAge_interpreter :
    ∃ o, Solidity.Prog.run (freshState StandardExample) setAge = .ok o ∧
      ∀ v, o.st.storage.findLive aliceAge = some (.prim v) → v.1 = 10 := by
  rcases compile_storage (Option.some_get setAge_frag).symm (by decide +kernel) 0 W_pos (fresh).bal
      0 W_pos with ⟨o, m', h1, h2, h3⟩ | ⟨_, h2⟩ | ⟨hp, _⟩
  · refine ⟨o, h1, fun v hv => ?_⟩
    have hp : PathSlot StandardExample false aliceAge.root aliceAge.path.erase (.prim .uint)
        (.root 13) :=
      PathSlot.field (segs := []) (PathSlot.root (T := .ref (.struct "Person")) rfl) rfl
    have hs := h3 _ _ v hp hv
    have hm := Solidity.Evm.Examples.setAge_run
    unfold slotAfter codeOf at hm
    rw [show run (compileProg 0 setAge) fresh = _ from h2] at hm
    simp only [Solidity.Evm.Examples.storeAt, Option.some.injEq] at hm
    omega
  · have := Solidity.Evm.Examples.setAge_run
    unfold slotAfter codeOf at this
    rw [show run (compileProg 0 setAge) fresh = _ from h2] at this
    cases this
  · exact absurd hp (by decide +kernel)

theorem overflow_frag : (inFragP (Frag.init []) overflow).isSome = true := by
  decide +kernel

/-- **`total += 1;` at `2^256 - 1` reverts in the typed run**, because it
reverts on the machine: it pays no one and asserts nothing, and
`compile_exact` makes the two revert together. -/
theorem overflow_interpreter :
    Solidity.Prog.run (freshState StandardExample) overflow = .error .revert := by
  rcases compile_exact (Option.some_get overflow_frag).symm
      (Sim.init StandardExample 0 W_pos (fresh).bal 0 W_pos) (by decide +kernel) (by decide +kernel) with
    ⟨_, _, _, h, _⟩ | ⟨h | ⟨ha, _⟩, _⟩
  · have := reverted_eq Solidity.Evm.Examples.overflow_run
    unfold codeOf at this
    rw [show run (compileProg 0 overflow) fresh = _ from h] at this
    cases this
  · exact h
  · exact absurd ha (by decide +kernel)

theorem payOwner_frag : (inFragP (Frag.init []) payOwner).isSome = true := by
  decide +kernel

/-- **`owner.transfer(30);` books `-30` at `5` and nothing at the contract
in the typed run**, because the machine moved `30` from the contract's
account into `5`'s: `compile_net` reads the run's ledger off the balances
at `5`, and the contract's own entry stays `0`. -/
theorem payOwner_interpreter :
    ∃ o, Solidity.Prog.run (freshState StandardExample) payOwner = .ok o ∧
      o.st.sem.getNet 5 = -30 ∧ o.st.sem.getNet 0 = 0 := by
  have hr := Solidity.Evm.Examples.payOwner_run
  unfold codeOf at hr
  cases h : run (compileProg 0 payOwner) (fresh 100) with
  | ok m k =>
    rw [h] at hr
    cases k with
    | zero =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨h0, h5, h00, h50, hs⟩ := hr
      obtain ⟨σ', h1, hnet, hself⟩ := compile_net (Option.some_get payOwner_frag).symm
        (Sim.init StandardExample 0 W_pos _ 0 W_pos) (by decide +kernel) h
      refine ⟨σ', h1, ?_⟩
      have h := hnet 5 (by decide) (by rw [hs]; decide)
      rw [h5, h50] at h
      rw [hs] at hself
      exact ⟨h, hself⟩
    | succ => simp only [reduceCtorEq] at hr
  | revert => rw [h] at hr; simp only [reduceCtorEq] at hr
  | fault => rw [h] at hr; simp only [reduceCtorEq] at hr

theorem callTwice_frag : (inFragP (Frag.init []) callTwice).isSome = true := by
  decide +kernel

/-- **The call runs in the typed run too**, and `total` reads `5` after it:
the machine run, through `compile_storage`. -/
theorem callTwice_interpreter :
    ∃ o, Solidity.Prog.run (freshState CallsExample) callTwice = .ok o ∧
      ∀ v, o.st.storage.findLive (Solidity.SRef.ofRoot "total" rfl) = some (.prim v) →
        v.1 = 5 := by
  rcases compile_storage (Option.some_get callTwice_frag).symm (by decide +kernel) 0 W_pos
      (fresh).bal 0 W_pos with ⟨o, m', h1, h2, h3⟩ | ⟨_, h2⟩ | ⟨hp, _⟩
  · refine ⟨o, h1, fun v hv => ?_⟩
    have hp : PathSlot CallsExample false (Solidity.SRef.ofRoot (C := CallsExample) "total"
        (T := .prim .uint) rfl).root (Solidity.SRef.ofRoot (C := CallsExample) "total"
        (T := .prim .uint) rfl).path.erase (.prim .uint) (.root 0) := PathSlot.root rfl
    have hs := h3 _ _ v hp hv
    have hm := Solidity.Evm.Examples.callTwice_run
    unfold slotAfter codeOf at hm
    rw [show run (compileProg 0 callTwice) fresh = _ from h2] at hm
    simp only [Solidity.Evm.Examples.storeAt, Option.some.injEq] at hm
    rw [show rootSlot CallsExample "total" = .root 0 from rfl] at hm
    omega
  · have := Solidity.Evm.Examples.callTwice_run
    unfold slotAfter codeOf at this
    rw [show run (compileProg 0 callTwice) fresh = _ from h2] at this
    cases this
  · exact absurd hp (by decide +kernel)

end Solidity.Evm.Examples
