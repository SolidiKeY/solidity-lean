import Solidity.Backend.Payments.Versioned
import Solidity.Evm.Interpreter

/-!
# G43 V2: witnesses and controls

On `payOwner`, `owner = 5; owner.transfer(30);`, from the fresh contract at
address `0` (`Evm.Examples.fresh`):

- `paying_premises`: `compile_correct_v2`'s premises hold together for this
  paying program, from every fresh contract (any balance below `2^256`, any
  balance map, any address) with every payment accepted;
- `paying_succeeds_both`: with `100` in the account, V2's first outcome:
  both runs succeed, in represented states;
- `paying_refused_both`: with `10`, a payment of `30` is refused on both
  sides: both revert;
- `oracle_carries_weight` (negative control): with `100` but a machine whose
  world refuses payments to `5`, the typed run succeeds and the machine
  reverts, so the frozen payment disjunct's shape is inhabited and V2's
  conclusion is false there; the pair is not a `Sim`, exactly because of the
  premise `Sim.oracle`. V2 depends on that premise, not on anything weaker.

A refusal by the world's `accepts` that the typed world also records
(`ext`) is not exercised here: `Sim.init` builds only the empty typed world.
-/

namespace Solidity.Evm.PaymentControls

open Solidity.Evm.Examples (payOwner fresh payOwner_frag)

/-- The typed fresh contract at address `0` with `balance`. -/
abbrev start (balance : Nat) (hb : balance < W) : Solidity.State StandardExample [] :=
  freshT StandardExample balance hb ⟨0, W_pos⟩

/-- **Joint satisfiability** of `compile_correct_v2`'s premises on paying
code, from every fresh contract with every payment accepted. -/
theorem paying_premises (balance : Nat) (hb : balance < W) (bal : Fin W → Nat)
    (self : Fin W) (hbalance : balance = bal self) :
    ∃ F', inFragP (Frag.init []) payOwner = some F' ∧ Prog.pays payOwner = true ∧
      Sim StandardExample 1 0 (Frag.init []) (freshT StandardExample balance hb self)
        (Machine.init bal self) ∧ 1 + Prog.pushes payOwner ≤ Lmax :=
  ⟨_, (Option.some_get payOwner_frag).symm, by decide +kernel,
    Sim.init StandardExample balance hb bal self hbalance, by decide +kernel⟩

/-- **A payment made on both sides**: from `100`, V2 gives its first outcome. -/
theorem paying_succeeds_both :
    ∃ (o : Solidity.Out StandardExample [] _) (m' : Machine),
      Solidity.Prog.run (start 100 (by decide)) payOwner = .ok o ∧
      run (compileProg 0 payOwner) (fresh 100) = .ok m' 0 ∧
      Sim StandardExample (1 + Prog.pushes payOwner) 0
        ((inFragP (Frag.init []) payOwner).get payOwner_frag) o.st m' := by
  rcases compile_correct_v2 (Option.some_get payOwner_frag).symm
      (Sim.init StandardExample 100 (by decide) (fresh 100).bal ⟨0, W_pos⟩ rfl) (by decide +kernel) with
    ⟨o, m', h1, h2, -, h4⟩ | ⟨-, hr⟩ | ⟨-, hf⟩
  · exact ⟨o, m', h1, h2, h4⟩
  · have h := Solidity.Evm.Examples.payOwner_run
    unfold Solidity.Evm.Examples.codeOf at h
    rw [show run (compileProg 0 payOwner) (fresh 100) = .revert from hr] at h
    cases h
  · have h := Solidity.Evm.Examples.payOwner_run
    unfold Solidity.Evm.Examples.codeOf at h
    rw [show run (compileProg 0 payOwner) (fresh 100) = .fault from hf] at h
    cases h

/-- The machine run from `10` reverts: the contract cannot pay `30`. -/
theorem payOwner_short_reverts : run (compileProg 0 payOwner) (fresh 10) = .revert :=
  Solidity.Evm.Examples.reverted_eq (by decide +kernel)

/-- **A payment refused on both sides**: from `10`, both runs revert. -/
theorem paying_refused_both :
    Solidity.Prog.run (start 10 (by decide)) payOwner = .error .revert ∧
      run (compileProg 0 payOwner) (fresh 10) = .revert := by
  refine ⟨?_, payOwner_short_reverts⟩
  rcases Payments.compile_revert (Option.some_get payOwner_frag).symm
      (Sim.init StandardExample 10 (by decide) (fresh 10).bal ⟨0, W_pos⟩ rfl) (by decide +kernel)
      payOwner_short_reverts with h | ⟨ha, -⟩
  · exact h
  · exact absurd ha (by decide +kernel)

/-- The machine at `100` whose world refuses every payment to `5`. -/
abbrev refusing : Machine := { fresh 100 with accepts := fun a _ => a.1 != 5 }

/-- **Negative control: the oracle premise carries the weight.** Beside the
typed fresh contract with `100`, the refusing machine reverts while the typed
run succeeds (the frozen payment disjunct's shape), so V2's conclusion fails
there; and the pair is not a `Sim`, because `Sim.oracle` fails at (`5`, `30`). -/
theorem oracle_carries_weight :
    ¬ Sim StandardExample 1 0 (Frag.init []) (start 100 (by decide)) refusing ∧
      run (compileProg 0 payOwner) refusing = .revert ∧
      (∃ o, Solidity.Prog.run (start 100 (by decide)) payOwner = .ok o) ∧
      ¬ (∃ o m', Solidity.Prog.run (start 100 (by decide)) payOwner = .ok o ∧
          run (compileProg 0 payOwner) refusing = .ok m' 0) := by
  have hr : run (compileProg 0 payOwner) refusing = .revert :=
    Solidity.Evm.Examples.reverted_eq Solidity.Evm.Examples.transfer_refused.2
  obtain ⟨o, ho, -⟩ := Solidity.Evm.Examples.payOwner_interpreter
  refine ⟨fun h => ?_, hr, ⟨o, ho⟩, fun ⟨_, _, _, h⟩ => by rw [hr] at h; cases h⟩
  have := h.oracle (uintT 5 (by decide)) (uintT 30 (by decide)) ⟨5, by decide⟩ ⟨30, by decide⟩
    rfl rfl
  simp only [freshT] at this
  cases this

/-! ## Axioms: Lean's three -/

/-- info: 'Solidity.Evm.PaymentControls.paying_succeeds_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms paying_succeeds_both

/-- info: 'Solidity.Evm.PaymentControls.paying_refused_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms paying_refused_both

/-- info: 'Solidity.Evm.PaymentControls.oracle_carries_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oracle_carries_weight

end Solidity.Evm.PaymentControls
