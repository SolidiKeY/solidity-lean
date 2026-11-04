import Solidity.Semantics.Nondeterminism.Source
import Solidity.Source.SemanticsExamples

/-!
# Witnesses for the split source semantics (S5.1, S5.2)

Kernel-checked sessions of `sourceSplit` itself, at an allowed environment:

- `envA` is allowed (`envA_allowed`): no account has code and every callee
  answers success at once.
- The fixed parameters use a constant hash (`zeroFixed`), so the creation
  address that `sessionAt` computes reduces to `0` in the kernel
  (`createAddress_zero`), so the contract is deployed at address `0` and
  requests go there; `SessionEnv.ZeroHasNoCode` speaks of accounts outside
  the system only, so this is consistent. Every selector is then `0x00000000`, and dispatch
  picks the one function with a body.
- `orderProg`'s `g()` returns `++x + x` after `x = 1`: `3` under legacy and
  `4` via IR (`order_legacy`, `order_viaIR`). So the property "completes
  with `3` or not at all" is not a `HoldsBoth` statement
  (`order_not_both`: the via-IR run gives `4`), while its legacy run gives
  `3`.
- `constProg`'s `g()` returns `7` under either pipeline, and a request with
  empty call data reverts (no `receive` or fallback). So `sourceSplit EB` is
  non-vacuous at every choice (`sourceSplit_nonVacuous`, through
  `Confined.nonVacuous`), and no choice rescues an always-reverting target
  (`sourceSplit_refutes`).
-/

namespace Solidity.Semantics.Nondeterminism

namespace SourceWitness

open Solidity.Roadmap
open Solidity.Source
open Solidity.Source.SemanticsExamples

/-- Fixed parameters with the constant hash `0`. -/
def zeroFixed : Solidity.Roadmap.Fixed where
  evm := { keccak := fun _ => 0, keccak_lt := fun _ => by decide,
           precompile := fun _ _ => none, precompileGas := fun _ _ => 0 }
  ledger := fun bal _ a => bal a
  regionLen := 1
  rootSlots := 1

/-- The creation address is `0` for every deployer and nonce. -/
theorem createAddress_zero (s : Address) (k : Fin (2 ^ 64)) : zeroFixed.createAddress s k = addr 0 := rfl

/-- `x = 1; return ++x + x;` -/
def gOrder : RBody EB := ⟨[], [uint], false, [uint], [uint],
  .stmt (setX (lit 1))
    (.stmt (.retVal rfl (.binary .add (.incDec true true (.state dX dX_ty rfl)) (.state dX dX_ty)) rfl) .nil), []⟩

/-- `return 7;` -/
def gConst : RBody EB := ⟨[], [uint], false, [uint], [uint],
  .stmt (.retVal rfl (lit 7) rfl) .nil, []⟩

/-- `C` with `g()` as given. -/
def progWith (b : RBody EB) : Program EB where
  body d := match d.name with
    | "g" => some b
    | _ => none
  consts _ := none
  inits _ := []
  ctor _ := none
  ctorLocals _ := []
  baseArgs _ := []
  contracts := ["C"]

def orderProg : SrcProg EB := ⟨progWith gOrder, .legacy, zeroFixed, "C"⟩
def constProg : SrcProg EB := ⟨progWith gConst, .legacy, zeroFixed, "C"⟩

/-- An allowed session: deploy `C`, then one request with call data `input`. -/
def envA (input : Bytes) : SessionEnv where
  deployer := user
  deployNonce := ⟨0, by decide⟩
  deployValue := word 0
  deployArgs := []
  balance := fun _ => word 0
  hasCode := fun _ _ => false
  requests := fun _ i => if i = 0 then some (.request ⟨user, addr 0, word 0, word 0, input⟩) else none
  callee := answerOnly

theorem envA_allowed (input : Bytes) : (envA input).Allowed :=
  ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

/-- The call data of `g()` under the constant hash. -/
def callG : Bytes := [0, 0, 0, 0]

/-- **Legacy**: `3` (the right operand `x` is read first). -/
theorem order_legacy :
    ((sourceSplit EB).sem (CompilerChoice.plain .legacy) orderProg (envA callG) (30 : Nat)).final =
      some (.success (wordBytes (toWord 3))) := by
  decide +kernel

/-- **Via IR**: `4` (source order). -/
theorem order_viaIR :
    ((sourceSplit EB).sem (CompilerChoice.plain .viaIR) orderProg (envA callG) (30 : Nat)).final =
      some (.success (wordBytes (toWord 4))) := by
  decide +kernel

/-- Completes with `3`, or not at all. -/
def threeOrUnfinished (x : Prefix Event Outcome) : Prop :=
  x.final = none ∨ x.final = some (.success (wordBytes (toWord 3)))

/-- **Negative control**: not under both pipelines, though legacy gives `3`. -/
theorem order_not_both (art : Pipeline → Artifact) :
    ¬ (sourceSplit EB).HoldsBoth art orderProg threeOrUnfinished := by
  intro h
  have hv := h .viaIR (GasOracle.const ⟨0, by decide⟩) (envA callG) (envA_allowed _) (30 : Nat) trivial
  have e : ((sourceSplit EB).sem ⟨.viaIR, art .viaIR, GasOracle.const ⟨0, by decide⟩⟩ orderProg
      (envA callG) (30 : Nat)).final = some (.success (wordBytes (toWord 4))) := order_viaIR
  rcases hv with hn | h3
  · rw [e] at hn
    cases hn
  · rw [e] at h3
    revert h3
    decide +kernel

theorem const_success (q : Pipeline) :
    ((sourceSplit EB).sem (CompilerChoice.plain q) constProg (envA callG) (30 : Nat)).final =
      some (.success (wordBytes (toWord 7))) := by
  cases q <;> decide +kernel

theorem const_revert (q : Pipeline) :
    ((sourceSplit EB).sem (CompilerChoice.plain q) constProg (envA []) (30 : Nat)).final =
      some (.revert []) := by
  cases q <;> decide +kernel

/-- **The split source is non-vacuous at every choice.** -/
theorem sourceSplit_nonVacuous : (sourceSplit EB).NonVacuous :=
  (sourceSplit_confined EB).nonVacuous (ps := constProg) (pr := constProg) rfl rfl
    ⟨envA callG, (30 : Nat), wordBytes (toWord 7), envA_allowed _, trivial, by decide +kernel, const_success⟩
    ⟨envA [], (30 : Nat), [], envA_allowed _, trivial, const_revert⟩

/-- **No choice rescues an always-reverting target** for the source. -/
theorem sourceSplit_refutes {RT : Type} {AT : RT → Prop}
    (t : SrcProg EB → SessionEnv → Prefixes RT Event Outcome)
    (hrev : ∀ p e rt d, AT rt → (t p e rt).final ≠ some (.success d)) (c : CompilerChoice) :
    ∃ p e, (sourceSplit EB).Allowed e ∧ ¬ Refines (sourceSplit EB).Admissible AT ((sourceSplit EB).sem c p e) (t p e) :=
  sourceSplit_nonVacuous.refutes t hrev c

end SourceWitness

end Solidity.Semantics.Nondeterminism
/-- info: 'Solidity.Semantics.Nondeterminism.SourceWitness.order_legacy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.SourceWitness.order_legacy
/-- info: 'Solidity.Semantics.Nondeterminism.SourceWitness.order_viaIR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.SourceWitness.order_viaIR
/-- info: 'Solidity.Semantics.Nondeterminism.SourceWitness.order_not_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.SourceWitness.order_not_both
/-- info: 'Solidity.Semantics.Nondeterminism.SourceWitness.sourceSplit_nonVacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.SourceWitness.sourceSplit_nonVacuous
/-- info: 'Solidity.Semantics.Nondeterminism.SourceWitness.sourceSplit_refutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.SourceWitness.sourceSplit_refutes
/-- info: 'Solidity.Semantics.Nondeterminism.SourceWitness.envA_allowed' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.SourceWitness.envA_allowed
