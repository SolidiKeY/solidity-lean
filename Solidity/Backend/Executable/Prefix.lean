import Solidity.Backend.Creation.Constructor

/-!
# Constructor consumers of the published creation prefix relation

Finite continuation prefixes compose without replacing the independent byte
runner. Stack-tail transport applies only to continuing PUSH/CODECOPY steps;
terminal RETURN/REVERT observations are composed through the existing runner.
No gas, account installation, source constructor or whole-EVM claim is made.
The prefix preserves stack suffixes; the terminal runner exposes no final stack.
An arbitrary suffix carries no 1024-word stack/headroom certificate.
-/
namespace Solidity.Backend.Executable
open Creation

/-- Two actual continuation segments form one prefix of the same byte code. -/
theorem prefix_trans {code a b c : List UInt8}
    {sa sb sc : List StackWord} {ma mb mc : List UInt8}
    (first : Prefix code a sa ma b sb mb)
    (second : Prefix code b sb mb c sc mc) : Prefix code a sa ma c sc mc := by
  induction first with
  | refl => exact second
  | step hf he rest ih => exact .step hf he (ih second)

/-- Continuing instructions preserve an arbitrary stack suffix. The premise
excludes terminal instructions and supplies the operands consumed by CODECOPY. -/
theorem effect_stack_tail {code : List UInt8} {i : Instr}
    {stack nextStack : List StackWord} {memory nextMemory : List UInt8}
    (step : effect code i stack memory = some (.next nextStack nextMemory))
    (tail : List StackWord) :
    effect code i (stack ++ tail) memory = some (.next (nextStack ++ tail) nextMemory) := by
  cases i with
  | push n imm =>
    cases step
    rfl
  | op o =>
    cases o <;> try { cases step }
    case RETURN =>
      cases stack with
      | nil => cases step
      | cons offset rest => cases rest <;> cases step
    case REVERT =>
      cases stack with
      | nil => cases step
      | cons offset rest => cases rest <;> cases step
    case CODECOPY =>
      cases stack with
      | nil => cases step
      | cons destination rest =>
        cases rest with
        | nil => cases step
        | cons source rest =>
          cases rest with
          | nil => cases step
          | cons length rest =>
            cases step
            rfl

/-- Every intermediate prefix step retains the same untouched stack suffix. -/
theorem prefix_stack_tail {code a b : List UInt8}
    {sa sb : List StackWord} {ma mb : List UInt8}
    (steps : Prefix code a sa ma b sb mb) (tail : List StackWord) :
    Prefix code a (sa ++ tail) ma b (sb ++ tail) mb := by
  induction steps with
  | refl => exact .refl _ _ _
  | step hf he rest ih => exact .step hf (effect_stack_tail he tail) ih

/-- Two separately proved constructor segments feed the existing exact-byte
exit theorem, including a protected caller stack suffix at every prefix step. -/
theorem constructor_segments (p : Placement pre bytes) (success : Bool)
    (args middle : List UInt8) (sa sb tail : List StackWord) (ma mb : List UInt8)
    (first : Prefix (pre ++ encode (exitWrapper success p.lengthWord p.offsetWord) ++ bytes ++ args)
      (pre ++ encode (exitWrapper success p.lengthWord p.offsetWord) ++ bytes ++ args)
      [] [] middle sa ma)
    (second : Prefix (pre ++ encode (exitWrapper success p.lengthWord p.offsetWord) ++ bytes ++ args)
      middle sa ma (encode (exitWrapper success p.lengthWord p.offsetWord) ++ bytes ++ args) sb mb) :
    let code := pre ++ encode (exitWrapper success p.lengthWord p.offsetWord) ++ bytes ++ args
    Exec code code tail [] (exitOutcome success bytes) := by
  exact (prefix_stack_tail (prefix_trans first second) tail).exec
    (p.exit success args (sb ++ tail) mb)

/-- A successful constructor cannot also revert, even with identical bytes. -/
theorem returned_excludes_reverted {code stream bytes other : List UInt8}
    {stack : List StackWord} {memory : List UInt8}
    (success : Exec code stream stack memory (.returned bytes)) :
    ¬ Exec code stream stack memory (.reverted other) := by
  intro failure
  cases success.deterministic failure

/-- Exact failure observations distinguish unequal constructor payloads. -/
theorem reverted_bytes_unique {code stream bytes other : List UInt8}
    {stack : List StackWord} {memory : List UInt8}
    (first : Exec code stream stack memory (.reverted bytes))
    (second : Exec code stream stack memory (.reverted other)) : bytes = other := by
  exact Outcome.reverted.inj (first.deterministic second)

/-- info: 'Solidity.Backend.Executable.prefix_trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms prefix_trans
/-- info: 'Solidity.Backend.Executable.effect_stack_tail' does not depend on any axioms -/
#guard_msgs in
#print axioms effect_stack_tail
/-- info: 'Solidity.Backend.Executable.prefix_stack_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms prefix_stack_tail
/-- info: 'Solidity.Backend.Executable.constructor_segments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms constructor_segments
/-- info: 'Solidity.Backend.Executable.returned_excludes_reverted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms returned_excludes_reverted
/-- info: 'Solidity.Backend.Executable.reverted_bytes_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reverted_bytes_unique
end Solidity.Backend.Executable
