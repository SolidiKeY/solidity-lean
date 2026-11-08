# Calculus options

These are model choices, not claims of complete EVM agreement. Types and
[tests](../Solidity/Examples/Tactics/) define each exact reading.

## O1. Who calls back (bug 5)

`noCallback` disables stipend-payment callbacks only. `try` and full-gas value
calls may still re-enter. Deterministic validity assumes all callbacks away.

## O2. `checked { … }`: an overflow fails the proof (`checkingOF`)

`checked` inserts range assertions. A failed assertion is panic, rejected by
both modalities; ordinary checked overflow is a revert accepted by box.

## O3. The strategy with callbacks

Use callback validity when the obligation can call back. Contradiction pruning
must retain the complete context; an impossible diamond update cannot be
replaced by its unwrapped condition.

## O4. Diamonds, calls, and the invariant a specification declares

Payment diamonds need actual funding/recipient acceptance and their continuation
and invariant conditions. A nonnegative amount does not supply acceptance.
Callback continuation must tolerate invariant-preserving state changes.

## O5. `ignoringOverflow { … }`: an overflow assumed away (`ignoringOF`)

Overflow is assumed away, not executed over unbounded machine integers.
`assume(false)` exhausts and is accepted by both modalities; it is a model-only
statement outside the EVM compiler fragment.

## O6. Clean array tails

`solc` adds no clean-tail premise. `clean` requires every relevant shadow slot
to be ordinary default. Reachability alone does not justify that assumption;
prove the interface preserves it.

## O7. The test runner reads callbacks

The obligation's operational semantics selects callback validity. Source
metadata cannot override it. A deterministic proof is not a callback proof.

## O8. Self-calls and address `0`

Address zero is assumed to have no code. Admitted self-call bodies execute in
a fresh call frame; other external results use the stated oracle/world model.
Failure rolls state back. These assumptions do not model gas.

## O9. Expression evaluation order

`Contract.evalOrder` defaults to legacy; `.viaIR` selects its expression preset.
The preset is not full viaIR/compiler equivalence; retain documented copy,
constructor and modifier differences in [solc-alignment.md](solc-alignment.md).

## O10. The assumption record of a verdict (Lean-only)

`ValidA` reads callbacks, tails and order. Overflow/hash/zero-address fields are
labels; policy admission does not create missing semantic theorems.

## O11. Caller models (Lean-only)

`none`, `staticOnly`, `nonReentrant R`, and `any` restrict allowed resumptions.
A declared lock needs a proof it guards the bodies. Weakening by attacker
inclusion applies only at the proved positive modality positions.

## O12. Reachable starting states (Lean-only)

`reachable M` is relative to the specified successful deployment/entry interface;
it excludes arbitrary within-transaction callback frames. The invariant must
be proved over that interface. Exhaustion is not successful reachability.

## O13. The target profile (Lean-only)

Version/pipeline/fork labels do not by themselves parameterize the run.
Only proved profile connections count; a matching label is no EVM theorem.
