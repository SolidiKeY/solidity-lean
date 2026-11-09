# Model and Solidity differences

Source/tests define operational behavior. These caveats prevent a model proof
from being mistaken for unrestricted chain correctness. The approved full-scope
target remains [coverage-plan.md](coverage-plan.md); gaps are work, not exclusions.

| Area | Boundary to retain |
|---|---|
| Failures | `assert` panic is rejected by both modalities. Ordinary arithmetic/index failures can collapse to revert, which box accepts. Exact catch payload support is local, not universal error equivalence. |
| Exhaustion | Both modalities accept model exhaustion; a diamond is not automatically successful execution or gas-bounded termination. |
| Allocation/length | Mathematical storage lengths and admitted allocations need not obey all solc `2^64` allocation limits; capacity and layout bridges remain explicit premises. |
| Constructors | Initial balance is modeled from `msg.value`; pre-existing balance at a predictable deployment address can invalidate this simplification. |
| Address zero | The model assumes no code at zero; the assumption is not proved from an arbitrary world. |
| Payments/callbacks | Funding and acceptance are explicit; stipend policy is not a proof of gas adequacy. Full-gas calls may re-enter. |
| Hashes/precompiles | Computation/vectors do not establish external-precompile equivalence or collision resistance. Keep any hash/layout premises. |
| Specifications | Storage frames can be stronger than the pinned SolKey synthesizer. Ledger/length frame permissions remain separately supported or refused; no implicit frame coverage. |

## Evaluation order

Legacy and `.viaIR` presets select expression schedules, not every compiler
pipeline behavior. Preserve early reads before later effects and conditional
operand evaluation. Internal-call implicit-copy/effect interactions remain a
viaIR alignment gap (`copiesBeforeEffects`). Reference-source/target ordering
also has documented limits. Zero-modulus ADDMOD/MULMOD behavior differs between
the source failure abstraction and raw opcodes.

## Modifier placeholder frames

Legacy reuses parameter/return slots across placeholders; viaIR uses distinct
invocation slots while retaining shared referents. Unsupported storage-alias
return shapes remain refused. A finite matching trace is not a universal
compiler theorem.

## Dirty locals after assembly

Cleaning narrow integers/bools at a Solidity use can discard raw bits that a
later assembly read observes. Readback requires its actual no-later-raw-read
condition; it is not general Source/assembly correspondence.

## Overloads differing only in return types

Solc rejects them. Source elaboration can accept and select the first; the P9
whole-program checker refuses such units. Do not infer source validity solely
from elaboration success.

<a id="where-the-interpreter-follows-solc-not-key"></a>

<a id="remaining-deltas-documented-intentionally-out-of-scope"></a>

<a id="arrays-past-their-end"></a>

<a id="transfer"></a>
