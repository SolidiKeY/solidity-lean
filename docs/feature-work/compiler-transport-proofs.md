# Compiler transport proof components

The modules in `Backend/Passes/` retain the existing intrinsic program and
abstract word-machine definitions. They transport checked compilation through
stack tails, selected address maps, sequential stages, loop scopes and explicit
frame changes. Input, payment freedom, heap ownership, frame/code capacity,
actual successful prefixes and reached suffix inputs remain proof premises.
Failure results expose no post-failure machine or invented address map.

## Reached failure and small-frame completion

The recovered failure controls run a guard after an allocating alias-rebinding
loop. The guard succeeds before that loop and reverts afterward. The complete
observation vector, wrong-order distinction, saved-tail corruption, stale map,
undersized frame and ordinary-revert distinctions are retained.

The completion controls obtain the full suffix output at frame five from the
actual compilation certificate and final execution. The same three selected
maps and loop cost witnesses precede every saved stack tail. Both source and
target associations, old-reference transport, allocation cost, actual new-object
address and complete final observation vector are preserved.

Here source execution means the existing intrinsic program evaluator. These
results do not establish independent Solidity Source admission or adequacy,
fetched physical bytecode execution, arbitrary calls/worlds or full compiler
composition. They are scoped proof components, not a completed V09 assignment.

## Recovery and validation boundary

Twenty-five owned dependency modules are byte-identical to the original V09
commit `5511806ccc2f2d5f347c3448c246d48f0a882e9e`; all 164 existing dependency
files match the integration base. Existing public core files are not replaced.
The producer's draft filenames and labels identify their original partial
workstream; validation status is recorded separately for this checkpoint.

Repairs remove a reserved local identifier, add explicit fact types, correct an
invalid reflexive heap-extension proof argument to the existing prefix law,
and derive the loop input before transporting the saved stack. Pointer proofs
use a variable target machine. Guard success follows the existing checked value
compiler on the actual reached representation, avoiding expansion of the whole
computed machine. Shared witness specifications and direct equality composition
reduce stored proof duplication without hiding the requested value behind a
wrapper or changing any premise, expected observation or formula.

All 27 requested theorem bodies compile, and their complete raw types, values
and standard-axiom reports export under the unchanged 100000-node/512-depth
limits. The original failed drafts, timeouts, resource refusals and source hashes
remain preserved. No larger heartbeat limit, unsafe evaluator or new axiom is
used. The existing global axiom/documentation findings remain baseline failures.

Loaded-object selector authentication, full kernel normalization, independent
replay and original release closure remain separate obligations. The diagnostic
sidecars explicitly retain those incomplete flags. Source and metadata success
here does not close any complete V09 or V17 compiler/EVM assignment.
