# G21/G41 Source boolean custom errors and indexed ABI observations

New modules BoolErrorAbi and BoolErrorAbiControls under Solidity.Lowering.V08.
No hand registration: coordinator registers them. Frozen original base remains
2fe1f8932f96be15b00df03ba2cde46f64a87758. Current helper was rebased onto
published origin/master e1e21297 before starting this component; relevant
published Source/BoolErrorLowering dependencies were inspected unchanged.

values builds actual indexed AbiEntry.Vals from arbitrary literal boolean
lists, with real validated AbiEntry.Word.bool. It is a typed value builder,
not another ABI semantics. word_bytes proves actual Source.wordBytes and
AbiEntry.wordBytes agreement for both full bool words. static_go proves the
actual assemble.go recursion independently of its starting offset;
encoding_agreement relates actual Source.abiLayout output to encodeArgs.
No desired encoded packet, decoder result or simulation hypothesis is used.

payload_agreement retains the actual global selector of the original Decl;
no ASCII signature assumption or selector noncollision hypothesis is added.
source_typed derives actual Source.execS at the unchanged list-length fuel
horizon with complete published L0/state preservation. packet_readback
executes code selected by the actual typed-statement emitter and observes
all bytes in its real reached Failure.Slice memory. Original Fits and stack
capacity bounds remain explicit. Source and target states remain distinct.
This is a closed literal-value output agreement and observation theorem,
not unknown-runtime-memory emission, dynamic code loading, a native/compiler
or Source-to-EVM relation, catch-phase/world/frame/rollback closure.

Populated source_client and target_client discharge actual type/selection,
Fits and stack premises using published fixtures. Negatives distinguish bool
word2 validation, swapped argument order, and missing word bytes; the last
two are byte inequality controls, not certified decoder-failure claims.
Lossless test-only rendering retains every byte for five Source and five
independent-codec argument packets, with equal expected vectors. No previous
observation/fixture was modified or omitted. These are kernel codec checks,
not new external compiler/EVM observations.

Automation first: generic rfl reached the existing heartbeat limit; successful
cases-b-rfl was selected without raising it. All raw attempts/failures retained.
Actual complete per-file MCP diagnostics pass both files. Scoped axiom output,
focused toolkit gates, complete vector checks and independent read-only
finder/skeptic source/artifact reviews accompany the checkpoint seal.
No Lean/server/builds by reviewers. No unchanged failed full gate repeated.

All full G21/G40/G41/G42 and both Backfills remain partial. General runtime
ABI decoding/dispatch/emission, declared demand and same-invocation execution
linkage, arbitrary world/callee/resource/transaction composition and mandatory
whole-lane gates remain open. Published P1/P2/P3/P6/P10 interfaces are not
absent, but their documented execution/provenance premises remain obligations.
P3/G42.03 stay with readonly-external. Old private nine-source V12 input is
preserved and is not a dependency of these new modules. Historical Suite124,
full1, cold124, rawdocs1/frozencomparison1, bodyexport1 and previous failed
attempts remain failures. Prior/publication doc equality is separate.
Original goal identity/status unchanged; no administration or publication.
