# V15 P10: fetched CALL/RETURNDATA/JUMP consumer

Human H10 authorizes this helper branch from published master
`e7cc378c275eafe7a047c63f672bedbed2fec6ff`, for V14 Q31 and the V13/V16/VY3/VY4
consumers. Original V15 branches/goal and all semantic/proof/resource holds remain
unchanged. Reserved Bridge adapters, core and vendor definitions are read only.

## Early typed interface checkpoint

New module: `Bridge/SolidityBridge/RoadmapV15/P10/Interface.lean`. Namespace
`SolidityBridge.RoadmapV15.P10`. `Site op` uses existing Backend.Op/Program and
actual EVM.State, with typed prefix/suffix and an explicit nonwrapping byte-PC
bound. It constructs the complete ordered Backend.encode code in an actual
reference state; other seed fields are retained. No decoder, execution, source
frame-origin or successful call result is a premise.

Public facts: Site.code_bytes, Site.pc_nat; decode_call, decode_return_size,
decode_return_copy, decode_jump, decode_jump_if, decode_jump_dest; corresponding
fetch_call/fetch_return_size/fetch_return_copy/fetch_jump/fetch_jump_if/
fetch_jump_dest. Fetch facts equate actual on-demand EVM.step to its actual
supplied dispatch; they retain its fuel, account-call and error semantics.
They do not yet establish charged driver gate adequacy or world correspondence.

`Bridge/SolidityBridge/RoadmapV15/P10/Controls.lean` inhabits a PC3 site after a
PUSH1 containing an embedded0xf1 byte and POP, with a nonzero nine-word caller
stack, memory and distinct buffers/context. Complete encoded bytes, all six
decoders, wrong instruction/PC, zero fuel and positive-outer/zero-nested-CALL
fuel are checked. A finder/skeptic request to audit all fourteen public facts
was fixed by adding the six decoder axiom reports.

Focused interface04 and controls02 pass under Lean-j1/LEAN_NUM_THREADS1,
12GiB/no-swap/4GiB admission reserve and unchanged300s per-file budget. All14
axiom reports use only propext/Classical.choice/Quot.sound. Exact cached source
identity for EvmYul/Conform, Backend.Opcode and package manifest was verified
against the existing checked cache; no new dependency/pin/toolchain was used.
Earlier proof/output-directory failures and guard02 headroom rejection remain
raw evidence. Repository-wide registered/full gates remain PENDING for this
early relay checkpoint; the next checkpoint adds charged execution consumers.

Independent read-only finder/skeptic reviews cleared source and controls without
Lean/build/server use. No reference success/driver/world/transaction/Osaka or
full G46/G47 completion is claimed. This is an early typed interface for relay.

## Remaining P10 work

Expose actual charged/fetched CALL through EVM.call, preserving its complete
state/outcomes rather than a payment Boolean. Expose return-data size/copy and
JUMP/JUMPI using original gate ordering, bounds, jump membership and state.
Run populated/negative/combination controls, scoped axioms and bounded registered
closure/full gates; distinguish supplied dispatcher fuel from nested-call fuel.
Actual source-lowering/ABI/physical frame/allocator/driver resource and full
world/transaction/trace/Osaka adequacy remain original open obligations.

## Runtime ownership evidence

Automatic approval review rejected a broad stopped-container cleanup because a
name prefix alone did not establish ownership. It did not execute. Exact
current-turn P10 container IDs were then individually verified against their
receipt hash, full workload command, unique barrier, working directory and
exited state before H1 cleanup; each removal has a retained receipt. No force,
unrelated process/container, cache, source or sealed artifact was removed.
Denied page-cache reclaim and the unchanged admission floor remain recorded.
