# G25-UCAST-1104: unsigned local casts

Status: implementation/proofs/scoped acceptance ready; full repository validation incomplete.

Producer integrator: V09. This independent core packet proves uint256-local
explicit casts to every legal narrower unsigned width (8,16,...,248).
The original qualified-units queue remains incomplete. H27 arrived during this
checkpoint and authorizes its owned inherited-signature normalization; it is
not a dependency of this cast packet and will be resumed after sealing it.
No signature/DeclId, H16 Source, Core ExtCall or construction API was edited.

## Checkout and selection

Exact base `6f3eedf0788ee1f8a3bcf230558c712ecdca04d5`; isolated persistent
worktree `/workspace/solidity-lean-ucast-1104`, branch
`codex/solidity-sol-20261103/ucast-1104`. The original worktree and checkpoint
`ec562cd73c051c1064aa99ac88d01a37321e0a02` were retained; its 155-entry
checksum manifest was verified at launch. A bounded fetch found no newer
published master or existing primitive-packet implementation. The V09 owner
queue contains a Source subtraction application with a supplied CompiledVal;
this cast family instead proves selection by `Evm.Memory.compileVal`.

All four named read-only inputs are verified in tests/primitive-packets-1104/UnsignedCast/inputs.json.
No pending producer, P8 admission inhabitant or QN-SIG decision is used.

## Implementation and general proofs

| Module under Solidity/Backend/PrimitivePackets/UnsignedCast | Result |
|---|---|
| Semantics.lean | Existing Source.convExplicit evaluation of actual locals; source_total derives the numeric witness from any typed uint256 local; existing unsigned remainder agrees with wrapped Source result |
| Compiler.lean | Actual public Evm.Memory.compileVal always selects this family; exact seven emitted symbolic instructions; full machine result over every saved stack |
| Transport.lean | Source/intrinsic/value-identity/selected-code composition from initial value alignment and StateRepr; both pipelines, arbitrary checked frame, nonempty saved tail and preserved representation; exact horizon0/1 timeout |
| Boundaries.lean | General zero,2^bits,maximum-word wrapping and Source input bounds; illegal/non-narrowing widths refused by the domain |
| Controls.lean | Inhabited Source state and positive-offset physical representation, two saved words, protected cursor/cells and actual Source/selected-machine execution |

For offset b and target local j the selected instruction list is exactly
`[mload(cellOf b j), push(2^bits), dup 1, jumpi 1, revert, swap 1, mod]`.
The existing nonzero-divisor guard is retained. No alternate interpreter,
untyped AST or manually supplied successful CompiledVal is a premise.

Source evaluation completes at every horizon fuel+2 with the full Source
state unchanged. Horizons0/1 actually return timeout with that same state;
no target timeout correspondence is inferred. Initial read/value alignment
and the existing full physical StateRepr are premises, not desired runs.
The machine theorem proves equality of the entire output machine with its
input plus one result word: all non-stack fields and every saved word remain.
The numerical result is n modulo2^bits; its bounds come from Source.wrap_mem.
The input may be any Source uint256 local, rather than only constants or a
postulated wrapped result. The checked flag is retained in both pipelines.

## Evidence and trust

Focused importing-consumer build and tests pass. The executable matrix uses
the actual Source evaluator and actual public compiler result, then runs its
selected symbolic code. All372 rows cover31widths × zero/power/max × two
pipelines × two checked modes. It observes wrapped Source contents, exact
seven instructions, stack `[result,77,88]` and protected cells `[64,10,99]`.
General boundary theorems cover the same values for every legal width.
The checker rejects altered tails, illegal width inventory, missing rows,
controller errors and unstarted receipts.

Actual Lean4.24.0(commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b),
Lake5.0.0-src+797c613. KeySort parsed377taclets,131read-bearing,tablecovers131;
annotations match. Runtime cgroup confirms12884901888 bytes and swap.max0.
Every job is serial, Lean-j1 and LEAN_NUM_THREADS=1, with a conservative
4GiB reserve guard. No proof budget, premise, exclusion or trust expansion.

All23 explicit theorem axiom reports and all72 module-owned declarations
(including synthesized equations) are pinned. There are no unsafe/partial
or axiom declarations. Only propext,Classical.choice,Quot.sound occur.
Raw initial elaboration and acceptance-harness failures are retained beside
passing logs; no failed run is relabeled as a pass. Source/log/runner/Lake
hashes make acceptance fail closed on stale evidence. The optimized Python
entrypoints refuse -O. Lean MCP diagnostics were unavailable.

Commands from the worktree:

- `python3 tests/primitive-packets-1104/UnsignedCast/check.py --run`: focused build,372matrix,livepins,tools/cgroups,KeySort; packet acceptance passes.
- `python3 tests/primitive-packets-1104/UnsignedCast/run.py check <file>`: per-file Lean-j1 with tstack131072; exact commands/timings in evidence logs.
- `python3 tests/primitive-packets-1104/UnsignedCast/run.py checkpoint full`: unchanged repository full gates; two actual attempts recorded below; neither completes the full gate.

The full-gate wrapper serializes independently spawned corpus probes through
a separate child-Lake lock, preserving their original semantics/budgets.
The VM writer lock remains held around the entire gate. Shared roots remain
unchanged as this helper packet must provide proposals for integration.


## Actual full-checkpoint results

Both unchanged full-gate attempts passed touched-module compilation, trust,
layers, doc paths, static TestSuite audit and global axiom pins (6,343 pins,
zero errors/unrecorded changes). Run-lean stopped at stale generated roots;
root/orphan gates identify exactly the five new modules, pending the required
producer/coordinator integration. No root/map was edited to suppress them.

The conservative H1 guard stopped the corpus phase in both attempts:
226.269 seconds/minimum4,291,649,536 bytes and
603.510 seconds/minimum4,191,498,240 bytes; process exit137 and controller
RuntimeError are retained. Corpus/full default library validation did not
complete and is not passing evidence. Strict automatic was then run as its
unchanged separate static command and passed; it does not complete full gates.

Between attempts, with no Lean/Lake active, POSIX_FADV_DONTNEED advised away
idle tool/build-cache pages: parent memory.current fell from11,645,218,816
to7,954,550,784 bytes. No files or proof artifacts were deleted or changed.
The hard cap/no-swap/reserve threshold stayed unchanged. A reclaim-aware guard
was considered in read-only reviews but not adopted: the original conservative
max-current reserve accounting remains. Raw command TSVs are retained byte-for-byte in sibling gzip files; readable
TSVs trim only trailing command spaces, as log-normalization.json records.
Both failed attempts stay explicit,
including the first checkpoint directory copy. Cache delivery and producer
registration/full validation remain outstanding integration obligations.

A final controller review found and fixed cleanup of unexpected prior wrappers;
exclusive config creation and owned-directory flags preserve earlier work.
A negative control confirms no child launches and the sentinel survives.
Pending/failure receipts prevent older passes from masking interrupted runs;
receipt acceptance also requires no controller error and a started process.
No protected fields, theorem premises or gates were weakened.

## Registration and area-row proposals

After V09 imports the packet, run the existing central register.sh; do not
copy a second root. Propose these five rows in docs/module-map/v09-passes.md:

| Module | Proposed description |
|---|---|
| Backend/PrimitivePackets/UnsignedCast/Semantics.lean | Actual Source uint256-local explicit cast and existing intrinsic narrowing semantics for every smaller legal uint width |
| Backend/PrimitivePackets/UnsignedCast/Compiler.lean | Public memory compiler selection and exact guarded narrowing code, full protected-machine execution |
| Backend/PrimitivePackets/UnsignedCast/Transport.lean | Independent Source-to-selected symbolic-code cast family with both pipelines and explicit horizon failures |
| Backend/PrimitivePackets/UnsignedCast/Boundaries.lean | General zero,power-of-two and maximum-word cast boundaries |
| Backend/PrimitivePackets/UnsignedCast/Controls.lean | Inhabited positive-offset Source/machine cast controls with protected memory and nonempty saved stack |

No generated root, shared module-map or H21 build/registry file is edited by
this helper. These five modules remain pending producer registration.

## Exact remaining correspondence boundary

This is a proved family translation between existing typed Source expressions
and existing typed Val expressions, followed by proved public selection and
execution in the published symbolic Evm.Instr machine. It does not invoke a
general Source-to-backend compiler. Abstract memory-cell loads and relative
instruction jumps are not assembled byte addresses; physical byte encoding,
relocation, gas and external EVM execution remain outside this packet.
The concrete Source fixture has a toy unused hash; no hash/heap/world
adequacy is inferred. General Source state and machine protection are proved,
while initial local alignment/StateRepr remain explicit assumptions. No
whole-V09, original-QN, source admission or Source-to-EVM completion claim.

## Reviews and checkpoint handoff

Separate read-only finder/skeptic reviewed the five implementation modules
without Lean/server calls and found no semantic defect. They confirmed actual
selection, full machine protection and the symbolic-code boundary. Final
checker/resource/trust reviews and checkpoint outcomes are recorded in the
owned evidence bundle; all scoped checks pass and full validation remains incomplete. Full head/base, original patch, handoff
and SHA256SUMS are generated from the final committed packet; no push is made.
