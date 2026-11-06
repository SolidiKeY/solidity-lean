# H62 item 1 infer helpers — preliminary handoff

Base: c6f550e281a7e5affa9a99bc2cdaed556dec00e4. This is an incomplete
inventory, not a completed checkpoint. Scope is the copied helpers only;
H55 retains both inferencers and their relations.

The lexical census reports Source `STy.isMapping`, `STy.isPayableArg`,
`STy.convLoc` and Frontend Static `isMappingTy`, `payableArg`, `convLoc`.
Its negative control detects a missing, duplicate, or unavailable source
file. It is not a Lean parser and cannot establish declaration equivalence,
reference completeness, or semantic preservation.

No Lean statement, proof, axiom, sorry, or original source was changed. No
helper module, migration patch, owner coordination, independent finder or
skeptic review, acceptance gate, affected validation, or comparative timing
has been completed. All four checkpoints and assigned backfill remain.

The coordinator-pinned official Lean 4.35.0 archive was verified against
SHA-256 7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d.
Lean reports 4.35.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc;
Lake reports 5.0.0-src+eb6cafb. A direct bounded KeySort diagnostic exited
0 in 1.91s, but does not satisfy the required MCP or run-lean.sh gate.
No runtime gate is claimed. The first attempted Lake command rejected -j1
as a Lake option; another diagnostic lacked /usr/bin/time. Neither passed.

Next: configure the pinned toolchain and serial -j1 driver without reusing
4.24 artifacts; obtain the required KeySort prerequisite; finish census,
fixtures and additive helpers, compare exact behavior and timings, arrange
owner coordination and independent reviews, then perform all required gates.

## Shape census and migration blocker (continuation)

`check_shapes.py` compares the six declarations with fixed token snapshots,
ignoring whitespace. It is a lexical check, not a Lean parser, proof, or
reference scanner. `test_shapes.py` checks all six against independent branch
mutations, and checks duplicate declarations, token splitting and absent files.
Both this test and `test_census.py` pass on the pinned base.

The source case inventory below covers the 18 `STy` constructors. Mapping
and payable columns are the expected Boolean outputs of both copies; the
location column is the expected output of both copies. For bytes/string,
`loc` is the input location, including memory, storage and calldata.

| Constructors | Mapping | Payable | Conversion location |
| --- | --- | --- | --- |
| `mapping` | true | false | memory |
| `address`, `contract` | false | true | memory |
| `bytes`, `string` | false | false | loc |
| `int`, `bool`, `fixedBytes`, `fixed`, `enum`, `udvt`, `array`, `struct`, `fn`, `rational`, `hexConst`, `stringLit`, `tuple` | false | false | memory |

These are source observations, not kernel-checked equivalence theorems.

On the unchanged base, the pinned 4.35.0 `./run-lean.sh` run used the
separate cache and external Lake configuration recorded in the evidence
directory, `LEAN_NUM_THREADS=1`, `-j1` per Lean process, a 12 GiB virtual
memory limit and the writer lock. The log shows `Solidity.KeySort` built in
1.5 s and then errors in `Solidity/Hash/CollisionBound.lean` (first at line
407: unsolved goal) and `Solidity/Language/FixedPoint.lean` (first at line
152: `generalize` failed). The already-failed run was interrupted, exit 130;
it did not complete the final gate. These files are outside this lane. No
runtime-gate pass or before/after comparison is claimed. Continue with
in-scope backfill; full validation requires the toolchain-migration owners
 to supply a compatible base, without changing frozen statements.

The writer-lock and exact-file ownership rules remain in force. A filesystem
search did not find `relay.sh` on this VM; no owner request or approval is
claimed. No inferencer merge or edit was made.
