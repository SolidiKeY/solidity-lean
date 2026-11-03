# G21 slice-expression ABI decoding consumer

New modules LiteralFailureSliceDecode and LiteralFailureSliceDecodeControls
under Solidity.Lowering.V08; coordinator registration only. Published master
6510c302 was fetched and inspected before this item; no relevant upstream
code advanced. Original helper/base/goal and old immutable seals preserved.

The actual Source.Calldata.evalE_cdSlice_ok already proves slice progress.
This consumer does not redo it: slice_ok composes it with the previous owned
LiteralFailureCalldataDecode.arm, closing that arm's data-expression premise
for arbitrary typed calldata-byte/index locals and either end mode. It keeps
original isIndex and types.all decodable guards, exact n+3 horizon, MemOK,
RValOK and NotStuck outcomes. No successful execution/decoder premise or new
admission/profile/semantics is introduced. This is local abi.decode, not an
external callee-return phase. It does not imply all inputs succeed.

The applied generic_client uses the actual populated caller context. Concrete
actual execution controls cover nonzero-offset4 slices, uint8 success7 and
dirty300 rejection, reversed/outside logical reference bounds,31-byte short
slice, toEnd ignoring the evaluated end value, and n2timeout before bounds.
Slicing prefix4 from a bytes packet then decoding allocates fresh object1;
full returned state has only the actual heap change, retaining old object0
and all old caller locals/state via the prior fixture identity laws.
Three complete actual calldata vectors and six index/allocation observations
are losslessly rendered; all prior vectors/scalars/seals remain unchanged.
These are Source/kernel controls, not new external compiler/EVM observations.

Final per-file MCP passes; a control annotation initially selected Core.Idx
instead of Source.Idx and was qualified without semantic changes. Both
independent source reviewers found no soundness issue and requested clearer
'ABI decoder arm' wording instead of 'callee decoder arm'; fixed. Focused
checks, raw outputs/failed attempt, scoped axioms and exact artifact reviews
are sealed separately. Reviewers use no Lean, servers or builds.

This closes one concrete data-expression family. Storage bytes decoding,
arbitrary effectful data expressions and full G21 remain open. G40/G41/G42
and both Backfills stay partial; G42.03/P3 remain RO. No unknown-memory
encoder, physical calldata relation, runtime target bounds branch, native
agreement, frame/world/resource or full-lane closure follows. Original
P1/P2/P3/P6/P10 premises remain explicit and old9V12 staging stays preserved
but is not imported by these modules. Historical Suite124/full1/cold124,
rawdocs1/frozencomparison1, bodyexport1 and previous failures remain failed;
prior/publication doc equality is separate. No unchanged heavy retry or
proof/fuel/node/time/resource increase. Goal unchanged blocked, no admin.
