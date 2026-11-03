# G21 conditional byte-data ABI decode consumers

New modules Solidity.Lowering.V08.LiteralFailureChoiceDecode and Controls.
Published master6510c302 was fetched/inspected before work; no relevant new
implementation was present. Original frozenbase2fe1f893, helper branch/goal,
all previous commits, manifests and expected observations preserved.
Coordinator registers the modules; Source and Solidity.lean unchanged.

choice_ok proves actual conditional-local evaluation for arbitrary intrinsic
result type and three typed caller indices. It consumes the published local
progress theorem, extracts the real boolean and proves the selected branch.
calldata_ok/memory_ok/storage_ok compose that result with the actual ABI
decoder arms. No successful data/decoder execution premise remains. Original
MemOK/RValOK, decodable and n+3 fuel conditions remain, with no new admission
predicate or allocation/disjointness restriction. Equal indices/aliases allowed.
This is constructor composition over the existing evaluator, not another one.

Actual populated controls show a valid calldata reference with missing physical
bytes can remain unselected: true selects completeword7 and succeeds, false or
swapped branches select missing data and revert. Shared references succeed for
both boolean choices. At n2, timeout precedes malformed decoding. Memory uses
two genuinely typed objects: freshobject1 contains the32byte word, oldobject0
contains valid bytes too short to decode; selected branch alone determines
success/revert. Storage has two equal valid references to the real stored2byte
object and reverts at the decoder head. Full returned locals/state equalities
are actual kernel controls; no wrong RefOK/dangling-memory witness is used to
suggest the Hoare theorem admitted malformed references. Inputs are72complete
bytes across calldata/memory/storage; raw output and exact comparison sealed.

Final per-file MCP passes both modules; initial ambiguous frame name was
qualified. Focused checks and13actual scoped axiom records accompany seal.
Finder/skeptic source and exact artifact reviews are independent/read-only,
without Lean/server/builds. No proof/fuel/node/time/resource limit increased.
No hosttest is promoted to a theorem; source pipeline parameters are not native
compiler pipeline observations. Existing successful storage kernel control
remains resolved and unchanged. Historical failed attempts/gates remain failed.

FullG21/G40/G41/G42 and BackfillsA/B remain partial. Effectful conditions/data,
all-profile source/native/runtime compilation, unknown-memory target encoder,
CALL/RETURNDATA source-origin, arbitrary callee/frame/world/resource and final
mandatory gates remain open. P3/G42.03 stay readonly-external; G42.05 pending
producer. Published interfaces retain their real premises; private9V12 input
preserved and not in these imports. Suite124/full1/cold124/rawdocs1/frozen
comparison1 and bodyexport1 are not rerun or relabeled. Prior/publication docs
multiset equality is separate. Goal unchanged blocked; no administration.
