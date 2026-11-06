# G21 assignment effects before conditional ABI decoding

New modules LiteralFailureEffectDecode and Controls under Solidity.Lowering.V08.
Master6510c302 fetched/inspected first; relevant definitions unchanged. Source
semantics and Solidity.lean stay read-only; coordinator registers modules.
Original base2fe1f893, helper branch, all seals and goal identity preserved.

assign_run proves actual evalE local bool assignment at n+3 returns the bit,
sets the actual caller slot and leaves the entire Source.St unchanged.
assign_ok derives MemOK/RValOK via the existing LocalsOK.set theorem. choice
is relative to an actual condition-expression triple and follows its REACHED
locals/state. assigned_choice discharges that premise with assign_ok.
calldata_ok/memory_ok/storage_ok compose the actual assigned condition and
typed local branches with the unchanged decoder arms at sufficient n+5 fuel.
No successful evaluation/decoder premise, new accepted-profile predicate,
alias separation, alternate evaluator or budget increase is introduced.
This sufficient fuel is not claimed minimal or a CPU/gas bound.

Actual populated controls prove oldconditiontrue→assignfalse→selected missing
bytes→empty revert, with caller condition FALSE in the reached expression
locals. True assignment before success returns7 with conditiontrue. Equal
references need no separation. At fuel3, timeout precedes assignment and keeps
oldconditiontrue. A stale-condition success claim is explicitly rejected.
Both staticflag values allow LOCAL assignment; this says nothing about static
storage-write permission. Memory and storage short-head decoder failures also
retain the updated boolean slot; existing heap/world data stay as recorded in
the full state equalities.

These are evalE/ExceptT expression outcomes, NOT execS local-frame restoration,
transaction rollback, external-call/static-world/P3 provenance or arbitrary
callee facts. O1/readonly-external ownership is untouched. Effectful arbitrary
conditions remain relative; this headline closed family is local boolean
literal assignment, with original decodable/reference/MemOK guards retained.

Final per-file diagnostics pass main/controls. Focused toolkit checks and15
actual standard-only axiom records accompany seal. New host observations
render the real outcome/condition table completely; expected source input
bytes are identical to the prior72-byte checked packet and retained unchanged.
Host rendering is testing only, not a new semantic function or kernel proof.
Independent finder/skeptic source and exact artifact reviews are read-only,
without Lean/server/builds. Existing finite storage-success kernel proof
stays resolved and unchanged; prior observations/seals not rewritten.

FullG21/G40/G41/G42 and BackfillsA/B remain partial. Unknown-memory/runtime
ABI emission/decoding, source/native/compiler/EVM/frame/world/resource
relations and mandatory final gates remain open. G42.03/P3 stay RO;
G42.05 waitsproducer. Published interfaces retain real premises, old9V12
staging preserved and not imported by this closure. Historical Suite124,
full1/cold124/rawdocs1/frozencomparison1/bodyexport1 remain failed, not retried.
Prior/publication doc equality is separate. Goal unchanged blocked; no admin.
