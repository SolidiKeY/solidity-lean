# H82 original-scope preservation packet

Handoff target: `solidity-h62-6-20261106/migrate-root-gate`.
This packet is metadata preservation only, not proof implementation or completed
migration. Current final head is recorded in the external H82 retirement receipt
after committing; this avoids claiming a commit contains its own hash.

Payload:

- original-assignment.txt: complete visible original worker user turn, including
  setup, all constraints, four checkpoints, full backfill, 123-entry owner map,
  result template and persistent-goal instructions. Transcribed from this thread.
- original-goal-objective.txt: complete launcher-supplied objective.
- original-environment-context.xml: initial user-supplied VM context.
- original-work-and-backfill-queue.md: complete queue extract from the assignment; only trailing separator blank
  lines are normalized. The complete original assignment remains verbatim.
- original-scope-manifest.json: exact original two prefixes and ten explicit files
  (nine production modules and one documentation path), plus original restrictions.
- source-provenance.json: source and original rendered digest provenance; hashes
  for the original assignment/objective/queue/scope transcriptions. Raw renderer
  bytes are unavailable; their digest is not claimed equal to a transcript hash.
- toolchain-pin.json: copied actual coordinator-provided official release pin.
- h62-inputs-relay.txt, h70-disposition.txt, h82-retirement-instruction.txt,
  h82-standing-rules-relay.txt, h82-retirement-resolution.txt: relevant later user relay bodies/instructions.
- open-queue-and-waits.schema-v1.json: every open checkpoint/backfill state and
  schema-v1 lane/item waits. Proof-only permission requests are withdrawn under
  H82; actual repair/validation waits remain; retirement/resume is resolved KEEP RETIREMENT.
- pause-capability.json: precise exposed-tool inability to apply PAUSED.
- SHA256SUMS: hashes of every other packet file, relative to this directory.

Both independent read-only reviewers checked the full original assignment,
queues and exact scope against the inherited original user turn, including the
owner map, without Lean/server, edits or external-owner messages. They found no
omission/transcription error. Their one current-policy clarity finding was fixed
by the H82 supersession note in the main lane document.

No H71 push authorization is available here; no push is performed. Original VM,
branch, code and H44 evidence are preserved. Root-gate must retrieve this packet
from the cumulative bundle/patch before starting transferred work; coordinator
local paths alone are not a transfer mechanism. Goal PAUSED cannot be applied
with the exposed tool schema; this is reported, not replaced by completion.
Q-H82-RESUME is resolved by h82-retirement-resolution.txt: KEEP RETIREMENT. Generic continue broadcasts do not revoke this stop. Coordinator will pause the existing goal after final head report and idle turn.
