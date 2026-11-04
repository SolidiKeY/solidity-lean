# NV-Selection static audit

Frozen base: b6ba0696102a7a038afe2ed333c09dff397cc5b2. Boundary: static review only; no kernel verification. The audit inventories every scanner-selected declaration, field, and incidental syntax line in all six pinned files, and records six dimensions with same-file evidence. It does not assert the status of any later master revision. The structural acceptance checks inventory and data shape, not the correctness of the substantive assessments.

## Triage

Owner for all items below: solidity-parallel-20261103 Selection owners.

* Interface.lean:34-42, InterfaceV2Controls.lean:24-33: the V1 prefix bound assumes stackBound and the 1025-PUSH certificate demonstrates gasless overflow. Migrate capacity consumers to V2's required capacity evidence and keep the counterexample as a regression; do not treat V1 as physical-capacity evidence.
* Premises.lean:10-14,35-51: V1 compiler and consumer implications can be vacuous with a false relation or absent producer premises. Use the V2 inhabited contracts where applicable and supply real compiler and decoder producers; do not infer producer existence from these structures.
* PremisesV2.lean:18-24,30-50: witnesses exclude False but need not cover source evaluations or execute a nonempty program; consumption still assumes compiler and decoder obligations and exact successful zero-cost IR outcomes. Develop source-linked coverage and nontrivial producer/consumer controls without weakening existing contracts.
* FrameCapacityV2.lean:46-58, InterfaceV2Controls.lean:63-79: identity frame, Unit/equality compiler and zero-budget empty-IR runtime witness are trivial inhabitants, not source/runtime correspondence. Add source-linked, nonidentity, nonempty execution controls and a genuine RuntimeConsumer/Bridge producer when those proofs are in scope.
* Interface.lean:83-98,103-115: control realization assumes successful assembly and structured execution, may choose zero steps, and lowering/roundtrip are supplied obligations. Provide inhabited nonempty execution and actual source/compiler and bridge evidence; roundtrip alone is not behavioral agreement.

Existing controls include DUP with protected tail and 1023/1024 height boundaries, V1 1025-PUSH overflow versus V2 rejection, wrong IR result rejection, and false-relation rejection (InterfaceV2Controls.lean:24-111). Empty-tail V2 capacity and arbitrary admitted tails are enforced (FrameCapacityV2.lean:7-13, InterfaceV2.lean:18-26); this does not cover tails outside the room premise. Positive real-source and complete runtime/bridge controls remain missing. The audit does not prove that these external obligations hold.

## Verification and reviews

Frozen script SHA-256: 2ac32fcb689aa102396368283ed2abcf1ad3e833b53b1b2fcafb3b21a043af00.
Command: PYTHONDONTWRITEBYTECODE=1 python3 tests/terra-20261103/audit-selection/accept.py.
Result: PASS — {"item": "NV-Selection", "files": 6, "entries": 84, "status": "PASS", "boundary": "static review only; no kernel verification"}. Log: /workspace/nonvacuity-audits-evidence/selection-accept.log.

Read-only finder pass: inspected all six source files and scanner candidates, tracing V1 prefix assumptions, V2 empty-tail capacity, DUP and overflow controls, and source/runtime premise fields. Read-only skeptic pass: checked that no no-op witness was reported as source correspondence, that the overflow control refers to V1, and that V2 capacity remains limited to admitted tails. These are manual static passes, without Lean server; independent Sol review remains required. No Lean or KeySort gate was run.


Coordinator clarification: this is a historical static audit of the frozen
`b6ba0696102a7a038afe2ed333c09dff397cc5b2` source inventory, not validation of
current master or a completed runtime producer. The zero-step bridge equation
is a required producer identity law; arbitrary adapters do not prove it by reflexivity.
The coordinator corrected that explanation without changing the frozen acceptance
script, input hashes, inventory, assessment classifications or evidence lines.
To reproduce acceptance, use the original item source snapshot in a separate
checkout and overlay these three audit output files before running accept.py
without a commit argument; acceptance on a changed input inventory must refuse.
