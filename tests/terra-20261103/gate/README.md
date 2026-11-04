# TF-gate isolated target controls

Run `PYTHONDONTWRITEBYTECODE=1 python3 tests/terra-20261103/gate/test_targets.py`.
The production gate and Git are real; Lake is a private recording executable.
PATH contains only explicit utility links and private Lake/elan mocks. An elan
poison marker must remain absent. No Lean process, toolchain download, host elan,
host cache or network is used. Each populated repository has independent commits,
source modules, importers, Scratch and example/corpus leaves, including paths with
spaces. Assertions compare the complete ordered Lake argument vector and saved
receipt, thread count, status and targets line; no target subset is accepted.

Cases: tracked and untracked Scratch-only; mixed production/Scratch with transitive
importing consumers; deletion retaining real importers; untracked production;
tracked ignored production; core-to-example policy; propagated backend failure.
Original gate must fail Scratch controls; corrected gate must pass all eight.
Set GATE_TOOL to an archived original gate for the RED control.

The coordinator's exact frozen fixture commit 9cc85b14fa3f611e183379c257b10b19e1aa5325
is absent locally and origin rejects that SHA as not its ref. This new test file
is additional focused evidence, NOT a replacement for its frozen accept.py.
No frozen assertions or historical RED logs were modified. Original committed-item
acceptance and repair of that exact fixture remain pending receipt of the packet.
No generated roots or module-map edits are needed for these script-only changes.
