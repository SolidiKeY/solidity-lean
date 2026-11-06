# H55 module-times backfill

Base: `4d3790eadb8a5212233bc7d5e345817476b2f590`. This is an
incomplete standalone backfill, not a production timing gate or a proof pass.
The H55 correction reserves existing producer and consumer files to their
current owners until the coordinator transfers exact leases. No such files
were edited here.

The existing `scripts/check-automatic.mjs` parses only Built TestSuite rows;
it does not require every intended module to occur, and its own documentation
says cache replays are not timed. Its cumulative memory-loop gate is a separate
requirement and must not be replaced by a per-module check.

At the base, `git ls-files '*.lean'` reports 7,166 tracked Lean paths:
6,261 under `Solidity/`, 629 under `Bridge/`, 251 under `tests/`, eight under
`vendor/`, and the remainder elsewhere. These are a broad census, not an
approved scope or a list of buildable Lake modules. Bridge source directories,
test controls, root modules, generated modules and optional libraries need
explicit discovery and classification; a filesystem count or only generated
roots cannot establish full coverage. In particular path-to-module mapping and
standalone controls must be checked against actual build configuration.

`scripts/h55/module-times/receipts.py` is a standalone JSON consumer for a
nonempty explicit inventory of source paths and one fresh successful receipt
per path, with a fixed 300-second maximum. It rejects missing, duplicate,
extra, malformed, failed, timeout, cached and over-budget records. The unit
controls use synthetic data only. It neither determines the assignment scope
nor executes Lean, enforces a timeout, authenticates the producer, the clock,
the tree, toolchain or cache, or ensures serial execution and resource bounds.
A forged successful row can pass. It must not be wired as a production gate
until those missing controls and a complete independently checked inventory
are supplied. Cumulative workload rules remain separate.

Validation: `PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s
tests/h55/module-times -p 'test_*.py' -v` passed two test methods with
boundary and negative cases. This is a software test, not a Lean proof or H56
measurement. Installed binaries report Lean 4.24.0 commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b` and Lake `5.0.0-src+797c613`;
no KeySort runtime gate was run.

Outstanding: authenticated complete inventory, actual H56 gate-VM execution,
real timeout/fake-time and failure controls, full-scope acceptance, independent
read-only finder and skeptic reviews without Lean server, owner migration
patches and exact leases, qualifying splits, identical-state before/after
wall and RSS with stop above 10% slowdown, affected-module and final gates,
cache pack, checksums and final handoff. No claim of completion is made.
