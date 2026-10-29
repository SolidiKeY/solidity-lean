# Contract-world wrapper certificate handoff

Implementation: `1e37a2256e277ef24b04284ad0de9f822feaca8c`, branch
`feature/world-reachable-catch`, based on
`f4dee4a29c2e208b36db4a4161a4723c735cd775`.

This increment adds a real bare creation-catch operation and exact execution
certificates for the existing factory/library source wrappers. It derives
funded reachability from an actual successful operation and explicit admission.
It does not add dynamic source arguments, general library results, or a
world-aware ordinary importer. The feature statuses remain partial.

[validation.json](validation.json) records versions, hashes, commands,
per-fixture before/after outcomes, axioms, resource measurements, shared edits,
reviews and exact remaining refusals. The existing real Solidity fixture and
all its expected observations are unchanged. Both legacy and viaIR analysis
fixtures pass the complete typed-source/kernel controls. These are semantic
proofs, not a compiler/EVM equivalence theorem.

The full combined gate passed: 686 default jobs, 259 TestSuite jobs, and the
frozen 377-taclet / 131-annotation sort comparison. It took 145m34.609s under a
single CPU, explicit Lean `-j1`, and a hard 12 GiB/no-swap cgroup. The recorded
peak equalled that cap. Earlier focused artifacts were retained; this is not
a clean-checkout cold benchmark. The complete raw log is preserved in
[run-lean.log.gz](run-lean.log.gz); the original interrupted output stream is
retained separately. Docker wait recorded terminal exit 0.

The three selected upstream cases are all **blocked**, in both required
legacy/viaIR pipelines, by the unchanged cross-contract host-adapter boundary.
[Original fixture text and expectations](upstream/fixture-observations.json)
are retained in full, including gas rows. No runtime or EVM agreement is claimed.
Per-filter runner reports remain in the adjacent directories; their large
all-snapshot coverage inventories are retained byte-for-byte as gzip files,
with compressed and uncompressed hashes recorded in validation.json.

The command scripts are exact records for this saved managed environment:
source the setup activation, copy `bounded-lakefile.toml` to the repository
root as `.world-bounded.toml`, and use the bounded Docker wrapper. For example:

```sh
source /workspace/.setup/activate.sh
cp tests/contract-world-certificates/bounded-lakefile.toml .world-bounded.toml
bash tests/contract-world-certificates/bounded-check-command.sh 'time ./run-lean.sh'
```
 Pipeline
replay copies the entire existing control file and regenerates hash-checked
fixtures. For a fresh upstream replay, change `--out` to a new directory so the
retained reports remain intact. The initial malformed replay invocation ran no
fixtures; its log is retained and was not counted as evidence.

Trust, orphan, layer, strict automation, inventory consistency and the affected
Node test pass. The prose-path audit retains 20 existing missing references in
untouched historical reports and an existing Mathlib citation. Independent
finder/skeptic reviews found no confirmed semantic defect; their requested
registration, concrete-operation coverage and scope clarifications were fixed.
No master push/merge or external message was performed.

The final independent reviews verified terminal log/exit and fixture, archive,
pipeline, source, control, model, compressed coverage and patch hashes without
Lean or builds. No confirmed inconsistency remained.
