# Step 8 transient world increment

Closed source factory targets can contain certified transient cells. `World.transact`
composes imported typed frames with one owner-specific reset/commit/rollback boundary.
General source-world statements and transient factory owners remain refused. Feature
status stays **partial**. No Step/Reachable, recursive representation or excluded
policy was changed.

- Starting master: `f4dee4a29c2e208b36db4a4161a4723c735cd775`.
- Combined gate: **exit 0**, 686 library jobs, 259 TestSuite jobs, 377 taclets and
  131 read-bearing annotations matched; 10,448.088 seconds, 12 GiB cgroup peak.
  The cap recorded 1,303 reclaim/limit events, **zero OOM/kills**; no stop was passed.
- Affected Node tests: **26 passed**, exit 0.
- Fresh per-file kernel checks and all **27 new named theorem axiom audits** passed.
  Five general laws use only `propext`; concrete controls use the standard three.
- External compiler/EVM: **22 signed transactions**, eleven per pipeline; exact
  returns/reverts/panic bytes retained. This is observational compiler/EVM evidence,
  separate from kernel proofs. Static creation is model evidence only.
- Upstream constructor and tuple fixtures: **working in legacy and viaIR**, all
  retained vectors matched. Multi-frame getter: **blocked**, host adapter unavailable;
  no pipeline execution or passing observation is claimed for that fixture.
- Inventory, orphan, layer, automatic and trust checks passed. Documentation-path
  check fails on **20 preexisting citations**, verified against starting master.

See [report.json](report.json) for exact command arrays, exits, timings, memory
counters, source hashes, shared edits, review results and remaining refusals;
[axioms.json](axioms.json) and [evm-observations.json](evm-observations.json) retain
the proof/reference split. Upstream JSON reports retain every actual observation;
`fixtures/` contains byte-identical pinned inputs including original expectations.
[log-index.json](log-index.json) records compressed and uncompressed SHA-256 hashes.
Logs are losslessly gzip-compressed; use `gzip -dc` to inspect.

The pre-implementation legacy refusal was checked before the edit. Both pipeline
refusals were additionally replayed from the exact starting-master importer source;
this later frozen replay is explicitly labelled, not presented as earlier execution.
The failed address-space attempt and interrupted observer driver remain separate
blocked evidence. The surviving original Docker build was collected to completion;
the historical 453-job image build is not a gate of this task.

For bounded reproduction, copy `lakefile.single-thread.toml` to the checkout root
as `lakefile.transient.toml`, source `/workspace/.setup/activate.sh`, override
`LEAN_NUM_THREADS=1`, and use the recorded commands inside a 12 GiB/no-swap scope.
The two driver scripts document the exact sequential command phases. Runtime mounts
were the attached `/workspace`, plus read-only `/usr` and `/opt`; no second clone
or VM was used. Optional reference packages were installed outside the core.

Final packaged static checks also completed under the 12 GiB/no-swap cap.
Staged whitespace, inventory, orphan, layer, automatic and trust gates passed;
the documentation gate retained exactly the same 20 preexisting missing citations.
Their command/exit/timing/memory rows are in `validation.staticFinal` and raw logs
are included in the log index. Finder and skeptic independently verified the
packaged evidence and found no confirmed defect.
