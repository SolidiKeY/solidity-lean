# User-requested diamond-try checkpoint publication

The user requested “commit and push to master what you have done”. This authorizes
publication of the retained partial checkpoint; it does not establish original
assignment completion or whole source/compiled-EVM correctness.

The merge preserves task parent `73aac3c53a69c43dd09ab3a1f4504977fc034b66`
and published master `91e94ab57305ca055127934fd9e68fe9ea5e6be3`, with the
original `f4dee4a29c2e208b36db4a4161a4723c735cd775` base retained in history.
Both parents’ root imports, frontend behavior, feature evidence/decisions and
trust entries survive the conflict resolutions. The source runner retains
master’s all-source-unit host/assembly checks and payment path together with
the narrow task-local self/creation/library adapters; foreign-unit host contexts
remain refused. Retry provenance now compares every emitted runtime adapter and
payment reference hash, with changed/missing-hash negative controls.

Fresh validation: 125 affected Node tests passed; orphan, layer, strict automatic,
trust and generated-inventory checks passed. KeySort passed. The 107-job focused
closure passed, including external-try soundness, M1 carrier and both pipeline tags
of creation/library source continuations (324 s, cgroup peak 4,016,254,976 bytes).
Contract, Body and generated Features have clean per-file MCP diagnostics.
Raw MCP logs retain client subprocess-cleanup “Event loop is closed” tracebacks
after the clean structured results and exit0; these are tool-cleanup warnings,
not Lean diagnostics. Twenty-five fresh carrier/formula/counterexample axiom audits use only the
standard permitted axioms. These are kernel/component checks, not new EVM runs.

The original full script stopped at its unchanged 1800-second bound: exit 124,
1801 s, cgroup peak 12,242,771,968 bytes. It did not reach TestSuite/sort completion.
A distinct supplemental all-task closure stopped at its 600-second diagnostic
bound: exit 124, 601 s, peak 4,410,531,840 bytes. Neither is a pass. No reported
Lean errors preceded either stop. Every check group used a verified hard 12 GiB,
zero-swap cgroup, serial Lean `-j1`, threads1, the writer lease and disk caches;
OOM/max events were zero. Full library/TestSuite/Corpus/Bridge confirmation is
not claimed. The documentation check is actual exit1: the same 48 missing
references as the published-master blob comparison, with zero new findings.

Independent finder and skeptic reviews were read-only, without Lean servers.
Their actual scope was the conflict areas and script provenance/wiring, not the
entire incoming master. The skeptic’s provenance finding was fixed and its exact
repair independently confirmed. No frozen observation/verdict, target/exclusion,
callback/default meaning, proof/resource budget or vendor interface was changed
by the integration repair. No historical engine or fixture ran.

The retained native family is still 12 working / 8 blocked, strict exit1;
its original receipts were not rerun or promoted. Six physical/nonprimitive rows,
two historical rows, P4 target-byte/resource correspondence, P5b original source
construction and P8 admission remain open. The [EVM component account](diamond-try-evm-memory.md)
continues to distinguish constructed states and symbolic opcode components from
whole original execution. This publication is a partial checkpoint.

Exact commands, stdout, resource footers, reviews, old preserved exports and
validation JSON: `/workspace/next10-diamond-try-evidence/publish-master`.
Actual push receipt and verified remote SHA are recorded there after publication.
