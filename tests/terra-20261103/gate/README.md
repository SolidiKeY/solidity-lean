# TF-gate real-script fixture

Run `PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/terra-20261103/gate -p test_cases.py -v` with Node on PATH. All 15 historical names are preserved exactly. `test_targets.py` retains eight additional target/isolation controls. Git, Bash, Node and audit scripts are real; only Lake is a private recording/failing backend. No Lean, host elan, host cache, network or downloads run. HOME/ELAN/XDG/config are private; inherited Git and shell-startup overrides are removed. Every gate row is checked against exact stdout, five-field TSV and complete mocked/wrapped invocation vectors.

The original usage, per-file paths, relative logs, HEAD, changed/reverse/deleted/renamed/diverged/root/untracked/Scratch/failure controls remain. Per-file checkout and relative-log paths exercise spaces. Integration checkouts deliberately contain no spaces: protected production JS URL/path defects are retained separately, not mistaken for audit results. Direct changed-root selection is preserved without adding the generated root to every module's importer closure; non-root closure remains H21's bounded policy.

Checkpoint/full controls populate real trust inventory, roots/Lake libraries, a standard axiom pin, a one-function parameterized Solidity/AST/TestSuite catalogue and report, real generated parity/corpus files, and a genuine automatic proof-shaped audit input. Each real audit first passes its populated positive control. Layer, trust, orphan, root, documentation, pin inventory, TestSuite report and automatic-classification negatives then require their specific diagnostics; infrastructure exceptions are rejected. Corpus and default-build refusals are explicit mock-backend failures. No mocked build establishes kernel validity, corpus semantics or EVM execution. The TestSuite catalogue uses a parameter to avoid the separately recorded protected zero-argument generated-pin quotation mismatch; the pin audit still has a real positive and shrinking-inventory negative.

Copied tool scripts are untracked fixture harness inputs; tracked populated Lean/catalogue/documentation inputs are deliberate audit subjects. No checker source, default, allowlist or expectation is patched in the disposable repositories. Optional TF_GATE_EVIDENCE writes full per-case audit/gate/receipt JSONL outside the checkout for review.

## Reconciled frozen acceptance

Historical `accept.py`, the exact original three files, RED and reviews remain
immutable in `history/tf-gate-9cc85b14.tar.gz` (SHA256
`d3c047d0346652e4abc5ef3d7570091d707f1b6d7872e3b1fb60c30c67498aba`).
The old acceptor remains byte-identical and intentionally rejects source drift.
Coordinator authorization 2026-11-04 12:49 resolves TF-CONTRACT-02 by creating
`accept_repaired.py`, never by changing the old pin or dropping assertions.

`freeze_acceptance.py inventory` generates `old_to_new.json`: every historical
case, assertion, artifact, rejection guard and backend check maps to its retained
or stronger replacement. It also inventories positive/negative audit controls
and all additional controls. After committing repaired inputs, run
`freeze_acceptance.py freeze` and commit only the two generated freeze files.
The snapshot pins that exact repaired source commit, all artifact and copied-tool
hashes, complete case sets and allowed changes. Its own bytes and generated runner
are bound by the exact final acceptance commit; the external seal hashes every
file, including the snapshot, avoiding a circular self-hash claim.

Two independent read-only finder/skeptic reviews must compare the full old/new
inventory on the exact acceptance commit before execution. Run:
`python3 tests/terra-20261103/gate/accept_repaired.py --head <reviewed-full-SHA>`.
No check-only or skip mode exists. Wrong HEAD, changed source/dependency/artifact,
missing/extra files, modified metadata, unexpected commits and missing head args
are exercised against the actual executable in sparse local clones. All old 15,
supplemental 8 and contract-tamper 10 cases must run without skip/xfail. Sparse
clones share read-only Git objects, perform no network and never execute Lean.

H21's published checkpoint-library policy is retained. Historical empty-target,
backend refusal and failed-log checks remain explicit; stdout and invocation
membership checks are strengthened to exact vectors. The unsafe host-elan
absence prerequisite is replaced by private HOME/path identity and complete
backend invocation checks. No production budgets, checker semantics, named case,
profile or refusal was weakened. Historical failureCount stays 2.

The supplemental TOOL is bound directly to this repository's gate.sh. The frozen
runner rejects any mismatching inherited GATE_TOOL before importing a test
module. A negative substitution control supplies an unpinned executable and
requires rejection plus proof that its execution marker was never created.
Historical override-based RED logs remain immutable predecessor evidence; the
corrected fixture provides no executable-substitution interface.
