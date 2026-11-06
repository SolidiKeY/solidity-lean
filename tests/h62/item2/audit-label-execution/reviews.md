# Read-only tooling reviews

These independent reviews certify the saved tooling only, not audit checkpoints.
Neither reviewer wrote files, ran Lean, opened a Lean server, or fixed code.

## Finder (`census_finder`)

Found eight signatures cut off at result-type `let` assignments and the absence
of pinned-blob comparisons. Both findings were fixed. Six scanner regressions
pass, including real-corpus and negative local-mutation cases.

Final command: Python `-B`, importlib-load `census.py`; call `modules(root)`;
for each path call `declarations(frozen_bytes(root,path).decode(),path)`;
independently scan masked text with `re.finditer(r"\b(theorem|lemma)\s+[^\s({\[:]+",clean)`
and compare `(path,line)` identities. Independently compare all eight affected
signatures against source up to the actual `:= by` or direct-term delimiter.
Exit 0; decisive output:

```text
pinned_blobs_verified_including_map 148
source_declarations 656
independent_token_omissions []
full_result_let_signatures_verified 8
preceding_variable_commands_field True
```

Final `blocked_report.py` Python AST and retention checks passed: 656 candidates
retained, proof counts zero, semantic status pending. The reviewer observed an
in-progress final probe; the worker regenerated `uncovered.json` only after the
final probe terminated with all 147 requested results present.

## Skeptic (`census_skeptic`)

Confirmed pinned-source protection; flagged inherited variables/private kernel
names as requiring elaboration, owner ambiguity accounting, official sysroot
imports misclassified as missing, pre-spawn headroom checks, bounded child
cleanup, and provenance wording. Fixes retain preceding variable source text,
count missing/ambiguous owners, resolve official sysroot `.olean` files, check
reserve/swap before spawning, bound TERM/KILL cleanup, and separate version
checking from the separately verified archive checksum.

Commands: `nl -ba scripts/h62/item2/audit-label-execution/serial_probe.py | sed -n '20,150p'`;
Python `-B` AST parsing, inspection of saved `results.json`, `/proc/swaps` and
`/sys/fs/cgroup/memory.max`. Both `Lean.Elab.Tactic` and `Lean.Elab.Deriving`
pass as official-sysroot artifacts. Observed swap entries zero; cap
17,179,869,184 bytes.

Reviewed `blocked_report.py` via `cat`, Python AST and in-memory mocked
Path reads/writes against the actual census: blocked probe exits 1 and retains
all 656 rows/owners; mismatched requested map refuses output; synthetic passing
imports exit 0 with proof counts still zero and semantics pending. No remaining
confirmed tooling finding. An import-report exit 0 is never a proof gate.

## Final evidence boundaries

`independent-probe/` and `full-map-probe/` are historical diagnostics with
superseded source-root lookup. Only `final-map-probe/` covers the final tracked
Bridge vendor roots and official sysroot lookup. Review approval does not imply
premise feasibility, exact elaborated signatures, totality/success, public
negative-compiler controls, or final build validation.
