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


## H70 source-owner and premise-bundle follow-up

Finder checked all 18 unmatched exact files and 51 declaration attributions,
including the declaration-free Frontend/Yul/Parsing.lean. Frozen integration
history and documents support VY1 (24 declarations) and V17 (27); registry producer
mapping and migration overlay ownership remain separate. No new H30 reservation
or write permission is claimed. Commands were read-only `git log --diff-filter=A`,
`git show`, `git merge-base --is-ancestor`, source/document `sed`/`rg`, and
`python3 -B` in-memory census regeneration/comparison.

Finder decisive output after actual changes:

```text
regenerated_enriched_census_matches_saved PASS
unchanged_identity_signature_and_original_owner_evidence 656
exact_missing_H30_files 18 attributed_declarations 51
new_H30_reservations_claimed 0
source_notes 10 definitions 7
forall_header_result_distinctions_retained PASS
```

Skeptic identified two concrete issues: Source.Data.Inner (E:=E) data was tagged
as a source equality premise due to :=; a synthetic wrong live_producer passed
reconciliation because no producer mapping ID was checked. Fixes ignore named
assignments/comments when detecting equalities and validate producer_mapping_id
against registry.owner. Tests include both original counterexamples, inferred
binder and result-quantifier distinctions, false witness and stale-signature
rejection, and exact H30-versus-source attribution counts.

Skeptic final read-only `python3 -B` in-memory checks passed: all 18 producer IDs
match their registry owners, a wrong producer raises live producer mapping
mismatch, named arguments/comments create no equality hints, actual equalities
still do, and all 656 statements retain pending witness/elaboration/fidelity.
Every attribution explicitly grants no edit permission. No remaining confirmed
finding in the fixes. Both reviews used no Lean, server, writes or fixes.

Review boundaries remain unchanged: ten manual source inspections plus source
routing for all rows do not establish any elaborated type, structure inhabitance,
per-input feasibility or simultaneous witness. No proof checkpoint is complete.


## H70 next routed receipt: overlay, quantifiers and modules

Finder independently reproduced the exact Hash patch checksum, Git pre/post
blob IDs and all 64 ordered raw source signatures, with original bytes unchanged.
No reported owner head was authenticated and no Lean/migration result claimed.

Skeptic reproduced two malformed-patch acceptances in memory: out-of-range
zero-count insertion and contradictory deleted-file metadata. Both are fixed by
strict exact metadata and positive in-range hunk checks, with negative regression
cases. Actual routed bytes still pass the inspection. No overlay was applied.

Final independent read-only Python `-B` checks from both reviewers confirmed:

```text
frozen_identity_and_signature_invariance 656
module_summaries 147 statement_identities 656 unique 656
zero_direct_named_theorem_modules 6
leading_result_groups 88 statements 86 source_binder_groups 513
bounded_prefix_retained_opaque 1 remaining_nested_quantifier_rows 1
quantifier_source_slice_and_offset_checks PASS
malformed_overlay_cases_rejected PASS
actual_hash_overlay_ordered_signatures_unchanged 64
```

The six zero-direct-theorem modules include definition-bearing files; no
imported-interface or inhabitance claim follows from that count. Headers,
leading result quantifiers, implication chains, local lets and nested results
remain separate. All source sort/inhabitance/witness/fidelity claims remain
pending. The finder identified a stale intermediate generated census after a
summary wording change; final generation/replay replaces that intermediate file.
No remaining code finding. Both reviewers used no writes, Lean commands or server.

The routed patch is an off-Git evidence asset because its exact context spaces
are checksum-significant. The committed receipt pins those bytes; the inspector
accepts an explicit relocated artifact path but always checks the routed SHA256.

Final artifact-path rechecks confirmed default receipt lookup and explicit
relocation produce identical inspections, bad checksums/non-basename receipts
are rejected, and current regenerated source census matches the saved artifact.
The full current suite has 26 passing tests; no remaining review finding.
