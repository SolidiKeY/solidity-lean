# Independent merge checkpoint reviews

Separate agents `finder` and `skeptic`, read-only; neither used Lean, its server,
or heavy checks. These verdicts apply only to inventory/merge, not full SOL-C3.

Initial reviews found producer-based uniqueness, unproved exact-fuel wording,
and name/position conflation. Fixes: direct inductive uniqueness, merge_fuel plus
merge_iff, generic identity traces with an explicitly open graph/name bridge.
Finder also warned against circular graph adequacy from WellFormed.linearizes.

Expanded source review: both found no mathematical defect or premise drift.
Finder requested concrete blocking tails; first_none_iff/obstruction_iff added.

Packet findings and verified fixes:

| Finding | Resolution |
|---|---|
| Historical successful log accepted after changing sources | Hash-bound bounded audit receipt includes exact sources/configuration/tooling/manifest, command/toolchain/resources and log hash; stale-receipt mutation is rejected. |
| Removing producer pin skips checking it | Exact six-file required pin inventory; missing-pin mutation rejected. |
| Nested modules invisible | Recursive discovery and nested-module mutation. |
| Modified/unsupported declaration forms or new constructors invisible | Restricted syntax fails closed; actual inductive constructors derived; hidden-declaration and extra-constructor mutations rejected. |
| Full mode can pass from status strings despite open work | Full mode unconditionally refuses until full schema is implemented. |
| Stuck.step has no inhabited control | Generic delayed_obstruction and closed delayed_refused, with exact axiom guards. |
| Prefix-matched exact filenames/untracked files escape scope | Exact-file membership plus directory prefixes and tracked/untracked inventory. |
| Interrupted monitor can release lock while work continues | Signal/exception cleanup retains lock until owned container confirmed stopped; actual cancellation test saves failed receipt, stop/reacquire/restart result. |

Final skeptic verdict: "Merge checkpoint source and packet: pass on read-only
review." Prior blockers resolved; no remaining merge checkpoint blocker found.
Verdict excludes graph lift, compiler fixtures, final gates and full completion.

Final finder verdict: "merge checkpoint acceptable", subject to recording these
reviews and committing/sealing the packet. No remaining concrete defect found.
Finder asked that runtime Docker approval cite the later explicit H26 recovery
message, not the original H26 lane approval; documentation now distinguishes them.

Final documentation-only updates record these verdicts and do not change proofs.
