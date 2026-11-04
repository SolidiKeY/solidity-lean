# H28 timing tools

Base: `6f3eedf0788ee1f8a3bcf230558c712ecdca04d5` (tree `114f3a4e901fc282cec56d9e210fcffb2776e0cd`).

## Item 1: retained receipt rows

`item1.py` implements the frozen mechanical parser. It reads JSON files, sorts paths, and emits a row for every `splitlines()` line. Only the specified `Built` pattern in milliseconds or seconds is interpreted; unmatched lines, including wall and RSS metadata, are retained as `unparsed`. This covers the frozen selected receipt subset, not a historical receipt audit. The contract uses a permissive search and Python line splitting; it does not preserve separators or original text for parsed rows.

The immutable acceptance input was copied byte-for-byte from `/workspace/h28-inputs/timing-tools/accept.py`; SHA-256 is `b4370444e260bd27cfb733584ffceaaa23040e55d2748a71aec98dc2dbc221c5`. `python3 tests/h28-terra/timing-tools/accept.py 1 b4370444e260bd27cfb733584ffceaaa23040e55d2748a71aec98dc2dbc221c5` exited 0: 31 black-box cases passed, full pinned selected corpus and scope checked; substantive review is separate. The frozen fixture manifest comprises all-source-rows, empty-source, comments-only, nested-strings, diagnostic-0 through diagnostic-4, timing-0 through timing-5, duplicate-paths, cross-file-duplicates, wrong-source-pin, missing-provenance, unknown-mode, invalid-budget-bool/nan/inf, boolean-seconds, malformed-times, invalid-seconds-null/string/nan/inf, missing-seconds, and complete-pinned-corpus.

Independent read-only Sol finder reported no mismatch after examining validation, ordering, line numbering, extraction, units and unmatched rows, and reported 30 fixtures, 1,000 generated cases and seven invalid-file variants. Independent read-only Sol skeptic reported no mismatch over 500 adversarial/randomized differential inputs. Neither used a Lean server. The skeptic noted inherited contract limits: permissive substring matching, truncation at punctuation, greedy last matching duration, infinity for huge numbers, unparsed scientific notation, Python splitlines semantics and rejection by exception for non-object top-level JSON. These are not claims of additional supported formats.

Items 2 and 3, backfill, coordinator rerun and final handoff remain pending. No Lean proofs are asserted by this script work.
