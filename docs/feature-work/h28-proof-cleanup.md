# H28 proof cleanup

Base: `6f3eedf0788ee1f8a3bcf230558c712ecdca04d5`; source tree `114f3a4e901fc282cec56d9e210fcffb2776e0cd`. The frozen corpus and case inventory is `tests/h28-terra/proof-cleanup/manifest.json`. Acceptance SHA256: `e8661890808e04da5bc7c0777aea29ed0bf39b99c5684e41d6df437975a12e1b`.

## Item 1: lexical census

`item1.py` consumes a JSON object from stdin and emits JSON. It reports `simp` and `simpa` tokens outside nested comments and strings, excluding tokens followed by `only`, as specified by the frozen oracle. Source paths and lines are retained. These are lexical candidates, including possible quotation or identifier-context false positives; owners must classify them. This is not a finished-proof verdict and performs no source edits.

Acceptance command: `python3 tests/h28-terra/proof-cleanup/accept.py 1 e8661890808e04da5bc7c0777aea29ed0bf39b99c5684e41d6df437975a12e1b`. Exit 0; output: `{"item": 1, "blackBoxCasesPassed": 31, "fullPinnedCorpus": true, "scopeChecked": true, "substantiveReview": "PENDING"}`. Measured wall 30.643 s, aggregate child peak RSS 661232 KiB via Python `resource`; Python 3.12.14. The acceptance output itself does not certify substantive review.

Independent read-only Sol finder: no confirmed mismatch in validation, masking, sorting, token regex, line numbering or output. Independent read-only Sol skeptic: no blocker; 30 frozen cases, six edge cases and 300 randomized comparisons against the model matched in-process. Neither used a Lean server. Both note lexical false positives require owner review. Coordinator rerun remains external and pending.

Items 2 and 3 remain pending at this checkpoint. No Lean proof or semantic equality/dead-code conclusion is asserted.

## Item 2: exact duplicate candidates

`item2.py` groups nonempty whitespace-normalized lexical declaration tails within and across input Lean files, preserving every path and name. The recognized declaration boundaries are those in the frozen oracle. Matching text is a candidate for owner review; it establishes neither alpha-equivalence nor semantic equality and does not authorize deletion.

`python3 tests/h28-terra/proof-cleanup/item2-controls.py` exited 0: cross-file, different-body, empty and duplicate-input controls passed. `python3 tests/h28-terra/proof-cleanup/accept.py 2 e8661890808e04da5bc7c0777aea29ed0bf39b99c5684e41d6df437975a12e1b` exited 0: 31 cases including full pinned corpus, wall 56.908 s and aggregate child peak RSS 732952 KiB. The frozen output marks substantive review pending, independently of the following reviews.

Independent read-only Sol finder found no mismatch; independent read-only Sol skeptic found no mismatch across the 30 fixtures, five targeted cases and 300 randomized comparisons. Neither used a Lean server. Trailing source can affect the frozen lexical grouping. Coordinator rerun remains external and pending. Item 3 remains pending at this checkpoint.

## Item 3: lexical occurrences

`item3.py` indexes every declaration recognized by the frozen lexical pattern and counts exact tokens across all input Lean files. Each row explicitly requires public and dynamic reference review. Counts do not resolve namespaces, aliases, quotations, generated references or external uses; no count proves deadness and no deletion is proposed.

`python3 tests/h28-terra/proof-cleanup/item3-controls.py` passed cross-file, masked-text and uncertainty controls. `python3 tests/h28-terra/proof-cleanup/accept.py 3 e8661890808e04da5bc7c0777aea29ed0bf39b99c5684e41d6df437975a12e1b` exited 0: 31 cases including full pinned corpus, wall 32.783 s and aggregate child peak RSS 793316 KiB. Frozen acceptance labels substantive review pending independently of these reviews.

Independent read-only Sol finder found no mismatch; independent read-only Sol skeptic found no mismatch in 30 fixtures, five targeted cases and 300 randomized comparisons. Neither used a Lean server. Coordinator rerun remains external and pending.

## Runtime gate

`lake -f .h28-runtime.toml build +Solidity.KeySort` passed inside `ubuntu:24.04` (image digest `sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852`), under the writer lock and with `LEAN_NUM_THREADS=1`. The temporary copy of `lakefile.toml` added `-j1` to `weakLeanArgs` and was removed after the check. The container reported `memory.max=12884901888` and `memory.swap.max=0`; available host memory before launch exceeded 12 GiB. Lean reported 4.24.0 (commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`), Lake 5.0.0-src+797c613, and `Build completed successfully (2 jobs).` Raw output is in `/workspace/h28-proof-cleanup-evidence/keysort.log`. KeySort wall and peak RSS were not captured. This runtime gate does not establish the coordinator reruns.
