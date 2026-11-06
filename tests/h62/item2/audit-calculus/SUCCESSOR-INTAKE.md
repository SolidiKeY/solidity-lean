# Successor intake and frozen lexical recovery

H82b delivered authenticated assignment/scope and final-stop metadata. The archive SHA256 is fab677d3e4ccbf57410c175c9665ac0fd689ddf574869e24d431e28de16f9ed4; all 557 indexed file checksums passed. Member head 4abcd439b60c63a6f02e91115599e6a730cd9bc9 was fetched exactly and merged into the existing H28 successor branch at 1ea58f4796a441c907dd0eca7387f1bdfe91be32. No master push occurred. The coordinator disposition resolves the prior prompt-metadata wait; the original transcription/rendered-hash distinction remains documented.

The additive recover_frozen_census.py driver reads the immutable audit base from Git and checks every mapped source against the authenticated member scope. It reproduces source-census.json byte-for-byte: SHA256 a2aa6d5e5837eac11ad80fc4eb59e4c3903e9d7f9d52e41bcbccb1e24dccc2da, 361 files, 5283 lexical declarations, 110 private declarations and three generator commands. It records zero verified joint witnesses; all 5283 lexical candidates remain uncovered in this recovery result. Existing census, acceptance, proof files and budgets are unchanged.

The sole live drift among frozen snapshot entries is docs/module-map/calculus.md. All 361 mapped Lean source hashes match. This is not a census of newly mapped live modules and does not transfer scope. Recovered source data and live-drift hashes are external in /workspace/h62-successor-evidence/frozen-census-v1 with SHA256SUMS. Reproduce using:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item2/audit-calculus/recover_frozen_census.py --out /workspace/h62-successor-evidence/frozen-census-NEW
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/h62/item2/audit-calculus -p 'test_*.py'
```

Use a fresh external output directory. The driver refuses overwrite, output inside the repository, unsafe paths, source/hash/roster/count mismatches and any recovered proof-coverage claim. All 55 Python controls pass. The initial read-only-sandbox run failed because temporary directories were unavailable; rerunning with authorized temporary-file access passed. This was an environment failure, not an accepted proof or benchmark result.

Independent read-only finder and skeptic both passed lexical recovery. They checked the exact census digest and external checksums, frozen/live separation, canonical paths, complete roster, unchanged acceptance guards and refusal controls. Neither used Lean/server or writes. No confirmed findings remained.

External receipts: /workspace/h62-successor-evidence/intake-recovery-v1. No Lean files changed or Lean checks ran in this checkpoint. No performance optimization or comparable before/after timing is claimed. Prior member witness counts are historical reported results until external kernel exports, compile receipts and proof evidence are retrieved and verified. The missing worker archive is evidence.tar.gz SHA256 ab34148530704ebe135e4385744fa1ad0b1052865141d955f52416f85863ff08.

All four original audit checkpoints remain unfinished: semantic owner/premise classification; joint witnesses; source compiler success and negative gas/fork/world controls; fidelity and final gates. The reported 5148 source candidates without joint checks and 13350 unclassified additional kernel cases remain outstanding. Exact-file permission waits are superseded by H82, while semantic producer information remains needed. Full PassCorrect bridges, intentional-contradiction distinctions, frozen signatures, budgets and trust rules remain binding. The H28 ContextControls pause and SyntaxRaw/ambient-axiom dependencies remain separate unresolved waits.
