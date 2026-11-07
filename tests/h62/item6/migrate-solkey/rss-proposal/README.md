# Unapplied new-release RSS import proposal

This is a static proof/import-only proposal for the isolated API fixture under
Lean4.35.0. It replaces the String.Lemmas umbrella with TakeDrop and
Pattern.TakeDrop.String. Do not apply it to old4.24, shared production files or
a generic cross-version fixture without a version-specific test overlay.

The exact existing eight propositions AND proof bodies are preserved. No edit
to live StringApiControls.lean occurred. The candidate explicit SDK source
header closure is330 versus361 for the original4.35 header; this is not measured
RSS or import visibility. All listed required defining sources remain reachable,
including endsWith_string_eq_false_iff. Every declaration remains subject to
actual visibility/signature and axiom checks before acceptance.

The generator requires both successful versioned source-matching captures and
the committed SHA pins for those reports and the SDK graph. Altered graph and
old-as-new capture controls reject input. No new Lean/benchmark was run.

From the repository root, git apply --check on narrow-imports.patch checks only
patch applicability. It does not apply or validate Lean. The candidate can be
reconstructed from the existing pinned fixture and this committed patch; no
VM-only source file is required for review. Graph provenance is the portable
evidence catalog's static-backfill.tar.gz member new-sdk-imports.json.

Independent finder and skeptic worked read-only without Lean/server/writes.
Both verified unchanged text, hash/version checks,361->330 source counts and
unaccepted status. Their missing-map/version-role findings were fixed; final
reviews report no further defect. STOP remains in force.

Pending: current H81 and root/gate RSS disposition, syntax prerequisite, then
approved per-file gate through scripts/coord-tools/gate.sh, meaning/signature/
axiom checks, and fresh comparable performance measurements. No waiver, shim,
compiler success or full migration acceptance is claimed.
