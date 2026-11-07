# Independent re-baseline reviews

Finder: detected that acceptance.py reconciled operational headers at the old
base and that census.py could store movable revision text. Both were fixed:
headers now use the selected census revision; revision resolves to a full commit
before reading blobs. Finder re-reviewed and found no further concrete issue.

Skeptic: independently detected old-base header validation and requested explicit
canonical scope provenance. CLI manifests now must equal the exact original base
path set, with input hash recorded. Its re-review confirmed revision, scope and
comparison fixes with no blocking code finding. Review was code-only while final
receipts were pending; subsequent worker receipts separately pass original 246
and operational 249 headers. No review is misrepresented as running those checks.

Both confirmed that added producer modules remain dependency-only and drift is
lexical, not API/proof/owner permission. Neither edited files or used Lean/server,
build or timing jobs. Final static logs and negative controls are off git in the
rebaseline-20261107 evidence directory. Prior stale acceptance.log remains labelled
historical; final acceptance-original.log and acceptance-operational.log are the
revision-specific receipts.
