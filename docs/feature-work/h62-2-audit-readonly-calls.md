# Audit readonly calls

The [checker](../../scripts/h55/module-times/readonly_audit_controls.py) and [fixtures](../../tests/h62/item2/audit-readonly-calls/) define the current scope and limitations.

## Checking the native and Source fixtures

Use the configured Lean 4.24 SDK and the existing bounded runner. Both output
paths must be private directories outside the checkout; the output directory
must not exist yet.

```sh
python3 -B scripts/h62/item2/audit-readonly-calls/bounded.py \
  --evidence "$AUDIT_EVIDENCE" --tag native --timeout 1800 -- \
  python3 -B scripts/h62/item2/audit-readonly-calls/rebuild_native_closure.py \
  --output "$AUDIT_OUTPUT"
```

This builds the selected dependency closure in an initially empty project
library, binds direct project imports to their preceding builds, and checks
both sibling import orders. It needs no historical receipt or project cache. The SDK,
Python runtime and CLI bootstrap remain trusted. The touched gate alone does
not check these test-local modules. Host cache/staging acceptance remains
separate from an isolated pass.

The fixtures preserve the original 792-obligation accounting. Their closed
Source/body/world examples do not establish full H121 callee/compiler/world
or physical-frame correspondence. Keep the existing Premises timing STOP;
the command refuses that dependency and gives no performance or runtime
qualification.

Historical proof-cleanup head
`fb0defdca5c5fe9baa7fd8c1e1271a91d255e1c9` is **UNVERIFIABLE** under H151.
Its original claim remains unproven. Fresh checks have new provenance and do
not recover or replace the missing result; it is not an active dependency.
