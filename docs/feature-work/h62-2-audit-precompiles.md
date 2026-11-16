# Audit precompiles

The [checker](../../scripts/h55/module-times/precompile_audit_controls.py) and [fixtures](../../tests/h62/item2/audit-precompiles/) define the current scope and limitations.

The [compiler-success fixture](../../tests/h62/item2/audit-precompiles/CompilerSuccess.lean)
constructs actual core compiler success and V2 agreement for an admitted nonempty
guard body, with success/failure controls and an arbitrary saved tail. It does
not establish metered stipend adequacy, fork correspondence or physical execution.
Check it with `scripts/coord-tools/gate.sh per-file tests/h62/item2/audit-precompiles/CompilerSuccess.lean`.
