The diagnostic generators `scripts/h62/item2/audit-v08-adapters/generate_mapped_census.py`
and `scripts/h62/item2/audit-v08-adapters/generate_calldata_census.py` accept
`--stream` to omit the global imported-constant sort. This still materializes
`toList`; it is not lazy or a bounded-memory guarantee. Default generated source
is unchanged. Source hashes, selected-module filtering, captured fields and
exclusive-write guards are retained. Bind any new capture to the current
collector/template hashes; do not relabel historical receipts. Sort captured
rows outside Lean when deterministic presentation is needed. Inventory and
name matching do not establish feasibility, statement fidelity or H68 adequacy.

`--result-shapes` optionally captures the conclusion head after all binders,
equality operand heads and their kernel defining modules, and syntactic
reflexivity. These are structural observations, without reduction or semantic
proof. A generated equation's defining module does not transfer ownership of
the referenced evaluator. Default captured fields remain unchanged unless the
option is enabled. Bind shaped captures to their own fresh generator hashes.
