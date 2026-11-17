# Conditional G49 interface graph

`census_graph.py` consumes the H55 constructor census through the existing H62
exporter and graph builder. It adds seven typed interface declarations while
retaining the five representative production views as pending. The original
`pending-inputs.json` source-only catalog remains unchanged.

The checked private input is in `SolidiKeY/solidity-lean-coord`, commit
`356fc3995378fb21a44e7c14ff9768e4d7cfefef`, directory
`evidence/solidity-h55-sol-20261106/g49-final-theorem/h55-constructor-census-evidence`.
Retrieve that exact directory outside the checkout, verify its `SHA256SUMS`, and
set `H55_PACKET` to it. All source objects for producer checkpoint
`4a0b111282472d79f9aefe546c2e24ae85f4e855` must already exist locally; intake
never fetches. `OWNERSHIP` is the explicit logical-owner snapshot, not an
assertion of current delivery-owner agreement.

```sh
python3 -B scripts/h62/item5/statement-graph/census_graph.py \
  --run "$H55_PACKET/final-constructors" --ownership "$OWNERSHIP" \
  --output "$PRIVATE_OUTPUT/conditional-graph.json"
python3 -B -m unittest discover -s tests/h62/item5/statement-graph -p 'test_census_graph.py' -v
```

The output must be new and outside the repository. Intake pins the immutable
run/results/export bytes, checks every recorded source and log with the H55
loader, verifies the complete import/check order against the producer commit,
and checks runner/exporter/driver/registry source bindings. The two exports must
agree. Changed snapshots, missing checks, witnesses and source drift are refused.
These are producer-supplied exported types: the run reports Lean 4.24 and does
not seal its executable/archive identity. This is not an official 4.35 migration
gate, a fresh local Lean run, full-project validation or runtime acceptance.

Counts use distinct scopes. Seven selected declarations plus five pending views
produce twelve blocked nodes. All 72 selected generic telescope/field entries
remain open conditions. The H55 constructor expansion separately counts 54
supplied slots, including repeated generic contexts; these are not instantiated
nested-path proof types. Neither number counts atomic logical premises. That
count remains unknown, and overlapping G49/G50 root closures must not be summed
as separate proofs. No witness or concrete producer is supplied or discharged.

Named inputs and public fields use their frozen H55 logical reference and the
supplied ownership snapshot. Generic Pass/Cert contexts and the aggregate's
`obligations` binder use G49.01 as an explicit adapter accounting default; package
fields inherit their stage reference. Each role records that basis. These
fallbacks organize conditional interface accounting, not producer assignments.
They do not select an actual Bridge owner or transfer a live lease. The graph wrapper is an opt-in private metadata artifact; no registry
or production consumer is activated. Full factories, canonical Source/runtime
bindings, compatibility acceptance and public residual proofs remain required.
The unit controls use explicitly unelaborated metadata for refusal/classification;
they are not proof evidence. Actual exports, logs, timings and receipts stay in
the private H145 evidence repository.
