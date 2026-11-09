# Source reference

Read the [source or current guidance](../../scripts/h55/g49-final-theorem).
This path is retained for links from checker-pinned reference documents.

## Constructor field census for final accounting

The H55 accounting helper now expands the supplied Lowering, Compilation and
Execution records through their existing Pass and Cert fields. It reuses the
H62 elaborated-type exporter, retaining each generic constructor telescope,
field type, projection declaration, Prop/data classification and logical owner
ID. These are generic constructor contexts, not instantiated nested-path types.
The delivery lane is an explicit operator argument; it does not establish owner
agreement or a producer proof.

One supplied slot is a terminal field under that expansion policy, or one
retained interface/function parameter. For the frozen interfaces, the three
packages expose 33 terminal slots: 18 proposition fields and 15 data fields.
Keeping the 15 named public predicates, four interface contexts and two compiler/
decode functions gives 54 supplied slots (24 original constructor binders minus
three package binders plus 33 package leaves). Public predicates and interface
objects remain opaque, so the atomic logical-premise count remains unknown.
All 54 rows retain explicit checked field or aggregate-binder types and logical
owner IDs, including the six opaque inputs. The actual public theorem still
has its original inputs and conclusion.

[ConstructorCensus](../../tests/h55/g49-final-theorem/ConstructorCensus.lean)
exports the seven selected declarations twice using the existing H62 exporter.
The optional `--h62-exporter` path of the bounded source checker seals both
identical outputs with the successful-run hashes. The default source/control
path keeps its module order and resource budgets. The census export has its own
success marker and claims no semantic-control or full-producer acceptance.

[constructor-slots.py](../../scripts/h55/g49-final-theorem/constructor-slots.py)
checks the source/log/output hashes, fixed field schema, constructor context
order, nested package references and named delivery lane. Its output stays
outside the checkout. The Python controls use explicitly unelaborated fixtures
to test missing fields, role relabeling, reordered contexts, axiom drift and
unnamed owners; they are external accounting tests, not proof witnesses.

```sh
python3 -B scripts/h55/g49-final-theorem/check-pass-correct.py --lean "$H55_LEAN_BIN" --evidence "$H55_CENSUS_DIR/run" --controls tests/h55/g49-final-theorem/ConstructorCensus.lean --h62-exporter
python3 -B scripts/h55/g49-final-theorem/constructor-slots.py --run "$H55_CENSUS_DIR/run" --collector solidity-h62-3-20261106/g52-differential --output "$H55_CENSUS_DIR/slots.json"
```

H55 owns this census and final accounting. H121b/H121c native producer work stays
with G52 under the coordinator's active route A. The five full producer families,
concrete stage bindings and public residual proofs remain required inputs;
reference payload matches and this structural census discharge none of them.
