# G21/G41 ordered heap-backed custom-error byte lists

Proof commit 35ab12cca86b1aad2fd258148db978e86a0d81b4 adds
Solidity.Lowering.V08.LiteralFailureDynamicListError and its Controls module.
Coordinator registration only; no Source, decoder or registry edits.

`arguments_run` evaluates actual indexed local arguments at count+extra+3.
`represented` ties each local pointer to its actual bytes/string heap object;
`all_represented` pairs these ordered arguments with the complete payload list.
`parts_run` and `encoding_run` derive the actual encoder execution, including
its different empty outer context, without an encoder-success hypothesis.
`source_run`/`source_typed` execute actual custom-error syntax at count+extra+4.
They preserve the complete caller Source state and return its actual symbolic
selector followed by the ordered argument bytes. This is local Source execution,
not a transaction rollback or static permission theorem.

`go_agreement`, `heads_acc` and `abi_agreement` derive agreement with the existing
indexed AbiEntry codec, at arbitrary raw offsets and argument counts. Metadata
retains the original modulo-word semantics. No natural-length nonwrap bound,
physical stack admission or gas conclusion follows from this total byte identity.
The relation allows repeated aliases; it imposes no disjointness condition.

Controls discharge actual declaration typing and heap representation in a populated
caller: old object0, bytes object1, string object2, older alias and account journal.
`three_client` reads aliases1/2/1; `repeated_client` is an inhabited arbitrary-arity
family, including zero. Wrong head/order/count controls and old-object/cursor
observations remain explicit. Fourteen complete argument vectors (3008 bytes)
compare both actual encoders, covering empty, zero,255,128 and31/32/33 lengths.
These vectors omit the symbolic selector; no external compiler/EVM claim is made.
Twenty-three scoped axiom outputs contain only existing standard axioms.

The initial generic-client elaboration exceeded unchanged200000 heartbeats;
explicitly naming its representation premise and simplifying replicated length
repaired elaboration without a budget increase. Both per-file diagnostics and
focused kernel checks pass. Earlier failed attempts remain in evidence.
Finder source review found no issue; final skeptic/artifact results are exported.

Validation uses the existing capped private tree and exact published SourceAbi /
SourceCustomErrors proof-hygiene versions from origin/master6510c302; semantic
source and new files are hash-bound to the helper checkout. It is not standalone
or whole-lane integration evidence. Previous seals and observations are unchanged.

G21, G40, G41, G42.01-.02, G42.04, G42.06 and Backfills A/B remain partial.
G42.03/P3 stays readonly-external; G42.05 awaits its producer. Missing actual
Source/native/target dispatch, unknown-memory runtime ABI encoder, CALL/RETURNDATA,
same-invocation/frame/world and resource composition are not discharged here.
Historical Suite124/181.061s, full1/5038.87s, cold124/5400.579s, bodyexport1,
raw docs1/frozen86vs83 comparison1 remain failures; prior/publication complete
finding equality is separate. No unchanged failed heavy gate was repeated.
The original persistent goal remains blocked unchanged.
