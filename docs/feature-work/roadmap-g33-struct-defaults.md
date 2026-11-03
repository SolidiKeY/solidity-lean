# G33 finite struct defaults

A finite fragment of G33 ([coverage plan](../coverage-plan.md)): default
construction of one struct pair and one nested struct in memory, source and
compiled, from the memory-reference-structs lane.

## Proved

- `Backend/MemoryOps/StructDefaults/SourcePair.lean`, `Frame.lean`:
  `Source.zeroVal` of a struct holding a `uint256` and a dynamic `bool[]`
  reference: child then parent object, exact addresses and cursor, old objects
  kept, timeout at fuel 0.
- `Nested.lean`, `NestedObservers.lean`: an outer struct holding that pair and a
  `bool`, through the actual field-evaluator equations.
- `Intrinsic.lean`, `NestedIntrinsic.lean`: `PairAt`/`NestedAt` relate the fresh
  source objects to intrinsic default allocation; both old heaps are framed
  independently.
- `Word.lean`, `NestedWord.lean`: `source_pair_word` and `source_nested_word`
  use `DefaultPlan.sound` for the run of a given plan's code, reached
  representation, allocator, identity-base extension, separation and the
  zeroed free region, joined to the intrinsic agreement through the shared
  intrinsic heap. The plans cost three and five cells. `SelectionControls.lean` proves the hand-built pair and nested plans equal
  the actual `defaultPlan?` results and transfers their exact word observations
  to selected code.

Premises: layout agreement, an actual `DefaultPlan`, `mapFree`, an initial
`StateRepr` and `StructAllocatorRepr`, a positive local-frame base and
`cursor + plan.cost < W`. The source address and the word root are not related directly. This is
agreement on the fresh objects, not a
representation theorem for the whole initial source heap.

`Controls.lean`, `WordControls.lean` and `NestedWordControls.lean` instantiate
the declarations, layouts and inputs, and check wrong roots, child and inner
pointers, pair insufficient fuel and the capacity premise arithmetic (which
denies an input premise; it is not a runtime revert or a `Panic(0x41)` claim).
`SelectionControls.lean` additionally observes the parent object at address2
and both typed fields, and proves the nested fuel8 timeout leaves the input
state unchanged. Several `wrong_*` controls follow directly from the positive
results.

## Open

Only the finite pair/nested layout with an empty primitive `bool[]` child.
Not covered: source struct admission, reference-element arrays, recursive graph
copying, arbitrary source graph refinement, solc physical addresses.

`Backend/InternalFlow/RuntimeFrameV3CallProducerRef.lean` proves typed
memory/tuple call-form transport and constructs the frozen V3 producer from
a checked call, explicit alias/profile agreement and real success/revert
witnesses. RefArrayControls supplies an allocating array-call instance.
`RuntimeFrameV3CallProducerRefTupleCall.lean` certifies tuple-call emission and
`RuntimeFrameV3CallProducerRefTupleControls.lean` inhabits a mixed tuple call.
`RuntimeFrameV3CallProducerRefStructDefaultTarget.lean` proves target execution
and reserved-word framing for finite default plans,
`RuntimeFrameV3CallProducerRefStructDefaultCompile.lean` uses them in the call
compiler, and `RuntimeFrameV3CallProducerRefStructDefaultControls.lean` inhabits
a nested finite-struct return; see
[reference expansion](p1-call-reference-expansion.md).
