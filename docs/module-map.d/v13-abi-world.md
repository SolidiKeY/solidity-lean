
| V13 independent preparation module | Purpose |
|---|---|
| `Backend/AbiWorld/ErrorLayout.lean` | Arbitrary-length published error-codec padding, exact offset/length/payload observations and packet noninterference. |
| `Backend/AbiWorld/ErrorRoundtrip.lean` | Existing machine-numeral agreement and arbitrary representable Error(string) roundtrip. |
| `Backend/AbiWorld/ErrorControls.lean` | Kernel boundary, malformed, nested and noncanonical error-returndata controls. |
| `Backend/AbiWorld/ErrorEmission.lean` | Published REVERT emitter adapter and intrinsic catch decoding, with architectural bounds. |
| `Backend/AbiWorld/WorldFrames.lean` | Published typed source-world separation, heterogeneous journal rollback and prefix observation transport. |
| `Backend/AbiWorld/Controls.lean` | Inhabited multiword emitter/catch and actual persistent/transient mutation/rollback combinations. |
| `Backend/AbiWorld/PublishedCallControls.lean` | Signature-polymorphic published static/role/callee refusals and inhabited self-address/library combinations; no compiled-call claim. |
| `Backend/AbiWorld/PublishedLayout.lean` | Arbitrary published source ABI layout lengths, offsets, payloads, concatenation and noninterference, with explicit canonical static widths. |
| `Backend/AbiWorld/PublishedLayoutControls.lean` | Empty, mixed, boundary, nested-packet and cursor-wrap kernel controls. |
| `Backend/AbiWorld/CatchTransport.lean` | Actual intrinsic self-call catch classification and decoded fresh-byte allocation/clause-pop consumers, retaining explicit executed-callee premises. |
| `Backend/AbiWorld/CatchControls.lean` | Discharged typed call/catch executions with Source/Failure bytes, old caller aliases, malformed/noncanonical packets, refusals and true divergence; no target/world compilation claim. |
| `Backend/AbiWorld/CompiledMemoryCalls.lean` | Published direct memory-return compiler/frame consumer, discharged state/base/allocator transport, alias/escape/store/stack and return-failure controls, bounded word-byte observer; no external-call/aggregate claim. |
| `Backend/AbiWorld/ReturnedBytes.lean` | Arbitrary-length represented uint-array word-cell observation, exact byte values/order/header/length, independent addresses/noninterference and existing Error codec/compiler-result transport. |
| `Backend/AbiWorld/ReturnedBytesPrefix.lean` | Actual compiled prefix producing a nonempty caller heap, typed old reference, represented state and exact producer-cost allocator cursor. |
| `Backend/AbiWorld/ReturnedBytesControls.lean` | Nonempty compiler applications at empty/3/31/32/33 and escaping33, full ordered payload/layout/resource/store observations and actual compiled uint300 plus wrong-claim negatives. |
| `Backend/AbiWorld/LibraryFrameTransport.lean` | Published installed-library caller refresh, exact live dependent heap/frame and transaction identity, selected actual success/caught typed tails, and separate outer ContractWorld checkpoint. |
| `Backend/AbiWorld/LibraryFrameControls.lean` | Populated-prefix library applications, caller/library storage separation, old aliases, exact payments, full packets/ordered results, real typed failure tails and observation-prefix composition; no compiled-world claim. |
| `Backend/AbiWorld/EntryTransport.lean` | Actual published ABI-entry verdict certificates select existing empty REVERT emission; typed entry/body-value/eager-lazy witness transport, explicit Fits/stack/fuel boundaries. |
| `Backend/AbiWorld/EntryControls.lean` | Inhabited aggregate/noncanonical diagnostic values and length-only reads, malformed-to-emitter executions, exact named refusals and stack exhaustion; no decoder compiler/native simulation claim. |

| `Backend/AbiWorld/PacketEmission.lean` | Value-specialized published typed codec to actual checked RETURN/custom-error byte emission; exact whole packet, selector, Fits/stack and memory interval premises. |
| `Backend/AbiWorld/EnumEntry.lean` | Actual nominal enum cardinality failure before arbitrary tail parameters, coupled to selected existing empty REVERT emitter; truncated-head and fuel boundaries retained. |
| `Backend/AbiWorld/EnumControls.lean` | Actual enum-before-dynamic-memory/calldata clients, complete ordered packet/selector/offset observations, wrong-range/truncation/refusal controls and post-enum eager/lazy reference. |

| `Backend/AbiWorld/WordArrayPacket.lean` | Actual represented full-uint word arrays to published typed ABI values/complete offset-length-word observations and post-execution literal packets; exact compiler/frame/cost premises and separate memory units retained. |
| `Backend/AbiWorld/WordArrayControls.lean` | Actual compiled alias/private-escape applications after populated caller setup; whole word300, old object/marker/store/sentinel, pointer/header/refusal/order diagnostics and literal packet endpoints. |

| `Backend/AbiWorld/CallerPacket.lean` | Exact committed V12 selected-call caller aliases to current represented uint-array codec observations; private combined-tree preparation, not runtime byte encoding. |

| `Backend/AbiWorld/MixedPacket.lean` | Actual represented uint scalar plus current captured dynamic array to heterogeneous codec head64/full ordered bytes; selected frame/resource transport and explicitly separate post-execution literal packets. |

| `Backend/AbiWorld/ArrayPairPacket.lean` | Two current represented uint arrays through the real codec: derived second offset/tail sizes, prefix noninterference, equal-alias and selected caller transport; no runtime byte encoder. |

| `Backend/AbiWorld/NestedUintPacket.lean` | Arbitrary nested uint-array intrinsic codec layout, post-length relative offsets, complete ordered full-word payloads, length and scoped prefix noninterference; no nested runtime representation. |

| `Backend/AbiWorld/CanonicalReadback.lean` | Actual embedded full-word loader readback; generic canonical uint-array eager/entry/body typed roundtrip with original fuel/allocation bounds, plus actual selected nested-inner decoding. |

| `Backend/AbiWorld/NestedReadback.lean` | Actual generic canonical nested uint-array mseq/allocator, indexed eager/memory/calldata/body/lazy readback and discharged canonical layout; preserves original size/fuel/allocation conditions. |

| `Backend/AbiWorld/BytesReadback.lean` | Actual generic byte-string mdec/eager/memory/calldata/body/lazy identity, exact padding and original rounded allocation/fuel bounds; no runtime encoder or native/world agreement. |

| `Backend/AbiWorld/TupleReadback.lean` | Actual canonical heterogeneous and two-dynamic-array entry/body typed identity, all memory/calldata array locations, reversed mixed order, exact sequential cursor and original sufficient fuel/allocation bounds. |

| `Backend/AbiWorld/EntryComposition.lean` | Unconditional indexed entry concatenation, exact head/cursor/fuel and ordered failures; actual dynamic codec window laws. |
| `Backend/AbiWorld/BytesArrayReadback.lean` | Actual canonical bytes/uint-array entry/body identities in both orders and all memory/calldata combinations, real rounded allocation and sufficient original bounds. |

| `Backend/AbiWorld/BodyComposition.lean` | Unconditional indexed bodyValues concatenation, actual tail head position and ordered eager/lazy failures with the original fuel. |
| `Backend/AbiWorld/TripleReadback.lean` | Generic actual typed bytes/uint-array/scalar entry/body identity for four memory/calldata combinations, codec-derived three-head layout and actual calldata-only entry origins. |

| `Backend/AbiWorld/WordListReadback.lean` | Uniform typed canonical entry/body induction over arbitrary existing validated-word Param/Vals lists, exact head bounds/cursor and original fuel; sufficient constructor case only. |
| `Backend/AbiWorld/StaticAggregateReadback.lean` | Actual tuple/fixed/dynamic-array consumers over validated-word Vals/Seq, real allocator/member-fuel/header conditions and tuple eager/lazy agreement. |

| `Backend/AbiWorld/DynamicListReadback.lean` | Actual assemble head/tail concatenation and uniform typed word/bytes parameter-list admission with exact dynamic offsets, allocation cursor and original fuel. |
| `Backend/AbiWorld/DynamicAggregateReadback.lean` | Arbitrary mixed word/bytes tuple member and constructor decoding, real outer allocation, original decreasing fuel and memory/calldata entry/body identity. |

| `Backend/AbiWorld/ByteSequenceReadback.lean` | Actual arbitrary-count dynamic-byte Seq/mseq canonical readback, fixed/array constructors and typed memory/calldata entry/body identity with exact outer/inner allocations and original fuel/header guards. |

| `Backend/AbiWorld/NestedByteReadback.lean` | Actual recursive Seq(array.bytes) codec/decoder induction, derived allocation and original sufficient fuel, nested fixed/array typed memory/calldata entry/body identity. |
| `Backend/AbiWorld/NestedByteListReadback.lean` | Generic heterogeneous nested byte-array/validated-word canonical entry/body composition beyond LeafShapes, with actual head/offset/cursor observations. |

| `Backend/AbiWorld/RecursiveLayout.lean` | Recursive canonical allocation, fuel and actual codec extents. |
| `Backend/AbiWorld/RecursiveReadback.lean` | Mutual actual recursive decoder/window readback. |
| `Backend/AbiWorld/RecursiveEntry.lean` | Uniform indexed canonical parameter entry/body identity. |

| `Backend/AbiWorld/LocationPeak.lean` | Location-sensitive sufficient recursive canonical allocation bounds and actual entry/body readback. |

| `Backend/AbiWorld/SiblingReadback.lean` | Indexed recursive sibling-prefix byte windows and actual decoder/entry/body noninterference. |

| `Backend/AbiWorld/{ReferenceFields,RawEntryTransport,SeqPrefix}.lean` | Canonical raw-entry/reference identity and actual indexed decoder sibling-prefix transport; sufficient guards only. |

| `Backend/AbiWorld/RawFreeTransport.lean` | Actual raw-entry free-bound transport for calldata or word-copy parameters; body admission remains separate. |
