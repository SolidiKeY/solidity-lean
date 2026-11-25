| `Correctness/Lowering/Total/Decode/Tables.lean` | Parameterized raw-to-Source decoder and proof that the original tables recover the landed decoder. |
| `Examples/Goals/LoopsDecode.lean` | Retained decoder table and original-decoder equivalence checks, separate from the shared loop examples. |
| `Correctness/Lowering/Total/Decode/Widths.lean` | Retained width-aware decoder tables for primitive locals, declarations and state variables. |
| `Correctness/Lowering/Total/Versions/Primitive.lean` | Retained primitive type representation relation and elementary/local type lemmas. |
| `Correctness/Lowering/Total/Decode/Spelling.lean` | Compatibility import and definitional original-table bridge for generalized spelling in Total/Spells.lean. |
| `Correctness/Lowering/Total/Decode/Marked.lean` | Retained marked-address, fixed-bytes and caller-aware decoder tables; existing coverage gaps remain explicit. |
| `Correctness/Lowering/Total/Versions/Matching.lean` | Retained version state relation and Source-to-model initial matching for sound tables, instantiated at widths. |
| `Correctness/Lowering/Total/Versions/Marked.lean` | Retained representation soundness proofs for marked-address and fixed-bytes decoder tables. |
| `Correctness/Lowering/Total/Versions.lean` | Retained version boundaries and contract decompositions with the original unresolved coverage, inference, simulation and allocation obligations. |
| `Correctness/Lowering/Total/Decode/BytesLiteral.lean` | Fixed-bytes literal normalization and model-alignment value faithfulness; shared call integration remains separate. |
| `Correctness/Lowering/Total/Decode/BytesLiteral/Checked.lean` | Fixed-bytes value faithfulness from contextual conversion, narrow-width fit and full-word numeric checks. |
| `Correctness/Lowering/Total/Decode/BytesLiteral/Evaluation.lean` | Source typed resolution and evaluation of normalized fixed-bytes literals, with local checked model-value agreement. |
| `Correctness/Lowering/Total/Decode/Calls.lean` | Executable additive call-spelling expression decoder, exact ExprX contract and conservative unclaimed-expression behavior. |
| `Correctness/Lowering/Total/Decode/WithExpr.lean` | Expression-parameterized statement/request decoding, registered-call integration, and exact v1 recovery for an empty registry. |
| `Correctness/Lowering/Total/Versions/CalleeBinding.lean` | Structural callee declaration/output interface, ordinary and recursive endpoints, with translator and semantic obligations open. |
| `Correctness/Lowering/Total/Decode/Callee/Parameters.lean` | Callee primitive parameter/return spelling, ordered type correspondence and actual Source frame construction. |
| `Correctness/Lowering/Total/Decode/Callee/Functions.lean` | Ordinary function declaration assembly with original body spelling, ordered modifiers and exact Source frame correspondence. |
| `Correctness/Lowering/Total/Versions/CalleeBinding/Resolved.lean` | Executable whole-unit elaboration and exact selected-declaration frame/body binding to the Source program. |
| `Correctness/Lowering/Total/Decode/Callee/Metadata.lean` | Ordinary function assembly from retained source identity, visibility and mutability, with exact header correspondence. |
| `Correctness/Lowering/Total/Decode/Callee/Declarations.lean` | Ordered assembly of all function entries, exact collected-declaration correspondence and count preservation. |
| `Correctness/Lowering/Total/Decode/Callee/Units.lean` | Contract-unit assembly preserving supplied declaration prefixes and exact translated-function table suffixes. |
| `Correctness/Lowering/Total/Versions/CalleeBinding/Functions.lean` | Original function-index selection tied to exact translated declaration and actual elaborated Source body. |
| `Correctness/Lowering/Total/Versions/CalleeBinding/Frame.lean` | Original parameter/return names, slot types, body spelling and flags bound to the actual selected Source frame. |
| `Correctness/Lowering/Total/Decode/Self.lean` | Self-aware decoder tables: `address(this)` and its balance spelled; the environment table has no gap. |
| `Correctness/Lowering/Total/Versions/Self.lean` | Self-aware version: soundness, boundary, Source typing/evaluation of the two reads and value faithfulness under related globals. |
