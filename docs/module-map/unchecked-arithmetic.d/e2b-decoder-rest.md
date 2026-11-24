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
