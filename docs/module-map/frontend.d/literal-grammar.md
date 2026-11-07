| `Frontend/LiteralGrammarH28/BodyPins.lean` | String-body theorem signatures and axiom reports. |
| `Frontend/LiteralGrammarH28/BoundaryPins.lean` | Quote/scanner theorem signatures and axiom reports. |
| `Frontend/LiteralGrammarH28/Classification.lean` | Hex/unicode literal relations and exact classification/refusal boundaries; keeps the raw unicode line/bidi guards. |
| `Frontend/LiteralGrammarH28/EncodingValue.lean` | `CodepointBytes`: independent `\u` escape byte arithmetic (surrogates included); hex pair/quad value bounds. |
| `Frontend/LiteralGrammarH28/FragmentCompleteness.lean` | Classification inversions extended to arbitrary fragment lists of every kind. |
| `Frontend/LiteralGrammarH28/Fragments.lean` | `Fragments`/`FragmentValue`: fragment sequences, byte concatenation and per-fragment splitting. |
| `Frontend/LiteralGrammarH28/FullControls.lean` | Kernel controls for every nonnumeric classification arm and fragment sequence, independent of compiler outcomes. |
| `Frontend/LiteralGrammarH28/FullPins.lean` | All public lane theorem signatures and axiom reports (the audit's pin source). |
| `Frontend/LiteralGrammarH28/Global.lean` | Literal classification inversion over unrestricted raw input. |
| `Frontend/LiteralGrammarH28/Lengths.lean` | Scanner split uniqueness and strictly shorter suffix; byte-length bounds for plain, hex and unicode literals and fragment sequences. |
| `Frontend/LiteralGrammarH28/ModeGrammar.lean` | All-mode (sol/yul/asm/pragma) literal and fragment grammar relation. |
| `Frontend/LiteralGrammarH28/ProofSafety.lean` | Safety report for the word-table proof tactic's generated declarations. |
| `Frontend/LiteralGrammarH28/Roundtrips.lean` | Constructive encode/classify round trips in every literal-bearing mode. |
| `Frontend/LiteralGrammarH28/Split.lean` | Exact literal splitting in each admitted lexer mode, any suffix kept. |
| `Frontend/LiteralGrammarH28/TaggedEncoding.lean` | Constructive hex/unicode literal encodings passing the line/bidi guards. |
| `Frontend/LiteralGrammarH28/Utf8Shape.lean` | `\u` escape byte shape (lead/continuation, non-overlong) and code-point recovery; no scalar check. |
| `Frontend/LiteralGrammarH28/WordTable.lean` | Exhaustive word-table return classes, proved by a checked proof-producing tactic. |
