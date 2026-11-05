# H28 G08 nonnumeric literal decoder completeness

Status: **done except the fresh solc fixture rerun** (see "Claude VM
completion"). The lane moved from a Codex VM to a Claude VM on 2026-11-05;
all 26 `Solidity/Frontend/LiteralGrammarH28/**` modules are registered in the
generated `Solidity.lean` root, so the former registration blocker
(Q-ROOT-01) and the cache-delivery question (Q-CACHE-01) are closed.

Exclusive writes: `Solidity/Frontend/LiteralGrammarH28/**`,
`tests/h28-sol/literal-grammar/**`, this file, and the lane's module-map
fragment `docs/module-map/frontend.d/literal-grammar.md`. Read-only inputs
(SHA256-pinned in `tests/h28-sol/literal-grammar/pins.json`):
`Checked/Lexer.lean`, `Checked/Token.lean`, `Checked/Tables.lean`,
`tests/upstream/grammar-0.8.38/SolidityLexer.g4`.

## Independent complete clause inventory

| Input/function | All clauses and branches | Current coverage |
|---|---|---|
| `escapeChar` | Quote single/double/backslash emit the original byte; n emits LF; r emits CR; t emits TAB; LF/CR emit empty; other bytes refuse. | kernel checked: escape_complete/escape_sound |
| `utf8` | cp < 0x80 emits one byte; otherwise cp < 0x800 emits two; otherwise three. Formula encodes all four-digit escapes including surrogates. No scalar or UTF8 validation may be added. | kernel checked: codepoint_iff and utf8_length |
| `strBody` | Empty; backslash-x plus two digits with true/false digit guard; backslash-u plus four digits with true/false digit guard; escaped CRLF; other backslash-c with successful/failed simple escape; raw byte with allowed-and-not-backslash true/false. Truncated x/u fall through the simple escape branch and refuse. Singleton backslash falls through the raw-byte branch and refuses. | kernel checked: body_iff and Body.toStrBody |
| `quotedBody` | Empty refuses; nonempty requires opening byte single/double quote and matching last byte, returns exact dropLast body; every failed guard refuses. Empty remainder, missing closer, unequal closer, invalid opener must be covered. | kernel checked: quotedBody_iff |
| `hexBody` | Empty accepts empty; pair followed by underscore requires both hex digits and nonempty suffix, recursively emits one byte; failed guard refuses; ordinary pair requires both hex digits, recursively emits one byte; failed guard refuses; singleton refuses. | kernel checked: hexBody_iff and encodeHex_roundtrip |
| `plainString` | quotedBody success dispatches printable(q) decoder; quotedBody failure refuses. Printable excludes quote, permits ASCII 32..126; strBody separately excludes raw backslash. | kernel checked: plainString_iff |
| `solTok` literal arms | Word and punctuation priority precede plain strings. Plain success emits str; plain failure dispatches hex prefix or unicode prefix. Hex requires quotedBody and hexBody. Unicode requires quotedBody, no irregularBreak and bidiBalanced before unicodeChar decoding. Other input falls through unchanged numeric arms. | kernel checked: solTok_literal_iff |
| `yulTok` literal arms | Bare hex refuses; word/punctuation priority; plain success emits str; hex prefix plus quotedBody/hexBody emits hexStr; otherwise unchanged numeric handling. Unicode is not a Yul literal arm. | kernel checked: Yul literal iff/impossibility |
| `classify` modes | Trivia priority, then sol; pragma semicolon/pragma-word handling; assembly punctuation priority then double-quoted raw length >2 plain string; Yul at arbitrary depth. | kernel checked: modeLiteral_iff |
| `untilQuote` | For literal delimiters 34/39: empty refuses; escaped CRLF copies three raw bytes; other backslash-c copies two; matching quote closes and leaves suffix; raw newline refuses; other raw bytes recurse. Singleton backslash belongs to raw-byte recursion then fails at end. | kernel checked: untilQuote_iff and ModeLiteral.split |
| Fragment concatenation | Lexer tokens contain individual fragment byte lists; concatenation laws must state exact byte sequence/order and refusal/classification boundaries. | kernel checked: modeSequence_iff and fragment append/flatten laws |

## Queue accounting

1. Independent Escape, Body, Quoted, HexBody, Plain, UnicodeLiteral, HexLiteral, Scan, Fragments, ModeLiteral and ModeSequence grammar/value relations are implemented independently of decoder outcomes. Body.toStrBody reuses existing strBody_sound. Numeric/EIP55 implementations remain immutable.
2. Arbitrary-length completeness/soundness covers simple, hex and Unicode escapes, escaped line ends, both quote modes and exact values. Scan/split theorems preserve every arbitrary suffix. Scanner iff is for literal delimiters 34/39; q=92 is an explicit negative boundary control.
3. Exact pair/underscore rules, independent byte/codepoint arithmetic, lengths, fragment concatenation values, universal classification iff/refusal consequences and all-byte constructive round trips are proved. All modes are characterized, including asm raw-source length/quote guards and unsupported pragma/Yul literal classes. Mixed-kind sequences are lexical; no parser-expression admission is claimed.
4. 242 kernel rows (28 hex, 53 body, 56 boundaries, 105 classification), inhabited positive and universal negative controls, 217 public theorem signatures/axiom pins (200 before the backfill) and 58 fixed compiler cases in both pipelines are implemented.
5. Backfill (2026-11-05, `Lengths`, `Utf8Shape`): see below.

The old StrBody relation overlaps at escaped CRLF for an always-true predicate; the decoder emits empty but that relation can derive LF. Body models CRLF priority without excluding accepted inputs. Both the old overlap and new exact result remain visible kernel witnesses.

CodepointBytes preserves the original arithmetic, including surrogates and arbitrary Nat behavior. Invalid UTF8 is not silently rejected. Unicode canonical encodings use ASCII escapes with proved no-irregular-break and balanced-bidi guards. All-byte assembly roundtrip includes the empty value using escaped LF so the existing raw-length guard is met.

The global generated-word-table range proof covers every original matcher branch at the existing budget. Its proof-producing tactic applies safe lemmas and checked equality elimination, fails on unsupported shapes/cap exhaustion, and introduces no trust shortcut. ProofSafety reports exactly eight safe owning-module definitions; the range theorem has no axioms. Failed budget/recursion experiments remain in scratch logs; no budget was raised.

## External compiler boundary

soljson 0.8.38+commit.1835d247.Emscripten.clang SHA256: `6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`. Fixtures request actual bytecode and AST in legacy and viaIR; exact values, Sol/Yul literal spans, error diagnostics, assembly flags, input/source/bytecode hashes are fixed. External observations are not kernel proofs or general conformance.

Initial strict comparison failed six rows (three cases times two pipelines), retained in evidence. Exact observation checking retains these differences: Unicode surrogate escape encodings are accepted by the byte model but rejected downstream by solc with SyntaxError 8452; plain surrogate escape compiles. solc accepts empty and single-quoted assembly flags, while the pinned model refuses raw length two and non-double quotes. Frozen producer/alignment files were not changed. JSON cannot transport arbitrary invalid UTF8 source bytes; byte-level kernel controls cover those cases.

## Claude VM completion (2026-11-05)

In progress: fresh `./run-lean.sh`, audit against a fresh axiom log, and
finder/skeptic reviews of the backfill and audit repair. Receipts follow when
they finish. Codex-era receipts (evidence/ subdirectories) are historical.
