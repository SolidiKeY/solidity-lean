# Checked lexer and parser (G08–G11)

Lane V05 of [the roadmap](../coverage-plan.md) ("Wave 1 — source syntax and
checked admission"). The target of every parse is S00's intrinsic syntax
(`Solidity/Source/Syntax.lean`, design in [source-s00-s01.md](source-s00-s01.md)),
pinned to solc 0.8.38 and its ANTLR grammar
(`tests/upstream/grammar-0.8.38/SolidityLexer.g4`, `SolidityParser.g4`).
S00 is read-only here; what it lacks is recorded under each Handoff.

All modules are under `Solidity/Frontend/Checked/` and import only
`Solidity.Source.Syntax` (and `Solidity.Keccak` for EIP-55), so the frontend
core reaches no elaborator, printer of `dl{}` or tactic front end. Every
stage is an executable checker: an untrusted function proposes, a decidable
certificate decides, and the soundness theorem holds by the check.

| Module | Content |
|---|---|
| `Solidity/Frontend/Checked/Token.lean` | tokens `Tok`, pieces `Piece` (kind and exact bytes), `Located`, `Error` |
| `Solidity/Frontend/Checked/Tables.lean` | byte-literal keyword/word/punctuation tables (generated: `scripts/checked-lexer-tables.py`) |
| `Solidity/Frontend/Checked/Lexer.lean` | `classify`, `split`, `scan`, the certificate `Lexed`, `lex`, `locate`, `tokens`; `lex_sound`, `lex_reprint`, `lex_locate`, `lex_error_pos` |
| `Solidity/Frontend/Checked/LexExamples.lean` | G08 coverage and controls |
| `Solidity/Frontend/Checked/Print.lean` | the yield `Syn.yield` under a layout; `Syn.toks`, `Syn.Derives` |
| `Solidity/Frontend/Checked/Prec.lean` | `Syn.level`, `Syn.precNode`, `Syn.prec` |
| `Solidity/Frontend/Checked/Parser.lean` | the untrusted parser `parseTokens` |
| `Solidity/Frontend/Checked/Check.lean` | `parse`, `parseWithLayout`; `parse_sound`, `parse_derives` |

`scripts/check-checked-frontend.mjs` checks the lexer-rule table against
`SolidityLexer.g4` and the generated tables against their generator.

## G08: checked lexical analysis

### Design

**Bytes, not characters.** G05's raw input is `SourceUnit.bytes`. Every
lexical class is ASCII except comments and `unicode"…"` literals, whose
content S00 keeps as bytes, so the lexer works on `List UInt8` and needs no
UTF-8 decoder. Offsets are byte offsets, as solc's source locations are.

**Three parts.**

1. `classify m raw : Option Kind` is the specification: what a *whole*
   lexeme is in lexer mode `m`, one clause per lexer rule. Words are
   keywords (`Kw`), elementary type names inside solc's bounds (`Elem`),
   units, booleans, reserved keywords (refused) or identifiers;
   `DecimalNumber` and `HexNumber` with single `_` between digits, octal
   refused; string, hex-string and unicode-string literals with the
   grammar's escapes (`\' \" \\ \n \r \t`, escaped line breaks, `\xNN`,
   `\uNNNN` as UTF-8); punctuation; whitespace and comments (NatSpec
   `///`/`/** */` flagged, kept as trivia); pragma words; the
   `AssemblyBlockMode` and `YulMode` lexemes.
2. `split m l` decides where the next lexeme ends (maximal munch). It is
   untrusted.
3. `lex` runs `scan` (split, then classify, with fuel) and accepts only
   pieces carrying the certificate `Lexed s ps`:
   * `(ps.map Piece.raw).flatten = s` — the pieces re-print the source;
   * `classifiedFrom .sol ps` — each piece is classified, in the mode its
     predecessors leave (`Mode.next`: `pragma` and `assembly` push a mode,
     `;` ends a pragma, Yul braces nest);
   * `munchFrom .sol ps` (maximal munch, `maximal`) — no token or
     whitespace run extended by any prefix of the next token (two bytes of
     a comment, one of whitespace) is a lexeme of its mode, so `1|.5`,
     `hex|"00"` and `ui|nt` are not certificates (`lexed_not_maximal`);
   * `noGlue ps` — no number is followed by an identifier character
     (`DecimalNumberFollowedByIdentifier`);
   * `Mode.after .sol ps = .sol` — no pragma or assembly block is left open.

**Modes** follow the lexer's `pushMode`/`popMode`: inside assembly, Solidity
keywords are identifiers, `:=` and Yul's keywords and numbers (no `_`, no
leading zero) are tokens; in a pragma, words are maximal runs without
whitespace, `;` or a comment start.

**Kernel cost.** Keyword and punctuation lookups are `match`es on byte
literals (`Tables.lean`), which the kernel evaluates as decision trees; the
first version, comparing against `String` spellings, took 2.7 s of kernel
time for 58 bytes, the table version 0.7 s. The witnesses in
`LexExamples.lean` are `decide +kernel` on short inputs; whole files are
lexed by compiled or interpreted code (the G11 regression).

### Theorems

| Name | Statement |
|---|---|
| `lex_sound` | `lex s = .ok ps → Lexed s ps` |
| `lex_reprint` | `lex s = .ok ps → (ps.map Piece.raw).flatten = s` (token/source correspondence: re-printing) |
| `locate_spec`, `lex_locate` | for every located token `x` of an accepted source, the bytes of `s` in `[x.start, x.stop)` classify as `x.tok` in its mode, and `x.stop ≤ s.length` (re-location) |
| `scan_error_pos`, `lex_error_pos` | `lex s = .error e → e.pos ≤ s.length` (located refusal) |
| `strBody_sound` | the string-body decoder is sound for `StrBody`, the grammar's `…StringCharacter*`/`EscapeSequence` transcribed as an inductive relation between a body and its bytes |
| `lexRules_classified` | a sample per rule: every rule of `SolidityLexer.g4` (180, all modes; names checked against the file by `scripts/check-checked-frontend.mjs`) has a sample lexeme classified as the rule says: its token class, trivia, or refused |
| `lexRules_cover` | every token class comes from some rule |
| `Kw.bytes_spell`, `Punct.bytes_spell`, `YulKw.bytes_spell` | the printing tables (`Render.lean`) agree with the spellings |
| `classify_kw`, `classify_punct`, `classify_words`, `classify_reserved` | the lexer's tables (`solWordTable`, `yulWordTable`, `punctExact`): every keyword, Solidity and Yul punctuation, Yul keyword, unit, fixed type word and boolean lexes to its token; every reserved keyword is refused in Solidity mode and accepted in Yul |

Witnesses (all `decide +kernel`): `lex_contract`, `lex_numbers`,
`lex_escapes`, `lex_hex_unicode`, `lex_comments` (NatSpec flags),
`lex_types` (bounds: `int7`, `bytes33`, `fixed8x81`, `uint08` are
identifiers), `lex_modes`, `lex_checksum` (EIP-55 flag set for a
checksummed address, cleared after one case change), `lex_ranges`.

Negative controls, each with its offset and message: `refuse_reserved`,
`refuse_octal`, `refuse_glued`, `refuse_underscore`, `refuse_hex_empty`,
`refuse_unterminated_string`, `refuse_newline_in_string`,
`refuse_bad_escape`, `refuse_nonprintable`, `refuse_odd_hex`,
`refuse_comment`, `refuse_char`, `refuse_pragma` and `refuse_assembly`
(located at the open `pragma`/`assembly`), and solc's scanner rules
(`solc_scanner_rules`: form feed, irregular line breaks, unbalanced
direction overrides, `hex` alone in Yul, empty or single-quoted assembly
strings refused; an escaped CR LF accepted). `yul_assign_outside` shows `:=`
is two tokens outside Yul. Wrong outputs fail the certificate: dropped
pieces (`lexed_wrong`) and non-maximal splits (`lexed_not_maximal`);
`natspec_flags` pins the NatSpec flags.

Axiom pins (`#guard_msgs`, registered in `TrustAudit.lean`): `lex_sound`,
`lex_error_pos` and `lexRules_classified` use `propext`; `lex_locate` uses
`propext` and `Quot.sound`.

### Deviations from the ANTLR lexer, recorded

Where the ANTLR lexer and solc 0.8.38's scanner differ, the lexer follows
solc (checked against `test/liblangutil/Scanner.cpp` and the syntax tests of
`tests/upstream/solidity-0.8.38.tar.gz`):

* form feed (and vertical tab) is not whitespace (the grammar's `WS`
  includes `\u000C`); single-line comments and unicode literals refuse
  form feed, vertical tab, U+2028 and U+2029;
* comments and unicode literals must balance the Unicode direction
  overrides (LRE, RLE, LRO, RLO, LRI, RLI, FSI against PDF, PDI), solc's
  "direction override underflow" and "mismatching" errors;
* an escaped CR LF in a string is one escaped line break;
* `hex` alone in Yul is refused (the grammar's unused `YulHex`);
* an assembly dialect or flag is a non-empty double-quoted string.

Other recorded choices:

* **Pragma comments** are trivia; the ANTLR `PragmaToken` (`~[;]+`) would
  absorb them. A pragma word is a whitespace-free run, so a pragma is S00's
  word list. `Munch` is not claimed in pragma mode (`a/*c*/` splits before
  the comment).
* **Numbered type names** follow solc's scanner, not the ANTLR token lists:
  `fixedMxN`/`ufixedMxN` with `8 ≤ M ≤ 256`, `8 ∣ M`, `0 ≤ N ≤ 80`
  (`FixDims`); spellings with leading zeros (`uint08`) or outside the
  bounds are identifiers.
* **EIP-55** is computed (Keccak-256 of the lowercase spelling) for 40-digit
  hexadecimal literals only, the only ones S01 types as addresses; the flag
  is `false` for every other length.
* **UTF-8** is not validated inside comments and `unicode"…"` literals;
  `\uD800`–`\uDFFF` escapes are encoded as three bytes, as solc does.
* EIP-55 is computed on the digits without `_`, as solc does.
* Yul paths are `ident (. ident)*` token sequences (the grammar's
  `yulPath`); solc's Yul scanner reads `x.slot` as one identifier. The tree
  is the same.
* `1._2` lexes as `1`, `.`, `_2` (a member access on a literal); solc reads
  one malformed number. The parse accepts the member access; S01's typing
  refuses it (`docs/feature-work/frontend-parse.md` G11 Handoff).
* `DoubleQuote`, `SingleQuote`, `OctalNumber`,
  `DecimalNumberFollowedByIdentifier`, `ReservedKeywords` and `YulHex` are
  refused, as no parser rule uses them.
* The soft keywords `from`, `error`, `revert`, `global`, `transient`,
  `layout`, `at` are identifiers (the grammar's `identifier` rule admits
  them); the parser reads them by context. `YulEVMBuiltin` names are Yul
  identifiers.

### G08 Handoff

* **Revision**: the commit that adds this section (lane branch
  `cloud/roadmap-l2-20261029/lane-parse`).
* **Theorems**: `lex_sound`, `lex_reprint`, `lex_locate`, `lex_error_pos`,
  `lexRules_classified`, `lexRules_cover`.
* **Premises**: none (axioms `propext`, `Quot.sound`).
* **Checks**: per-file Lean diagnostics clean; `node scripts/check-checked-frontend.mjs`.
* **Remaining**: uniqueness of the certificate (`Lexed s ps → Lexed s qs →
  ps = qs`) is not proved; maximal munch looks one piece ahead. Completeness
  (the scanner never refuses a source the classes admit) is tested on the
  corpus, not proved. `classify` is a hand transcription of the rules; only
  the string bodies have an inductive grammar with a soundness proof
  (`strBody_sound`). A refusal's offset is proved inside the source
  (`lex_error_pos`), not proved to be the first malformed byte. The
  scanner's fuel (`scan`'s "out of fuel") is unreachable since `split`
  consumes a byte, which is tested, not proved. UTF-8 validity is not
  checked.
* **For S00**: nothing required.

### G08 Review

Finder (read-only, solc's scanner tests extracted from the tarball):
12 findings. Fixed: form feed and vertical tab, irregular line breaks and
Unicode direction overrides (1, 2), `hex` alone in Yul (3), escaped CR LF
(4), assembly strings (6), stale documentation of the munch check and of
the test-file name in `Tables.lean` (7, 8), the table theorems extended to
the tables `classify` uses (9: `classify_words`, Yul punctuation and
keywords), mislabelled controls (10), the error message (11). Recorded:
Yul dotted identifiers (5) and `1._2` (12) under the deviations.

Skeptic: "partially supported". Fixed: the certificate accepted
non-maximal splits (`1|.5`, `hex|"00"`): `maximal` now tries every prefix
of the next token, with `lexed_not_maximal` as the control (1); an
inductive string-body grammar with `strBody_sound` (2, for string bodies
only); the reserved-keyword list is checked against `ReservedKeywords` by
`scripts/check-checked-frontend.mjs` and the coverage claim reworded to "a
sample per rule" (3); unterminated pragma and assembly blocks are located at
their start and a failed certificate at its first failing piece (4);
NatSpec flags for `////` and `/***/` (6); the stronger wrong-output control
`ui|nt` (7). Recorded under Remaining: uniqueness, completeness, the
precision of error offsets and the fuel bound (1, 4, 5, 9).

## Reviews

Each checkpoint ends with a read-only finder and a separate skeptic review
(no Lean server); confirmed findings are fixed and listed here.
