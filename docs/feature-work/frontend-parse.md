# Checked lexer and parser (G08–G11)

Lane V05 of [the roadmap](../coverage-plan.md) ("Wave 1 — source syntax and
checked admission"). The target of every parse is S00's intrinsic syntax
(`Solidity/Source/Syntax.lean`, design in [source-s00-s01.md](source-s00-s01.md)),
pinned to solc 0.8.38 and its ANTLR grammar
(`tests/upstream/grammar-0.8.38/SolidityLexer.g4`, `SolidityParser.g4`).
S00 is read-only here; what it lacks is recorded under each Handoff.

All modules are under `Solidity/Frontend/Checked/`. The lexer, yield,
precedence predicate, parser and check import only S00
(`Solidity/Source/Syntax.lean`, `Ctor.lean`; `Decls.lean` in the
witnesses) and `Solidity.Keccak` (for EIP-55); `Certificate.lean` adds G05's
interface (`Solidity/Roadmap/Frontend.lean`). None reaches an elaborator, a
printer of `dl{}` or a tactic front end. Every stage is an executable
checker: an untrusted function proposes, a decidable
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
| `Solidity/Frontend/Checked/Check.lean` | `parse`, `parseWithLayout`, `parseInProfile`, `parseCat`; `parse_sound`, `parse_derives`, `parseInProfile_sound` |
| `Solidity/Frontend/Checked/Render.lean` | canonical token spellings, `Syn.print` |
| `Solidity/Frontend/Checked/Certificate.lean` | G05's parse stage: `Parses`, `parseChecker`, `produce` |
| `Solidity/Frontend/Checked/TypeExamples.lean`, `ExprExamples.lean`, `UnitExamples.lean` | G09, G10, G11 controls and coverage |
| `scripts/parse-corpus.mjs`, `scripts/ParseCorpus.lean`, `tests/parse-corpus/baseline.json` | the corpus regression (G11) and the round-trip backfill |

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
  refuses it (G11 Handoff, "For S01").
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

## G09: type and declaration syntax

### Design

**The specification is the yield.** `Syn.yield t L` (`Solidity/Frontend/Checked/Print.lean`)
is the token sequence `t` derives, one clause per S00 constructor, read off
the grammar rule the constructor represents (`grammarCtors`,
`Solidity/Source/Upstream.lean`): `mapping ( key name? => typeName name? )`,
`function ( parameterList? ) attrs (returns ( parameterList ))?`,
`typeName [ expression? ]`, `struct name { member+ }`, a state variable's
`typeName attrs name (= expression)? ;`, and so on. S00's trees keep the
source's parentheses (`(e)` is a one-component tuple), so the yield inserts
none: it is a derivation, not a pretty printer.

**Layouts.** Two spellings are below S00's abstraction: the order of a
definition's attributes (the grammar's `( visibility | stateMutability |
modifierInvocation | Virtual | overrideSpecifier )*` with at-most-once
predicates, which S00 stores as fields) and the fragments of a concatenated
string literal. A layout `L : List Choice` records them in pre-order:
`attrs order` per attribute-bearing node (function, constructor, modifier,
fallback, receive, state variable, function type), `frags lengths` per
string literal, `layoutFirst` for a contract with both `layout at` and `is`.
`Syn.toks t L = some ts` (the yield consuming all of `L`) is the derivation
of `ts` under those choices, and `Syn.Derives t ts := ∃ L, t.toks L = some ts`.

**The parser** (`Solidity/Frontend/Checked/Parser.lean`) is untrusted
recursive descent, one function per grammar rule in a `mutual` block,
structural on a fuel argument so the kernel evaluates it. It returns the
tree and the layout it read; `capture` reorders the layout into the yield's
pre-order (a function's attribute order is known only after its
parameters). It is intrinsic: it builds `Syn c` directly, with the statement
context `SCtx` and the `elementaryTypeName[false]` proofs, so no untyped
intermediate layer exists.

**The check** (`Solidity/Frontend/Checked/Check.lean`): `parseLocated`
accepts the parser's tree only if its yield under the returned layout is
exactly the lexed token sequence and `Syn.prec` holds (G10).
`parseCat p` does the same for one category (`parseType`, `parseExpr`).

**Printing** (`Solidity/Frontend/Checked/Render.lean`): `Tok.render`
spells each token canonically (exact decimal mantissa and exponent, EIP-55
casing for checksummed hex literals, `\xNN` escapes), `renderToks` joins
tokens with one space, and `Syn.print t L` renders the yield.

### Theorems

| Name | Statement |
|---|---|
| `parse_sound` | `parseWithLayout src = .ok (u, L) → ∃ ps, lex src = .ok ps ∧ Lexed src ps ∧ u.toks L = some (tokensOf ps) ∧ u.prec` |
| `parse_derives` | `parse src = .ok u → ∃ ps, lex src = .ok ps ∧ u.Derives (tokensOf ps) ∧ u.prec`: the grammar-derivation form of "`parse s = ok t` → `t` re-prints to `s`'s tokens" |
| `parseCat_sound`, `parseType_derives`, `parseExpr_derives` | the same for one category |
| `declCtors_covered` | **acceptance coverage**: each of the 21 type and declaration constructors (`elem`, `fnType`, `mapping`, `userType`, `array`, `param`, `struct`, `structMember`, `enum`, `udvt`, `stateVar`, `constant`, `event`, `eventParam`, `error`, `errorParam`, `usingPart`, `usingPath`, `usingAliases`, `usingAlias`, `topPart`) occurs in an accepted program of `declCorpus` |
| `declCorpus_accepted`, `declCorpus_in_profile` | the corpus is accepted and has no syntax-level rejection (`Syn.rejections`) |
| `recursive_struct`, `mutual_structs` | a struct mentioning itself (`S[]`, `mapping(uint => S)`), and two structs mentioning each other, have those edges in S00's declaration graph (`Syn.decls`, `Decl.refs`) |
| `print_text`, `print_roundtrip`, `print_checksum_flag` | the printed text of a parse; printing the corpus and parsing it again gives the same nodes and tokens; a checksum flag and unicode line-break/override bytes survive printing |

Witnesses (`decide +kernel`, `Solidity/Frontend/Checked/TypeExamples.lean`):
`type_array_of_array` (`uint[2][]` is a dynamic array of `uint256[2]`),
`type_mapping_named` (named keys and values), `type_function`,
`type_payable_path` (`address payable`, `a.b.C[]`, `fixed128x18`),
`type_attr_order` (one tree, two layouts), `stateVar_attr_order`,
`transient_soft` (`transient` is an attribute before a name and a name
before `;`), `type_second_visibility` (a second visibility ends a function
type's attributes and is the state variable's, as in solc's
`function_types_variable_visibility.sol`), data locations in parameters
(`declCorpus`), `import_empty_refused`. Tree witnesses compare nodes and yields (`sameTree`), since
`Syn` has no `DecidableEq` and elaborator `rfl` on whole units overflows the
stack.

Negative controls: `type_refused` (a payable mapping key, an unclosed
`[`, a repeated function-type attribute, a missing value type, an empty
`returns ()`, trailing tokens), `decl_refused` (repeated state-variable
attribute, empty struct and enum, a constant without value, a UDVT over a
non-elementary type, a non-user-definable operator), each with its offset.

### G09 Handoff

* **Theorems**: `parse_sound`, `parse_derives`, `parseType_derives`,
  `declCtors_covered`, `recursive_struct`, `print_roundtrip`.
* **Premises**: none. Axioms: `propext` for `parse_derives`, `parseType_derives`
  and `declCtors_covered` (pinned); `parse_sound` as well.
* **Status of the soundness statements**: translation validation. The
  parser is untrusted and `parse_sound` holds because `parseLocated` checks
  the yield; the assurance rests on `Syn.yield` being the grammar, a hand
  transcription reviewed clause by clause against `SolidityParser.g4` (G09
  finder review). Nothing here proves the parser accepts every grammatical
  input; the corpus regression (G11) measures that.
* **Remaining**: the yield is a transcription of the grammar per
  constructor, checked against the grammar only through S00's
  `grammarCtors` and the witnesses; that the printed text re-lexes to the
  same tokens is checked on witnesses and the corpus, not proved for every
  token; uniqueness of the parse for type names (that two trees with one
  yield are equal) is not proved. The greedy reading of a function type's
  attributes before a state variable's (`function () internal x;`) follows
  solc and is not part of `Syn.prec`.
* **Coverage scope**: `declCtors_covered` lists the type and data
  declaration constructors; the declarations with bodies (`contract`,
  `interface`, `library`, `inherit`, `function`, `modifier`, `constructor`,
  `fallback`, `fbNoParams`, `fbParams`, `receive`, `modInv`) and `varDecl`
  are G11's and covered by its whole-constructor theorem.
  `declCorpus_in_profile` is near vacuous for types: no type or
  declaration constructor triggers an S00 exclusion.
* `sameTree` compares pre-order constructors and yields under one layout;
  that it implies equality is not proved.
* **For S00**: `fallback() external returns (uint) {}` is grammatical
  (solc refuses it later, TypeError 5570) but has no S00 tree
  (`fbNoParams` carries no returns), so the parser refuses it. S00's `importPath`/`assembly` flags as
  `String` force non-ASCII import paths and flags to be refused (the
  bytes would not round-trip through `String`); a `Bytes` field would admit
  them.

### G09 Review

Finder (traced every type and declaration yield clause against
`SolidityParser.g4`, and the layout order of functions with string-literal
modifier arguments, fallbacks with returns, function-type state variables
and contracts with both headers; no mismatch). Fixed: a second visibility
after a function type was refused instead of ending the type (1:
`fnTypeAttrs`, `type_second_visibility`); a 40-digit hex literal whose
lowercase spelling is its checksum lost its cleared flag when printed (2);
unicode literals printed raw bytes the lexer refuses (3: `\xNN` for every
non-printable byte); empty import paths were accepted (4); docs (6, 7, 9),
an invariant comment (8). Recorded: `fallback() … returns` (5, For S00).

Skeptic: "partially supported". Fixed: data locations exercised (2), the
statement status reworded as translation validation (1), coverage scope and
the near-vacuous profile check stated (3, 4), the stale script name (5),
`sameTree`'s status (6), the docstring and a mutual-reference witness (7).
Recorded: printed text re-lexing is tested, not proved (5).

## G10: expressions

### Design

The parser reads expressions as solc's `parseExpression` does: a binary
expression by precedence climbing over solc's levels, then an assignment
(right side a whole expression) or a conditional (both branches whole
expressions); prefix operators take a unary expression; postfix index,
slice, member, call-options (only when `{` is followed by `identifier :`),
call and `++`/`--` chain on a primary. Primaries: identifiers, literals
(string fragments joined, recorded as a `frags` choice), numbers with a unit,
elementary type names (`elementaryTypeName[false]`: the tree carries the
proof that the type is not `address payable`), `payable(…)`, `type(T)`,
`new T`, tuples (`(e)` included, components possibly empty) and inline
arrays.

`Syn.prec` (`Solidity/Frontend/Checked/Prec.lean`) decides which of the trees
with one yield is meant: every node satisfies `Syn.precNode`, the binding
levels of the grammar's `expression` alternatives (`Syn.level`: assignment
0, conditional 1, `||` 2, `&&` 3, equality 4, order 5, `|` 6, `^` 7, `&` 8,
shifts 9, `+ -` 10, `* / %` 11, `**` 12, prefix 13, postfix `++ --` 14,
index/member/call 15, primaries 16) with left associativity except `**`,
`?:` and assignment. Where the grammar and solc's parser read one token
sequence differently the input is refused, so the accepted tree agrees with
both:

* `-x++`: the grammar reads `(-x)++` (UnaryPrefix is listed first), solc
  `-(x++)`;
* `x++.f`, `x++ ++`: the grammar accepts, solc's parser does not;
* `a ? b : c = d`: the grammar reads `(a ? b : c) = d`, solc `a ? b : (c = d)`
  (it occurs in solc's own accepted tests, `controlFlow/storageReturn/ternary_fine.sol`,
  which the corpus regression lists);
* `[]`: solc's parser accepts it (a type error later), the grammar does not;
* `type(address payable)`, `type(mapping(…))`, `type(function …)`: the
  grammar's `Type ( typeName )` accepts them, solc reads the argument as an
  expression and refuses them;
* a statement beginning with a tuple without an expression component
  (`() = f();`, `(,) = h();`): the grammar accepts, solc's statement parser
  refuses (ParserError 6933).

Greedy readings, as in solc: `new T[](n)` and `new a.B` keep `[]`/`.B` in
the type name (an index or member never has a `new` base).

### Theorems

| Name | Statement |
|---|---|
| `parseExpr_derives` | an accepted expression derives its tokens and satisfies `Syn.prec` |
| `parseExpr_prec_root` (with `Syn.prec_root`) | an accepted expression satisfies `Syn.precNode` at its root (and by `Syn.prec`, at every node) |
| `addSub_left_assoc`, `mul_left_assoc`, `or_left_assoc` | the right operand of a left-associative operator is never an operator of its level |
| `exp_right_assoc`, `assign_right_assoc`, `cond_right_assoc` | `**`, assignment and `?:` associate to the right |
| `mul_over_add`, `bit_levels`, `bitOr_over_order`, `addSub_levels`, `prefix_over_exp` | binding levels |
| `prefix_suffix_refused`, `cond_false_assign_refused`, `postfix_base` | the disagreements and solc-only refusals as precedence failures |
| `binary_levels` | for every binary constructor (quantified over its operator), `Syn.precNode` holds exactly when the operands are at the levels of its rule |
| `every_operator` | each of the 20 binary operators, 12 assignment operators, 6 prefix and 2 postfix operators, spelled out literally, parses into its constructor; `assignSpellings_complete` and `prefixSpellings_complete` check the lists cover S00's `AssignOp` and `PrefixOp` |
| `exprCtors_covered` | **acceptance coverage**: each of the 32 expression and argument constructors occurs in an accepted expression |

Witnesses (`decide +kernel`): `tree_precedence` (13 trees: `a + b * 2`,
`a - b - 2`, `a ** b ** 2`, `-a ** 2` as `(-a) ** 2`, chained assignment,
nested conditionals, `a = b ? 1 : 2`, the logical, bitwise and shift levels,
`!a.b()`, `a++ + ++b`, `delete a[1]`), `tree_forms` (19 trees: tuples with
empty components, `(a)`, `()`, inline arrays, slices `a[1:]`/`a[:b]`,
`a[]`, positional and named calls, call options, `new uint[](3)`,
`new a.B`, `type(C).max`, `payable(a)`, `address(this).balance`,
`x.address`, units, string concatenation, compound assignment).

Out of the profile: `expr_out_of_profile` (`>>>`, `>>>=` and `years` parse
and are rejected with `unsignedRightShift`/`removedUnits` by
`parseInProfile`, which admits a unit only when S00's `Syn.rejections` is
empty; `parseInProfile_sound`); `exprCorpus_in_profile`.

Negative controls: `expr_refused` (the two ambiguous forms `-a++` and
`a ? b : c = d`, the solc-only refusals `a++.f` and `a++ ++`, `type` of an
`address payable` or a mapping, an unclosed parenthesis, a trailing comma, a missing operand, an empty
inline array, empty call options, juxtaposed expressions,
`address payable(a)`), and `expr_parenthesized` (the parenthesized forms
are accepted).

### G10 Handoff

* **Theorems**: `parseExpr_derives`, `parseExpr_prec_root`, the
  associativity and level lemmas, `every_operator`, `exprCtors_covered`.
* **Premises**: none (axioms `propext`).
* **Status**: translation validation. The level lemmas are statements
  about `Syn.precNode`, and `Syn.prec` (checked on every accepted parse)
  applies it at the root (`parseExpr_prec_root`) and, by `Syn.all`'s
  definition, at every node; a lemma relating `Syn.all` to S00's subterm
  relation `Syn.Sub` is not proved. Grammatical ambiguities such as
  `a + b * c` are resolved by `Syn.prec`; that it selects exactly one tree
  is the unproved unambiguity below.
* `Syn.precNode` puts no condition on repeated call options
  (`f{a: 1}{b: 2}`), which solc's parser accepts and its type checker
  refuses.
* **Remaining**: unambiguity is not proved: that two trees satisfying
  `Syn.prec` with one yield are equal (so `Syn.prec` selects exactly one
  tree). It is checked on every witness and the corpus. Completeness (that
  the parser finds the `Syn.prec` tree whenever one exists) is not proved.
* **For S01**: `1._2` (G08) and `x.address` on a non-address are accepted
  syntax; their refusal is typing.

### G10 Review

Finder (traced against solc's syntax tests): precedence levels and
associativity match solc's token precedence and the grammar's alternatives;
no case where the parser's tree fails `Syn.prec` while another reading
passes. Fixed: `type(address payable)`, `type(mapping…)`, `type(function…)`
were accepted (1); a statement-start tuple without an expression
(`() = f();`) was accepted (2); `[]` recorded as a disagreement and an
unreachable branch merged (3); `a ? b = c : d = e` in solc's accepted tests
noted (4); docs (5).

Skeptic: "partially met". Fixed: the claim restated as translation
validation with the subterm step and unambiguity recorded (1, 2, 6); the
degenerate `cond_right_assoc`, the level lemmas quantified over operators and
both directions (`binary_levels`, `bit_levels`) (3); out-of-profile
expressions refused precisely (`expr_out_of_profile`, `parseInProfile`,
`exprCorpus_in_profile`) (4); literal operator spellings and completeness of
the operator lists (5); repeated call options noted (7).

## G11: statements, definitions and whole units

### Design

Statements are parsed in their context `SCtx` (S00's intrinsic `loop` and
`unchecked` flags): `break`/`continue` exist only inside a loop, an
`unchecked` block only as a block item outside another, so "break outside a
loop" and nested `unchecked` are parse refusals, located. The parser reads a
statement beginning with a type name followed by a data location or an
identifier as a declaration (`a.b c;`), a leading `(` as a tuple declaration
when one parses (`(uint a, , bool b) = f();`), `revert` followed by an
identifier as a revert statement, `emit`/`revert` targets as paths, call
options only before `identifier :` (so `try e {` opens the block), and the
`else` of `if (a) if (b) x; else y;` as the inner `if`'s (`Syn.prec`'s
`openIf` refuses the other tree). Definitions: functions (including
`fallback`/`receive` as names), modifiers with and without parameters,
constructors, `fallback`/`receive` definitions, state variables, structs,
enums, UDVTs, events, errors, `using`; contracts (`abstract`, `layout at`,
`is` with arguments, either order), interfaces, libraries; pragmas (S00's
word lists), the three import forms; assembly with dialect, flags and a Yul
body (all of S00's Yul constructors).

**Admission at the syntax level.** `parseInProfile` admits a parsed unit
only when S00's precise rejection `Syn.rejections` is empty, and refuses
with the manifest ids of the excluded constructs (assembly other than the
canonical rethrow, `layout at` with a non-literal base, `>>>`, `years`,
`pragma experimental solidity`, invalid modifier bodies).

**The G05 parse stage** (`Solidity/Frontend/Checked/Certificate.lean`):
`Units` (one tree per source unit, named), `UnitParses`/`Parses` (each
unit's bytes lex and its tree derives the tokens under some layout and
satisfies `Syn.prec`), `parseChecker : Checker Input Units Parses` (the
certificate is the layouts; `check` re-lexes the bytes and compares the
yields; `sound` by `checkUnits_sound`), the untrusted `produce` with
`produce_accepted`, and `FrontendSpec.ofParse` / `FrontendSpec.ofParse_checker`
fixing a `FrontendSpec`'s syntax and parse relation for the later stages.
The checker reads bytes, never a digest.

### Theorems

| Name | Statement |
|---|---|
| `parse_sound`, `parse_derives` | whole-source parsing (from G09): an accepted unit derives its tokens and satisfies `Syn.prec` |
| `parseInProfile_sound` | an admitted unit is a parse with no syntax-level rejection |
| `checkUnits_sound`, `parseChecker` | G05's parse-stage `Checker`: acceptance implies `Parses` |
| `produce_accepted` | the producer's output is accepted by the checker |
| `allCtors_covered` | **every one of S00's 112 constructors** occurs in an accepted program of the lane's corpora |
| `profileCtors_covered` | every constructor except the 11 Yul constructors outside the canonical rethrow occurs in an accepted, in-profile program |
| `unitCorpus_in_profile`, `yul_rejected`, `unit_out_of_profile` | the statement corpus is admitted; assembly (not the rethrow), `layout at f()` and `years` are refused with their features |
| `dangling_else`, `decl_or_expr` | the `else` binds to the nearest `if`; declaration versus expression statements; `revert E();` versus `revert("x");` |
| `demo_parses`, `demo_wrong`, `demo_named_base` | a two-unit input is produced and accepted by the G05 checker; the units' trees swapped under the right names are refused by the yield comparison; a hand-made tree with named base arguments (which the parser never returns) is refused by `Syn.prec`'s node conditions |

Negative controls (`unit_refused`): `break` outside a loop, a function
definition inside a block, nested `unchecked`, `unchecked` as an `if` body,
`try` without `catch`, a `virtual` constructor, `fallback()` with returns,
a repeated `receive` attribute, an empty `is`, an unterminated pragma, a
malformed Yul `let`, `() = g();` and `(,) = g();`, each with its offset.

### Corpus regression

`scripts/parse-corpus.mjs prepare` extracts solc 0.8.38's
`test/libsolidity/syntaxTests` from `tests/upstream/solidity-0.8.38.tar.gz`,
splits multi-source tests at `==== Source: … ====`, and adds every `.sol`
file under `tests/` (those under `illegal/` or `nocompile/` expected
refused); elaborating `scripts/ParseCorpus.lean` from the repository root
(open it in the Lean server, or `lake env lean scripts/ParseCorpus.lean`)
parses every unit, prints each accepted one and parses it again; `node
scripts/parse-corpus.mjs report` counts against solc's expectation and
compares with the baseline `tests/parse-corpus/baseline.json` (`--write`
records it). A syntax test is expected refused exactly when its
expectations list a `ParserError` other than 6275 (an import source not
found, the import resolver's). Every disagreement is listed in the
baseline with a reason; the report fails when one has none.

Results (4056 units; the interpreted run takes about five minutes):

| Corpus | Expected | Accepted | Refused |
|---|---|---|---|
| solc syntax tests (3542) | accepted (3208) | 3126 | 82 |
| | refused (334) | 45 | 289 |
| repository `.sol` (236) | accepted (222) | 221 | 1 |
| | refused (14) | 13 | 1 |

Round trip (print each accepted unit, parse it again, compare nodes and
tokens): 0 failures over the 3405 accepted tests.

The 141 disagreements, by reason (the reasons of
`scripts/parse-corpus.mjs`, each applied only in its direction):

| Count | Reason |
|---|---|
| 19 | pragma: version and pragma words are S01's settings check; S00 keeps the words |
| 18 | Yul analysis (builtin and reserved names): assembly is outside the profile (parseInProfile) |
| 15 | fallback/receive form without an S00 tree (solc refuses it later) |
| 13 | repository negative example: refused by solc's later stages, not its parser |
| 10 | parameter attribute other than a data location: grammar refuses (solc later) |
| 9 | constructor attributes without an S00 tree (solc refuses them later) |
| 9 | UDVT over a non-elementary type: grammar refuses (solc later) |
| 7 | Yul dotted names in declarations: grammar refuses (solc later) |
| 7 | SPDX license comment: trivia here, checked by solc's parser |
| 6 | file-level constant without value or non-constant: S00's constant needs `constant … = e` |
| 6 | `type(…)` of an expression: S00's metaType takes a type name |
| 6 | solc's syntax checker, a later stage: intrinsic in S00 (SCtx) or the grammar |
| 4 | abstract interface/library or library inheritance: no S00 tree (grammar refuses) |
| 3 | grammar/solc disagreement refused by Syn.prec |
| 3 | misplaced `_` in a number: solc's syntax checker, refused by the lexer |
| 2 | `[]`: grammar refuses (solc later) |
| 2 | `catch Name()` with no parameters: no S00 tree |
| 1 | Yul multi-variable assignment from a non-call: grammar refuses (solc later) |
| 1 | solc's nesting-depth limit |

No disagreement is a refusal by this parser of a program that solc
compiles: every "expected accepted, refused" test fails in a later solc
stage, except the three `Syn.prec` refusals of grammar/solc disagreements
and the S00-representation gaps listed.

### G11 Handoff

* **Theorems**: `parse_sound`, `parse_derives`, `parseInProfile_sound`,
  `checkUnits_sound`, `produce_accepted`, `allCtors_covered`,
  `profileCtors_covered`.
* **Premises**: none.
* **G05**: the parse stage of `Chain` is `parseChecker` (or
  `FrontendSpec.ofParse_checker`); the raw-input check (`Input.Ok`), the
  resolution and metadata stages are S01/G12–G15's.
* **The parse stage provides** G05's `Checker.sound` and the producer's
  `accepted` (`produce_accepted`, `produceOpt_accepted`); `Checked.complete`
  (every admitted input produced) is not provided, since the parser's
  completeness is open and `Parses` is not proved functional.
  `FrontendSpec.ofParse` only packages the syntax and parse relation.
* **For G15** (admission, the solc-JSON adapter): the checked trees are
  S00's, so the adapter's equivalence is between `Syn .unit` (per unit,
  `Units`) and the imported program. G15 needs from this lane: `parse`
  /`parseWithLayout` per unit, `Parses` as the parse relation, the
  classified disagreements of the corpus regression above (each with its
  reason in `tests/parse-corpus/baseline.json`), and `parseInProfile` for
  the syntax-level profile. **Blockers for G15**, not provided here: a
  located yield (`tokens` gives each token's byte range, but the tree
  carries none, so solc's `src` fields cannot yet be related to nodes) and
  the uniqueness of the precedence tree (without it `Parses` may relate an
  input to more than one tree).
* **For S00**: solc's parser accepts, and a later stage refuses, forms S00
  has no tree for, so this parser refuses them: `fallback() … returns (…)`,
  `receive` with parameters or returns, a non-`external` `fallback`,
  `abstract interface`/`abstract library` and library inheritance,
  `constant`/`immutable`/mutabilities on parameters, constructor attributes
  beyond `payable` and visibility, UDVTs over non-elementary types,
  file-level constants without a value, `catch Name()` with no parameters,
  an empty struct, `[]`, `type(expression)`.
* **For S01**: `1._2` (a member `_2` of the literal `1`, G08) and
  `x.address` on a non-address are accepted syntax; their refusal is
  typing.
* **Remaining**: completeness and unambiguity (G09, G10); the statement
  disagreements of the corpus.

### G11 Review

Finder: layout order and the producer/checker agreement confirmed; corpus
extraction (`// ----`, `==== Source:`, latin1 bytes, 6275) confirmed.
Fixed: the parser-only refusals (named modifier and base arguments, empty
import paths, statement-start empty tuples, `type(…)` of non-expression
types) moved into `Syn.precNode`, so `Parses` and the checker refuse them on
hand-made trees too (1: `demo_named_base`); a stronger `demo_wrong` (2);
Yul expression statements, multi-variable right sides and empty `switch` as
node conditions (3); corpus reasons apply only in their direction and,
where possible, to the parser's message (4); stale script comments (5); the
S00 and S01 handoff lists (7); `() + 1;` (9, by the same node condition).
Recorded: refusal locations are not compared with solc's (6).

Skeptic: "partially met". Fixed: `UnitParses` carries the lexer's
certificate `Lexed`, which the checker checks (2); the parse stage's `sound`
and `accepted` stated, `complete` recorded as not provided, `produceOpt` for
`Chain.frontend` (3); `FrontendSpec.ofParse` described as packaging (4);
the expectation rule's exceptions and per-disagreement reasons, `illegal/`
and `nocompile/` files expected refused (5, 6); the baseline regenerated,
the counts filled in, the rule stated exactly (7); one canonical Lean step
without a duplicate `main` (8); `profileCtors_covered` over
`parseInProfile` (9); the G15 blockers (located yield, uniqueness) stated as
blockers (10). Recorded: completeness and uniqueness (1).

## Reviews

Each checkpoint ended with a read-only finder and a separate skeptic review
(no Lean server); the confirmed findings and their fixes are recorded in the
checkpoint's Review section above.
