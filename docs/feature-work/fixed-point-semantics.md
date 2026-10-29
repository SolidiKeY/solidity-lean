# Fixed-point types — reference semantics

The user decided full fixed-point support, beyond the acceptance boundary of
pinned solc 0.8.38 ([G00 Q6](../solidity-scope.md#user-decisions-2026-10-29)).
solc 0.8.38 type-checks `fixedMxN`/`ufixedMxN` but generates no code for them
(`UnimplementedFeatureError 1834: Fixed point types not implemented.`), so
there is no compiler behaviour to align with. This document fixes what "full
support" means: the language rules collected from the pinned specification
(§1), the reference values and operations in
`Solidity/Language/FixedPoint.lean` (§2), the choices where the
specification is silent (§3), and the roadmap owners of the remaining work
(§4). Nothing is wired into the AST, the elaborator, the compiler or the
feature manifest.

- **Base revision:** `caf52ecd4dde5d37cbc0098d47de1a01aa218285`
  ("Record resource and environment decisions").
- **Branch:** `cloud/roadmap-w1-20261029/fixed-point-semantics`.
- **Deliverables:** this document; `Solidity/Language/FixedPoint.lean`
  (imports nothing), registered in `Solidity.lean`; one row each in
  [module-map.md](../module-map.md), [README.md](../README.md) and one status
  paragraph in [coverage-plan.md](../coverage-plan.md).

## Sources

The pinned tarball `tests/upstream/solidity-0.8.38.tar.gz` holds the upstream
`test/` tree only (11,622 files; no `docs/`, no grammar, no compiler
sources). The syntax tests below come from it. The specification text and
the compiler sources were fetched from the `v0.8.38` tag of
`github.com/ethereum/solidity` (raw files, 2026-10-29) and are not checked
in; their SHA-256 digests:

| File at `v0.8.38` | SHA-256 |
|---|---|
| `docs/types/value-types.rst` | `714def57cf5e3bd205bdf89623ddde41519d4324bb72bb3465ea79852841998b` |
| `docs/abi-spec.rst` | `bda1c34bf57f3c63e426486e688bf24feda1c8fe439209df1cb4dec8c884eb79` |
| `docs/grammar/SolidityLexer.g4` | `b6eb8ffcb358b8a854b22ed0e3df6ced8c42760a3da4f77899ba9c65a6dd7132` |
| `docs/grammar/SolidityParser.g4` | `663afb0d91d482a886a6879c801ba6b6f83f34e250d3e8d9406b1ab198272b6a` |
| `liblangutil/Token.cpp` | `bed6f977029f8f3a986d850496c9812897a30472af931ced7201755e27cd3c8b` |
| `libsolidity/ast/Types.cpp` | `12dc5df7741a2b9b97d5e2eb1dcafa2e83025b6f0faf92d08fc00b5235cd1277` |
| `libsolidity/ast/Types.h` | `11e7b27488c8160dcbe3e950de56dc0cfe08f6b770cb4ddb027a561228d59f7c` |
| `libsolidity/analysis/TypeChecker.cpp` | `20d4db6a5c37df65d4c6e23af2f541e79a0c35552ce73a5838f5a7de5ab3eb63` |
| `libsolidity/analysis/ConstantEvaluator.cpp` | `291adc577e2e83c50977280be73820407b27128685b55ec59cef41f3192abe60` |
| `libsolidity/codegen/YulUtilFunctions.cpp` | `11f70e2d35a52821a7a7c2ee8a4eb46684a6e912891662c7e404f67cb1626507` |
| `liblangutil/Token.h` | `9cd4b25d34af461e8396bbf45806aadbf4810d552e91cd0e60fdb7b1e419e8fd` |
| `docs/types/conversion.rst` | `30f233dd96d65d4f74ddaf4125389d43cfb27a46baca3256a8a89248d01a5015` |
| `docs/control-structures.rst` | `4f1954c3a09ddcebdf16221578c5b036f479b8a07608b0b931fa34137182ad6b` |

Compiler behaviour below is **by source reading**: running solc 0.8.38 was
not possible in this session (`binaries.soliditylang.org` is not reachable;
running a downloaded binary was refused), so no row is confirmed by
execution except where an upstream syntax test states the diagnostic.
Recording these files in `tests/upstream/snapshot.json` (or a sibling
snapshot) is a child obligation of G00 (§5).

## 1. The language specification

`file:line` references are to the files above at `v0.8.38`; test paths are
under `test/libsolidity/` in the tarball.

| Topic | Specification | Compiler (source reading) and tests |
|---|---|---|
| Spellings | `fixed`/`ufixed`, `fixedMxN`/`ufixedMxN`; `fixed`, `ufixed` alias `fixed128x18`, `ufixed128x18` (`value-types.rst:161–170`). | `Token.cpp:192–262`. |
| M and N | `M` divisible by 8, 8 … 256; `N` 0 … 80 inclusive (`value-types.rst:169`). The ABI spec says `0 < N <= 80` (`abi-spec.rst:66–67`). The ANTLR lexer allows only `[1-9][0-9]*` for M and N in `fixed`, and two or more digits in `ufixed` (`SolidityLexer.g4:37,94`). | The scanner is authoritative: `8 ≤ M ≤ 256`, `M % 8 = 0`, `0 ≤ N ≤ 80`, shortest decimal spelling (no leading zero); anything else is an **identifier**, not an error (`Token.cpp:192–262`). Tests: `syntaxTests/types/weird_sized_types.sol` (`fixed0x0`, `fixed01x1`, … are identifiers), `nameAndTypeResolution/298_…0x7_mxn.sol`, `300_…7x8_mxn.sol`, `302_invalid_fixed_type_long.sol` (DeclarationError 7920), `parsing/declaring_fixed_and_ufixed_variables.sol` (`fixed40x40`, `ufixed8x8`, `fixed32x32`). |
| Value | — (the language doc gives no value set). ABI: `fixed<M>x<N>` "denotes the value `v` as `v / (10 ** N)`" (`abi-spec.rst:66–67`). | `FixedPointType` range: the `M`-bit integer, signed or unsigned, divided by `10^N` (`Types.cpp:826–841`, `maxIntegerValue`/`minIntegerValue`; `RationalNumberType::isImplicitlyConvertibleTo`, `Types.cpp:1018–1031`, checks a fractional literal's scaled integer against `M` bits and an integer literal against `min/maxIntegerValue`). Tests: `types/rational_number_literal_to_fixed_implicit.sol` (`fixed8x1` holds `-12.8` and `12.7`, `ufixed8x2` holds `2.55`), `parsing/declaring_fixed_literal_variables.sol` (`fixed40x40` cannot hold `3.14`). |
| Literals | A decimal literal with a `.` "has fixed point type" (`SolidityLexer.g4:238–240`). | A literal is a `RationalNumberType`; a fractional literal's mobile type takes as many digits as fit in 256 bits (at most 80), rounds **toward zero** there, then the fewest bytes (`Types.cpp:1231–1267`); an integer literal's mobile type is an integer type. Implicit conversion of a literal requires an exact scaled integer that fits, and a non-negative literal for `ufixed` (`Types.cpp:1018–1031`). Tests: `nameAndTypeResolution/313_fixed_type_size_capabilities.sol`, `316_…_lost_data.sol` (`1/3` not implicit to `ufixed256x1`), `328_rational_to_fixed_literal_expression.sol`, `denominations/fixed_point_division.sol`. |
| Operators | Comparisons `<= < == != >= >`; arithmetic `+ -`, unary `-`, `* / %` (`value-types.rst:172–175`). | `FixedPointType::unaryOperatorResult` admits `-`, `++`, `--`, `delete` — unary `-` **also at `ufixed`**, unlike `IntegerType` (`Types.cpp:793–810`). `binaryOperatorResult` refuses bit operators `\| ^ & ~`, boolean operators and `**`, and admits the rest at the common type (`Types.cpp:843–856`) — this does **not** exclude the shifts `<< >> >>>` (`Token.h:302,306`), which `IntegerType` filters through `isValidShiftAndAmountType` (`Types.cpp:573–577` disables `>>>`). Test: `smtCheckerTests/operators/shifts/shr_unused.sol` (`x >>> 6` at `fixed` passes the type checker and stops in code generation). `**` with a fixed exponent is refused (`nameAndTypeResolution/333_…_15.sol`, `334_…_neg.sol`). Mixed integer/fixed operands run at the common type (`343_integer_and_fixed_interaction.sol`). |
| Checked vs unchecked | Silent for fixed-point. Integers: checked overflow `Panic(0x11)`, division or modulo by zero `Panic(0x12)` (`control-structures.rst:640–641`), the latter not disabled by `unchecked { }` (`value-types.rst:122,142`); wrapping in `unchecked { }`. | No code generation. |
| Rounding | Silent for runtime arithmetic. | Compile-time literals round toward zero (`Types.cpp:1249`, "we round towards zero"); rational `%` is `a - b·trunc(a/b)` (`ConstantEvaluator.cpp:105–114`). |
| Implicit conversions | General rule: implicit only "if it makes sense semantically and no information is lost" (`conversion.rst:14`). | Fixed→fixed: target has ≥ N digits, ≥ M bits, and an integer-part range that contains the source's (`Types.cpp:773–786`). Integer→fixed: the integer's range inside the integer-part range (`Types.cpp:615–619`). Fixed→integer never (`306_invalid_int_implicit_conversion_from_fixed.sol`); fixed→`bytes32` never (`322_fixed_to_bytes_implicit_conversion.sol`); `315_…_size.sol` ("Too many fractional digits"). |
| Explicit conversions | Silent. | Fixed→any fixed, fixed→any integer (`Types.cpp:788–791`); integer→fixed where the implicit conversion exists (`Types.cpp:626–627`) and at the same signedness and width (`Types.cpp:639–640`); `bytesM`→fixed at the same width (`Types.cpp:1367–1368`); literal→fixed through its mobile type (`Types.cpp:1039–1062`). Test: `317_fixed_type_valid_explicit_conversions.sol` (`ufixed8x1(1/3)`). |
| ABI | `enc(X)` is `enc(X·10^N)` read as `int256` (signed) or `uint256` (`abi-spec.rst:218–221`); selectors use `fixed128x18`/`ufixed128x18` for the aliases (`abi-spec.rst:71–72`); packed mode concatenates types shorter than 32 bytes without padding (`abi-spec.rst:755`). | `calldataEncodedSize` 32 (padded) or `M/8` (`Types.h:551`). Cleanup and conversion code is unimplemented (`YulUtilFunctions.cpp:3994–3995`, `cleanupFunction`; `3560–3564`, `3589–3590`, `conversionFunction`), as are left alignment (`400–401`) and typed shifts (`554`, `577`). |
| Storage | Silent. | `storageBytes = M/8`, `leftAligned = false`, a value type (`Types.h:552–554`): packed like `intM`. Tests place fixed types in structs, arrays and mapping keys (`324_fixed_points_inside_structs.sol`, `inlineArrays/inline_array_fixed_types.sol`, `323_mapping_with_fixed_literal.sol`), all UnimplementedFeatureError. |
| Other | — | `type(T)` refused for a fixed `T` (error 4259, "An enum type, contract type or an integer type is required", `TypeChecker.cpp:217–223`); inline assembly access to a fixed variable is *unimplemented* (`unimplementedFeatureError` 5016, `TypeChecker.cpp:809–816`), not a type error; `type MyFixed is fixed;` is accepted with no diagnostic (`syntaxTests/userDefinedValueType/all_value_types.sol`). |

### Findings

- **F1 — solc's implicit fixed→fixed test is lossy.** It compares integer
  parts only. `fixed8x3 → ufixed8x3` is accepted (both integer parts are
  `0`, since `minIntegerValue` truncates `-0.128` to `0`) though `-0.128` has
  no `ufixed8x3` value; `ufixed8x3 → ufixed8x4` is accepted though `0.255`
  exceeds `ufixed8x4`'s `0.0255`. A sweep over same-signedness pairs with
  `M ≤ 128`, `N < 40` found 34,929 accepted pairs that do not contain the
  source range, and the opposite-signedness pairs (like the first example)
  69,269 more (104,198 in all; both reviewers reproduced the counts with an
  independent script). The sweep compares solc's test, computed with
  truncating division as in `Types.cpp:826–841`, with containment of the
  scaled bounds after multiplying by `10^(N'−N)`. The Lean witness is `Fx.solc_lossy` (kernel-checked). This
  contradicts the documented rule "no information is lost" (Q1).
- **F2 — the shifts `<< >> >>>` are not excluded** by
  `FixedPointType::binaryOperatorResult` (source reading). The amount goes
  through the common type too, so `x << 2` shifts by a fixed-point amount.
  The upstream test `smtCheckerTests/operators/shifts/shr_unused.sol`
  (`fixed x; assert(x >>> 6 == 0);`) passes the type checker and fails in
  code generation (`YulUtilFunctions.cpp:577`). The documentation lists only
  comparisons and arithmetic (Q4).
- **F3 — unary `-` is admitted at `ufixed`**, as at no unsigned integer type
  (Q5).
- **F4 — `N = 0`.** The language and the scanner admit `fixedMx0`; the ABI
  spec says `0 < N`. Proposal P4 below.
- **F5 — the ANTLR lexer disagrees with the scanner** on single-digit `M`/`N`
  (`ufixed8x1` is not an `Ufixed` token in `SolidityLexer.g4:94`) and on
  `N = 0` (`fixed8x0` is not a `Fixed` token, `SolidityLexer.g4:37`). The scanner
  (what solc runs) wins; S00/G08 should record the grammar as non-normative
  here.

## 2. The reference model (`Solidity/Language/FixedPoint.lean`)

Namespace `Solidity.Language.FixedPoint`. The module imports nothing; the
values are intrinsic, as [intrinsic.md](../intrinsic.md) requires.

**Types and values.**

- `FxTy` — `signed`, `bits` (M), `digits` (N) and the proof `valid` of the
  scanner bounds; `FxTy.mk?` builds one exactly for the (M, N) the scanner
  admits (the shortest-spelling rule is the lexer's, G08); `FxTy.fixed`, `FxTy.ufixed` are the aliases; `FxTy.name` the
  canonical (selector) name; `FxTy.scale` = `10^N`; `FxTy.lo`/`FxTy.hi` the
  `M`-bit bounds; `FxTy.inRange`; `FxTy.storageBytes` = `M/8`;
  `FxTy.maxInt`/`FxTy.minInt` solc's integer-part bounds.
- `Fx t` — `{v : Int // t.inRange v = true}`: the scaled integer `v`, denoting
  `v / 10^N`. `Fx.zero` is the default and what `delete` writes.
- `Fail` — `overflow` (`Fail.panicCode` = `0x11`) and `divZero` (`0x12`), the
  `Panic(uint256)` codes the observation of G01 Q5 must carry. `Mode` —
  `checked` (default) or `unchecked`.

**Operations** (all at one type; two fixed operands first convert to
`FxTy.common?`; an integer operand converts to the fixed type when
`FxTy.intImplicit` admits it, exactly by `Fx.ofInteger_inRange`, and
otherwise the operation is refused, as solc's `Type::commonType` refuses
`uint256 + fixed`):

| Operation | Definition | Failure |
|---|---|---|
| `Fx.add`, `Fx.sub`, `Fx.neg` | `a + b`, `a - b`, `-a` on scaled integers | checked: `overflow` outside the range; unchecked: wrap modulo `2^M` (`Fx.wrap`) |
| `Fx.mul` | `tdiv (a·b) 10^N` (exact product, extra digits truncated toward zero; Q8) | as above |
| `Fx.div` | `tdiv (a·10^N) b` | `divZero` if `b = 0` (both modes), else as above |
| `Fx.mod` | `tmod a b` (sign of `a`) | `divZero` if `b = 0`; never overflows (`Fx.mod_inRange`) |
| `Fx.inc`, `Fx.dec` | `a ± 10^N` (the value `1`) | as `add` |
| `Fx.lt`, `Fx.le` (and `== != > >=` likewise) | integer order of the scaled integers | — |
| `Fx.implicit` | along `FxTy.subsumes`: `a · 10^(N'−N)` | total |
| `Fx.explicit m` | `Fx.rescale` (truncate toward zero when digits drop), then ranged by `m` | per Q2 |
| `Fx.ofIntegerExplicit m`, `Fx.ofBits` | integer → fixed by value; `bytesM` → fixed by bit pattern (Q7) | per Q2 / total |
| `Fx.toIntTrunc` | fixed → integer by value (Q7): `tdiv a 10^N`, then the integer conversion | — |
| `Fx.ofLiteral?`, `Fx.literalTrunc` | implicit literal (exact or refused); explicit literal folded exactly at the target's N (P1) | — |
| `Fx.toWord`, `Fx.ofWord?` | ABI word (two's complement mod `2^256`); decoding range-checks (P5) | `none` = decoding revert |

**Theorems** (premises in parentheses; all checked by the Lean server with
`propext`, `Classical.choice`, `Quot.sound` at most — `#print axioms` on
`Fx.ofWord_toWord`, `Fx.solc_lossy`, `Fx.mod_eq`, `Fx.ofInteger_inRange`,
`Fx.implicit_lt`; `Fx.solc_lossy` uses none):

- `Fx.wrapInt_inRange`, `Fx.wrapInt_of_inRange` (`t.inRange v`),
  `Fx.wrapInt_emod` — wrapping lands in range, keeps an in-range integer, and
  is the identity modulo `2^M`.
- `Fx.result_of_inRange` (`t.inRange v`) — an in-range result is exact in
  both modes; `Fx.result_checked_overflow` (`t.inRange v = false`).
- `Fx.add_eq` (`t.inRange (a.1 + b.1)`) — **addition agrees with scaled
  integer addition when it does not overflow**, in either mode;
  `Fx.add_overflow` (`t.inRange (a.1 + b.1) = false`) — checked addition
  panics `0x11`; `Fx.add_unchecked` — unchecked addition wraps; `Fx.sub_eq`
  likewise; `Fx.add_comm`, `Fx.mul_comm`, `Fx.add_zero`.
- `Fx.mul_one` (`t.inRange t.scale`: the type holds `1`).
- `Fx.div_zero`, `Fx.mod_zero` — `Panic(0x12)` in either mode; `Fx.div_eq`
  (`b.1 ≠ 0`, result in range); `Fx.tmod_between`, `Fx.mod_inRange`,
  `Fx.mod_eq` (`b.1 ≠ 0`).
- `Fx.lt_iff`; `Fx.implicit_sameValue`, `Fx.implicit_lt`
  (`t.subsumes t'`) — the implicit conversion keeps the number and the order;
  `Fx.inRange_mul_of_subsumes`; `Fx.explicit_of_subsumes` — the explicit
  conversion is the implicit one where that exists, in either mode.
- `Fx.ofInteger_inRange` (`t.intImplicit lo hi`, `lo ≤ k ≤ hi`) — solc's
  implicit integer→fixed test is exact: such a conversion never fails;
  `Fx.ofIntegerExplicit_of_implicit`.
- `Fx.toWord_range`, `Fx.ofWord_toWord` — ABI decoding inverts encoding;
  `Fx.pow_bits_le`.
- `Fx.solc_lossy` (F1), plus `example`s: scanner bounds, the upstream literal
  tests, truncating division (`1.00/3.00 = 0.33`, `-1.00/3.00 = -0.33`),
  `-(-12.8)` overflowing at `fixed8x1` and wrapping unchecked, checked and
  wrapping multiplication, `-3.50 % 1.00 = -0.50`.

## 3. Choices where the specification is silent

Proposals that follow from solc's documented integer rules, a recorded
decision or a confirmed exclusion, and need no user decision:

- **P1 — literals fold exactly.** An explicit conversion of a literal rounds
  the exact rational at the *target's* N (`Fx.literalTrunc`), not through
  solc's mobile type (which first rounds at its own N; for
  `ufixed256x80(1/3)` that type has 77 digits). This follows "fold rational
  constants exactly" ([solidity-scope.md](../solidity-scope.md#what-belongs-in-the-model)).
  An out-of-range explicit literal is Q2.
- **P2 — division by zero** panics `0x12` in checked and unchecked code, as
  solc's integer `/` and `%` do (`control-structures.rst:640–641`,
  `value-types.rst:122,142`), and G01 Q5 observes the code exactly. This
  departs from the current core, which reads both `0x11` and `0x12` as a
  plain revert ([solc-alignment.md](../solc-alignment.md), "Division" and
  `checked { }` rows); the same G01 Q5 revision applies to integers.
- **P3 — unchecked** arithmetic wraps the (Q8) result modulo `2^M`, as
  `unchecked` integers wrap at their width.
- **P4 — `N = 0`** is a type (scanner), with ABI name `fixedMx0`
  (`FxTy.name`), encoded as an `intM`/`uintM` word.
- **P5 — ABI decoding** reverts on a word that is not the sign- or
  zero-extension of an `M`-bit integer, as solc's decoder does for
  `intM`/`uintM`; packed encoding is the `M/8`-byte two's complement.
- **P6 — storage** packs `M/8` bytes right-aligned like `intM`; physical
  layout stays unobservable ([solidity-scope.md](../solidity-scope.md#user-decisions-2026-10-29),
  "Readings"). A mapping key hashes as its padded ABI word.
- **P7 — common type** of two fixed operands is solc's `Type::commonType`
  over the (Q1) implicit conversion (`FxTy.common?`); an integer operand
  converts when solc's integer test admits it, exactly
  (`Fx.ofInteger_inRange`).
- **P8 — as in solc's type checker:** no `**` with fixed operands, no bit
  operators, no `type(T)` for a fixed `T`; a UDVT over a fixed type
  wraps/unwraps by identity. Inline-assembly access to a fixed variable,
  which solc reports as unimplemented rather than refuses, falls under the
  confirmed assembly/Yul exclusion (G00 Q1).

Decisions the user must make (also in the handoff block):

- **Q1 [Implicit]** solc's implicit fixed→fixed test accepts lossy
  conversions (F1). Options: *exact subset* — accept only solc's pairs whose
  range is contained (`FxTy.implicitOK`), refusing e.g. `fixed8x3 →
  ufixed8x3` (Recommended: solc's documented rule is that an implicit
  conversion loses no information, `conversion.rst:14`, and the program can
  still say `ufixed8x3(x)` explicitly, so no computation becomes
  inexpressible); *solc's set, checked* — accept all of solc's pairs and
  panic `0x11` on a value that does not fit; *solc's set, wrapping* —
  accept all and wrap. Note that the recommended option **narrows** solc's
  type-checker acceptance (and, through P7, the mixed operations it
  admits); G00 Q6 asks for support beyond solc's *compiled* boundary, which
  for these programs is empty, so the choice is the user's.
- **Q2 [Explicit]** An explicit conversion whose value does not fit.
  Options: *wrap at run time, reject out-of-range constants at compile
  time* (Recommended: solc's integer rules — explicit conversions of values
  cut higher-order bits and never fail, `conversion.rst:61`, while an
  explicit conversion of an out-of-range literal to an integer type is a
  type error, `Types.cpp:1054–1055`; for fixed, solc accepts e.g.
  `ufixed8x1(100.5)` through the mobile type); *wrap everywhere*, constants
  included; *panic `0x11` at run time*, rejecting constants.
- **Q3 [Rounding]** `*`, `/` and digit-dropping conversions. Options:
  *toward zero* (Recommended: solc's literal rounding, integer `/`, and
  rational `%` all truncate toward zero); *toward −∞*; *half-to-even*.
- **Q4 [Shifts]** `<<`, `>>`, `>>>` with fixed operands (F2). Options:
  *reject* (Recommended: the documented operator list omits them, integers
  reject `>>>`, and solc's typing would make the shift amount a fixed-point
  value, which has no defined meaning); *shift the scaled integer by an
  integer amount* as for `intM`, rejecting `>>>`.
- **Q5 [UfixedNeg]** unary `-` at `ufixed` (F3). Options: *accept as solc's
  type checker does* (encoded: `0x11` unless the operand is `0`, wraps in
  `unchecked`; Recommended: G00 Q6 asks for support beyond solc's boundary,
  and this keeps every program solc's type checker accepts); *reject* as for
  `uintM`.
- **Q6 [IncDec]** `++`/`--` (spec silent). Options: *add the value 1*
  (encoded, `Fx.inc`; agrees with `x += 1` wherever the literal `1`
  converts; at types without `1`, such as `fixed8x3`, `++x` type-checks and
  always panics `0x11`); *add one unit in the last place* (`10^−N`). No
  recommendation: the evidence (solc admits `++` at every fixed type) fits
  both.
- **Q7 [Reinterpret]** explicit conversions between fixed and integer types,
  and `bytesM`→fixed. Options: *integers by value, `bytesM` by bit pattern*
  (encoded: `Fx.ofIntegerExplicit`, `Fx.toIntTrunc`, `Fx.ofBits`; by value
  the explicit conversion agrees with the implicit one wherever both exist,
  `Fx.ofIntegerExplicit_of_implicit`; with Q2 = wrap, `fixed256x18(int256 x)`
  then wraps for most `x`); *by bit pattern* — the same-width,
  same-signedness shape solc admits is the shape of its bit-preserving
  conversions such as `uint160`↔`bytes20`, with the value reading only where
  the implicit conversion exists (hybrid); *by value throughout*
  (`bytesM` read as its unsigned integer). No recommendation: the evidence
  points both ways.
- **Q8 [Intermediate]** `*` and `/`: the result of the exact product or
  quotient, truncated (encoded; P3 then wraps that result in `unchecked`),
  or the EVM-native `((a·b) mod 2^256) / 10^N`. Options: *exact*
  (Recommended: the ABI spec defines the value `v / 10^N`, and only the
  exact reading makes checked `*` fail exactly when the true result does not
  fit; cost: a 512-bit multiply-divide in G25); *word-native*, with overflow
  of the intermediate a `0x11` panic in checked code.

The Lean model keeps both variants where Q2 is open (`Mode` on
`Fx.explicit`/`Fx.ofIntegerExplicit`) and encodes the stated option for the
others; changing an answer changes one definition.

## 4. Owners

The `fixedPoint` manifest row (`docs/solidity-features.json`, scope
`upstream`) is owned by the sibling task g00-manifest-rev. For it: the row
should move to `model`, cite this document and `Solidity/Language/FixedPoint.lean`
as local evidence, and list the owners below; the in-profile count changes
with it. This task did not edit the manifest.

| Work | Groups | What |
|---|---|---|
| Admission | S00, G08, G09, G10, G11, G15 | Scanner bounds and shortest spelling (`FxTy.mk?`; F5), `fixed`/`ufixed` aliases, fractional decimal literals, fixed types in every type position (UDVTs, arrays, structs, mapping keys); fixed literals and operators in expressions (G10); G15 classifies fixed-point source in profile. |
| Typing | S01, G13 | Implicit/explicit conversion relations (Q1, Q2, Q7), literal typing and exact folding (P1), operator typing (Q4, Q5, P8), common type (P7). |
| Source semantics | S02, S04.02 | Expressions over `Fx` values with `Fail` panics (Q3, Q6, Q8); ABI/storage observations of fixed values (P4–P6). S02 must reuse `Fx` or prove correspondence with it. |
| Lowering | G16, G17, G18, G21 | Scalar lowering of every `Fx` operation and conversion at every (M, N, signedness), checked and unchecked; compound assignments and `++`/`--`; fixed elements of aggregates (G18); ABI/calldata and the `0x11`/`0x12` panic payloads. |
| Backend | G25, G26, G27, G28, G45, G46 | Machine agreement of scaled arithmetic, including the 512-bit multiply-divide for `*`/`/` (Q8) and signed truncation; expression compilation (G26); storage packing (P6); EVM correspondence of the generated routines. |
| ABI | G40, G41 | Decoding validation (P5), encoding, selectors with canonical names (P4), packed encoding. |
| Verification transfer | G51, G52, G53 | Calculus rules over fixed values (SolKey has no fixed-point sort, so no KeY rule exists to follow); differential testing has no solc reference — test the compiler against this model (the upstream PRBMath `UD60x18`/`SD59x18` contracts in the tarball are candidate cross-checks for `ufixed256x18`/`fixed256x18` with truncating rounding, unverified). |

## 5. Remaining child obligations

- Answer Q1–Q8; then adjust the encoded variants.
- G00: record the fetched specification/compiler files (§Sources) in the
  upstream snapshot, or pin them otherwise; re-confirm F1–F3 by running the
  pinned solc.
- g00-manifest-rev: update the `fixedPoint` row (§4).
- S01/S02: prove the source typing and expression semantics against `Fx`.
- Not proved here: associativity laws (they fail under truncation, e.g.
  `(a·b)·c ≠ a·(b·c)`); that `FxTy.subsumes` implies `FxTy.solcImplicit`
  (both reviewers' sweeps found no counterexample, so `FxTy.implicitOK`
  very likely equals `FxTy.subsumes`; the conjunction is kept until it is
  proved); value preservation of `Fx.explicit` when digits drop (only the
  subsumed case, `Fx.explicit_of_subsumes`); the 104,198 count of F1 is a
  script result, not a Lean theorem (only its two witnesses are,
  `Fx.solc_lossy`).

## Gates

Recorded in the handoff (`CLOUD-RESULT`) of this task: Lean diagnostics,
`check-layers`, `check-orphans`, `check-trust`, `check-doc-paths`, and the
full `./run-lean.sh`.

## Review

A read-only finder and a separate read-only skeptic reviewed the first
commit (`dc75d1c`); neither used the Lean server. Confirmed findings and
their fixes:

| Finding | Source | Fix |
|---|---|---|
| F2 missed `>>>`, the fixed shift amount, and the upstream test `shr_unused.sol` | both | F2, §1 operator row and Q4 rewritten |
| The §1 ABI row cited shift code (`YulUtilFunctions.cpp:554,577`) as ABI code | finder | cites `cleanupFunction`/`conversionFunction`; shifts named separately |
| Explicit integer→fixed was described as same-width only; solc also admits every implicit pair | both | §1 row and `Fx.ofIntegerExplicit` docstring |
| `0x12` was attributed to the repository's integer semantics, which reads it as a revert | finder | P2, module docstring: cite solc's `control-structures.rst`/`value-types.rst` and G01 Q5; the departure is stated |
| Inline-assembly access was presented as a language rule; solc reports it unimplemented | finder | P8 places it under the confirmed assembly/Yul exclusion |
| `Token.h`, `conversion.rst`, `control-structures.rst` lacked digests | both | added to §Sources |
| `type(T)` citation, literal range `1018–1031`, mobile-type wording, `Types.h` lines | both | corrected |
| F1's sweep omitted opposite-signedness pairs | both | both counts given (34,929 + 69,269) |
| F5 omitted `N = 0` | finder | added |
| Mixed integer/fixed operands had no stated conversion | finder | §2 operations paragraph, P7 |
| "Checked" docstrings on theorems that hold in both modes | finder | `Fx.add_eq`, `Fx.sub_eq`, `Fx.div_eq` docstrings |
| `FxTy.mk?` overclaimed the spelling rule | finder | §2 wording |
| `Fx.ofWord?` premise `0 ≤ w < 2^256` undocumented | finder | docstring |
| Q1's recommendation narrows solc's type-checker acceptance without saying so | skeptic | Q1 states it and leaves the choice to the user |
| The exact `*`/`/` intermediate was a silent choice (P4) | skeptic | became Q8 |
| Fixed→integer conversion was in no question; Q7's evidence was one-sided | skeptic | Q7 covers both directions, gives the bit-pattern evidence and the wrap consequence, no longer recommends |
| Q2 merged constants with run-time values | skeptic | Q2's recommended option rejects out-of-range constants, as for integers |
| Q5/Q6 lacked a recommendation rationale | skeptic | Q5 recommended with evidence; Q6 explicitly none, with the `fixed8x3` case |
| Bare `simp` in `Fx.pow_bits_le` | skeptic | `simp only [Int.natCast_pow, Int.cast_ofNat_Int]` |
| Owners missed G10, G18, G26 | skeptic | added |

Not changed: the finder's suggestion to drop `FxTy.solcImplicit` from
`FxTy.implicitOK` (the implication is unproved; §5), and P1's
double-rounding claim, which both reviewers confirmed.
