# Fixed-point types — reference semantics

The user decided full fixed-point support, beyond the acceptance boundary of
pinned solc 0.8.38 ([G00 Q6](../solidity-scope.md#user-decisions-2026-10-29)).
solc 0.8.38 type-checks `fixedMxN`/`ufixedMxN` but generates no code for them
(`UnimplementedFeatureError 1834: Fixed point types not implemented.`), so
there is no compiler behaviour to align with. This document fixes what "full
support" means: the language rules collected from the pinned specification
(§1), the reference values and operations in
`Solidity/Language/FixedPoint.lean` (§2), the choices where the
specification is silent, with the user's answers (§3), and the roadmap
owners of the remaining work (§4). Nothing is wired into the AST, the elaborator, the compiler or the
feature manifest.

- **Base revision:** `caf52ecd4dde5d37cbc0098d47de1a01aa218285`
  ("Record resource and environment decisions").
- **Branch:** `cloud/roadmap-w1-20261029/fixed-point-semantics`; continued
  by the lane `cloud/roadmap-l1-20261029/lane-fixed` (§6), which merged it
  at base `ceb0d54b5be37fe04b8417a9be4ef9fedeeac429`.
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
| `Fx.explicit` | `Fx.rescale` (truncate toward zero when digits drop), then wrap (Q2) | total |
| `Fx.ofIntegerExplicit`, `Fx.ofBits` | integer → fixed by value, wrapped; `bytesM` → fixed by bit pattern (Q7) | total |
| `Fx.toIntTrunc` | fixed → integer by value (Q7): `tdiv a 10^N`, then the integer conversion | — |
| `Fx.ofLiteral?`, `Fx.explicitConst?`, `Fx.literalTrunc` | implicit literal (exact or refused); explicit constant folded exactly at the target's N (P1), refused when out of range (Q2) | `none` = compile error |
| `Fx.toWord`, `Fx.ofWord?` | ABI word (two's complement mod `2^256`); decoding range-checks (P5) | `none` = decoding revert |

**Theorems** (premises in parentheses; all checked by the Lean server with
`propext`, `Classical.choice`, `Quot.sound` at most — `#print axioms` on
`Fx.ofWord_toWord`, `Fx.solc_lossy`, `Fx.mod_eq`, `Fx.ofInteger_inRange`,
`Fx.implicit_lt`, `Fx.explicit_of_subsumes`, `Fx.ofIntegerExplicit_of_implicit`, `Fx.add_eq`; `Fx.solc_lossy` uses none):

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
  conversion is the implicit one where that exists.
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

- **P1 — constants fold exactly.** An explicit conversion of a literal rounds
  the exact rational at the *target's* N (`Fx.literalTrunc`), not through
  solc's mobile type, which first rounds at its own N. This follows "fold
  rational constants exactly" ([solidity-scope.md](../solidity-scope.md#what-belongs-in-the-model)).
  An out-of-range explicit constant is a compile error (Q2). (Corrected in
  §6.2: the earlier example `ufixed256x80(1/3)` is out of range at 80 digits,
  so it is a compile error, not a rounding difference. The two routes differ
  in value only at the edge shown by the second `explicitRat?` example in
  `Solidity/Language/FixedPoint/Literals.lean`.)
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

### User decisions (2026-10-29)

The questions Q1–Q8 below were put to the user, who answered all of them
on 2026-10-29 (relayed by the batch coordinator; the coordinator records
them in [solidity-scope.md](../solidity-scope.md) as a "Second round"
section). The model encodes every answer; no question is open.

| Question | Decision | Encoded by |
|---|---|---|
| Q1 [Implicit] — solc's implicit fixed→fixed test accepts lossy conversions (F1) | Only the exact, range-contained subset of solc's pairs. This narrows solc's type-checker acceptance (and, through P7, the mixed operations it admits); `ufixed8x3(x)` stays expressible explicitly. | `FxTy.implicitOK`, `FxTy.common?`, `Fx.implicit` |
| Q2 [Explicit] — an explicit conversion whose value does not fit | Wrap modulo `2^M` at run time, as explicit integer conversions cut higher-order bits (`conversion.rst:61`); an out-of-range constant is a compile error, as for integer types (`Types.cpp:1054–1055`), although solc's fixed-point type checker admits e.g. `ufixed8x1(100.5)`. | `Fx.explicit`, `Fx.ofIntegerExplicit` (both total, wrapping), `Fx.explicitConst?` (`none` = compile error) |
| Q3 [Rounding] — `*`, `/` and digit-dropping conversions | Toward zero, as solc's literal rounding, integer `/` and rational `%`. | `Int.tdiv`/`Int.tmod` in `Fx.mul`, `Fx.div`, `Fx.mod`, `Fx.rescale`, `Fx.literalTrunc`, `Fx.toIntTrunc` |
| Q4 [Shifts] — `<<`, `>>`, `>>>` with fixed operands (F2) | "Do what solc does": no such program compiles, so shifts are **rejected**. Why: solc's type checker admits a shift whose left operand is fixed (F2), but code generation then fails the assertion `solUnimplementedAssert(_type.category() != Type::Category::FixedPoint, …)` in `typedShiftLeftFunction`/`typedShiftRightFunction` (`YulUtilFunctions.cpp:554,577`), reported as `UnimplementedFeatureError` — the upstream test `shr_unused.sol` expects exactly that for `x >>> 6` at `fixed`. A fixed shift *amount* under an integer or literal left operand is already a type error (`isValidShiftAndAmountType`, `Types.cpp:573–583`). | no shift operation is defined on `Fx` |
| Q5 [UfixedNeg] — unary `-` at `ufixed` (F3) | Accepted, as solc's type checker does: `0x11` unless the operand is `0`, wrapping in `unchecked`. | `Fx.neg` |
| Q6 [IncDec] — `++`/`--` | Add or subtract the value `1`. At a type without `1` (e.g. `fixed8x3`) `++x` type-checks and always panics `0x11`. | `Fx.inc`, `Fx.dec` |
| Q7 [Reinterpret] — explicit fixed↔integer and `bytesM`→fixed | Integers convert by value; `bytesM` converts by bit pattern. With Q2, `fixed256x18(int256 x)` wraps for most `x`. | `Fx.ofIntegerExplicit`, `Fx.toIntTrunc`, `Fx.ofBits` |
| Q8 [Intermediate] — `*` and `/` | The exact product or quotient, then truncated (and, unchecked, wrapped: P3); the backend needs a 512-bit multiply-divide (G25). | `Fx.mul`, `Fx.div` |

`Mode` remains only where the language has both behaviours: arithmetic in
checked code and in `unchecked { }`. Explicit conversions take no mode.


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

- G00: record the fetched specification/compiler files (§Sources) in the
  upstream snapshot, or pin them otherwise; re-confirm F1–F3 by running the
  pinned solc.
- g00-manifest-rev: update the `fixedPoint` row (§4).
- S01/S02: prove the source typing and expression semantics against `Fx`.
- Not proved here: associativity laws (they fail under truncation, e.g.
  `(a·b)·c ≠ a·(b·c)`); value preservation of `Fx.explicit` when digits
  drop (only the subsumed case, `Fx.explicit_of_subsumes`); the 104,198
  count of F1 is a script result, not a Lean theorem (only its two
  witnesses are, `Fx.solc_lossy`). That `FxTy.subsumes` implies
  `FxTy.solcImplicit`, open here before, is `FxTy.solcImplicit_of_subsumes`
  (§6.1), so `FxTy.implicitOK` is exactly `FxTy.subsumes`.

## Gates

Run on 2026-10-29 (4 cores, 15 GB):

- Lean server diagnostics on `Solidity/Language/FixedPoint.lean`: no
  messages; no `sorry`, axiom, `native_decide`, `implemented_by` or
  `maxHeartbeats` in it.
- `node scripts/check-layers.mjs`: 155 core modules, 0 reach the elaborator;
  `node scripts/check-orphans.mjs`: 734 reachable, 0 orphaned;
  `bash scripts/check-trust.sh`: 0 findings;
  `bash scripts/check-doc-paths.sh`: 46 missing references, as at the base.
- `./run-lean.sh`: the first run (61 min 38 s wall clock) built the default
  target (719 jobs) and lost `Solidity.TestSuite.Derived17` to the out-of-memory
  killer (Lean exit 137; about 15.6 GB in use machine-wide, Lean server
  included) while the TestSuite modules built in parallel. The re-run at
  `c51a819` (4 min 16 s) built both targets ("Build completed successfully",
  719 and 262 jobs; `Derived17` alone in 226 s, peak about 13.4 GB in use),
  then `check-solkey.sh` reported 37 mismatches — the base's count — and
  exited 1 for them.

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

After the reviews the user answered Q1–Q8 (§3); the model now encodes the
answers: explicit conversions wrap and take no `Mode`
(`Fx.explicit`, `Fx.ofIntegerExplicit`), constants out of range are refused
(`Fx.explicitConst?`), and the Q4 rationale cites the code-generation
assertion that stops every fixed shift.

Not changed: the finder's suggestion to drop `FxTy.solcImplicit` from
`FxTy.implicitOK`, and P1's double-rounding claim, which both reviewers
confirmed. The implication was unproved then; it is now
`FxTy.solcImplicit_of_subsumes` (§6.1), and the conjunction stays because it
states the decision's form ("the range-contained subset of solc's pairs").

## 6. Lane `lane-fixed` (roadmap-l1, 2026-10-29)

The lane owns this document, `Solidity/Language/FixedPoint.lean` and the
modules `Solidity/Language/FixedPoint/*.lean`. Its work queue: (1) the
decisions' laws, (2) literals and constants, (3) the ABI, (4) storage
packing, (5) a conformance sweep over the pinned upstream tests. Each
checkpoint below has its handoff and review.

### 6.1 Checkpoint 1 — the decisions and their laws

The second-round decisions were already encoded (§3). `Mode` keeps only
`checked`/`unchecked`; no obsolete variant is left, because explicit
conversions lost their mode in `fb5c81a`. The new module
`Solidity/Language/FixedPoint/Laws.lean` proves the laws the reviews asked
for. A checked `*` or `/` range-checks only the truncated exact result, and
the exact product or quotient is an unbounded intermediate. This is the
intended reading of Q8: no intermediate overflow is observable, and a
lowering (G16/G25) must not revert on one.

- **Checked/unchecked agreement where nothing overflows.**
  `Fx.add_agree_of_inRange`, `Fx.sub_agree_of_inRange`,
  `Fx.neg_agree_of_inRange`, `Fx.mul_agree_of_inRange`,
  `Fx.inc_agree_of_inRange`, `Fx.dec_agree_of_inRange` and
  `Fx.div_agree_of_inRange` each take the no-overflow premise on the exact
  integer. `Fx.mod_agree'` needs no premise. The same facts read from a
  checked success are `Fx.add_agree` … `Fx.mod_agree`, from
  `Fx.result_unchecked_of_checked` and `Fx.result_agree`. `Fx.result_val`
  says every result, unchecked included, is the wrap of the exact integer;
  `Fx.result_checked_val` says a checked one is that integer.
- **Unary minus at `ufixed` (Q5).** `Fx.neg_unsigned`: checked, `.ok a` if
  `a = 0`, else `overflow`.
- **`*`/`/` exactness and truncation (Q3, Q8).**
  - `tdiv_trunc` and `tdiv_rem` give truncating division on `Int`.
  - `Fx.mul_trunc`: `r·10^N` lies between `0` and `a·b`, within one `10^N`.
  - `Fx.mul_exact`: exact when `10^N ∣ a·b`.
  - `Fx.div_trunc`: `a·10^N = r·b + e` with `|e| < |b|` and `e` of the sign
    of `a`, which determines `r`.
  - `Fx.div_exact`.
  - `Fx.inc_val`, `Fx.dec_val`: checked `++`/`--` move by the value 1 (Q6).

  These are stated for checked results. The unchecked ones are the wrap of
  the same integer (`Fx.result_val`).
- **Conversion truncation and lossless round trips.**
  - `Fx.rescale_down_trunc` and `Fx.toIntTrunc_trunc`: dropping digits and
    converting to an integer truncate toward zero.
  - `Fx.rescale_down_exact`, `Fx.rescale_up_down`.
  - `Fx.explicit_sameValue` and `Fx.explicit_explicit`: an explicit
    conversion keeps the value, and converting back returns it, whenever
    the value is representable at the target (no nonzero digit dropped,
    rescaled integer in range). This covers narrower widths, the other
    signedness and fewer digits, value by value.
  - `Fx.explicit_implicit`.
  - `Fx.toIntTrunc_ofIntegerExplicit`: integer → fixed → integer.
  - `Fx.ofIntegerExplicit_toIntTrunc`: fixed → integer → fixed, with no
    fractional part.
  - `Fx.toBits_ofBits`, `Fx.ofBits_toBits` (Q7). `Fx.toBits`, in the core
    module, only witnesses that `ofBits` is a bijection on `[0, 2^M)`. solc
    has no fixed→`bytesM` conversion.
- **Implicit ⇒ value-preserving (Q1).**
  - `FxTy.solcImplicit_of_subsumes` and `FxTy.implicitOK_iff`:
    `implicitOK = subsumes`.
  - `FxTy.subsumes_iff`: `subsumes` holds exactly when every value of `t`
    has a same-valued value of `t'`.
  - `FxTy.subsumes_refl`, `FxTy.common?_subsumes`.
  - `Fx.implicit_preserves`: value, `<`, `<=` and distinctness, through
    `Fx.implicit_le` and `Fx.implicit_injective`.
  - `Fx.common?_preserves`.

`#print axioms` pins (`#guard_msgs`) at the end of the module cover
`FxTy.implicitOK_iff`, `FxTy.subsumes_iff`,
`Fx.result_unchecked_of_checked`, `Fx.mul_trunc`, `Fx.div_trunc`,
`Fx.explicit_explicit`, `Fx.implicit_preserves` and `Fx.neg_unsigned`. Each
is `[propext, Classical.choice, Quot.sound]`.

**Handoff.**
- S01/S02 can take `implicitOK` as `subsumes` and cite
  `Fx.common?_preserves` for mixed operands.
- G16/G25 lowering proofs can target `Fx.result_val` (unchecked is the wrap
  of the exact integer) and `Fx.mul_trunc`/`Fx.div_trunc` for the 512-bit
  multiply-divide.

Not proved:
- associativity, which fails under truncation (witness in §6.6);
- how far an explicit conversion lands from the value when the value is not
  representable (it wraps, by decision Q2);
- order preservation of explicit conversions (proved for unwrapped values
  in §6.6: `Fx.explicit_le`).

**Review.** A read-only finder and a separate read-only skeptic reviewed
`aa4bb50`. Neither found a blocking defect. The confirmed findings were
fixed in the next commit:

| Finding | Source | Fix |
|---|---|---|
| Agreement was only stated from a checked success | skeptic | `…_agree_of_inRange` per operation, `Fx.mod_agree'` |
| No truncation law for conversions | skeptic | `Fx.rescale_down_trunc`, `Fx.toIntTrunc_trunc`, `Fx.rescale_down_exact` |
| Lossless round trips covered only subsumed pairs | both | `Fx.explicit_sameValue`, `Fx.explicit_explicit`, `Fx.ofIntegerExplicit_toIntTrunc` |
| `subsumes` was a range test only by its docstring | skeptic | `FxTy.subsumes_iff` (both directions) |
| Order preservation was only `<` | both | `Fx.implicit_le`, `Fx.implicit_injective` in `Fx.implicit_preserves` |
| "between `0` and `x`" was not stated | finder | sign conjuncts in `tdiv_trunc`, `Fx.mul_trunc` |
| Checked-only laws were unqualified | finder | docstrings and the bullet above name the mode |
| No general law for unary minus at `ufixed` | finder | `Fx.neg_unsigned` |
| `Fx.toBits` was new semantics in the laws module | both | moved next to `Fx.ofBits` in the core, with its status |
| `FxTy.lo_le_zero`/`hi_nonneg` duplicated core proofs | finder | moved to the core; `Fx.mod_inRange` uses them |
| Untyped `have`s | finder | typed throughout `Solidity/Language/FixedPoint/Laws.lean` |
| Stale review note on `solcImplicit` (§Review) | finder | reworded |
| Intermediate overflow of `*` was unstated | skeptic | stated as intended, above and in the module docstring |

### 6.2 Checkpoint 2 — literals and constants

New module `Solidity/Language/FixedPoint/Literals.lean`. The constants are
Lean core's normalized `Rat`, which lives in `Init`, so the core stays
dependency-free.

- **Exact folding.** `CExpr` covers literals, unary `-`, `+ - * / %` and
  `**`; `CExpr.eval` folds them as solc's
  `ConstantEvaluator::evaluateBinaryOperator` does. `/` and `%` by zero, a
  non-integer exponent, a result over solc's 4096-bit precision bound
  (`fitsPrecision`) and a power that fails solc's pre-check
  (`fitsPrecisionExp`, 32-bit exponent) are compile errors (`none`). `%` is
  `p − trunc(p/r)·r`, with the sign of the dividend. Bit operators and
  shifts are left out: solc refuses them on fractional constants, and the
  shift decision rejects them on fixed operands. Examples: `0.1 + 0.2` is
  exactly `0.3`; `(1/3)·3` is exactly `1`; `2 ** -2 = 0.25`;
  `-7.5 % 2 = -1.5`; `2 ** 2049` is refused.
- **Only the value matters.** `Fx.ofLiteral?_congr`,
  `Fx.literalTrunc_congr`, `Fx.ofRat?_mkRat`, `Fx.explicitRat?_mkRat`.
- **Implicit conversion of a constant.**
  - `Fx.ofRat?` / `Fx.ofLiteral?`; `Fx.ofLiteral?_eq_some_iff` says it is
    exact.
  - `Fx.ofLiteral?_isSome_iff_solc`: it accepts exactly what solc's
    `RationalNumberType::isImplicitlyConvertibleTo` accepts (no negative
    value into `ufixed`; integers by `minIntegerValue`/`maxIntegerValue`;
    fractions by an exact scaled integer that fits). Unlike the
    fixed→fixed test (F1), solc's literal test is already lossless, so
    there is no deviation here.
- **Explicit conversion of a constant (Q2, Q3, P1).**
  - `Fx.explicitRat?` / `Fx.explicitConst?`.
  - `Fx.explicitConst?_eq_some_iff`: it is the truncated scaled integer.
  - `Fx.explicitConst?_eq_none_iff`: a compile error exactly when that
    integer is out of range.
  - `Fx.explicitConst?_trunc`: toward zero, within one unit.
  - `Fx.explicitConst?_of_ofLiteral?`: it agrees with the implicit
    conversion where that exists.
- **Mobile type of a fractional constant.** `mobileFx?` is solc's
  `RationalNumberType::fixedPointType`, read from `Types.cpp:1231–1267` at
  `v0.8.38` (digest as in §Sources, re-fetched and re-checked here). An
  integer constant's mobile type is an integer type (`integerType`,
  `Types.cpp:1207–1213`), which belongs to the integer typing.
  - `mobileFx?` takes as many digits as keep the magnitude ≤ `2^256 − 1`
    (`2^255` if negative), stopping when exact and at 80. It truncates
    toward zero and uses the fewest bytes of the magnitude, or of
    `2·(magnitude − 1)` when negative.
  - `mobileFx?_inRange`: the mobile type holds the truncated constant.
  - `mobileFx?_exact`: the constant converts implicitly to it exactly when
    its digits suffice.
  - `digitsGo_le_of_exact`, `digitsGo_exact`, `mobileFx?_exact_of_digits`:
    solc's loop stops at the first exact digit count that fits, so a
    constant exact at some `d ≤ 80` digits within the bound is exact at its
    mobile type.
  - Examples: `0.5 : ufixed8x1`, `-12.8 : fixed8x1`, `-12.9 : fixed16x1`,
    `1/3 : ufixed256x77`; `2^256 + 0.5` has none.
- **Common type with a constant operand.**
  - `litCommon?` (`x op c`) follows solc's `Type::commonType`. For a
    fractional `c` it tries the mobile type second; for an integer `c` it
    only converts `c` to `t`. The result is restricted to a type at which
    the constant is exact: `litCommon?_exact`, and `litCommon?_solc` (it
    types only what solc types, at solc's type; `solcLitCommon`
    transcribes `Types.cpp:286–296`).
  - `litCommonRev?` (`c op x`) refuses a fractional `c`, as solc's
    `RationalNumberType::binaryOperatorResult` does ("Fractional literals
    not supported.", `Types.cpp:1075–1078`). `litCommonRev?_eq_solc` shows
    it is solc's rule exactly (`solcLitCommonRev`).

**Deviations from solc's type checker.**

| Case | solc 0.8.38 (source reading) | Here | Status |
|---|---|---|---|
| Out-of-range explicit constant, e.g. `ufixed8x1(100.5)`, `ufixed256x80(1/3)` | Accepted through the mobile type | Compile error | Intended (Q2) |
| Explicit constant value | Truncated at the mobile type's digits, then converted | Truncated once, at the target's digits | Intended (P1). Where the exact fold fits the target, the value can differ only when the target has more digits than the mobile type (proved: `Fx.explicitRat?_mobile_route`, §6.6); and then, by argument (not proved), only when the loop stopped on the magnitude bound (`2^256 − 1`, or `2^255` when negative). Witness: `ufixed256x1((2**257 - 1) / 20)` is `2^256 − 1` here and `2^256 − 6` through solc's route. |
| Explicit constant with no mobile type, e.g. `ufixed256x0(2**256 - 0.5)` | Refused (`isExplicitlyConvertibleTo` needs a mobile type) | `2^256 − 1` (in range after truncation) | Intended (P1: exact folding at the target) |
| Common type `x op c` where `c` is not exact at the mobile type, e.g. `ufixed8x77 y; y + 1/3` | Common type `ufixed256x77`, `c` truncated | Refused | Intended (Q1: lossy conversions are explicit) |
| `c op x` with a fractional `c`, e.g. `0.5 * x` | Refused ("Fractional literals not supported.") | Refused, as solc | Follows solc; question QL1 below asks whether full support should admit it |
| A standalone fractional constant that is inexact at its mobile type, e.g. the inline array `[1/3]` | Element type `ufixed256x77`, truncated | `mobileFx?` gives solc's type; the model does not decide whether the truncation is admitted | Open: question QL2 below |
| A fractional constant as an ABI argument, e.g. `abi.encode(0.1)` | Refused ("Fractional numbers cannot yet be encoded.", TypeError 6090) | Refused, as solc, until QL2 is answered | Follows solc; QL2 |
| Constant expressions with bit operators, shifts or over-large literals | Folded (integers) or refused | Not in `CExpr` | Not modelled; integer constants belong to the integer typing |

**Handoff.** S01/G13 can type constant subexpressions with `CExpr.eval`
and give fixed-point types with `Fx.ofRat?` (implicit), `Fx.explicitRat?`
(explicit), `mobileFx?` (standalone constants such as inline-array
elements; `abi.encode` of a fractional constant is refused as in solc
until QL2) and
`litCommon?`/`litCommonRev?` (mixed operands). Not done:
- comparisons between two constants. solc compares them at run time
  through their mobile types and refuses a pair whose mobile types have no
  common type, e.g. `0.5 < -0.5` (`ufixed8x1` against `fixed8x1`). That
  rejection and the comparison itself are not modelled;
- constants of other categories (integer `mobileType`, `bytesM`,
  addresses), which belong to the integer typing;
- a proof that the two routes agree when the target has fewer digits (done
  in §6.6: `Fx.explicitRat?_mobile_route`).

**Scope questions** (raised here, not answered; the rest of the checkpoint
does not depend on them):

- **QL1 [LitFirst]** — solc refuses `c op x` for a fractional constant `c`
  and a fixed-point `x` ("Fractional literals not supported."), while it
  types `x op c`. Should full support admit `c op x` like `x op c`? The
  model follows solc (`litCommonRev?`).
- **QL2 [MobileTrunc]** — a fractional constant that needs a type of its
  own gets solc's mobile type. In an inline array, e.g. `[1/3]`, solc
  types it `ufixed256x77` and truncates it. As an ABI argument, e.g.
  `abi.encode(0.1)`, solc refuses it ("Fractional numbers cannot yet be
  encoded."). Q1 makes lossy implicit conversions explicit. Should such
  constants be refused everywhere, admitted at the mobile type only when
  exact there (`abi.encode(0.1)` then compiles), or admitted and truncated
  as solc does for arrays?

**Review.** A read-only finder and a separate read-only skeptic reviewed
`28cbc41`. Both checked the mobile type, the folding, the precision bounds
and every worked value against the pinned sources, and confirmed them.
Confirmed findings and their fixes:

| Finding | Source | Fix |
|---|---|---|
| `c op x` with a fractional `c` was typed; solc refuses it (`Types.cpp:1075–1078`) | both (blocking) | `litCommonRev?` refuses it; `litCommonRev?_eq_solc`; QL1 |
| Integer constants used the fixed-point mobile branch (`ufixed8x0 x; x + 300` was typed) | both (blocking) | the mobile branch applies only to fractional constants; example added |
| `litCommon?_exact` proved safety only, with no link to solc | skeptic | `solcLitCommon`, `litCommon?_solc` |
| `mobileFx?_exact` was near-tautological and one-directional | both | now an iff, plus `digitsGo_exact`/`mobileFx?_exact_of_digits` (the loop stops when exact) |
| P1 edge stated only for positive constants; the no-mobile-type case was missing | both | deviation rows rewritten; `2^256 − 1/2` example |
| `abi.encode(1/3)` truncates silently, unaddressed under Q1 | skeptic | QL2 (its premise corrected in checkpoint 5: solc refuses fractional ABI arguments; the truncating case is the inline array) |
| Constant comparisons: solc's rejection of mobile pairs without a common type | skeptic | "Not done" note corrected |
| `CExpr` omissions (bit operators, shifts, literal size) unrecorded | finder | deviation row |
| `mobileFx?` described as the mobile type of every constant | finder | the bullet names fractional constants only |
| `ratPow` docstring claimed an unchecked early return | finder | docstring corrected |
| Untyped `have`s | finder | typed |

### 6.3 Checkpoint 3 — ABI

New module `Solidity/Language/FixedPoint/Abi.lean`. It reads the ABI
specification (`abi-spec.rst:66–72, 213–221, 755` at `v0.8.38`, §Sources):
the value `v / 10^N` is encoded through its scaled integer `v` as a 32-byte
big-endian two's-complement word, as `int256`/`uint256` are. solc 0.8.38
generates no ABI code for fixed-point types: `cleanupFunction`
(`YulUtilFunctions.cpp:3994–3995`) and the legacy cleanup are
unimplemented for them, so no validator can be generated. The coder
behaviour below is therefore proposal P5, by analogy with `intM`/`uintM`.
It is not compiler behaviour, and no differential test against solc is
possible.

- **Words.** `Fx.encode : Fx t → Fin (2^256)` (`Fx.encode_val`: the word is
  `Fx.toWord`).
- **Coder v2 decoding (P5).** `Fx.decodeV2` reads the word as `int256`
  where signed, then range-checks it.
  - `Fx.decodeV2_isSome_iff` is the dirty-upper-bit condition. An unsigned
    word must be `< 2^M`; a signed one must be `< 2^(M−1)` or
    `≥ 2^256 − 2^(M−1)`, i.e. the sign extension of its low `M` bits. This
    is what solc's `validator_revert_t_intM` checks for `intM`
    (`eq(value, cleanup(value))`, then `revert(0, 0)`).
  - Decoding is exactly the inverse of encoding: `Fx.decodeV2_encode`
    (round trip), `Fx.encode_of_decodeV2` (only a value's own word decodes
    to it) and `Fx.decodeV2_eq_none_iff` (every other word is rejected).
- **Coder v1 (G00 Q4: the legacy pipeline may select v1 by pragma).**
  `Fx.decodeV1` does no validation and cleans the low `M` bits, as v1
  cleans `intM` (`Fx.decodeV1_eq_ofBits`). Cleaning on load and cleaning
  before each use cannot be told apart. `Fx.decodeV1_of_decodeV2`: the
  coders agree on every word v2 accepts. `Fx.decodeV1_encode`.
- **Bytes.**
  - `beBytes`/`beNat` (big-endian): `beNat_beBytes`, `beBytes_beNat`,
    `beNat_lt`.
  - `Fx.abiEncode` (32 bytes, `Fx.abiEncode_length`) and
    `Fx.abiDecodeV2` on an isolated 32-byte head:
    `Fx.abiDecodeV2_abiEncode` and `Fx.abiEncode_of_abiDecodeV2` (only the
    canonical bytes decode).
  - `Fx.encodePacked`: `abi.encodePacked` of a top-level argument, the
    `M/8`-byte two's complement, unpadded. Solidity has no packed decoder;
    `Fx.ofPackedBytes` and `Fx.ofPackedBytes_encodePacked` only show that
    the packed bytes lose nothing.
- **Canonical type names (P4).** `FxTy.name`: `fixed` and `ufixed` are
  spelled `fixed128x18` and `ufixed128x18`. `N = 0` keeps its `x0`, which
  the ABI specification excludes (`0 < N`). That is a deliberate extension,
  since the scanner admits these types (F4). Signature strings and their
  Keccak selectors are G40's.
- **Worked values.** `-1.0 : fixed8x1` is the word `2^256 − 10`. The word
  `0xff` at `fixed8x1` is rejected by v2 and cleaned to `-0.1` by v1.
  `256` at `ufixed8x2` is rejected.

`#print axioms` pins: `Fx.decodeV2_eq_none_iff` and
`Fx.abiEncode_of_abiDecodeV2` use `[propext, Quot.sound]`;
`Fx.decodeV2_isSome_iff` and `Fx.ofPackedBytes_encodePacked` use
`[propext, Classical.choice, Quot.sound]`.

**Handoff.** G40/G41 can lower fixed-point parameters and return values as
`intM`/`uintM` words and cite `Fx.decodeV2_isSome_iff` for the validation.
Known cost: the words are `Fin (2^256)`, while `Fx.toWord` is an `Int` and
the repository's `Semantics.Word` (`Solidity/Semantics.lean`) is a
range-checked `Int`. The conversions are not written. Importing
`Semantics.lean` here would tie the import-free reference model to the
whole semantics. The byte functions are local; `bytesNat` and `wordBytes`
in `Solidity/RevertBytes.lean` compute the same bytes, but the equality is
not proved and that module pulls in Keccak.

Not done:
- dynamic aggregates of fixed values, whose elements are padded words in
  the standard encoding and also in packed mode (arrays pad elements to 32
  bytes) (G40);
- calldata heads at offsets, and the non-strict decoder's acceptance of
  trailing data;
- event topics: an indexed fixed parameter's topic is its word
  (`Fx.encode`);
- user-defined value types over fixed types, which use the underlying
  name and word;
- the empty revert data of a v2 validation failure (G01 Q5).

**Review.** A read-only finder and a separate read-only skeptic reviewed
`663c0da`. Neither found a correctness defect. The finder confirmed the
byte order, the v2 condition against `validator_revert_*`, the v1 cleaning
and every worked value. Confirmed findings and their fixes:

| Finding | Source | Fix |
|---|---|---|
| The doc and docstring read as solc behaviour; solc generates no fixed-point ABI code | both | stated as P5 by analogy, above and in the module docstring |
| The handoff cited `Fx.decodeV2_eq_none_iff` for the bit validation | skeptic | it cites `Fx.decodeV2_isSome_iff`; `_eq_none_iff` is described as the inverse property |
| `decodePacked` presented as an ABI operation | both | renamed `Fx.ofPackedBytes`, documented as an injectivity witness |
| Packed arrays, event topics, UDVTs, head offsets and trailing data were unmentioned | both | "Not done" |
| `N = 0` departs from the ABI spec without saying so here | finder | stated in §6.3 and the module docstring |
| The "selector" bullet only showed names | skeptic | now "canonical type names"; selectors are G40's |
| Three word types; `Fin (2^256)` matches neither neighbour | skeptic | stated as a known cost in the handoff |
| Citation `abi-spec.rst:218–221` incomplete | finder | `213–221` |
| Untyped `have`s | finder | typed |
| Duplicate byte helpers (`RevertBytes.lean`) | finder | recorded in the handoff; not merged (see there) |

### 6.4 Checkpoint 4 — storage packing

New module `Solidity/Language/FixedPoint/Storage.lean`.

**Where the layout is a choice.** For the source semantics the physical
layout is not observable: per the scope's "Readings", solc's slot behaviour
fixes the logical alias semantics, not the packing. At the backend, the
layout becomes observable through the `storageLayout` output,
`eth_getStorageAt`, upgrades under `delegatecall` and gas, so a backend
proof (G28) fixes it as part of its specification. Inline-assembly
`.slot`/`.offset` access is closed (P8). solc emits no storage code for
fixed-point types, so the layout chosen here is `intM`'s rule carried over
(P6). A fixed value takes `M/8` bytes (`FxTy.storageBytes`), lower-order
aligned at a byte offset of its slot, and holds its `M`-bit
two's-complement pattern, not sign-extended (`Types.h:552–553`:
`storageBytes`, `leftAligned = false`).

- **Byte ranges of a word.** `field w off len` reads bytes and
  `setField w off len v` writes them.
  - `field_setField`: read after write.
  - `field_setField_below` and `field_setField_above`: a write leaves every
    disjoint range alone.
  - `setField_field`: writing back what is there changes nothing.
  - `setField_setField`: the last write wins.
  - `setField_lt`: a write inside the slot keeps a 256-bit word.
  - Helpers: `pow_off_len`, `parts_eq`, `parts_mod`, `parts_div`,
    `parts_hi`, `setField_parts`, `setField_low`, `setField_div`,
    `setField_hi`, `field_eq_mod`, `low_lt`, `val_lt`.
- **Fixed values in one slot.** `Fx.load t w off` and
  `Fx.store w off h a` (`h : off + M/8 ≤ 32`) work on a `Slot`, a
  `Fin (2^256)`.
  - `Fx.load_store`: read after write.
  - `Fx.load_store_disjoint`: another fixed value in a disjoint range is
    undisturbed.
  - `Fx.field_store_disjoint`: so is any disjoint byte range, whatever it
    holds.
  - `Fx.store_load`, `Fx.store_store`.
  - `Fx.load_zero`: an untouched slot reads as the default, `0`.
- **Packing a sequence (solc's rule).** `place` puts each value type at
  the next free offset, or at offset 0 of the next slot when it does not
  fit.
  - `place_fits`: every item of at most 32 bytes lies inside its slot.
  - `place_pairwise`: no two items overlap (`Apart`).
  - Supporting facts: `place_after`, `place_sizes`, `place_length`,
    `Apart.symm`, `place_apart` (any two distinct indices).
  - Example: `fixed8x1 a; ufixed16x2 b; fixed c; ufixed256x0 d;` places
    `a`, `b`, `c` at slot 0, offsets 0, 1, 3, and `d` at slot 1.
- **The slots of a contract.** `Store` is `Nat → Slot`. `Fx.loadAt` and
  `Fx.storeAt` address a slot and an offset. `layout tys` is the placement
  of typed state variables (`layout_length`, `layout_size`, and
  `layout_fits`, which supplies the `store` premise).
  - `Fx.loadAt_storeAt`: read after write.
  - `Fx.loadAt_storeAt_apart`: a write leaves every value apart from it
    unchanged, in its own slot or any other.
  - `Fx.layout_frame`: writing variable `i` of a layout leaves every other
    variable `j` unchanged.
  - `Fx.layout_load_store`: read after write, per variable.
- **Mapping keys (P6).** `Fx.keyWord` is the padded ABI word whose hash
  addresses the entry. `Fx.keyWord_injective`: distinct keys are distinct
  words. The hash belongs to the storage-hashing lane.

`#print axioms` pins:
- `Fx.load_store`, `Fx.load_store_disjoint`, `Fx.layout_frame` and
  `Fx.field_store_disjoint` use `[propext, Classical.choice, Quot.sound]`;
- `place_pairwise` and `Fx.keyWord_injective` use `[propext, Quot.sound]`.

**Handoff.** G28 can take `layout` as the offsets of fixed state
variables. Its frame obligation for them is `Fx.layout_frame`, and its
read-after-write obligation is `Fx.layout_load_store`. For mixed layouts
with other value types it can use `place` together with
`Fx.field_store_disjoint`. S04.02 can read a fixed-valued storage
observation as `Fx.loadAt`.

Not done:
- the solc rule that structs and arrays start, and are followed by, a new
  slot;
- packed fixed elements of storage arrays (`floor(32 / (M/8))` per slot);
- a typed `place` over every value type: `layout` is typed for fixed types
  only, and `place` takes sizes;
- connecting `Store` to the repository's typed storage
  (`Semantics/Storage.lean`), which keeps logical values, not packed words.

**Review.** A read-only finder and a separate read-only skeptic reviewed
`678bd3d`. The finder confirmed the layout rules against
`layout_in_storage.rst` and `Types.h` at `v0.8.38`: low-order alignment,
no sign extension, next-slot overflow, the example, and key padding.
Confirmed findings and their fixes:

| Finding | Source | Fix |
|---|---|---|
| No storage map or layout-level frame theorem; `place_pairwise` was not connected to `load`/`store` | both (main gap) | `Store`, `Fx.loadAt`/`Fx.storeAt`, `layout`, `Fx.loadAt_storeAt_apart`, `Fx.layout_frame`, `Fx.layout_load_store` |
| `place` untyped; nothing produced the `store` premise | skeptic | `layout` over `List FxTy`, `layout_size`, `layout_fits` |
| "Free choice of layout" was applied beyond the source semantics; "solc's" layout overstated (solc emits no fixed storage code) | skeptic | restricted above and in the module docstring; `intM`'s rule carried over |
| "packed value of any type" overclaimed `Fx.load_store_disjoint` | both | docstrings name fixed types; `Fx.field_store_disjoint` listed |
| "hash distinct words" read as a hash claim | both | reworded |
| Size-0 items | both | docstring: harmless, and no value type has them (`FxTy.storageBytes_pos`) |
| Pins were partial | skeptic | three more pins |
| `Types.h:552–554` should be `552–553`; "low-order bytes first" ambiguous | finder | corrected |
| `storageBytes_bits` sat in the `Fx` namespace | finder | moved to `FxTy` |

Not changed: the generic names `field`, `setField` and `place` stay in
`Solidity.Language.FixedPoint`. That namespace is not opened alongside
`Semantics`, so the names do not clash with `Semantics/Heap.lean` or
`Semantics/Storage/Ops.lean`.

### 6.5 Checkpoint 5 — conformance sweep

**Method.** The pinned tarball `tests/upstream/solidity-0.8.38.tar.gz` was
unpacked outside the repository. Every `.sol` file under
`test/libsolidity/{syntaxTests,semanticTests,smtCheckerTests}` matching
`\bu?fixed(\d+x\d+)?\b` was taken: 87 files in all, of which 81 are in
syntax or semantic tests. The C++ unit tests (`SolidityTypes.cpp`, type
identifiers) and the Yul tests are outside the sweep. A file counts as a real fixed-point use when the
token occurs in code (outside strings and comments) or a fixed-point type
appears in its expected diagnostics. That leaves 68 files: 64 with code
uses and 4 whose messages name a mobile type. The 19 false positives:
- "fixed bytes" in messages: the four `array/concat/bytes_concat_wrong_type_*`
  tests, `errors/error_bytes_concat_wrong_type.sol`,
  `events/event_bytes_concat_wrong_type.sol`,
  `bytesNN_index_assign/delete` and `288_conditional_with_all_types.sol`;
- identifiers and strings: `FixedFeeRegistrar`, `mapping_string_key`,
  `create_random`, `memory_bytes_delete_element_neighbor`;
- user-defined `uint256` wrappers: `userDefinedValueType/fixedpoint.sol`,
  `smtCheckerTests/userTypes/fixedpoint.sol`, and the three PRBMath files;
- `smtCheckerTests/typecast/downcast.sol`.

None of these uses a fixed-point type. The regex cannot find tests about
fractional constants whose diagnostics never name a fixed type. A second
pass over the expectations matching `Fractional|fractional|rational_const`
added 13 such files, and the finder added one more,
`layout_fractional_number.sol`, whose message says "must evaluate to an
integer". That makes 14 rows marked † below. Every other fractional-literal
test is about integer typing (array indices, enum conversions, `addmod`
arguments), which fixed point does not change. solc's verdict is the test's
expectation: a test whose only error is `UnimplementedFeatureError 1834`
passes solc's type checker. The decided rules' verdict is computed where a
function decides it: `Solidity/Language/FixedPoint/Conformance.lean`
holds one kernel-checked `example` per such test, and all of them pass.
Otherwise the verdict is argued from the rule named in the table.

**Classification.** "Accept" means the program compiles under the decided
rules (G00 Q6, full support); "reject" means a compile error.

| Test (under `syntaxTests/` unless marked) | solc 0.8.38 | Decided rules | Basis | Status |
|---|---|---|---|---|
| `constants/mod_div_rational.sol` | accept | accept | `CExpr.eval`, `Fx.ofRat?` (Conformance) | agrees |
| `denominations/fixed_point_division.sol` | reject (the `uint` line); `ufixed(4 ether / 3 hours)` accepted, suggests `ufixed256x62` | same | `Fx.explicitRat?`, `mobileFx?` (Conformance) | agrees |
| `inlineArrays/inline_array_fixed_types.sol`, `inline_array_rationals.sol` | accept | accept | explicit constants and `litCommon?` for the element type (Conformance) | agrees |
| `nameAndTypeResolution/303_…`, `343_integer_and_fixed_interaction.sol`, `smtCheckerTests/operators/fixed_point_add.sol`, `smtCheckerTests/file_level/free_function_4.sol` | accept | accept | `FxTy.intImplicit` (Conformance); the result type `ufixed128x18` of `uint64 + ufixed` is P7, argued | agrees |
| `304`, `305`, `307`, `312`, `314`, `324_fixed_points_inside_structs.sol`, `parsing/lexer_numbers_with_underscores_fixed.sol`, `types/rational_number_literal_to_fixed_implicit.sol` | accept | accept | `Fx.ofRat?` (Conformance) | agrees |
| `smtCheckerTests/operators/fixed_point_compound_add.sol` (`b[0] += 1`) | accept | accept | `litCommon?` (Conformance) | agrees |
| `323_mapping_with_fixed_literal.sol` | accept | accept | `Fx.ofRat?`, `Fx.keyWord` | agrees |
| `328_rational_to_fixed_literal_expression.sol` | accept (all seven lines) | reject: lines `e` and `f`, `ufixed256x80(9.445)` and `ufixed256x80(1.2)`, are out of range at 80 digits; the other five are accepted | `Fx.explicitRat?` (Conformance), which is `Fx.explicitConst?` on the normalized rational; `Fx.explicitConst?_eq_none_iff` characterizes the refusal | intended deviation (Q2: an out-of-range constant is a compile error) |
| `317_fixed_type_valid_explicit_conversions.sol` | accept | reject: `ufixed256x80(1/3)` and `ufixed248x80(1/3)` are out of range; `ufixed8x1(1/3) = 0.3` is accepted | `Fx.explicitConst?_eq_none_iff` (Conformance) | intended deviation (Q2) |
| `parsing/declaring_fixed_and_ufixed_variables.sol` | accept | accept | `FxTy.mk?` (Conformance) | agrees |
| `userDefinedValueType/all_value_types.sol` (`type MyFixed is fixed`) | accept | accept | P8 (identity wrap/unwrap) | agrees |
| `313_fixed_type_size_capabilities.sol` | reject (`b`, `e`) | reject (`b`, `e`); the other four accepted | `Fx.ofRat?` (Conformance) | agrees |
| `315_fixed_type_invalid_implicit_conversion_size.sol` | reject | reject | `FxTy.implicitOK_iff` (Conformance) | agrees |
| `316_…_lost_data.sol`, `parsing/declaring_fixed_literal_variables.sol` | reject, suggesting `ufixed256x77`, `ufixed16x2` | reject; `mobileFx?` gives each suggested type | `Fx.ofRat?`, `mobileFx?` (Conformance) | agrees |
| `344_one_divided_by_three_integer_conversion.sol`, `321_rational_to_bytes_implicit_conversion.sol`, `327_rational_index_access.sol` (fractional constant at `uint256`/`bytes32`) | reject, suggesting `ufixed256x77`, `ufixed8x1`, `ufixed8x1` | reject; `mobileFx?` gives each suggested type | rejection by the integer/bytes typing, argued; the suggestion by `mobileFx?` (Conformance) | agrees |
| † `types/encoding_fractional.sol`, `encoding_fractional_abiencoderv2.sol`, `encoding_packed_fractional.sol`, `encoding_packed_fractional_abiencoderv2.sol` (`abi.encode(0.1, 1)`, packed) | reject (TypeError 6090; packed also 7279 for the integer literal) | reject, as solc, until QL2 is answered | QL2 (§6.2) | agrees for now; QL2 may turn it into an intended deviation |
| `306_invalid_int_implicit_conversion_from_fixed.sol`, `322_fixed_to_bytes_implicit_conversion.sol` | reject | reject | no implicit fixed→integer or fixed→`bytesM` conversion (§1; Q7 is explicit only) | agrees |
| `329_…_signed.sol`, `330_…_unsigned.sol`, † `331_rational_as_exponent_half.sol`, † `332_rational_as_exponent_value_neg_quarter.sol` (fractional exponent of a constant) | reject | reject | `CExpr.eval` (Conformance) | agrees |
| † `372_shift_constant_right_fractional.sol` (`0x42 >> (1 / 2)`) | reject | reject | shifts are not folded on fractional constants (`CExpr`), and Q4 rejects fixed shifts; argued | agrees |
| `333_…_15.sol`, `334_…_neg.sol` (`**` with a fixed exponent) | reject | reject | P8 (no `**` on `Fx`) | agrees |
| `338`–`341` (`~ \| ^ &` on fixed) | reject | reject | P8 (no bit operators on `Fx`) | agrees |
| `operators/signed_rational_modulus.sol` (`.5 % a`; `a` and `c = a % b` accepted by both) | reject ("Fractional literals not supported.") | reject | `litCommonRev?_eq_solc` (Conformance) | agrees (QL1 asks whether to extend) |
| `types/too_small_negative_numbers.sol` | reject (not implicit; explicit possible) | reject; explicit gives `0` | `Fx.ofRat?`, `Fx.explicitRat?` (Conformance) | agrees |
| `types/rational_number_div_limit.sol` | reject (4096 bits), suggests `ufixed8x80` | reject; `mobileFx?` gives `ufixed8x80` | `fitsPrecision`, `mobileFx?` (Conformance, with `2<<4094` written by hand: shifts are not in `CExpr`) | agrees |
| `array/length/const_cannot_be_fractional.sol`, `319`, `320` (fixed array lengths), † `318_invalid_array_declaration_with_rational.sol`, † `array_length_fractional_computed.sol` | reject | reject | array lengths are integer constants (G13), unchanged by fixed point; argued | agrees |
| † `indexing/array_multidim_rational.sol`, † `literalOperations/exponent.sol` (`a ** (1/2)`), † `constants/initialization/addmod_mulmod_rational_arg.sol`, † `enums/literal_conversion_error.sol`, † `storageLayoutSpecifier/layout_fractional_number.sol` | reject | reject | integer typing, unchanged by fixed point; argued | agrees |
| `298`, `299`, `300`, `302`, `types/weird_sized_types.sol` | identifiers (DeclarationError, or accepted as variable names) | the same | `FxTy.mk?` bounds (Conformance); the leading-zero spellings by the scanner's spelling rule (G08), argued | agrees |
| `smtCheckerTests/operators/shifts/shr_unused.sol` (`x >>> 6` at `fixed`) | accept (type checker) | reject | Q4 (shifts rejected) | intended deviation (Q4) |
| `inlineAssembly/unimplemented_fixed_type_variable.sol`, `unimplemented_ufixed_type_variable.sol` | UnimplementedFeatureError 5016 (no compile) | reject | assembly/Yul exclusion (G00 Q1, P8) | agrees |
| `inlineAssembly/solidity_keywords.sol` (`let fixed := 1` in Yul) | accept | outside the model (Yul) | assembly/Yul exclusion | not applicable |
| The nine `elementary_non_address_state_mutability_*.sol` tests (`errors/`, `events/`, `modifiers/`, `parsing/` ×5, `tryCatch/`) | ParserError 9106 | the same | parser (S00/G08), unchanged | agrees |
| `parsing/fixed_literal_with_double_radix.sol`, `invalid_fixed_conversion_leading_zeroes_check.sol`, `lexer_numbers_with_underscores_fixed_fail.sol`, `308_rational_unary_plus_operation.sol` | ParserError/SyntaxError | the same | lexer and parser, unchanged | agrees |
| `types/address/type_type_to_address.sol` (`address(fixed)`) | reject | reject | no conversion from a type expression | agrees |

**Result.** Counted in files: 68 found by the regex and 14 by the second
pass (†), 82 in all.
- 3 files deviate from solc's type checker, in 5 lines, each intended:
  `317` lines `a` and `b`, and `328` lines `e` and `f`, by Q2 (out-of-range
  explicit constants); `shr_unused` by Q4.
- `inlineAssembly/solidity_keywords.sol` is outside the model.
- The four `encoding_*fractional*` files agree until QL2 is answered.
- All others agree.

No defect was found. This is weak evidence for most decisions, because the
upstream tests do not exercise them. Gaps for G15/G51:
- Q1's narrowing of solc's lossy fixed→fixed conversions (F1; `315` is a
  case solc rejects itself);
- Q2's run-time wrapping;
- Q3's run-time rounding;
- Q5's unary minus at `ufixed` (the negations in `307` and `312` are
  constants);
- Q6's `++` at a type without `1`;
- Q8's exact `*`/`/`;
- P1's rounding witness and the no-mobile-type row (§6.2);
- the `ufixed8x77 y; y + 1/3` refusal;
- QL2's inline-array truncation.

**Handoff.** G15 can take the table as the fixed-point slice of its
in-profile classification;
`Solidity/Language/FixedPoint/Conformance.lean` is the regression check a
change to the rules must keep passing. G51
(differential testing) has no solc execution to compare against for any of
these tests: every accepted one stops in solc's code generation.

**Review.** A read-only finder and a separate read-only skeptic reviewed
`c836970`. Both confirmed the counts (87/81/68/64/4/19), every solc verdict
against its test's expectation, and the mobile-type suggestions. Confirmed
findings and their fixes:

| Finding | Source | Fix |
|---|---|---|
| `abi.encode(0.1)`/`encodePacked(0.1)` tests (TypeError 6090) were missed by the regex, and QL2's premise (that solc truncates `abi.encode(1/3)`) was wrong | finder | second pass (†); rows added; QL2 and the §6.2 rows and handoff corrected |
| Other fractional-literal tests were swept inconsistently | finder | added (†) with the scope stated; the author's own second pass added `331`, `332` and `372` |
| "68 uses" counted files; deviations were not given per line | skeptic | counts in files and lines |
| Basis cells overstated what is computed (inline array element type, `b[0] += 1`, `343`'s result type, `div_limit`'s shift, `328`'s function) | skeptic | `litCommon?` examples added; argued rows marked |
| `shr_unused` "agrees with solc's compiler" was meaningless (solc's compiler rejects every fixed program) | skeptic | now "intended deviation (Q4)" |
| Untested decisions were under-listed | skeptic | gap list above |
| Name rows (`299`, leading zeros) argued, not computed | both | `299`'s width added to the example; leading zeros marked argued |
| `344`/`321`/`327` rejections cited `Fx.ofRat?` though they target `uint256`/`bytes32` | finder | split row; rejection argued |
| `315`'s accepted `ufixed a = 11/4` not checked | finder | added |
| "6 `bytes_concat_wrong_type_*` tests" | finder | named exactly |

### 6.6 Backfill — remaining laws (roadmap backfill item 2)

The work queue was done, so the lane took backfill item 2 of
`docs/coverage-plan.md`: complete the fixed-point module and prove the
remaining laws. Items 1, 3 and 4 belong to other lanes or wait for the
Codex lanes. Item 5 (the stipend cost rule) is outside this lane's files.

- `tdiv_trunc`'s companion `tdiv_tdiv`: truncations compose
  (`(x tdiv a) tdiv b = x tdiv (a·b)` for `a > 0`).
- `Fx.rescale_rescale_down`: dropping digits in two steps is dropping them
  at once. `Fx.rescale_mono`: rescaling is monotone.
- `Fx.explicit_le`: an explicit conversion keeps the order of the values it
  does not wrap.
- `Fx.literalTrunc_rescale`, `Fx.explicit_mobile_route` and
  `Fx.explicitRat?_mobile_route` (`Solidity/Language/FixedPoint/Literals.lean`)
  compare two routes when the target has no more digits than the mobile
  type. The first route types the constant at its mobile type, then
  converts it with this model's run-time conversion (Q2, Q3); solc
  type-checks this route but generates no code. That route is the wrap of
  the exactly folded value. Where the exact fold fits the target, the two
  routes give the same value. Out of range, solc accepts and this model
  refuses (Q2).
- `Fx.add_assoc`: `+` is associative wherever the checked sums exist.
- A witness that `*` is not associative (`Laws.lean`, `example`):
  `(0.01 · 0.50) · 2.00 = 0.00` but `0.01 · (0.50 · 2.00) = 0.01` at
  `ufixed16x2`.

Pins: `tdiv_tdiv`, `Fx.explicitRat?_mobile_route`, `Fx.explicit_le`,
`Fx.rescale_mono`, `Fx.rescale_rescale_down` and `Fx.add_assoc` use
`[propext, Classical.choice, Quot.sound]`.

This covers the laws of backfill item 2. The module is not complete. Still
open:
- the more-digits half of the P1 comparison (argument only);
- the distance of a wrapped explicit conversion (Q2);
- constant comparisons, and integer and `bytesM` constants (§6.2);
- QL1 and QL2;
- ABI dynamic aggregates, calldata heads, topics, UDVTs and the empty v2
  revert data (§6.3);
- storage slot starts for structs and arrays, packed array elements, a
  typed `place` over all value types, and wiring `Store` to the typed
  storage (§6.4).

**Review.** A read-only finder and a separate read-only skeptic reviewed
`030a48d`. Both found the proofs sound. Confirmed findings and their fixes:

| Finding | Source | Fix |
|---|---|---|
| The route theorem compares the model with itself (solc generates no code) and hid the out-of-range case behind its premise | both | `Fx.explicit_mobile_route` (premise-free, with wrap); docstrings and this section say "this model's run-time conversion" and name the out-of-range case |
| The more-digits half was presented as proved; "the §6.2 argument" pointed at nothing | both | the §6.2 row marks it as an argument, not proved |
| "Completes backfill item 2" overclaimed | skeptic | "Still open" list above |
| `+` associativity neither stated nor proved | skeptic | `Fx.add_assoc` |
| solc "Rounded" at the mobile digits; it truncates | both | corrected |
| Pins for the new laws missing; the `Laws.lean` docstring not updated; `literalTrunc_rescale` named without `Fx.` | both | added, updated, renamed in the doc |
