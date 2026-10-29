# Source semantics S02: prerequisites and expressions

Lane V04, checkpoints 1 and 2 (roadmap rows S02 in
[coverage-plan.md](../coverage-plan.md)). The S02 prerequisites
(checkpoint 1) and the independent expression semantics on S01's
resolved form (checkpoint 2). Statements, calls and modifiers are in
[source-s03.md](source-s03.md); transactions are in
[source-s04-state.md](source-s04-state.md#s0404-transactions); the
composition and the ledger are in [source-s05.md](source-s05.md).

## Modules

| Module | Content |
|---|---|
| `Solidity/Source/Typing.lean` (extended) | Typing rules S02 needs: struct members (`Typed.member`, `LVal.member`), struct construction (`structNew`), external calls with and without `{value: v}` (`extCall`, `extCallValue`), `transfer`/`send`, `abi.encode`, `abi.encodePacked`, `abi.encodeWithSelector`, `abi.encodeWithSignature` (`abiEncode`), copies into storage (`assignCopy`, `STy.copiesTo`) |
| `Solidity/Source/Resolved.lean` (extended) | The matching `RExpr`/`RLVal` constructors and their elaboration (`Typed.toR`), `Env.fieldTy?_of_fieldAt` |
| `Solidity/Source/Elaborated.lean` | `RBody`, `RModInv`, `RInit`, `RBaseArg`, `Program`, `Elaborated` (a resolution with its resolved bodies) |
| `Solidity/Source/Value.lean` | `RVal`, `Halt`, decidable equality of `STy`, wrapping (`wrapBits_mem`), checked and unchecked arithmetic, shifts, powers, comparisons, conversions of values |
| `Solidity/Source/Machine.lean` | Layouts (`Env.layout`, `Env.cellTy`), `Locals`, the state `St`, frames `Fr`, `Glob`, the monad `EM`, storage and memory operations, copies and deletion |
| `Solidity/Source/Eval.lean` | The interpreter (expressions here; statements and calls in S03) |
| `Solidity/Source/Unique.lean` | Uniqueness of meaning (Q1) and the literal-typing controls |
| `Solidity/Source/Infer.lean` | Type inference computing derivations (item 1b) |
| `Solidity/Source/Elaborate.lean`, `ElaborateExamples.lean` | The elaborator `Resolution → Option Elaborated` and its controls (item 1b) |

## Checkpoint 1: prerequisites

### Resolved bodies in the resolution

`Elaborated` is a `Resolution` with a `Program`: every body as an
`RItems` in its frame (`RBody`), the modifier invocations of a body
resolved against its locals (`RModInv`), each contract's state variable
initializers (`RInit`), each constant's value, and each constructor's
base-constructor arguments (`RBaseArg`). `Elaborated.bodies_typed` records
that each carried body is the elaboration (`ItemsD.toR`) of a typing
derivation of its syntax, with the frame's types. `RBody.ofDerivation`
builds one from a derivation; `RBody.ofDerivation_typed` shows it
satisfies the coherence.

The existing `Resolution` and every public S01 name are unchanged;
`Elaborated` is added beside them.

### Uniqueness

The original design took a canonical choice instead of proving
uniqueness: the semantics reads only the carried `Program`, so a unit's
meaning is a function of its elaboration.

The reviews then answered Q1: follow solc. A literal is always a
constant, and it converts implicitly to a compatible `bytesN`. That is now
the typing (module `Solidity/Source/Unique.lean`):

- **`Typed.constShape`.** Every derivation of a constant expression
  (`Syn.const`) has its rational type, or, for a bare or parenthesized
  hexadecimal literal, its `hexConst` type, and elaborates to that
  constant. Supporting lemmas:
  - `Syn.const_binOp`: a folding operation has constant operands, and
    comparisons and logical operators never fold;
  - `STy.common?_const`: two constant types never meet;
  - `Syn.const_hexLit`.
- **`zeroLength_illTyped`.** `0.length` has no derivation (before, it had
  one at every `bytesN`).

**Uniqueness of meaning for every expression, statement and body** (Q1):

| Theorem | Statement |
|---|---|
| `Typed.unique` | two derivations of one expression have one type and one `RExpr` (`HEq`) |
| `LVal.unique`, `TypedArgs.unique`, `TypedSlots.unique`, `OptCond.unique`, `OptExpr.unique` | the same for lvalues, argument lists, tuple slots and loop parts |
| `StmtD.unique`, `ItemsD.unique` | two derivations of one statement or block leave the same locals and have one `RStmt`/`RItems` |
| `RBody.ofDerivation_unique` | two derivations of one function body give one `RBody` |
| `Typed.const_unique` | the constant-expression corollary |

The expression proof is a strong induction on the syntax's size (`Uniq Γ n`
holds the hypothesis below size `n`), with one lemma per syntactic shape
(`uniqE_bin`, `uniqE_ident`, `uniqE_callIdent`, …) so that each stays
under the default heartbeat limit. The shapes several rules share:

| Shape | Constructors, and what separates them |
|---|---|
| literal and constant expressions | `const`/`litBytes`/`paren`/folding operators, by `Typed.constShape` |
| `ident` | `loc`/`state`/`this`/builtins (resolution is functional) |
| `tuple` | `paren`/`tuple` |
| `unaryPrefix` | `neg`/`negFixed` by type |
| `member` | `length`/`balance`/`magic`/`member` by the operand's type |
| `call (ident f)` | `convUser`/`callInternal`/`structNew`/builtins by what `f` resolves to |
| `call (member c f)` | `extCall`/`transfer`/`send`/`abiEncode` |
| `assign` | `assign`/`assignCopy` (`implicit` and `copiesTo` are disjoint); `compound` (`AssignOp.fits` is false for `.assign`) |
| `index` | by the base's type |
| binary operators | `order`/`eq` versus `compareConst`, by `constShape` on the operands and `STy.common?_const` |

The statement proof is a mutual structural recursion on the first
derivation. Two statement shapes needed a rule change (below):

- `return (x);` with one return type was both `retVal (paren …)` and
  `retTuple … .nil`, which elaborate differently. `StmtD.retTuple` now
  requires two or more components (`σs ≠ []`), and `argsFit_single`
  separates it from `retVal`.
- `_;` in a modifier was `placeholder` or `expr (ident "_")`. `StmtD.expr`
  now refuses `_` in a modifier (`(C.inModifier && e.isUnderscore) = false`).
- The rethrow's variable was not determined at all: its premise
  `(body.paths.map IdPath.last).all (· == d)` held for every `d`, because
  `Syn.paths` collects no Yul names, so any `bytes memory` local could be
  the one rethrown (skeptic review). The premise is now
  `rethrowVar? body = some d`, the buffer the body names
  (`rethrowVar_canonical`).

This is uniqueness of meaning, not of derivations: `(1)` is both `const`
and `paren (const …)`, and both elaborate to `const 1`.

### Typed rules changed (for G13's checker)

| Rule or definition | Before | Now |
|---|---|---|
| `STy` | — | new constructor `hexConst (q : Q) (len : Nat)`: a hexadecimal literal of `2·len` digits |
| `Typed.const` | premises `e.const = some q`, `e.isAddressLit = false` | adds `e.hexLen? = none` |
| `Typed.litBytes` | `n.fitsBytes len = true → Typed Γ (lit (num n)) (fixedBytes len h)` | `(Syn.lit (.num n)).hexLen? = some len → Typed Γ (lit (num n)) (hexConst n.value len)` |
| `Syn.hexLen?` | — | new: `2·len` digits with `1 ≤ len ≤ 32`, through parentheses, not a checksummed 40-digit literal |
| `Syn.isAddressLit` | bare literal only | also through parentheses (its type is now category-polymorphic) |
| `Syn.const` | folded checksummed 40-digit literals | a checksummed 40-digit literal is no constant |
| `STy.implicit` | — | adds `rational q → bytesN` when `q = 0`; `hexConst q n` to integers and fixed point as a rational, and to `bytes{m}` when `m = n` or `q = 0` |
| `STy.explicit` | — | `hexConst` like `rational` |
| `STy.mobile`, `isAmount`, `isIndex`, `isZeroConst`, `inBounds`, `abiArg` | — | `hexConst` like `rational` (`mobile` keeps `hexConst` when no integer type holds it) |
| `RExpr.bytesLit` | `bytesLit (n) (hn : fitsBytes) : RExpr (fixedBytes len h)` | now `bytesLit (n : NumLit) (len : Nat) : RExpr E Γ (.hexConst n.value len)` |
| `RVal` | — | gains `hex` |
| `Syn.hexLen?` (literal gaps) | — | also refuses 39–41 digits: solc reports these as address-like, so they are neither numbers nor bytes |
| `Syn.const` (literal gaps) | — | a 39–41-digit hexadecimal literal is no constant |
| `STy.common?` | `implicit` either way | solc's `binaryOperatorResult`: two constants, or a constant on the left of a `bytesN`, have no common type; otherwise a constant first takes its mobile type (`x + 0x0100` with `x : uint8` is `uint16`) |
| `STy.shiftTy` | — | new: a constant left operand of `<<`, `>>`, `**` with a non-constant amount is at `uint256` (`int256` when negative), as solc's `binaryOperatorResult`; two constants fold |
| `Typed.shift`, `Typed.exp` | result at the left operand's type | at `shiftTy` of it |
| `StmtD.expr` | `Typed (C.at L) e τ` | adds `(C.inModifier && e.isUnderscore) = false` |
| `StmtD.retTuple` | `Typed … e σ → TypedSlots … s σs → argsFit …` | adds `σs ≠ []` |
| `StmtD.rethrow` | `(body.paths.map IdPath.last).all (· == d) = true` (true of every `d`) | `rethrowVar? body = some d` (new function, `Typing.lean`) |

`NumLit.fitsBytes` is kept but no rule reads it any more.

Further consumer-visible changes:

- `HasType.of_const` takes `e.hexLen? = none`.
- `Typed.lit_num` concludes `hexConst` instead of `fixedBytes`.
- `Syn.const` no longer folds checksummed address literals. Array lengths
  and the constant premises of `shift`/`exp` read it too.
- `.hex` values are consumed only by conversion nodes; the evaluator's
  fallbacks treat them as stuck elsewhere.
- The new `rational 0 → bytesN` rule applies to any constant expression
  equal to zero (`bytes4 x = 1 - 1;`), as solc's `m_value == 0` test does.

Controls (`Unique.lean`, `SemanticsExamples.lean`):

| Theorem | Statement |
|---|---|
| `hex_to_bytes2`, `hex_to_bytes4_refused`, `hex_to_uint16`, `zero_to_bytes4` | which conversions a literal admits |
| `zeroLength_illTyped` | `0.length` has no derivation |
| `shiftTy_literal`, `common_literal_bytes_refused`, `common_mobile_step`, `address_like_refused` | the literal gaps: `1 << x` at `uint256`, `0x12 == b` refused, `x + 0x0100` at `uint16`, 40-digit literals refused |
| `hex_literal_bytes` | evaluating `bytes2(0x1234)` gives `0x12 0x34` |

### Review (Q1)

A read-only finder and a separate skeptic reviewed the Q1 change. Fixed:

- the stale docstrings (`Elaborated`, `Const`, `Value`, `Unique`);
- the module title, which now says uniqueness of *meaning*;
- the missing corollary, now `Typed.const_unique`;
- the missing conversion controls;
- the stale lines in `source-s00-s01.md`.

Recorded at the first review; the first five rows were fixed later (see "Review (Q1 completion)"):

| Finding | Status |
|---|---|
| Statement-level non-uniqueness (`retVal`/`retTuple`, `_`) | fixed: `StmtD.unique` |
| `lit << x` and `lit ** x` | fixed: `STy.shiftTy` types them at `uint256`/`int256` |
| Hex literals of 39–41 digits that are not a checksummed address | fixed: refused (`Syn.hexLen?`, `Syn.const`) |
| A literal on the left of a `bytesN` operand (`0x12 == b`, `0 == b`) | fixed: `STy.common?` refuses it |
| `STy.common?` mobile-type step | fixed |
| `abi.encodePacked` of a literal | accepted; solc error 7279 |
| An enum conversion of an out-of-range constant | panics at run time instead of being a compile error |
| `RExpr.bytesLit` | does not tie `len` to the digit count; only `Typed.litBytes` does |
| `Typed.const`'s `isAddressLit` premise | now redundant (harmless) |

### Review (Q1 completion)

A read-only finder and a separate skeptic reviewed the uniqueness proof and
the literal gaps. Fixed:

- **`StmtD.rethrow`** (skeptic): the first change, `head? = some d` over
  `Syn.paths`, left rethrow untypable, since `Syn.paths` collects no Yul
  names (and the original premise held of every `d`). Now
  `rethrowVar? body = some d`, with the control `rethrowVar_canonical`.
- the controls now test what they claim: `common_mobile_step` at
  `hexConst 256 2` (`0x0100`), `shiftTy_literal` with the negative case,
  `common_literal_bytes_refused` with `0 == b`, `address_like_refused` at
  39, 40 and 41 digits against 38;
- the table rows (`Typed.shift`/`Typed.exp`, `shiftTy`'s condition) and the
  overclaiming heading;
- the stale `Elaborated` module docstring.

Recorded, not fixed:

| Finding | Status |
|---|---|
| `Elaborated` ties only `prog.body` to derivations; `consts`, `inits`, `ctor`, `ctorLocals`, `baseArgs` and modifier invocations (`mods`) are unconstrained, and `prog.body d = none` is allowed | item 1b (below) |
| `_ = 1;` in a modifier | solc parses any statement starting with `_` there as the placeholder (a parse error); the model types it if `_` resolves |
| The literal-gap controls are about `STy`, not whole derivations | `STy.common?` and `shiftTy` are the only places the rules read these types |

### Typing gaps closed

| Gap (S01 "What S01 does not do") | Rule | Semantics |
|---|---|---|
| struct members | `Typed.member`, `LVal.member` (`Env.fieldAt`; not on `calldata` as an lvalue) | `RExpr.member`: a storage `field` step or a memory field |
| struct construction | `Typed.structNew` (`S(args)`, the members accepting the arguments) | allocates a memory struct |
| external calls | `Typed.extCall`, `Typed.extCallValue` (exactly one `external`/`public` overload along the callee contract's linearization; `{value: v}` only for `payable`) | `RExpr.extCall` |
| `send`/`transfer` | `Typed.send`, `Typed.transfer` on `address payable` | payments |
| `abi.*` | `Typed.abiEncode` (`AbiKind`, `STy.abiArg`) | standard and packed encoding |
| memory/storage copies, string literals into storage | `Typed.assignCopy` (`STy.copiesTo`) | `storeData`/`storeVal` |

Controls: `TypingExamples.gasleft_untyped` and `msgValue_refused` were
extended to refute the new constructors, and `Typed.ident_builtin_not_struct`
was added. Every existing S01 control still passes.

Not closed: `abi.decode` and other type names as values, `new`, inline
arrays, slices, named arguments, calldata references, and tuple
destructuring (`declTuple`). The ledger in [source-s05.md](source-s05.md)
records these as gaps.

## Item 1b: the elaborator

`elaborate : Resolution → Option Elaborated` (`Elaborate.lean`) builds the
program the semantics runs from a unit's syntax, with no hand-written
resolved terms:

- **Inference** (`Infer.lean`): `Typed.infer`, `LVal.infer`,
  `TypedArgs.infer`, `StmtD.infer`, `ItemsD.infer` return a derivation, so
  they are sound by construction. They follow the rules' premises in order;
  where several rules share a shape, the choice does not matter by
  `Typed.unique`/`StmtD.unique`. Recursion is structural on a fuel equal to
  the syntax's node count (`Syn.nodes`), which the recursion never exhausts
  first. Completeness (a derivation exists ⇒ inference finds one) is not
  proved.
- **Coherence** (`Elaborated.lean`): `Elaborated` now ties every part of
  the program to a derivation, not only bodies:

  | Field | Statement |
  |---|---|
  | `bodies_typed` | each body is `ItemsD.toR` of a derivation in its frame (as before) |
  | `mods_typed` | each modifier invocation's arguments are `RArgs.convert` of a `TypedArgs` derivation in a context with the body's locals (`RConvArgs.Derived`) |
  | `ctor_typed` | a contract's constructor is the body of its constructor declaration |
  | `consts_typed`, `inits_typed` | a constant's value and a contract's initializers are `.conv` of a derivation of the variable's initializer, implicitly converted to its type (`RInit.Derived`) |
  | `baseArgs_typed` | base-constructor arguments are converted derivations in the constructor's locals |

  The elaborator builds each piece as a subtype carrying that proof, so the
  fields hold by construction.
- **Where the syntax goes**: a constructor's invocations that name a
  contract (`constructor() B(x)`) are base arguments, the others modifiers;
  `is B(args)` arguments are typed in the contract's scope with the
  constructor's locals present but unnamed (`anonLocals`), so they fit the
  constructor's frame without being visible.

Controls (`ElaborateExamples.lean`, `#guard`, evaluated by compiled code):
a unit with `contract C is A(7)`, an initializer `uint256 x = 3`, a modifier
`pos(k)` with `require(k > 0); _;` and `g(k)` returning `x + a` elaborates;
deployed and called, `g(2)` returns `12` and `g(0)` reverts; a unit
assigning `true` to a `uint256` does not elaborate.

Limitations:

- `RConvArgs.Derived` says the arguments come from *some* argument list's
  derivation, not that it is the invocation's syntax; the elaborator uses
  the syntax, but the field does not record it.
- A modifier needs a body to be invoked (`Decl.frame?`); named arguments
  (`f({a: 1})`) do not elaborate.
- `progOf` elaborates a body each time the semantics looks it up (lazy, not
  cached); kernel evaluation of elaborated programs is therefore slow, and
  the controls use `#guard`.
- `elaborate` refuses a unit if any body, initializer or base argument
  fails; it does not check `WellFormed` (bases, clashes, pragmas).

## Checkpoint 2: expressions

### Values

`RVal D τ` is a run-time value of type `τ`:

- the `Val` of a value or reference type (S04.01);
- `const q` for a constant, which `conv` converts exactly at its use;
- `strLit bs` for a string literal;
- a tuple of these.

Constants never exist at run time except through a conversion node.

### Arithmetic

All operations are in `Value.lean`.

- **Integers.** Checked integer operations panic out of range
  (`intRes`, `intRes_overflow`); `unchecked` wraps (`IntTy.wrap`,
  `IntTy.wrap_mem`, `intRes_unchecked`). `/` and `%` truncate toward zero
  (`Int.tdiv`, `Int.tmod`). Division or modulo by zero is `Panic(0x12)` in
  both modes (`intBin_divZero`).
- **Fixed point** follows the second-round decisions:
  - `*` and `/` are exact, then truncated toward zero;
  - unary `-` on `ufixed` panics unless the value is 0;
  - `++`/`--` add or subtract the value 1;
  - explicit conversions rescale, truncate toward zero and wrap.
- **Shifts.** `<<` wraps, `>>` is arithmetic on signed integers, and on
  `bytesN` both shift the bit pattern. Neither ever computes a power
  beyond the type's width.
- **Powers.** `**` uses `powMod` when unchecked, and in checked mode
  panics once the base's absolute value is at least 2 and the exponent
  exceeds the width.

### Effect order

The order depends on the pipeline (`Glob.pipeline`; G00 Q4 revised: the
two solc pipelines, as recorded in
[solc-alignment.md](../solc-alignment.md#evaluation-order)):

- binary operators, comparisons, shifts and `**` evaluate the right
  operand first under legacy and the left operand first via IR
  (`evalPair`);
- `addmod`/`mulmod` evaluate their arguments right to left under legacy;
- an assignment evaluates its right-hand side before its target; a
  compound assignment and `++`/`--` resolve their target once;
- arguments of calls, events, errors, tuples, structs and `abi.*` are
  evaluated left to right;
- `&&`, `||` and `?:` evaluate only the operand they select.

Controls: `order_legacy`, `order_viaIR`, `order_differs`, `short_circuit`.

### References and aliases

| Value | Meaning |
|---|---|
| storage reference | a logical `SPath`. A state variable of reference type evaluates to its root path; members, indices and keys append steps (`field`, `index`, `key` with the key's contents) |
| memory reference | a heap address |

`Env.cellTy` is the logical layout of S04.01. A value-type path holds its
value. A dynamic array, `bytes` or `string` holds its length at its own
path. An aggregate path holds nothing.

How an assignment treats a reference depends on its target:

- assigning to a local or a memory element copies the pointer;
- assigning to a storage location copies the contents, member by member
  (`storeVal`, `storeData`), and deletes the elements past a shorter new
  length;
- converting storage to memory copies (`loadMem`, nested aggregates
  allocated);
- converting memory to memory keeps the pointer.

`delete` resets storage below a path but leaves mappings, as solc does
(`deleteStor`). In memory, `delete` assigns a fresh zeroed object.

### Failures

| Failure | Result |
|---|---|
| array and `bytes` indices out of bounds | `Panic(0x32)` |
| enum conversions out of range | `Panic(0x21)` |
| `assert` | `Panic(0x01)` |
| `require`/`revert` with a message | `Error(string)` data (`errorData`) |
| custom errors | selector and ABI-encoded arguments |
| invalid ABI words in decoding | revert with no data |
| writes in a static frame | revert with no data |
| run-time type mismatches | `Halt.stuck`, never reached by the controls |

`Halt.timeout` marks the end of a horizon, not a behaviour. See
[source-s03.md](source-s03.md#horizons).

### Coverage and determinism

The interpreter matches every constructor of `RExpr`, `RLVal`, `RStmt`
and `RItems` without a wildcard. Lean's exhaustiveness check is therefore
the per-constructor check; [source-s05.md](source-s05.md) states the
ledger. The semantics is a function, so it is deterministic by
construction. The non-trivial determinism property is horizon
independence, discussed in [source-s03.md](source-s03.md#horizons).

### Controls (`Solidity/Source/SemanticsExamples.lean`)

| Theorem | Statement |
|---|---|
| `add_overflow_checked`, `add_overflow_unchecked` | `255 + 1` at `uint8`: `Panic(0x11)` checked; `0` unchecked |
| `div_by_zero` | `x / 0` in `unchecked`: `Panic(0x12)` |
| `order_legacy`, `order_viaIR`, `order_differs` | `++a + a` at `a = 1`: `3` legacy, `4` via IR, and legacy is not `4` |
| `short_circuit` | `false && (++a > 0)` leaves `a = 1` |

## What S02 does not do

These items are also listed under `limitations:`.

- **Uniqueness of derivations.** Not true (`(1)`); uniqueness of meaning is proved, see "Uniqueness".
- **Calldata.** `cdRef` values are never produced. External arguments
  are decoded into values, and dynamic ABI types are not decoded
  (`decodeWord` is `stuck` on them).
- **Call options other than `value`.** Not modelled, and neither are
  function-type values or calls through them, `new`, `abi.decode`,
  `type(T)`, slices or inline arrays.
- **Nested arrays.** `uint[][]` keeps the inner location in S01's type
  elaboration, so storage-to-memory conversion of nested arrays is not
  typable, and the copy helpers move inner element types with `withLoc`.
- **Allocation order of struct constructors.** Legacy and via-IR differ
  here, but addresses are unobservable, so this is not modelled.
- **Literal evaluation order inside `abi.encode*`.** Fixed at left to
  right.

## Gates

Recorded in [source-s05.md](source-s05.md#handoff-s05). The
checkpoint-level results (Lean diagnostics clean on every touched file,
G07 checks) are listed there.

## Review

A finder and a separate skeptic reviewed checkpoints 1–5 together. See
[source-s05.md](source-s05.md#review).

## Handoff (S02)

Theorems: `wrapBits_mem`, `IntTy.wrap_mem`, `FixTy.wrap_mem`,
`intRes_overflow`, `intRes_unchecked`, `intBin_divZero`,
`STy.eq_of_same`, `STy.same_refl`, `Env.fieldTy?_of_fieldAt`,
`RBody.ofDerivation_typed`, and the controls above.

What S03 builds on:

- `evalE`, `evalLoc` and `evalConvArgs`;
- `Locals` with `restore`, `getAt` and `setAt`;
- the `EM` monad, in which a halt keeps the state, so emitted events are
  never lost.

For integration, the sibling lanes read four additions: the new `Typed`
constructors, the new `RExpr` constructors, `Elaborated`, and the
`DecidableEq STy` instance in `Value.lean`. A checker (G13) has to produce
the new derivations.
