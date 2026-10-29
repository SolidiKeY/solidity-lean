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

Typing derivations are not unique, and this checkpoint does not prove
uniqueness. The assignment allowed a canonical choice instead. The choice
here is the carried `Program`: the semantics reads only that, so a unit's
meaning is a function of its elaboration. What is not proved is that two
different derivations of one body behave the same. Known sources of
non-uniqueness in S01:

- a hexadecimal literal is a constant (`Typed.const`) or a `bytesN`
  (`Typed.litBytes`);
- a zero literal is a `bytesN` of every length (`NumLit.fitsBytes`);
- a comparison of two literals is `compareConst` or, at `bytesN`,
  `compare`.

These alternatives are not always harmless. For example, `0.length` has a
derivation at every `bytesN` (values 1 to 32), and solc refuses it. The
fix is solc's literal typing: a literal is always a rational, and the
rational converts to `bytesN` when compatible. That changes `STy` or
`Typed` constructors that the sibling lanes read, so it is listed under
`questions:` (Q1).

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

- **Uniqueness of derivations.** Not proved; see "Uniqueness" and Q1.
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
