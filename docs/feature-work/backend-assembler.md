# Backend: EVM byte encoding and assembler (G45.05, G45.04)

Roadmap group G45 ([coverage-plan.md](../coverage-plan.md), wave 5),
lane "assembler" of batch `roadmap-l1-20261029`. The checkpoints are
prepared against an instruction datatype defined here, which the later
G45.01–G45.03 lowering targets. They do not depend on the source semantics
or on `Solidity/Evm/**`, and touch neither.

Fork: Osaka ([G00 Q3](../solidity-scope.md#user-decisions-2026-10-29)). The
EIP-170/EIP-3860 code-size limits and the gas caps are idealized (G01 Q2,
G06 Q2): no size bound is imposed on assembled code, and gas is not
modelled.

## Checkpoint 1 — G45.05 byte encoding

Modules: [Opcode.lean](../../Solidity/Backend/Opcode.lean),
[Jumpdest.lean](../../Solidity/Backend/Jumpdest.lean),
[Checks.lean](../../Solidity/Backend/Checks.lean). They import nothing but
each other (no `Solidity.*` module, no Lean meta code), so they elaborate
in seconds and sit outside both the core and the elaborator layer of
[parallelism.md](../parallelism.md).

### The instruction datatype

- `Op` — every Osaka opcode without immediate data: the 80 fixed opcodes,
  including `CLZ` (`0x1e`, EIP-7939), `TLOAD`/`TSTORE` (`0x5c`/`0x5d`,
  EIP-1153), `MCOPY` (`0x5e`, EIP-5656), `PREVRANDAO`, `BLOBHASH`,
  `BLOBBASEFEE` and `INVALID` (`0xfe`); and the indexed families `DUP n`,
  `SWAP n` (`n : Fin 16`) and `LOG n` (`n : Fin 5`). No EOF opcode: EOF is
  not part of Osaka.
- `Instr` — `op o`, or `push n imm` with `n : Fin 33` and
  `imm : Vector UInt8 n`. `PUSH0` is `push 0 #v[]`. The immediate is
  intrinsically exactly `n` bytes, most significant first, so there is no
  oversized or truncated `PUSH` instruction to rule out afterwards.
- With the 33 `PUSH` widths that is 150 opcodes, the Osaka count; the
  `#guard` in `Checks.lean` counts the bytes that decode.

### Encoding and decoding

- `Op.code`, `pushCode`; `Instr.encode`, `encode : Program → List UInt8`.
- `Op.ofCode` and `pushWidth` read a byte. `decode : List UInt8 → Option
  Program` refuses an undefined opcode and a `PUSHn` with fewer than `n`
  bytes left. (The EVM executes such code, reading missing immediate bytes
  as zero; jump-destination analysis below is defined on all bytes for that
  reason. `decode` is the inverse of `encode`, not an execution front end.)
- Reading is checked once over all 256 bytes (`tableAgrees_all`,
  `decide +kernel` on a Boolean table, no `native_decide`), which gives
  `Op.code_ofCode` and `pushCode_of_pushWidth`; writing is checked by cases
  over `Op` and `Fin 33` (`Op.ofCode_code`, `Op.pushWidth_code`,
  `pushWidth_pushCode`).

| Theorem | Statement |
|---|---|
| `decode_encode` | `decode (encode p) = some p` |
| `encode_injective` | `encode p = encode q → p = q` |
| `encode_decode` | `decode c = some p → encode p = c` |
| `Op.code_injective` | distinct opcodes have distinct bytes |
| `length_encode` | `(encode p).length = size p` |

### Jump-destination analysis

`starts c` scans a byte list from offset 0, stepping over each `PUSHn`'s
`n` immediate bytes (whether or not they exist). `jumpdests c` keeps the
boundaries that hold `0x5b`, and `validJumpdest c i` asks whether `i` is
one; this is the yellow paper's `D_J`. EvmYul's `D_J_aux`
(`Bridge/vendor/EvmYul/EVM/Semantics.lean`) differs: it stops scanning at
the first byte its table rejects (an undefined opcode, and `CLZ`, which its
pre-Osaka table lacks), so it drops every later `JUMPDEST`. Checkpoint 3
records this as a known divergence.
`InPushData c i` holds when `i` lies inside the immediate of a `PUSH` at a
boundary.

| Theorem | Statement |
|---|---|
| `mem_starts_iff_boundary` | `i ∈ starts c ↔ Boundary c i`, the yellow paper's recurrence `N(i, w)` as an inductive predicate |
| `mem_starts` | `i ∈ starts c ↔ i < c.length ∧ ¬ InPushData c i` |
| `validJumpdest_iff` | `validJumpdest c i ↔ c[i]? = some 0x5b ∧ ¬ InPushData c i` |
| `starts_encode_append` | `starts (encode p ++ X) = offsets of p ++ (starts X shifted by size p)` |
| `validJumpdest_encode_append` | a `JUMPDEST` instruction of `p` is a valid destination in `encode p ++ X`, for any `X` |
| `validJumpdest_encode_append_iff` | for `n < size p`: `validJumpdest (encode p ++ X) n ↔ ∃ k, p[k]? = some (op JUMPDEST) ∧ offset p k = n` |
| `validJumpdest_encode_prefix` | relocation: `validJumpdest (encode q ++ Y) (size q + n) = validJumpdest Y n` |
| `validJumpdest_encode_iff` | `validJumpdest (encode p) n ↔ ∃ k, p[k]? = some (op JUMPDEST) ∧ offset p k = n` |

`mem_starts` is the partition statement: every byte of the code is either
an instruction boundary or push data, never both. `InPushData` is defined
through the boundaries `starts` computes, so `mem_starts` and
`validJumpdest_iff` are consistency statements about one scan. The
independent description is `Boundary`, the recurrence written as an
inductive predicate (`Boundary.zero`, `Boundary.next`), and
`mem_starts_iff_boundary` proves the scan computes exactly it.
`validJumpdest_iff` is the G45.05 requirement "a JUMPDEST at an instruction
boundary, not inside PUSH data". The `encode … ++ X` forms are what the assembler needs: code
placed in front of other bytes (a runtime section, data, metadata) keeps
its jump destinations.

### Checks

`Checks.lean` pins solc's prologue `PUSH1 0x80 PUSH1 0x40 MSTORE` as
`60 80 60 40 52`, the Osaka additions, the `DUP`/`SWAP`/`LOG`/`PUSH` ranges,
the 150-opcode count, refusals of undefined opcodes (`0x0c`, `0xfb`) and of
truncated immediates, and `jumpdests` on data-shadowed, `PUSH0`, truncated
and undefined-opcode code. The bytes that decode are compared with a literal list
of the 150 Osaka opcode bytes, written out from the execution-specs table,
so the table is checked against a second transcription and not only
against itself. It pins the axioms of the ten theorems of the tables above
that matter downstream: Lean's own `propext`, `Quot.sound` and, for the
ones reasoning through `omega`/`by_cases` (`mem_starts`,
`mem_starts_iff_boundary`, `validJumpdest_iff`,
`validJumpdest_encode_append_iff`, `validJumpdest_encode_prefix`),
`Classical.choice`. No `native_decide`, no `sorry`.

### Review (checkpoint 1)

Read-only finder and skeptic subagents, no Lean server. Confirmed
findings, all fixed:

- Finder: the document claimed `starts` is EvmYul's `D_J_aux`; it is not,
  since EvmYul stops at the first byte it cannot parse. Reworded, and
  recorded for checkpoint 3.
- Finder: the module docstring overstated what the 256-byte table proves,
  cited only G01 Q2 for gas, and two `have`s closed with bare `simp`
  (now `List.take_left'`/`List.drop_left'`). The README row described
  checkpoints not yet done.
- Skeptic: `InPushData` is defined through `starts`, so the
  characterization was scan-relative. Added `Boundary` and
  `mem_starts_iff_boundary`.
- Skeptic: the trailing-bytes direction and relocation behind a prefix were
  missing. Added `validJumpdest_encode_append_iff` and
  `validJumpdest_encode_prefix` (with `offset_lt_size`).
- Skeptic: the axiom attribution was wrong and the pins did not cover the
  tables. Pinned five more theorems and corrected the sentence.
- Skeptic: no explicit `PUSH`/opcode disjointness lemma
  (`ofCode_of_pushWidth`, now part of the 256-byte table), `Instr.opcode`
  moved next to `encode`, `Instr.size_push` named, and the 150-opcode count
  is checked against a literal list.

Judgment calls kept as they are, with reasons:

- `decode` is partial (undefined bytes, truncated final `PUSH`). It is the
  inverse of `encode`, which is what G45.05 asks for. Arbitrary bytes, such
  as solc output with CBOR metadata, are read by the jump-destination
  analysis, which is total. The assembler places data after code through
  the `encode p ++ X` forms.
- `validJumpdest` filters a list per query, which is quadratic over a
  whole program. It is a specification; nothing decides it on large code.
  A bitmap implementation with an equivalence lemma can replace it if a
  later check needs speed.
- Numeric `PUSH` immediates (big-endian value, minimal width) belong to
  the assembler and are in checkpoint 2.

### Handoff (checkpoint 1)

- **Branch:** `cloud/roadmap-l1-20261029/lane-assembler`, from base
  `ceb0d54b`. The commit that adds this section carries the checkpoint.
- **Theorems:** the two tables above; headline `decode_encode`,
  `encode_injective`, `encode_decode`, `validJumpdest_iff`,
  `mem_starts_iff_boundary`, `validJumpdest_encode_iff`.
- **Premises:** none (no hypotheses beyond the statements, no axioms
  beyond Lean's).
- **Checks:** `lean_diagnostic_messages` clean on the three modules;
  `node scripts/check-layers.mjs`, `node scripts/check-orphans.mjs`,
  `bash scripts/check-trust.sh` pass; `bash scripts/check-doc-paths.sh`
  reports the base's 46 missing references and no new one. Elaboration of
  the three modules takes seconds (they import no `Solidity.*` module).
- **Remaining:** agreement with EvmYul's decoder (checkpoint 3, with the
  `D_J_aux` divergence above); the modules are not listed in
  `scripts/check-layers.mjs`'s `CORE` (that script is outside this lane's
  files), though they reach no elaborator module.
