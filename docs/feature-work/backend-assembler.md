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

## Checkpoint 2 — G45.04 assembler

Module: [Assembler.lean](../../Solidity/Backend/Assembler.lean), vectors in
[Checks.lean](../../Solidity/Backend/Checks.lean). Checkpoint 1's revision
is `add105250de969fa432db3a246ec74e5dccb58d5`.

### Items

In solc's vocabulary (`libevmasm`'s `AssemblyItem`), over any label type
`L` with decidable equality and any library-name type `Lib`:

| Item | Assembles to |
|---|---|
| `instr i` | `i` |
| `tag l` | `JUMPDEST`, defining `l` |
| `pushTag l` | `PUSHw` of `base + off(l)`: absolute, relocated by the section's base |
| `pushTagRel l` | `PUSHw` of `off(l)`: section-relative; `base` plus it is a valid destination of the whole code |
| `pushLibraryAddress x` | `PUSH20` of `x`'s address, or 20 zero bytes and a link reference |

A jump is `pushTag l` followed by `instr (op JUMP)` or `JUMPI`; the theorem
below is about every `pushTag`, so it covers every jump written that way.
A jump through a raw `instr (push …)` or a computed address is not a
resolved jump and is not covered. `assemble base link items` returns the
program (one instruction per item) and the link references
`(byte offset, library)` of the placeholders `link` leaves open; the
offsets are into the whole code (the section's first byte is `base`), as
solc's `linkReferences` are. Per [G05 Q1](../solidity-scope.md#second-round-2026-10-29) the
session deploys and links every library itself, so in the pipeline `link`
is empty and every library push becomes a reference that `linkBytes`
fills once the address is known.

### Width selection

Each label gets one width `W l : Fin 33` for all its pushes. `fixWidths`
starts at 0 everywhere and repeats `widen`: each width becomes
`min 32 (max (W l) (byteWidth (base + tagOffset W l)))`. Widths never
shrink and are capped at 32, so `Σ (32 - W l)` over the referenced labels
drops whenever a round changes something: that is the `termination_by`
measure, and `fixWidths_stable` states the fixpoint. A single pass is not
enough, because widening one push moves every later tag
(`Checks.crossing`: the target is at 255 under `PUSH0`, at 256 under
`PUSH1`, too far for one byte, and at 257 under `PUSH2`; three rounds).
Starting from 0 lets a tag at absolute offset 0 be reached by `PUSH0`.

`assemble` then checks the layout explicitly (`layoutOk`: distinct tags,
every referenced tag defined, every absolute target below `256 ^ W l`), so
soundness does not depend on the fixpoint argument; `assemble_isSome`
shows the check passes whenever it can.

### Theorems

| Theorem | Statement |
|---|---|
| `assemble_pushTag` | `items[k] = pushTag l` ⇒ `out.code[k]` is `push (W l) imm` with `ofBytesBE imm = base + offset out.code j = base + tagOffset W items l`, where `tagIndex items l = some j` and `out.code[j] = JUMPDEST`; and for every encoded prefix `pre` with `size pre = base` and every trailing `X`, `validJumpdest (encode pre ++ encode out.code ++ X) (ofBytesBE imm)` |
| `tagIndex_unique` | with distinct tags, `items[j] = tag l` ⇒ `tagIndex items l = some j`: the destination is *the* tag of `l` |
| `assemble_pushTagRel` | `items[k] = pushTagRel l` ⇒ it pushes `offset out.code j` of that tag, and `base` plus that value is a valid destination of the whole code |
| `assemble_layout` | one instruction per item, `offset out.code k = itemOffset W items k`, and `size out.code` is the layout's total: where a next section starts |
| `assemble_isSome` | distinct tags, referenced tags defined, and every target under the all-32-byte layout below `256^32` ⇒ assembly succeeds |
| `link_patch` | in the whole code (`encode pre ++ encode out.code ++ X`, `size pre = base`), `linkBytes … out.linkRefs addr` is `encode pre ++ encode out'.code ++ X` for the code `out'` assembled with the link map completed by `addr`; `out'` has no references left, the same offsets, and the same instruction at every non-library item, so the jump theorem holds after linking |
| `fixWidths_stable`, `fixWidths_le` | the iteration ends at a fixpoint, above its start |
| `ofBytesBE_toBytesBE`, `lt_pow_byteWidth`, `byteWidth_le` | big-endian immediates round-trip; `byteWidth` is the least sufficient width |

The prefix condition `size pre = base` with `pre` an *encoded program* is
what relocation needs: arbitrary prefix bytes could end in a truncated
`PUSH` whose immediate swallows the section's first bytes. The trailing
bytes are arbitrary (data, CBOR metadata, another section). The output
also decodes: `decode_encode` applies to `out.code`, and
`validJumpdest_encode_iff` gives the converse of the jump theorem for a
section alone.

### Deviations from solc's `libevmasm`

The output is correct by the theorems above but is not byte-identical to
solc's:

- solc gives every tag push one shared width (`bytesPerTag`, at least one
  byte); here each label has its own width, and a tag at absolute offset 0
  is pushed by `PUSH0`, which solc never does for a tag.
- solc assembles each sub-assembly from offset 0 (runtime code runs at
  0). Here a section may sit at any `base`; `base = 0` is solc's case.
  `pushTagRel` is a section-relative offset, as solc's `PushTag` inside a
  sub-assembly placed elsewhere would be, not a relative jump (the EVM
  before EOF has only absolute jumps).
- A label used only by `pushTagRel` is still sized and checked for its
  absolute offset, which can make its push wider than needed.

### Out of scope here

Several sections in one image (creation code embedding the runtime as
data), solc's `PushSub`, `PushSubSize`, `PushProgramSize` and `PushData`,
and tags of a sub-assembly referenced from its parent belong to the
artifact layout (G44.02) and its composition (G45.06). The theorems here
are local to one section; `assemble_layout` gives the section's size, from
which a caller computes the next `base`.

### Checks

`Checks.lean` assembles a solc-shaped branch at base 0 and at base `0x20`
(the absolute push moves from `0x0a` to `0x2a`, the relative one does
not), a tag at offset 0 reached by `PUSH0`, the width-crossing case, refusal
of a missing and of a duplicate tag, and a library call whose placeholder
`linkBytes` fills to exactly the bytes assembled with the address. The
five assembler theorems are pinned at Lean's three axioms.

### Review (checkpoint 2)

Read-only finder and skeptic subagents, no Lean server. Confirmed findings,
all fixed:

- Skeptic: the jump theorem did not tie its index to *the* tag, and fixed
  neither the push width nor uniqueness. `assemble_pushTag` now names
  `tagIndex items l = some j`, the width `W l` and the value as
  `base + tagOffset W items l`; `tagIndex_unique` (through
  `filterMap_nodup_index`) gives uniqueness from distinct tags.
- Skeptic and finder: link references were section-relative and
  `link_patch` covered the section alone. References now start at `base`,
  and `link_patch` is stated over the whole code, prefix and suffix
  included (`linkBytes_from` takes both).
- Skeptic: nothing said linking keeps offsets and jumps. `link_patch` now
  states equal offsets and unchanged non-library instructions.
- Skeptic: no export of the section size. Added `assemble_layout`.
- Skeptic: `pushTagRel`'s theorem said nothing about the whole code. It
  now proves `base` plus the value is a valid destination; the document
  no longer calls it a relocated jump.
- Finder: the deviations from `libevmasm` were unrecorded (section above),
  the crossing example's arithmetic was misdescribed, a `Checks` comment
  named a relative push the vector did not contain, and several `have`s
  had no type (now annotated).
- Skeptic: "covers every jump" overclaimed; reworded to jumps written as
  `pushTag` plus `JUMP`/`JUMPI`, and the out-of-scope section added.

Judgment calls kept: per-label widths (correct, smaller code, recorded as
a deviation); soundness through the explicit `layoutOk` check instead of
the fixpoint, with `assemble_isSome` showing the check passes when it can;
no minimality proof of the chosen widths.

### Handoff (checkpoint 2)

- **Branch:** `cloud/roadmap-l1-20261029/lane-assembler`; checkpoint 1 at
  `add105250de969fa432db3a246ec74e5dccb58d5`, this checkpoint in the commit
  that adds this section.
- **Theorems:** `assemble_pushTag`, `tagIndex_unique`,
  `assemble_pushTagRel`, `assemble_layout`, `assemble_isSome`,
  `link_patch`, `fixWidths_stable`; axioms pinned in `Checks.lean` (Lean's
  three).
- **Premises:** none beyond the statements: `size pre = base` with `pre`
  encoded, distinct tags (checked by `assemble`), the 32-byte bound of
  `assemble_isSome`.
- **Checks:** `lean_diagnostic_messages` clean on `Solidity/Backend/Assembler.lean`
  and `Solidity/Backend/Checks.lean` (all `#guard` vectors pass); layer, orphan, trust and
  doc-path scripts as in checkpoint 1.
- **Remaining:** multi-section images and solc's sub-assembly items
  (G44.02/G45.06); byte-identical solc output is not a goal.
