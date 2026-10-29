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
(`Bridge/vendor/EvmYul/EVM/Semantics.lean`) computes the same set, by the
checkpoint 3 vectors (a test through its extracted table, not a theorem).
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

- Finder: the document claimed `starts` is EvmYul's `D_J_aux` without
  evidence. The finder's reason for doubting it (that `D_J_aux` stops at
  the first unparsed byte) was itself wrong: `parseInstr` maps every byte
  without an arm to `some INVALID`, so the scan never stops early.
  Checkpoint 3 checks the agreement and corrects this entry.
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
- **Remaining:** program-level `decode` agreement with EvmYul, which needs
  the Bridge build (checkpoint 3); the modules are not listed in
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

## Checkpoint 3 — agreement with EVMYulLean and EthereumJS

Checkpoint 2's revision is `c1d3cf6ae79e08bd6bbebadb8ba9a7e047b338de`.

### What could and could not be run

The Bridge package needs Mathlib, and on this VM its build cache is
unreachable: the network policy refuses `lakecache.blob.core.windows.net`
(and `mathlib4.lean-cache.cloud`) with HTTP 403. Building Mathlib from
source does not fit the lane, so no Bridge module was written: a Lean
adapter that runs the vendored `decode`/`D_J` could not be elaborated, and
unchecked Lean is not committed. The agreement is therefore checked from
the core, against data taken from the references:

- [scripts/check-backend-vectors.mjs](../../scripts/check-backend-vectors.mjs)
  reads the vendored EVMYulLean tables from their source (`parseInstr` in
  `Bridge/vendor/EvmYul/EVM/Instr.lean`, `argOnNBytesOfInstr` in
  `Bridge/vendor/EvmYul/EVM/Semantics.lean`; not edited), and runs
  EthereumJS at Osaka (`@ethereumjs/evm` 10.1.3, pinned in
  `scripts/evm-vectors/package.json`): its opcode table
  (`getOpcodesForHF`) and its jump-destination scan
  (`Interpreter._getValidJumpDestinations`) on 300 randomized byte strings
  biased towards `PUSHn`, `JUMPDEST` and undefined bytes, and on 200
  randomized encoded programs (any Osaka opcode, `PUSHn` with `n` random
  bytes), with the value EthereumJS reads for each `PUSH1`–`PUSH32`.
  The script fails on any `parseInstr` or `argOnNBytesOfInstr` arm it
  cannot read.
- It writes them as literals to
  [EvmVectors.lean](../../Solidity/Backend/EvmVectors.lean), whose
  `#guard`s compare them with `byteName`, `immWidth` and `jumpdests`. With
  no argument the script fails when the committed file differs from what
  the references give now.

```sh
npm ci --ignore-scripts --prefix scripts/evm-vectors
node scripts/check-backend-vectors.mjs          # drift check
node scripts/check-backend-vectors.mjs --write  # regenerate
```

### Results

| Check | Result |
|---|---|
| EthereumJS Osaka opcodes (150), by byte and name | equal to ours, and no other byte is defined by either |
| EVMYulLean `parseInstr` arms (149), name and immediate width | equal to ours on every arm; the arms are our 150 opcodes minus `CLZ` |
| EVMYulLean on all 256 bytes, through its table (`evmYulParse`) | our immediate width everywhere, `JUMPDEST` exactly at `0x5b` |
| EthereumJS's jump-destination scan, 300 random codes | equal to `jumpdests` |
| EVMYulLean's `D_J_aux`, transliterated over its table (`evmYulDJAux`), 300 random codes and 200 programs | equal to `jumpdests` |
| 200 random encoded programs | `decode` accepts each, `encode` gives its bytes back, `jumpdests` is EthereumJS's, and every `PUSH1`–`PUSH32` value (`pushValues`, through `ofBytesBE`) is EthereumJS's |
| EVMYulLean's `decode` immediate, transliterated (`evmYulPushValue`), on the 200 programs | equal to our values |

### Recorded divergences of the vendored EVMYulLean

- **`CLZ`.** Its table predates EIP-7939 (its `TargetSchedule` is still
  Cancun, a G06 residue): `0x1e` parses as `INVALID`. Execution differs;
  jump destinations do not, since neither reading has an immediate.
- **Truncated final `PUSHn`.** Its `decode` takes the value of the bytes
  present (`uInt256OfByteArray` of `extract'`), while the yellow paper and
  EthereumJS (`setLengthRight`) pad the missing bytes with zeros on the
  right: for `61 01` EVMYulLean pushes 1, the yellow paper `0x0100`
  (both pinned in `Solidity/Backend/EvmVectors.lean`, EthereumJS's value as generated). Our `decode` refuses
  such code; it concerns G46's execution bridge, not encoding.
- Undefined bytes parse as `some INVALID`, so `D_J_aux` scans every byte
  and agrees with `D_J` and with `jumpdests`.

### Limits

These are tests, not theorems: the EVMYulLean data is read from its
source text, and `evmYulDJAux` is a transliteration of `D_J_aux` (with fuel
for its `partial`), not the vendored function. The decoder agreement on
programs (`decode` at each offset, with `UInt256` immediates) needs the
Bridge build; its statement is ready: for `p : Program` and `k` below its
length, EvmYul's `decode (encode p) (offset p k)` is the opcode of `p[k]`
with, for `push n imm` and `n > 0`, the immediate `(ofBytesBE imm, n)`.

EthereumJS's jump-destination scan reads byte ranges, not its opcode table,
so the scan vectors check `starts` itself; the opcode-table vectors check
the table.

**Status: partial.** The opcode tables, jump destinations, `encode`/
`decode` and `PUSH` values agree with EthereumJS at Osaka and with
EVMYulLean's tables and a transliteration of its `D_J_aux` and `decode`
immediate. Not done: a `Bridge/` module that runs the vendored `decode`
and `D_J` themselves, blocked by the Mathlib cache (see above); it is the
open question of this checkpoint.

### Review (checkpoint 3)

Read-only finder and skeptic subagents, no Lean server.

- Skeptic: the decoder and `PUSH` values were not compared, and the random
  inputs were byte strings only. Added the 200 random encoded programs
  (decode, re-encode, jump destinations, `PUSH` values against EthereumJS)
  and the transliterated EVMYulLean immediate.
- Skeptic: no status was given; the status is now partial, with the
  missing Bridge module named, and the checkpoint-1 lines say "test, not
  theorem".
- Finder: the source extraction could drop a differently written arm
  silently. The script strips comments and fails unless every arm of both
  functions was read.
- Finder: the bytes `0xe6`–`0xe8` (EIP-8024, after Osaka) are now among
  the biased bytes, the generated header records `@ethereumjs/common`'s
  version, and the checkpoint-1 handoff names what remains precisely.
- Judgment call kept: the vectors module lives in the core. It holds
  literal data and `#guard`s, imports only `Solidity.Backend.Assembler`,
  and runs nothing external; the Bridge module it stands in for is the
  open item.

### Handoff (checkpoint 3)

- **Branch:** as above; checkpoint 2 at `c1d3cf6a`, this checkpoint in
  the commit that adds this section.
- **Checks:** `node scripts/check-backend-vectors.mjs` (no drift);
  `lean_diagnostic_messages` clean on `Solidity/Backend/EvmVectors.lean`
  and `Solidity/Backend/Opcode.lean` (new `Op.name`, `byteName`); layer,
  orphan, trust and doc-path scripts as before.
- **Remaining:** the Bridge module running the vendored functions, with
  the decoder statement given under Limits; it needs a reachable Mathlib
  cache (or a Mathlib build from source).

## Checkpoint 4 — G45.03 preparation: structured control flow

Checkpoint 3's revision is `aa884362cd180400f770d6706699d64372116440`.
Module: [Control.lean](../../Solidity/Backend/Control.lean), vectors in
`Solidity/Backend/Checks.lean`.

`Block` is structured code: `code is` (straight-line instructions),
`seq a b`, `ite cond thn els` and `loop cond body`, where a condition is
an instruction sequence leaving one word. `Block.expand b n` turns it into
assembler items over `Nat` labels drawn from `n` on, returning the next
free label, in the shapes of solc's legacy code generator
(`ContractCompiler`'s `IfStatement` and `WhileStatement`):

| Block | Items (fresh labels `n`, `n+1`) |
|---|---|
| `ite c t e` | `c; ISZERO; pushTag n; JUMPI; t; pushTag (n+1); JUMP; tag n; e; tag (n+1)` |
| `loop c b` | `tag n; c; ISZERO; pushTag (n+1); JUMPI; b; pushTag n; JUMP; tag (n+1)` |

solc's `while` also places a `continue` tag before the backedge, and its
`if` without `else` uses one tag; both come with `break`/`continue` below.

| Theorem | Statement |
|---|---|
| `tags_range`, `expand_le` | the expansion defines labels only in `[n, next)` |
| `tags_nodup` | it defines each label at most once |
| `refs_defined` | every label it references, it defines |
| `expand_assemble_isSome` | it assembles whenever its widest layout fits 32-byte pushes |
| `loop_tagIndex`, `ite_tagIndex` | placed after any items `pre` (and before any `post`) among distinct tags, a loop's head and exit labels are its first and last items; an `if`'s false label follows `iteHead` (condition, conditional jump, true branch, jump to the end) and its end label is its last item |
| `loop_jumps`, `ite_jumps` | in the assembled code, every push of those labels (the backedge, the loop exit, the jump to the false branch, the jump to the end) has the absolute offset of exactly that item as its value |
| `pushTag_value` | the general form: a push of a label whose tag is item `j` pushes `base + offset out.code j` |
| `expand_loop_layout` | for a top-level loop: head first, exit last, both `JUMPDEST`, exit offset plus one is the code size |

The placement lemmas take the surrounding items as parameters, so a loop or
`if` nested in a `seq`, a branch or another loop is covered as long as the
whole item list has distinct tags; `tags_nodup` gives that for a whole
expansion. That every jump of an expansion lands on its own label's
`JUMPDEST` is the general `assemble_pushTag` with `tagIndex_unique`; the
two `…_jumps` theorems state it for the structured jumps by position.

`Checks.lean` assembles a countdown loop to
`5b 5f 54 15 60 10 57 60 01 5f 54 03 5f 55 5f 56 5b` (backedge to the head
at 0 by `PUSH0`, exit at the last byte `0x10`) and an `if`/`else` to
`5f 54 15 60 0e 57 60 01 60 01 55 60 14 56 5b 60 02 60 01 55 5b` (false
branch at `0x0e`, end at `0x14`).

**Not claimed.** That the expanded code *runs* the structured program
needs a step semantics of the EVM over these instructions (stack, `JUMPI`
on the popped word, the backedge's iteration): that is G45.03 proper, and
G45.01/G45.02 fix what conditions and bodies leave on the stack. `code`
and conditions are raw instructions, so nothing yet forbids a raw jump
inside them.

### Review (checkpoint 4)

Read-only finder and skeptic subagents, no Lean server.

- Finder and skeptic: the `if` was not solc's legacy shape (no `ISZERO`,
  branches swapped). It now emits `ISZERO` and the true branch first,
  pinned by a byte vector.
- Skeptic: the layout theorem covered a top-level loop only and never
  named the backedge's value. Added `loop_tagIndex`/`loop_jumps` and
  `ite_tagIndex`/`ite_jumps` for any placement, through `pushTag_value`.
- Finder: `offset out.code 0 = 0` was a trivial conjunct (dropped); "every
  jump lands" was stated as if it were a theorem of this module (reworded
  above); the review section pointed nowhere; generic list helpers were
  public (now `private`); no `if` byte vector (added).
- Judgment calls kept, listed under Remaining: `Block` has no
  `break`/`continue`/`return` and no stack discipline, and `code` may hold
  raw jumps; the generic `tagIndex_isSome` and `itemOffset_succ` sit in
  `Solidity/Backend/Control.lean` because only it uses them so far.

### Handoff (checkpoint 4)

- **Branch:** as above; this checkpoint in the commit that adds this
  section.
- **Theorems:** `Block.tags_nodup`, `Block.refs_defined`,
  `Block.expand_assemble_isSome`, `Block.loop_jumps`, `Block.ite_jumps`,
  `Block.expand_loop_layout`; axioms pinned in `Checks.lean` (Lean's
  three).
- **Checks:** `lean_diagnostic_messages` clean on all six
  `Solidity/Backend/` modules (a convention pass typed the remaining
  `have`s in `Opcode.lean`, `Jumpdest.lean` and `Assembler.lean`); layer,
  orphan, trust and doc-path scripts.
- **Remaining for G45.03:** the execution meaning of the expansion;
  `break`/`continue`/`return` with an environment of exit labels; a block
  type whose `code` excludes jump opcodes and carries a stack effect.
