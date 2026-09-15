# Solidity Rewrite-Calculus and Compiler Verification

This document describes the verification present in this `Solidity`
Lean package: the Solidity-in-KeY rewrite calculus (sections below), and the
verified Solidity → EVM compiler of `Solidity/Evm/`
(["Verified EVM compilation"](#verified-evm-compilation)).

## Scope

The project formalizes the Solidity-in-KeY rewrite calculus and gives its
statements executable meaning.  Its source language is the AST in
`Solidity/AST.lean`; it is not parsed Solidity source code
and it has no ABI, deployment, calldata, or gas claim.  The `Evm/` modules
add a compiler from a fragment of that AST to an EVM-style machine, with a
machine-checked semantic-preservation theorem against the interpreter of
`Semantics.lean`.

The executable semantics models storage trees, an identity-indexed memory
heap, local bindings, and the abstract `net` transfer ledger.  The
`sol!{ < stmts > (post) }` and `sol!{ [ stmts ] (post) }` forms are checked by
`SolidityJudgment.check` / `SolidityJudgment.Holds`.

## Verified components

| Component | Location | Verification provided |
| --- | --- | --- |
| Syntax and measures | `AST.lean` | Solidity expression, statement, and block model; measures used by the executable definitions. |
| Rule enumeration | `Rules.lean` | Rule names, applicability conditions, residual-block constructors, fresh scratch names, and the `stepCases` inventory. |
| Coverage/completeness | `Completeness.lean` | A statement has a first step iff an actual rule of the calculus applies; the completeness theorem is restricted to exactly those covered statements. |
| Multi-step rewriting | `MultiStep.lean` | One-step and reflexive/transitive block rewrite relations and their lifting lemmas. |
| Executable semantics | `Semantics.lean` | A total interpreter. Lean checks termination structurally on statements and with the `4 * WrappedExpr.size + rank` measure for mutually recursive expression evaluation. |
| Semantic state algebra | `SemanticsProperties.lean` | Storage read-after-write, update frames, allocation freshness, heap well-formedness, and recursive storage-to-memory copy frame preservation. |
| Concrete rule checks | `RuleValidation.lean` | `native_decide` validations comparing a rule's original statement and non-empty residual block on discriminating concrete states. |
| Symbolic soundness | `RuleSoundness.lean` | A `<rule>_sound` theorem per unfold rule with a non-empty residual block, relating the original statement and residual block under the interpreter; the two call rules are stated relative to inlining, and three statements carry a documented `sorry` (see `docs/module-map.md`). |
| Compositional soundness | `RewriteSoundness.lean` | Local rule soundness lifts through fresh suffixes and through reflexive-transitive derivations, modulo scratch aliases. |
| Rule uniqueness | `Uniqueness.lean` | Mutual exclusion through the total `candidate` dispatcher and `applicable_eq_candidate`. |
| Rewrite termination interface | `Termination.lean` | A decreasing block measure produces a well-founded rewrite relation and a non-increase theorem for finite derivations. |
| Regression examples | `Examples/Taclets/` | Ports of KeY taclet examples, checked against the executable semantics with `native_decide`. |

The symbolic soundness theorems account for capture-introduced scratch aliases
with agreement of environments outside those names.  Rules that move an
evaluation across the interpreter's order carry explicit purity, success, or
shape hypotheses where needed; these are part of the theorem statements, not
unproved compiler assumptions.

## Verified EVM compilation

`Solidity/Evm/` compiles a fragment of the Solidity AST
to an EVM-style stack machine and proves the compilation preserves the
semantics.  The machine's instruction meanings follow Nethermind's
[EVMYulLean](https://github.com/NethermindEth/EVMYulLean), the reference
EVM formalization in Lean (`2^256`-modular words, `DIV`/`MOD` zero
conventions, `0`/`1` comparisons, word-keyed storage, `JUMPI`, `REVERT`).

| Module | Content |
| --- | --- |
| `Evm/Machine.lean` | Instruction set, one-step relation `Step`, closure `Steps`, abort observation `Reverting`, code-in-context predicate `codeAt`, and the fuel-bounded runner `run` for differential tests. |
| `Evm/Compile.lean` | `compileExpr`/`compileStmt`/`compileBlock`/`compileProgram`: solc-style code generation — locals on the EVM stack (`DUP`/`SWAP`), one storage slot per primitive global root, forward jumps for `&&`, `\|\|`, ternaries, `if`, `require`/`assert`, explicit zero-divisor guards, overflow guards for `uint` `+`/`-`/`*` (`checkedOpCode`), and the balance-checked `transfer` (`transferTail`, reserved balance word `balanceSlotW`). Partial: `none` marks a construct outside the verified fragment. |
| `Evm/BoundedSemantics.lean` | `evalW`/`execW`/`execWBlock`: a uint256-bounded mirror of the official interpreter (checked `uint` `+`/`-`/`*` revert on overflow exactly as the official `checkArith` does — `applyCheckedW`; other out-of-range arithmetic and word-ambiguous comparisons are `.stuck` = "no claim"), and the agreement theorems `evalW_agree`/`execW_agree`/`execWBlock_agree` tying every `.ok`/`.revert` outcome back to `Semantics.evalValue`/`execStmt`/`execBlock`. |
| `Evm/Correctness.lean` | The preservation proof, a forward simulation in the style of Leroy's verified IMP-to-VM compilation: representation relations (`ReprVal`, `ReprSVal`, `ReprState`), `compileExpr_sim`, `compileStmt_sim`/`compileBlock_sim`, and the headline theorems `compile_preserves_ok` / `compile_preserves_revert`. |
| `Evm/Examples.lean` | `native_decide` differential tests (official interpreter vs. machine runner on compiled code, comparing final storage on every layout root, the net ledger and the contract balance — including overflow reverts and insufficient-balance reverts) and concrete instantiations of both preservation theorems (`okProg_preserved`, `revertProg_preserved`, `overflowProg_preserved`, `transferRevertProg_preserved`). |

**The preservation statement.**  For a block `b` compiled against a storage
layout `L` (`compileProgram L b = some code`) and any machine storage
representing the initial state (`ReprState L [] s [] st`):

- if the bounded semantics succeeds, `execWBlock s b = .ok s'`, then the
  official interpreter also computes `s'`, and the machine runs `code` from
  `⟨0, [], st⟩` to `⟨code.length, σ', st'⟩` with `st'` representing `s'`'s
  storage on every root of `L` (`compile_preserves_ok`,
  `final_storage_decodes`);
- if the bounded semantics reverts, the official interpreter reverts and the
  machine reaches a `REVERT` instruction (`compile_preserves_revert`).

The bounded semantics is the precise fragment side condition: its
`.stuck` outcomes (intermediate arithmetic outside `[0, 2^256)` on the
operators the compiler does *not* guard — `**` and every `int`-typed
operator —, `==` on an `int`/`bool` pair, short-circuit on a non-boolean,
a negative transfer amount, a net-ledger entry leaving `[0, 2^256)`)
carry no claim, and the agreement theorems guarantee it never disagrees
with the official interpreter where it does claim something.  Overflow
of `uint` `+`/`-`/`*` and an unfunded `transfer` are *not* boundaries:
the source semantics reverts there, the compiled code carries the
matching guard, and `compile_preserves_revert` covers them
(`overflowProg_preserved`, `transferRevertProg_preserved`).

**Judgment transfer.**  The project's dynamic-logic verdicts
(`SolidityJudgment.check`/`Holds` — run the block, evaluate the
postcondition, a revert validating `box` and refuting `diamond`) transfer
to the machine in one step.  `compileJudgment L b post` compiles the block
followed by the postcondition under the block's final local context;
`judgeW`/`revertW` are decidable bounded checkers (dischargeable by
`native_decide`); and `judgment_transfer` / `judgment_transfer_revert`
turn one checked verdict into both the official `Holds` **and** a machine
reading — the compiled code runs from any representing storage to the end
of the code with the word `1` on top of the stack, or reaches a `REVERT`
instruction.  `Evm/Examples.lean` instantiates this for plain, mapping,
reverting, and (inlined) call-bearing judgments.

**Compiled fragment.**  Expressions: literals, stack locals, primitive
global storage roots, global mapping entries `m[k]` (`uint => uint` and
`uint => bool` roots), global array elements `a[k]` and lengths
`a.length`, primitive fields `r.f` of global struct roots, all binary
operators (short-circuit `&&`/`\|\|`, guarded `/`/`%`, overflow-checked
`uint` `+`/`-`/`*`), `!`, ternaries.
Statements: expression statements, assignments to locals, primitive
roots, mapping entries, array elements, and struct fields, compound
assignments (all those targets included),
`a.push(e)`/`a.push()`/`a.pop()` on global array roots,
`recipient.transfer(amount)`, `uint`/`bool` local declarations
(branch-local declarations are rejected so the two arms of an `if`
agree on the stack shape), `if`/`else`, `require`/`assert`, `revert`.

**Struct roots.**  Field `f` of a struct root compiles to the derived
slot of `f`'s static index in `structDef` — a compile-time constant, so
reads are `PUSH slot; SLOAD` and writes `PUSH slot; SSTORE`.  The
static/run-time position correspondence is not assumed: the bounded
semantics claims a field access only when the stored struct's
field-name spine equals the declaration's (`structSpineOf`), and
`struct_field_at_findIdx` converts that spine equality into the
positional facts the simulation needs.  Non-primitive fields (nested
structs, member arrays and mappings) carry no machine claim
(`ReprField`), and every access to them stays outside the fragment.

**Checked arithmetic.**  The source semantics is solc ≥ 0.8: `+`, `-`,
`*` at `uint` revert when the result leaves `[0, 2^256)`
(`Semantics.checkArith`).  The compiler emits the corresponding guard
(`checkedOpCode`): after `ADD`, `(l+r) < l` detects the wrap; before
`SUB`, `l < r` detects the underflow; after `MUL`, `r = 0 ∨ p / r = l`
holds exactly when the product did not wrap (`mul_overflow_iff`, a
theorem about `Nat`, not an assumption).  `checkedOp_sim` proves each
tail computes the checked result's word or reaches `REVERT` exactly
when `checkArith` reverts; the bounded semantics (`applyCheckedW`)
takes the official path on these operators, so overflow is a proved
revert rather than a `.stuck` boundary.  `**`, the comparisons and the
`int` operators keep the unchecked tails: their overflow remains a
boundary (`checkArithW`), as does the `int`-typed range.

**Transfers.**  The interpreter's abstract `net` ledger lives in
machine storage at `netSlotW addr = netBase + addr`
(`netBase = 2^255 + 2^225`), a third region provably disjoint from
both direct root slots (`< 2^31`) and derived slots
(`< 2^255 + 2^224`), and the contract's own balance
(`State.selfBalance`) in the reserved word `balanceSlotW = 2^255 + 2^226`,
disjoint from all three (`balanceSlotW_ne_*`).  `recipient.transfer(amount)`
compiles to `transferTail`: load the balance word, `REVERT` unless it
covers the amount (the EVM's value-transfer check, which the source
semantics mirrors by reverting), store the debited balance, then debit
the recipient's ledger slot.  The `ReprState` invariant carries every
in-range address's ledger entry and the balance word (`ReprState.balance`,
maintained by every update lemma and by `debitBalance`); the bounded
semantics claims a transfer only when the debited ledger entry stays in
`[0, 2^256)` — the official ledger is an unbounded `Int` and can go
negative, which a word machine cannot represent, so such executions
are out of the fragment (no claim) rather than mis-claimed.  A
negative amount is stuck on both sides (`uint` amounts are untypable).

**Remaining boundary.**  Two constructs stay outside the fragment, for
structural reasons rather than missing engineering:

- *Nested structured element types* — mapping values, array elements,
  or struct fields that are themselves mappings/arrays/structs (e.g.
  `alice.account.balance`, `wallet.stash[k]`, `matrix[i][j]`).  The
  Keccak-free slot derivation is injective by *arithmetic*, which
  works for exactly one level of derivation: composing it overflows
  the 256-bit slot space (`2^224 · 2^224 > 2^256`).  Real EVM layouts
  nest by iterating Keccak, whose injectivity is only conjectural
  (collision resistance); supporting nesting here would replace this
  development's unconditional disjointness theorems with a
  cryptographic assumption.
- *Memory and reference aliasing* — the interpreter's identity-indexed
  heap (`memoryDecl`, reference-typed locals, storage↔memory copies).
  The machine has no memory model; a faithful treatment needs
  `MLOAD`/`MSTORE`, an allocator, and a heap–memory correspondence
  relation — a separate project of at least this size.

**Function calls.**  The source semantics gives `Stmt.callStmt` meaning
only through inlining (`Semantics.execStmt` is stuck on a call;
`SolidityJudgment.checkInlined` expands through the function table first,
mirroring KeY's `functionBodyExpand`).  The compiler follows the same
convention: `compileProgramInlined L depth b` compiles
`inlineBlock depth b`, and `compileInlined_preserves_ok` /
`compileInlined_preserves_revert` restate the preservation theorems for
it — no new trust, since the inliner sits on the source side of the
simulation, inside both the interpreter run and the compiled code.  An
unexpandable or out-of-fuel call leaves a residual `callStmt`, which
`compileStmt` rejects: compilation fails closed rather than claiming
anything.  On call-free blocks `compileProgramInlined` coincides with
`compileProgram` (`compileProgramInlined_callFree`).

**Mappings.**  A mapping root at layout slot `i` stores its entry for key
`k` at the derived slot `mapSlotW (slotWord i) kw = (i+1)·2^224 + kw`
(a gas-free stand-in for the Keccak-derived slots of real EVM storage;
`MAPSLOT` is the machine's version of solc's `keccak256(key ‖ slot)`).
Keys are restricted to `[0, 2^224)` and layouts to `2^31` roots, which
makes derived slots provably injective and disjoint from the direct-slot
region (`mapSlotW_inj`, `mapSlotW_ne_slotWord`) — the collision-freeness
that real EVM code only gets from Keccak's conjectured
collision-resistance is a theorem here.  `ReprRoot` represents a mapping
root entry-wise: for every in-fragment key, the word at the derived slot
represents the entry's value (absent keys read the mapping's default, so
the machine's untouched region must represent the default too).

**Arrays.**  An array root keeps its length at the direct slot (the
solc layout) and element `j` at the derived slot `mapSlotW slot j`.
Compiled reads and writes carry an explicit machine bounds check
(`SLOAD` the length; `DUP`; `LT`; `JUMPI`; `REVERT`) that provably
mirrors the interpreter's out-of-bounds revert — including the order
subtlety that a write's bounds revert fires only after the right-hand
side evaluated, and that on the machine an out-of-range key compares
unsigned against the length word.  `push` stores the element at index
`length` and bumps the length slot; `pop` reverts on an empty array and
decrements the length (the stale element slot is unobservable, since
every read bounds-checks first).  The compiler and the bounded
semantics dispatch mapping-vs-array on the same `isArrayTy` type
predicate, so the emitted code shape and the semantic formula always
agree; a type/storage-shape mismatch claims nothing.  Arrays are
bounded by `2^224` elements (`push` past that is out of the fragment),
which keeps every element slot inside the injective derived-slot
region.

**Machine deltas vs. EVMYulLean**, documented in `Evm/Machine.lean`: no gas
metering, relative forward jumps instead of absolute targets with
`JUMPDEST` validation (compiled code becomes position-independent, which
the code-in-context lemmas rely on; an assembler to absolute targets is a
layout-arithmetic pass kept out of scope), no 1024-item stack bound
(`DUP`/`SWAP` depths are still checked against the real 16 limit), a
`MAPSLOT` instruction deriving mapping-entry slots arithmetically instead
of `KECCAK256` over scratch memory (see **Mappings** above), and no
value-transfer instruction: `transfer` is bookkeeping on the reserved
storage words `netSlotW`/`balanceSlotW` rather than a `CALL` with value,
and the contract balance is that storage word rather than
`SELFBALANCE` (see **Transfers** above).

## Boundaries

- Terminal rules have an empty residual block. Each has a state update
  (`Wp/TerminalUpdate.lean`) with a theorem `execStmt s stmt =
  terminalUpdate r stmt s` under the rule's guard
  (`Wp/Terminal/Update*.lean`, dispatched in `Wp/TerminalRules.lean`);
  their behavior is also exercised concretely by `Examples/Taclets/`.
- The generated rule set contains no catch-all fallback. Uncovered statements
  have no `RuleStep`; they are not silently deleted.
- The interpreter's termination is Lean-checked. The rewrite calculus's
  generic well-foundedness implication is Lean-checked in `Termination.lean`,
  but the concrete all-rules decreasing-measure certificate is still open.
- The rewrite-calculus work proves properties of the formal AST, rewrite
  rules, and interpreter; the `Evm/` work proves preservation from that
  interpreter to the EVM-style machine above. Neither proves correspondence
  with Solidity source parsing, solc, Yul, real Ether transfers, or
  external-call behavior.

## Maintenance checklist

When adding or changing a rule, update `Rules.lean` consistently: the
`RuleName` constructor, `ruleEffect`, every required `ruleNames`
entry, `candidate`, and its `applicable_eq_candidate` case.  Add a
`RuleValidation.lean` entry for a non-empty residual block, keep the
corresponding symbolic soundness theorem current, and import any new module
from `Solidity.lean`.

Validate edits with Lean MCP diagnostics when available; otherwise run the
relevant project build from this directory with `./run-lean.sh`.
