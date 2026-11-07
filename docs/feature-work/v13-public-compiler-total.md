# V13: G42 public compiler success (H62/H69) and the H68 payload

Lane `cloud/move6-20261106/v13-abi` (H75: moved from the Codex lane
`solidity-v12-v17-20261031/v13-abi-world`). Modules:
`Backend/AbiWorld/PublicCompilerTotal.lean` and its Controls.

## Q-G42-PUBLIC-COMPILER: the reconciled declaration

Read-only inspection of master, RO's v2 interface
(`origin/cloud/move6-20261106/ro-base`, `Lowering/Readonly/SourceDispatchInterfaceV2`)
and the G49 base (`origin/cloud/move6-20261106/g49-base`):

| Item | Fixed as |
|---|---|
| Public compiler declaration | `Solidity.Evm.Compiler.compile (b : Nat) (F : Frag Γ) (P : Prog C Γ Δ) : Option (Compilation b F P)` — the single checked entry every G38/G40/G42 consumer selects ("public compiler" in `abi-entry.md`, `g38-failure-paths.md`). No separate G42 world-call compiler exists: `g42-world-call-consumers.md` records that no world CALL is implemented. RO's V2 interface is Source-only (dispatch partition, histories) and declares no compiler. |
| Fixed outcome/returndata observation | `Compiler.Compilation.Agrees`, obtained from `Compilation.Input` by `Compilation.correct`: success with typed state, stack and the branch's `Rep`; a disjunction pairing each source outcome with a machine outcome (one direction, no converse): source revert or asserting panic with machine `.revert`; source success with a payment revert; divergence with fault (or payment revert). The machine `revert` carries **no returndata**. The core branch refuses `revertData`/`catchData`/`tryCall` (`inFrag` returns `none`); refusal by the seven memory backends is observed in examples, not proved generally. |
| Supported input domain (this lane's statement) | `PublicCompilerTotal.ProgOk`: inductive predicates over the intrinsic syntax that mention no acceptance function, fragment or compile result (the word-fit conditions read the backend storage layout `Evm.offset`). Storage paths (aliases; roots; struct fields whose offset fits a word; `uint`-keyed mappings; dynamic and word-sized fixed arrays); values: literals, booleans, locals, environment reads other than `address(this).balance`, storage reads, every typed unary and binary operator, ternaries and storage-array lengths; statements: storage value assignment, local assignment, value declarations, storage-alias declarations with an initializer and rebinds, plain (a path through no array index and no indexed alias, `FreePath`) or indexed (through an array index or an indexed alias, `IndexedPath`; H96), each alias keeping the kind of its declaration (`Kinds`), `op=`/`++`/`--` on locals and storage locations, `require`, `assert`, `revert`, `if`, blocks, `while`, internal calls with value arguments and no or one value return. Widened by H87 and H96 (2026-11-06). |

**Framing and H87.** The domain is a subset of the core branch's fragment.
The user's decision H87 (relayed 2026-11-06, answering Q1) required widening
before acceptance: signed `&`/`|`/`^`, aliases and storage compound
assignment. All three are now in the domain; signed bitwise needed a compiler
extension (below). Remaining exclusions (H87: they stay documented gaps), in
two kinds:

- refused by the compiler: `address(this).balance` (`simpleIn`), non-`uint`
  mapping keys and word-overflowing offsets (`locIn`), `send`, memory
  statements outside the core branch, multiple returns, recursion and
  external/self/library calls;
- compiled by the core branch but outside this domain: aliases declared
  unset (unreadable until rebound; a later rebind is accepted by the compiler
  but this domain does not track it), rebinds that change an alias's kind
  (accepted, but where `if` branches disagree the meet marks the alias `dead`
  so a later read is refused, and a loop whose body changes a flag fails the
  fixed-point check; the Controls show the loop refusal; a kind change at top
  level, or the same change in both branches, is compiled and could be
  covered by letting a rebind update `K`), transfers, `push`/`pop`/`delete`,
  `assignIncDec` (`x = l++`) and static storage copies.

**H96 (2026-11-06): aliases through an array index.** The judgement now
carries the kind of each alias in scope (`Kinds`, a list read by position:
`true` = indexed). A declaration or rebind to an `IndexedPath` (an array index or
an indexed alias in the path's own chain of bases; an index inside a mapping
key does not count) records or requires `true`; to a `FreePath`,
`false`. `Matches K F` says the fragment flags each alias as its kind
(`fragile`/`ok`); `IndexedPath.not_free`, `FreePath.bindFl` and `IndexedPath.bindFl` show the compiler binds
exactly that flag, and `Frag.set_of_get` that a kind-preserving rebind leaves
the fragment unchanged, so meets and loop fixed points still hold. Call bodies
start from no kinds (`Frag.init`).

The domain is not widened to G01 `S.Admitted`.

The Controls kernel-evaluate the public entry on `address(this).balance` and
on an `int`-keyed mapping read and observe refusal (`isNone`), and on a signed
`&` and observe the former refusal is gone; the word-fit conditions are
refusals by `locIn`'s code without a kernel control.

## H87 compiler extension: signed `&`, `|`, `^`

The source reads `&`, `|`, `^` at `int` in two's complement
(`Semantics.uintBitwise`). `Evm/Layout.lean` now admits them at `int`
(`binInFrag`: any non-`bool` type) and emits the opcode on the words
(`sTail .band = [.and]`, `.bor`, `.bxor`). `Evm/SimLemmas.lean` proves the new
`stail_simT` cases: `bitwise_sgn` shows the source result is the signed reading
of the operator on the words (via `wordOf_sgn`, `signedOf_eq_sgn`), the result
stays an `int256`, and `sword_sgn` matches the pushed word. Every consumer of
`tail_simT` (core, memory, object backends) inherits it. This closes R12's
signed-bitwise half (`roadmap-g04-restrictions.md`; the signed `>>` half was
already compiled through `sarCode`). Two other lanes' controls asserted the
old refusal and are now the acceptance fact (hand-off to their owners,
diamond-try checkpoint and v09-compiler-passes)
(`PrimitivePackets/Bitwise/Selected.signed_accepted`,
`Passes/BitwiseValueContextControls.signed_acceptance`; pin renamed).
Stale records, proposed for their owners and not edited here: R12 in
[G04 restrictions](roadmap-g04-restrictions.md) (both halves now compiled;
`Layout.lean:410` moved), the note in
[V09 passes](roadmap-v09-compiler-passes.md) that signed `&`, `|`, `^` stay
uint-only, and the generated [G03 ledger](roadmap-g03-ledger.md) (and its
JSON) via `scripts/roadmap-g03-ledger.py`, which still calls signed `&`, `|`,
`^` refused.
Checking note: `Layout.lean` is imported early, so this rebuilds most of the
library once; no proof became slower by design.

## Compiler-success (totality) theorem

- `compile_core b hF hP : ∃ G h, Compiler.compile b F P = some (.core G h)` for
  every base `b`, every `Matches K F` (each storage alias of `Γ` flagged as
  its kind in `K`; value locals unconstrained; e.g. `Frag.init Γ` with
  `K = []`, the fragment of a whole program or call body) and every
  `ProgOk K P`. Against the pre-H87 version, which held for every `F` on
  alias-free programs, this excludes only fragments with a dead alias.
- `compile_isSome`: the same as `isSome`; `compile_init` at `Frag.init Γ` for `ProgOk [] P`.
- `compile_agrees`: the selected result satisfies the fixed observation
  `Agrees L frame base σ m` from every `Sim C L b F σ m` with `L ≤ Lmax`
  (the core push bound is discharged because domain programs push nothing).

The proof shows (by mutual induction on the domain) that values are accepted
from every readable fragment, that programs push, pay and shrink nothing, and
that `inFragP` only pushes locals (`Grows`) flagged as their kinds and
kind-preserving rebinds leave the fragment unchanged (`Frag.set_of_get`), so branch meets, scope
restriction and the loop fixed-point check hold. Axioms: `propext`, `Classical.choice`, `Quot.sound` (the library standard)
(guarded in the Controls). H87 changed the compiler (signed bitwise, above),
two other lanes' controls (below) and this lane's own theorems (a
`Readable F` premise); H96 replaced it by `Matches K F`, changed `ProgOk P`
to `ProgOk K P` and `compile_init` to `ProgOk [] P`. No frozen statement
changed; no `maxHeartbeats` option is used.

Controls: an inhabited program using a storage read, a storage alias with a
rebind, a mapping write through it, root and indexed storage `+=`, `++`,
signed `&`, `|`, `^`, a
`while` loop with `+=`, a branch with a `revert`, and a value internal call
is accepted through the theorem at every base and, independently, by kernel
evaluation; its code is nonempty. `program_agrees_fresh` meets the `Sim` premise
with the published `Sim.init` fresh contract, so `Agrees` is reached, not
vacuous. H96 controls: `indexed` (`row = rows[x]`, `row[0] += x` and a
kind-preserving rebind inside a loop, a rebind in a branch, indexed writes and
reads) is accepted by the theorem and by kernel evaluation, with the
fresh-machine witness `indexed_agrees_fresh`; `kindChange_refused` (an indexed
alias rebound to a plain path in a loop) and `unsetRead_refused` are
kernel-observed refusals, `kindChange_outside` its contrapositive. `nested`
covers an alias of an indexed alias, a mapping inside an array element and a
fixed-array element (theorem and kernel). No control has a struct field
through an indexed path (`IndexedPath.field`; proved generally). `intKey_outside` is the contrapositive of totality on a refused program.

Limits: this is totality of the entry on this domain. It does not extend the
domain to unset aliases, kind-changing rebinds, memory, transfers/sends,
pushes/pops, deletes, multiple returns, recursion, external/self/library calls
or returndata, and it
does not discharge G01 `PublicCorrectness.coverage`, whose domain is
`S.Admitted` of a whole source input.

## Q-H68-PAYLOAD (P1-REVERT): delivered

H87/H85 (user decision): waited for producers; G49 `PassCorrect` merged to
master first and this lane does not define the call-session language.

H68 asks V13 for `p1_frame_bridge` in its P1-REVERT variant: a
`BridgeGoal (A x) (B x) ps pt beta nu Local` whose `pc` is a full
`G49Final.PassCorrect` between `Behaviour.ofLang` of canonical
`Lang Event Outcome` languages for the source call session and the emitted
`plan.code` session, with `Local` the original `PendingBareRevertProducer`
fields (`RevertingEntry`, `BareRevertClaim`).

**Delivered on this branch (H114/H115; base master `d3597eca2` supplies the
languages).** With V12's canonical
version-2 P1 languages (`Backend/InternalFlow/RuntimeFrameP1LangV2`) and the
version-2 machine (`Evm/MachineV2`) on master, `Backend/AbiWorld/P1RevertBridge`
proves

```lean
p1_revert_bridge (b) (hF : Matches K F) (hs : StmtOk K s K')
    (noAssert : Stmt.asserts s = false) :
  BridgeGoal (A b F s) (B b F s) () () id (fun _ _ => ()) (Local b F s)
```

- **Context (NativeContext_frame):** a statement `s` of this lane's totality
  domain, its alias kinds `K`, a matching fragment `F` and base `b`.
- **Approved_frame:** `Matches K F`, `StmtOk K s K'` and no `assert`.
- **A / B:** `sourceLang (fun _ => s)` and `targetLang (lift code)` of
  `P1LangV2`, where `code` is what `Compiler.compile b F (s;)` emits (compiler
  output, not a hand-written image). No second language is defined.
- **Domain (`admitted`):** the compiler's own core `Input`
  (`Sim C L b F caller machine ∧ L + pushes ≤ Lmax`, with `pushes = 0` in the
  domain); it does not mention the outcome.
- **beta / nu:** the identity environment map and the unit bound, as in V12's
  `p1_frame_bridge`.
- **Local:** for every admitted input, the version-2 form of
  `PendingBareRevertProducer.required_bare_revert` (a bare source revert is a
  target revert with empty data and the caller's journal) and the frame
  agreement `targetSem (lift code) e = sourcePrefix (s.run caller)`.

The full `PassCorrect` (`need_ok`, `back`, both directions, every admitted
input and every outcome) comes from `agree`, which reads
`PublicCompilerTotal.compile_agrees`: success with no data, a bare revert as a
version-2 revert with empty data and an unchanged journal, divergence as a
fault; payment is impossible in the domain.

Controls (`P1RevertBridgeControls`): `require(total != 0)` from the published
fresh contract (`Sim.init`) is a reverting admitted input (not an
`InterfaceV2.RevertingEntry`), with the target
revert derived from the bridge's `Local`; `require(total == 0)` succeeds on
both sides at the same input; axioms are guarded.

Limits the bridge depends on (from `P1LangV2`): callee code is never run
(the domain makes no external call, so the version-2 reply/accepts oracles are
not consulted); gas and depth are not resources; data windows play no part
(the core code reverts without data). **`assert` is excluded:** the source
observes a failing `assert` as `revert(Panic(0x01))` while the core compiler
emits a data-free revert (`assertFalse_source`, `assertFalse_target_bare`) —
a compiler gap in panic data, recorded. Source and target also agree, but
both differ from solc, on reverts the source keeps data-free where solc
returns data (checked-arithmetic `Panic(0x11)`, index `Panic` codes,
message-carrying `require`/`revert`, `docs/solc-alignment.md`); `P1LangV2`
calls itself canonical only when reverts carry their data in the source, so
for those statements this bridge is a source-to-compiled-code refinement
within the model, not a solc-data claim; `assert` is the only such case
where source and compiled code themselves disagree.
**Deviations from the H68 request, stated plainly (finder review).**

1. It is not built from a `PendingBareRevertProducer` (InterfaceV2/V3;
   instances exist: `RuntimeFrameNoneProducer.make_failure`,
   `V3BareRevertProducer`). It gives a version-2 analog of
   `required_bare_revert` for compiler output; `Local` has no
   `RevertingEntry` existential (a reverting input exists only in the
   Controls, and for many statements, e.g. a plain assignment, none exists).
2. The endpoints are the core compiler's frame-free code, not the P1
   `plan.code`/cursor/frame: admission is `Sim`, not `InterfaceV1.Entry`;
   `Input.frame`, `base` and `start` are unconstrained and unused; the
   requested StateRepr, protected stack, BaseExtends, allocator-growth and
   cursor facts are not in `Local`, nor are the success-case stack and `Rep`
   facts that `Agrees` provides.
3. `Approved_frame` (the totality domain, no `assert`) is the compiler's
   implemented fragment, which the request's wording forbids as an
   `Approved_i`; it is this delivery's context, not a claim about P1 frames.

Whether this delivery satisfies Q-H68-PAYLOAD, or the bridge must be built
over a `PendingBareRevertProducer`'s P1 frame endpoints, is a scope question
(CLOUD-RESULT Q1).

## Remaining V13 queue

The Codex lane's last item, G42.04 library body/binding adequacy, still waits
on the actual library body producer (`Lowering/V08/LibraryPremises.lean`
names it as an explicit producer duty); `LibraryResultPacket` is unchanged.

## Reviews

Read-only finder and skeptic reviews (no Lean server) of the two modules and
this document. No soundness or vacuity defect. Confirmed findings, fixed:
the Controls docstring overclaimed refusal controls for every side condition
(now three kernel refusals, the word-fit conditions stated as code-only);
`Agrees` was written with ↔ (now one-directional pairs); the returndata
refusal is proved only for the core branch; `BridgeGoal` is a schema name, not
a Lean declaration; the domain's dependence on `Evm.offset` and its being a
restatement of the core fragment are stated explicitly (framing left to the
user as a scope question). The skeptic confirmed `compile_agrees` adds no
premise to `Compilation.correct` and that `Sim.init` meets its premise.

### H87 widening reviews

Read-only finder and skeptic reviews of the H87 commits. The finder confirmed
the signed-bitwise semantics (two's-complement AND/OR/XOR, result always an
`int256`, matching solc) and that every backend inherits `tail_simT`.
Confirmed findings, fixed: alias restrictions were mislabelled compiler
refusals (now domain choices, with the actual obstruction stated); the domain
was overclaimed as the core fragment minus alias bookkeeping (now a stated
subset, with transfers, `push`/`pop`/`delete`, `assignIncDec` and static copies
listed as compiled but outside); a stale "nothing changed" sentence; the
`Readable` premise constrained value locals (now only aliases); controls
lacked indexed storage `op=` and signed `|`/`^` (added). Recorded as proposals
for owners: R12, the V09 note and the G03 ledger. Raised as a question:
array-indexed aliases (answered by H96, now covered). No runtime-value control for signed `&` beyond the
general `stail_simT` proof.

### Hand-off: other lanes' controls changed by H87

Owners should verify: `Solidity/Backend/PrimitivePackets/Bitwise/Selected.lean`
`signed_refused` → `signed_accepted` (diamond-try checkpoint) and
`Solidity/Backend/Passes/BitwiseValueContextControls.lean` `signed_refusal` →
`signed_acceptance` (v09-compiler-passes; pin renamed in
`scripts/g07-axiom-pins.json` and its fragment).

### H96 reviews

Finder: Lean definitions behave as documented (`FreePath`/`IndexedPath`
disjoint and exhaustive over `PathOk` paths; `Matches.read`, both `bindFl`
lemmas and `Frag.set_of_get` agree with `Compile.lean`; unset-read refusal
accurate). Fixed: the `if` meet was described as refusing kind mixing (it
marks the alias `dead`, refusing a later read); "array index anywhere" and
"index-free" overstated or misdescribed the kinds; the unset-alias exclusion
was attributed to solc (it is a domain choice); stale `Readable` wording.
Skeptic: no vacuity (nontrivial `K` is matched; kinds cannot be chosen
inconsistently), `indexed_agrees_fresh` meets every premise jointly, no
axiom/`sorry`/`maxHeartbeats`. Fixed: added `nested` controls; documented
kind changes at top level as compiled-but-outside and the H96 signature
changes.

### P1-REVERT reviews

Skeptic: no soundness or vacuity defect; every `Agrees` outcome covered;
journal argument sound (lifted base code journals nothing; the domain has no
transfer/send/recursion); no axiom/`sorry`/`maxHeartbeats`. Fixed: solc-data
caveat; independent kernel runs for both guard controls. Finder: `agree`,
`Local`, beta/nu and the assert exclusion confirmed. Fixed: wrong claim that
no `PendingBareRevertProducer` instance exists; "delivered on master"
wording; reverting-entry vocabulary; the three deviations above stated
plainly and raised as a question.
