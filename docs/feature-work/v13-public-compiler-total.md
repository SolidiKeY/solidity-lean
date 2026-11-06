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
| Supported input domain (this lane's statement) | `PublicCompilerTotal.ProgOk`: inductive predicates over the intrinsic syntax that mention no acceptance function, fragment or compile result (the word-fit conditions read the backend storage layout `Evm.offset`). Storage paths (aliases; roots; struct fields whose offset fits a word; `uint`-keyed mappings; dynamic and word-sized fixed arrays); values: literals, booleans, locals, environment reads other than `address(this).balance`, storage reads, every typed unary and binary operator, ternaries and storage-array lengths; statements: storage value assignment, local assignment, value declarations, storage-alias declarations with an initializer and rebinds, both to index-free paths (`FreePath`), `op=`/`++`/`--` on locals and storage locations, `require`, `assert`, `revert`, `if`, blocks, `while`, internal calls with value arguments and no or one value return. Widened by H87 (2026-11-06). |

**Framing and H87.** The domain is the part of the core branch's fragment
that does not depend on alias bookkeeping: each side condition mirrors a check
of `simpleIn`, `locIn` or `bindFl`. The user's decision H87 (relayed
2026-11-06, answering Q1) required widening before acceptance: signed
`&`/`|`/`^`, aliases and storage compound assignment. All three are now in the
domain; signed bitwise needed a compiler extension (below). The remaining
documented gaps (H87: stay gaps): `address(this).balance`, non-`uint` mapping
keys, aliases bound through an array index or left unset, memory,
transfers/sends, pushes/pops/deletes, multiple returns, recursion and external
calls. The domain is not widened to G01 `S.Admitted`.

The Controls kernel-evaluate the public entry on `address(this).balance` and
on an `int`-keyed mapping read and observe refusal (`isNone`), and on a signed
`&` and observe the former refusal is gone; the word-fit and alias conditions
are refusals by `locIn`/`bindFl`'s code without a kernel control.

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
already compiled through `sarCode`). The Bitwise packet control that asserted
the old refusal is now the acceptance fact
(`PrimitivePackets/Bitwise/Selected.signed_accepted`,
`Passes/BitwiseValueContextControls.signed_acceptance`; pin renamed).
Checking note: `Layout.lean` is imported early, so this rebuilds most of the
library once; no proof became slower by design.

## Compiler-success (totality) theorem

- `compile_core b hF hP : ∃ G h, Compiler.compile b F P = some (.core G h)` for
  every base `b`, every `Readable F` (all locals known readable, e.g.
  `Frag.init Γ`, the fragment of a whole program or call body) and every
  `ProgOk P`.
- `compile_isSome`: the same as `isSome`; `compile_init` at `Frag.init Γ`.
- `compile_agrees`: the selected result satisfies the fixed observation
  `Agrees L frame base σ m` from every `Sim C L b F σ m` with `L ≤ Lmax`
  (the core push bound is discharged because domain programs push nothing).

The proof shows (by mutual induction on the domain) that values are accepted
from every readable fragment, that programs push, pay and shrink nothing, and
that `inFragP` only pushes readable locals (`Grows`) and rebinds leave a
readable fragment unchanged (`Readable.set`), so branch meets, scope
restriction and the loop fixed-point check hold. Axioms: `propext`, `Classical.choice`, `Quot.sound` (the library standard)
(guarded in the Controls). No compiler, statement, premise or observation is
changed; no `maxHeartbeats` option is used.

Controls: an inhabited program using a storage read, a storage alias with a
rebind, a mapping write through it, storage `+=` and `++`, a signed `&`, a
`while` loop with `+=`, a branch with a `revert`, and a value internal call
is accepted through the theorem at every base and, independently, by kernel
evaluation; its code is nonempty. `program_agrees_fresh` meets the `Sim` premise
with the published `Sim.init` fresh contract, so `Agrees` is reached, not
vacuous. `intKey_outside` is the contrapositive of totality on a refused program.

Limits: this is totality of the entry on this domain. It does not extend the
domain to array-indexed or unset aliases, memory, transfers/sends,
pushes/pops, deletes, multiple returns, recursion, external/self/library calls
or returndata, and it
does not discharge G01 `PublicCorrectness.coverage`, whose domain is
`S.Admitted` of a whole source input.

## Q-H68-PAYLOAD (P1-REVERT): blocked on missing producers

H87/H85 (user decision): wait for producers; G49 `PassCorrect` merges to
master first and this lane does not define the call-session language.

H68 asks V13 for `p1_frame_bridge` in its P1-REVERT variant: a
`BridgeGoal (A x) (B x) ps pt beta nu Local` whose `pc` is a full
`G49Final.PassCorrect` between `Behaviour.ofLang` of canonical
`Lang Event Outcome` languages for the source call session and the emitted
`plan.code` session, with `Local` the original `PendingBareRevertProducer`
fields (`RevertingEntry`, `BareRevertClaim`).

It cannot be delivered without inventing endpoints, which H68 forbids:

1. `Solidity.Roadmap.G49Final.PassCorrect`/`Behaviour` exist only on
   `origin/cloud/move6-20261106/g49-base` (head `191bce52`), not on master;
   `BridgeGoal`/`p1_frame_bridge` are H68 schema names in that branch's doc,
   not Lean declarations;
   importing it would make this lane depend on an unmerged lane.
2. No canonical G01 `Lang Event Outcome` exists for intrinsic call sessions or
   emitted-code sessions; the g49 document itself records that
   `typedRunPrefixes` is not one. Any `A`/`B` built here would be a new
   language chosen by this lane — an "arbitrary Behaviour", explicitly
   rejected by the request.
3. `BareRevertClaim` covers bare revert only; PassCorrect's `need_ok`/`back`
   need all outcomes and prefixes, i.e. the success transport
   (`ReturnClaim`) and panic/exhaustion/divergence producers that are absent
   for the failure-only producer.

No frozen statement was changed and no premise was added. Owners of the
missing pieces: G49 (merge of PassCorrect), the G01/P1 canonical intrinsic
session language, and the P1 success producers (V12/MRS/V17).

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
