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
| Fixed outcome/returndata observation | `Compiler.Compilation.Agrees`, obtained from `Compilation.Input` by `Compilation.correct`: success with typed state, stack and the branch's `Rep`; source revert or (asserting) panic ↔ machine `.revert`; payment refusal; divergence ↔ fault (or payment revert). The machine `revert` carries **no returndata**: the entry refuses `revertData`/`catchData`/`tryCall`, so no ABI returndata is observed by it. |
| Supported input domain (this lane's statement) | `PublicCompilerTotal.ProgOk`: inductive predicates over the intrinsic syntax that mention no compiler function, fragment or compile result. Alias-free storage paths (roots; struct fields whose offset fits a word; `uint`-keyed mappings; dynamic and word-sized fixed arrays); values: literals, booleans, locals, environment reads other than `address(this).balance`, storage reads, every typed unary operator, every typed binary operator except `&`/`|`/`^` at `int`, ternaries and storage-array lengths; statements: storage value assignment, local assignment, declarations, local `op=`/`++`/`--`, `require`, `assert`, `revert`, `if`, blocks, `while`, internal calls with value arguments and no or one value return. |

The side conditions are recorded compiler gaps, not success filters: the
Controls kernel-evaluate the public entry on a signed `&` and on
`address(this).balance` and observe refusal (`isNone`), so neither the theorem
nor the domain hides them.

## Compiler-success (totality) theorem

- `compile_core b F hP : ∃ G h, Compiler.compile b F P = some (.core G h)` for
  every base `b`, every fragment `F` and every `ProgOk P`.
- `compile_isSome`: the same as `isSome`.
- `compile_agrees`: the selected result satisfies the fixed observation
  `Agrees L frame base σ m` from every `Sim C L b F σ m` with `L ≤ Lmax`
  (the core push bound is discharged because domain programs push nothing).

The proof shows (by mutual induction on the domain) that values are accepted
from every fragment, that programs push, pay and shrink nothing, and that
`inFragP` only pushes readable locals (`Grows`), so branch meets, scope
restriction and the loop fixed-point check hold. Axioms: `propext`, `Classical.choice`, `Quot.sound` (the library standard)
(guarded in the Controls). No compiler, statement, premise or observation is
changed; no `maxHeartbeats` option is used.

Controls: an inhabited program using a storage read, a `while` loop with
`+=`, a branch with a mapping write and a `revert`, and a value internal call
is accepted through the theorem at every base and, independently, by kernel
evaluation; its code is nonempty. `signedAnd_outside` derives from the
theorem and the observed refusal that the domain is not every program.

Limits: this is totality of the existing entry on this domain. It does not
extend the domain to aliases, memory, transfers/sends, pushes/pops, deletes,
multiple returns, recursion, external/self/library calls or returndata, and it
does not discharge G01 `PublicCorrectness.coverage`, whose domain is
`S.Admitted` of a whole source input.

## Q-H68-PAYLOAD (P1-REVERT): blocked on missing producers

H68 asks V13 for `p1_frame_bridge` in its P1-REVERT variant: a
`BridgeGoal (A x) (B x) ps pt beta nu Local` whose `pc` is a full
`G49Final.PassCorrect` between `Behaviour.ofLang` of canonical
`Lang Event Outcome` languages for the source call session and the emitted
`plan.code` session, with `Local` the original `PendingBareRevertProducer`
fields (`RevertingEntry`, `BareRevertClaim`).

It cannot be delivered without inventing endpoints, which H68 forbids:

1. `Solidity.Roadmap.G49Final.PassCorrect`/`Behaviour`/`BridgeGoal` exist only
   on `origin/cloud/move6-20261106/g49-base` (head `191bce52`), not on master;
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
