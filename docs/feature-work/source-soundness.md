# Source soundness (lane V04b)

Lane `cloud/roadmap-l3-20261030/lane-soundness`: integrate the source
semantics of lane-semantics ([source-s05.md](source-s05.md)) with master's
G13 checker, then type soundness of the interpreter: preservation and
gap-relative progress (user decision 2026-10-30).

## Checkpoint 1: integration

The merge of `cloud/roadmap-l2-20261029/lane-semantics` into this branch
(base `8445c3f`, a `--no-ff` merge) conflicted only in shared lists
(`Solidity.lean`, `TrustAudit.lean`, `docs/coverage-plan.md`,
`docs/module-map.md`); every line of both sides is kept.

G13's checker (`Solidity/Frontend/Static/Infer*.lean`) was written against
S01 before lane-semantics changed its typing. Each break listed in
[source-s05.md's Handoff](source-s05.md#handoff-s05) is fixed:

| Checker part | Change |
|---|---|
| `Infer.lean` `constRes` | checks the third premise `e.hexLen? = none` of `Typed.const` |
| `Infer.lean` `litRes` | one `litBytes` derivation when `hexLen? = some len` (type `hexConst n.value len`); the 32 `fixedBytes` typings and the `lens` table are gone |
| `Infer.lean` `binPair` | `shift`/`exp` read `τa.shiftTy` |
| `Infer.lean` `common?` users | unchanged code; results follow `STy.common?` |
| `Infer.lean` new arms | `member` and `LVal.member` (`structMemberRes`), `structNew` (in `callIdentRes`), `extCall`, `transfer`, `send` (`memberCallOne`, `payRes`, `payOne`), `extCallValue` (`valueCallOne`), `abiEncode` (`abiRes`), `assignCopy` (in `assignRes`) |
| `InferStmt.lean` | `.expr` checks `(C.inModifier && e.isUnderscore) = false`; `.retTuple` only for a non-empty slot list; `rethrow` reads `rethrowVar? body = some d` |
| `InferComplete.lean`, `InferStmtComplete.lean` | completeness for every new constructor; `hasType_iff`, `stmtOK_iff`, `itemsOK_iff` proved again, and `wellFormed_iff` (`WellFormedCheck.lean`) unchanged |
| `InferExamples.lean` | `zero_types`: `0x00` has one type; `hexCall_typed` (below) |
| `Standalone.lean` | its `STy.isConstTy` clashed with S02's; renamed `STy.isConstOnly` (the `hexConst` case it adds is unreachable: `standalone` sends a hexadecimal literal to its mobile integer type). Behaviour change from Q1: `abiArgTys` of `0x00` went from 33 types to one (`uint8`), solc's |

**Receivers and call options.** `infer` stays structural over `Syn`: the
call rules need the typing of a callee's subterms (`c` in `c.f(…)`, `c`
and `v` in `c.f{value: v}(…)`), so `Res` has three auxiliary results that
no typing or lvalue projection returns: `recv` (a typed receiver, at
`a.m`), `named` (a typed call option, at `.namedArg x v`) and `withValue`
(both, at `.callOptions`). `callRes` takes the callee's results and
selects the rule by the callee's syntax.

**Overload deviation removed.** lane-static recorded that S01's per-typing
uniqueness gave `f(0x01)` with `f(uint8)` and `f(bytes1)` two derivations,
where solc reports an ambiguity. Under solc's literal typing (Q1) `0x01`
has the single type `hexConst 1 1`, which both overloads accept, so
`callInternal`'s uniqueness premise fails: `hexCall_typed` now states that
the call has no type ([frontend-static.md](frontend-static.md) updated).

**Controls** (`InferExamples.lean`, kernel `decide`; contract `K` with a
struct `P { uint256 a; }`, `g(uint256) external payable`,
`h(uint256) external`):

| Theorem | Witness | Negative control |
|---|---|---|
| `member_checked` | `p.a : uint256`, one lvalue, `p.a = x` | `p.b` untyped |
| `structNew_checked` | `P(x) : P memory` | `P()` untyped |
| `extCall_checked` | `k.g(x)`, `k.h(x)` | `k.z(x)` untyped |
| `extCallValue_checked` | `k.g{value: x}(x)` | `k.h{value: x}(x)` (not payable); `k.g{gas: x}(x)` (unmodelled option, recorded gap: solc accepts it) |
| `pay_checked` | `q.transfer(x)`, `q.send(x)` on `address payable` | both on `address` |
| `abiEncode_checked` | `abi.encode(x) : bytes memory` | `abi.encode(p)` (a struct): S01 refuses, solc accepts (deviation below) |
| `zero_types` | `0x00` has exactly one type | — |
| `hexCall_typed` | — | `f(0x01)` ambiguous, refused |

**Deviations found by the review** (S01's, not the checker's; the checker
decides S01 faithfully):

- `abi.encode`/`encodeWithSelector`/`encodeWithSignature` arguments are
  S01's `STy.abiArg`: value types, integral constants, string literals and
  memory `bytes`/`string`. solc 0.8 (ABI coder v2) also encodes structs,
  arrays and calldata `bytes`/`string`. `encodePacked` of a constant
  (`abi.encodePacked(1)`), which solc refuses (7279), is accepted (recorded
  in [source-s02.md](source-s02.md)).
- Call options other than a single `value` (`gas`, `salt`, several
  options) have no type (recorded S02 gap).

**Two inference engines.** lane-semantics' `Typed.infer`
(`Solidity/Source/Infer.lean`) returns one derivation per expression for
the elaborator; it is sound but has no completeness proof and makes fixed
choices where rules overlap (`assign` before `assignCopy`, `retTuple`
before `retVal`). G13's `infer` enumerates every derivation and is
complete; by `Typed.unique` (and `StmtD.unique`) both give the same
meaning. Unifying them (the elaborator reading G13's checker) is open.

**Untested here**: `encodeWithSelector`/`encodeWithSignature`, `assignCopy`
and the calldata exclusion of `LVal.member` have completeness proofs but no
kernel control.

Pins: `#guard_msgs` `#print axioms` for the new controls in
`InferExamples.lean`; `TrustAudit.lean` has a checkpoint-1 block (the four
decision theorems and the six controls).

lane-parse's modules (`Solidity/Frontend/Checked/`) do not import S01's
typing and are unaffected; they build in the full gate.

### Gates (checkpoint 1)

- Lean diagnostics clean (language server) on `Infer.lean`,
  `InferComplete.lean`, `InferStmt.lean`, `InferStmtComplete.lean`,
  `InferExamples.lean`, `Standalone.lean`, `UserOps.lean`,
  `WellFormedCheck.lean`, `Consts.lean`.
- Full gate `./run-lean.sh` (build9, on `0a6a408` plus the axiom
  `#print`s, 16m37s): `lake build` 903 jobs and `lake build
  SolkeyTestSuite` 262 jobs completed successfully (`Derived17` built, no
  out-of-memory kill); `check-solkey` 37 mismatches (baseline 37). The
  earlier runs (build3–build5) lost `Frontend/Checked/UnitExamples`,
  `Source/Horizon` and `Examples/Tactics/OpenLoops` to out-of-memory kills
  when they ran beside each other (`OpenLoops` takes about 8 GB); they
  build alone.
- The root module did not build after the lane-semantics merge:
  `Solidity.Source.Program` was declared twice (G12's units in
  `Units.lean`, S02's elaborated program in `Elaborated.lean`). Renamed
  G12's to `UnitSet`; a duplicate-name scan then found Horizon's
  `execS_step`/`execItems_step`/`forIter_step` against this lane's
  (renamed `*_nsStep`) and `Inheritance.lean`'s `Env.ctorParams`/
  `Decl.modInvs` against `Elaborated.lean`'s (renamed `Env.ctorArity`/
  `Decl.modInvList`). Four duplicates between Calculus/Semantics modules
  of the base (`Out.eq_of_st`, `Op1.eval_none`, `BinOp.shortT_of_lazyB`,
  `Op2.eval_none_of_strictB`) do not break the root build and were left.
- `node scripts/check-g07.mjs --log` on build9: every check passes but
  two: `check-axiom-pins` reports 86 unrecorded pins of other lanes
  (`Backend/Creation`, `Backend/Failure`, `Bridge/…/ExternalEvm`), left
  unrecorded; this lane's 54 are recorded; and
  `roadmap-g03-ledger --check` reports stale generated output, already
  stale at the base `8445c3f` (`Evm/Compiler.lean` line numbers).
  `check-doc-paths` 46 (baseline), required control pins 23/23, 0 error
  lines.
- Axioms at build9 (`0a6a408`): 45 `#guard_msgs` pins at the end of
  `SoundnessExamples.lean`, `ptrCopy_refused`/`ptrDelete_refused` (fixes
  of checkpoint 3) in `InferExamples.lean`, `static_value_call_halts` in
  `SemanticsExamples.lean` (only `propext`, `Classical.choice`,
  `Quot.sound`); `TrustAudit.lean` checks 43 checkpoint 2-3 headlines and
  the 10 checkpoint-1 ones (language server, no errors). The pins were
  turned from `#print`s into `#guard_msgs` after build9 and checked with
  the language server. Later counts are in "Gates (checkpoints 2-4)".

### Gates (checkpoints 2-4)

Every later head was gated by `./run-lean.sh` (`lake build` 903 jobs and
`lake build SolkeyTestSuite` 262 jobs completed successfully,
`check-solkey` 37 mismatches, the baseline) before its `CLOUD-RESULT`
marker: builds 10-12 (typing decisions, function level), 14-16 (UDVT
decoding, review fixes), 18-22 (elaborated frames, `return (a, b)`,
dispatch parameters), 23-25 (calls inside expressions), 26 (Panic `0x41`,
which changes `Eval.lean` and `Horizon.lean`), 27-28 (follow-ups and the
two-body witness; build 26's ordering of the `0x41` checks was rejected
in integration review and fixed after it), 29 (`c37f137`, `CallsOK` per
contract), 30 (`93bcaca`, offset check before the `0x41` panic), 31
(`e79abee`, location read/write preservation), 32 (`1f9722e`, review
fixes), 33 (`3aa644e`, `HeapShaped`). Build13 failed (the getter change, `Horizon.lean`
heartbeats) and was reverted. Each marker records its build; the last
gated head is in the final `CLOUD-RESULT`. `check-g07 --log` passed every
check but the two baselines above (86 unrecorded pins of other lanes,
the stale G03 ledger). The lane's pins (`SoundnessExamples.lean`,
`InferExamples.lean`, `SemanticsExamples.lean`) are recorded in
`scripts/g07-axiom-pins.json`, and `TrustAudit.lean` has one block per
milestone, all with the standard axioms only.

### Review (checkpoint 1)

Finder and skeptic (read-only, no Lean server).

Confirmed and fixed:

- `infer` evaluated `infer a` three times at `a.m` (once each for
  `memberRes`, `structMemberRes`, `recvRes`) and `infer n` once per callee
  result at `.callOptions`: now bound once (`let`).
- `frontend-static.md` still described the overload deviation, "33 types"
  and the speed bound from before Q1, listed `abi.*`, structs and external
  calls as untyped, and kept the overload item open in its handoff:
  updated.
- `member_checked` claimed "assigned" without an assignment: `p.a = x` is
  now part of it.
- The `gas` and struct-`abi.encode` controls were presented as solc
  refusals: they are S01 gaps, now recorded above (and in the docstrings).
- `hexCall_typed`'s name says the opposite of its statement; the name is
  kept (pins, TrustAudit lists) and the docstring says so.
- `isConstOnly`'s description: the real behaviour change (`abiArgTys` of a
  hexadecimal literal) is recorded instead.
- The relation to lane-semantics' `Typed.infer` is recorded above.

Answered (not defects): the auxiliary results `recv`, `named`,
`withValue` never reach `tysOf`/`lvsOf`/`inferTys` (both reviewers);
completeness covers every new constructor, none vacuously (finder);
`f(0x01)` is refused by solc too (skeptic); `extCallValue`'s shape matches
`callRes` exactly (skeptic).

### Integration review (coordinator, master + checkpoint 1)

Skeptic, confirmed and fixed: the root-import clash (Gates); EIP-214 in
`callAddr` (Checkpoint 3); statuses of S02/S03/S04.04 and V04 in
`coverage-plan.md` now say partial and list what is open; stale text in
`source-s02.md` (dynamic ABI decoding), `source-s05.md` (its stuck list,
with the storage assignment of arrays of mappings) and the G13 status;
Panic 0x41 and user-defined value type decoding cross-listed in
`solc-alignment.md`. Not confirmed: that `s1 = s2` for a storage struct
with a nested mapping is `stuck`: the struct's memory layout is empty
(`Decl.structFields` at `memory` fails for a mapping member), so the
copy silently does nothing; an array of mappings is `stuck`. Both are
now refused by S01 (`mapAssign_refused`; decision 2026-10-30,
`source-s02.md`, "Typing decisions").

Finder, fixed: `Value.lean`'s non-`only` `simp`s; the six checkpoint-1
pins recorded in `scripts/g07-axiom-pins.json`; `abiEncode_checked`
presented as a known S01 gap (`source-s02.md`); `zero_types` states the
type `hexConst 0 1`; the `InferExamples` section header and the
`Unique.lean` docstring.

Speed: `Horizon.lean` (about 2200 lines, minutes to check) re-checks on
any change to `Eval.lean`'s mutual block; `SemanticsExamples.lean` has 13
kernel evaluations.

## Checkpoint 2: preservation (partial)

**What a well-typed run-time state is.** Most of the state is typed by
construction (S04.01): a value of type `τ` is a `Val D τ` (ranges, enum
bounds, byte lengths inside), locals are `Locals D Γ`, storage and
transient storage are `Storage D L` over the layout `Env.cellTy`, every
memory object carries its type, and calldata objects too. So
preservation of those parts holds by construction for every step. What
is not intrinsic is where **references** point (`Solidity/Source/WellTyped.lean`):

| Predicate | Meaning |
|---|---|
| `Val.RefOK E H v` | a `memory` reference of type `τ` names an object the heap typing `H` gives type `τ`; a `storage` reference of type `τ` a path with `Env.pathTy p = some τ`; no value is a `calldata` reference (the semantics creates none) |
| `DataOK`, `DataListOK`, `RValOK`, `RValsOK`, `LocalsOK` | the same for memory contents, run-time values and locals; all monotone in `H` (`HeapTy.Le`) |
| `HeapOK h` | every object of the heap agrees with the heap's own typing |
| `StOK E H s`, `EMOK` | a well-typed machine state (heap well typed, typing extending `H`) and interpreter state (with the locals) |

**Hoare triples** (`Solidity/Source/Hoare.lean`): `Hoare P m Q X` over
`EM`, with a rule for every combinator the interpreter uses (`pure'`,
`bind`, `halt'`, `lift'`, `st'`, `setSt'`, `modSt'`, `locals'`,
`setLocals'`, `sub'`, `attempt'`, `dite'`, `ite'`, `conseq`,
`cases_pre`). Preservation of an invariant `I` is a triple with `I` in
the pre- and postconditions and the halt condition; progress is one whose
halt condition is `NotStuck`.

**Proved for the memory operations** (preservation and, where they read,
progress): `alloc_ok` (the state stays well typed, the new address has the
object's type), `allocRef_ok` (the new reference agrees), `heapPut_ok`
(a write of agreeing contents keeps the state well typed; `stuck` only at
an address of another type), `heapObj_ok`, `heapAt_ok` (a read at the
type the heap typing gives is never `stuck` and returns agreeing
contents; `heapAt` has no caller in the interpreter), `storRef_ok`; the heap facts `HeapOK.alloc`, `HeapOK.write`,
`Heap.alloc_le`, `Heap.alloc_ty`, `HeapOK.empty`.

**Proved for location reads and writes** (preservation, halts included;
added after marker `7b94a9b`): `writeLoc_local_pres`, `writeLoc_mem_pres`
(`memSet_pres`: array elements and struct members, through
`DataListOK.setNth`), `writeLoc_memByte_pres` (bytes and strings), and the
reads `readLoc_local_pres`, `readLoc_mem_pres` (`memElem_pres`, through
`DataListOK.nth` and `asVal_ok`: the value read agrees),
`readLoc_memByte_pres`; the generic `heapObj_pres` and `heapPut_pres`.
A written value must agree (`v.RefOK`). Storage locations (`storeVal`,
`writeAt`, `readAt`) are not covered.

**Finding: progress for memory accesses needs object shapes.** `HeapOK`
says where references point, but not that a top-level object of a memory
reference type is a `Data.bytes`/`Data.string`/`Data.array`/`Data.struct`
rather than a `Data.val`. The negative control `ptrHeap_byte_stuck`
builds a well-typed heap (`ptrHeap_ok`; the full state is `EMOK` too,
trivially at `Γ = []` and the empty heap typing) whose object at `1` is a
`bytes memory` stored as a pointer, and a byte write there is `stuck`
("not bytes"). No allocation or `heapPut` site creates such an object
(`zeroData` and `loadMem` match all four memory reference types before
their `Data.val` arms, and a mapping has no memory location; the other
`allocRef` and `heapPut` sites build aggregates), so the gap is in the
invariant, not the semantics (proved for the zeroing allocator and storage copier, `zeroOK`, `loadOK`
below; not yet for the other allocation sites). Progress for `memSet`,
`writeLoc .memByte`, `memElem` and `heapBytes` (`readLoc .memByte`,
conversions to fixed bytes, `bytesOfRV`) needs `HeapOK` strengthened with
this shape condition, and `memElem` also needs elements to be `Data.val`
(`Data.asVal`, "inline aggregate element"): the census "heap" row below.
The shape condition is now `HeapShaped` and the progress lemmas below
cover all of these but the `heapBytes` callers other than
`readLoc .memByte` (`memElem` is covered under `HeapInner`, below). Every site that builds a memory array or struct
stores `Data.val` elements (`zeroElems`, `zeroFields`, `loadElems`,
`loadFields`, the ABI decoder, `structNew`, `memSet`), so the element
condition is also a proof gap only.
Progress proofs must use `heapPut_ok`, which keeps the halt detail
`heapPut_pres` drops. `delete` of a local or memory location keeps
`MemOK` (`deleteLoc_mem`, below); storage `delete` and locals holding
calldata references are not covered (`Val.RefOK` of a `cdRef` is
`False`; the semantics creates none).

**The shape invariant, first use.** `HeapShaped h` (`Data.Top`: a
top-level object is a `Data.val` only at a type without a location) is
kept by allocation of a shaped object (`HeapShaped.alloc`) and by writes
(`HeapShaped.write`, `heapPut_shaped`, which also proves `heapPut`
succeeds at the address's own type). With it, `writeLoc_memByte_ok`
proves progress and preservation of a byte write at an address the heap
typing gives a `bytes`/`string` type: it writes or panics, never `stuck`.
Witness `bytesHeap_byte_write`; control `ptrHeap_not_shaped` (the
well-typed but unshaped `ptrHeap` is excluded). Reading the code finds
no unshaped allocation (`zeroVal` calls `zeroData` only at memory types,
all aggregates; `loadMem` reaches its `Data.val` arm only at types without
a location; the other `allocRef` and `heapPut` sites build aggregates), so
what remains is a proof gap, not a semantic one. The zeroing
allocator is proved: `zeroOK` (joint induction on fuel over `zeroData`,
`zeroVal`, `zeroElems`, `zeroFields`, structure `ZeroOK`) shows each keeps
`MemOK` (`EMOK`, `HeapShaped`, `HeapInner`), halts included; `zeroData`
builds an agreeing, shaped object with bare-value elements, `zeroElems`
and `zeroFields` agreeing bare-value elements, and `zeroVal`'s value
agrees (`allocRef_mem`, `Hoare.memGrow` for the growing heap typing,
`Val.default_loc`); witness `zeroArr_alloc`. Composed with the write:
local and memory writes of agreeing values keep `MemOK` (`writeLoc_local_mem`,
`writeLoc_mem_mem`, `writeLoc_memByte_mem`, through `memSet_top`,
`writeLoc_memByte_top`, `heapPut_top` and the conjunction rule
`Hoare.and`), so `delete` of a local or memory location keeps `MemOK`,
halts included (`deleteLoc_mem`; witness `arrHeap_delete`: `true`
reset to `false`). Storage writes are not covered.

**Review of `deleteLoc_mem`** (finder and skeptic, read-only, no
blocker): the side condition and "halts included" were confirmed, and
`Hoare.and` is sound for the deterministic `EM`; fixed: the witness now
starts from `true` and reads element `0` back as `false`, the `zeroOK`
docstring points to `deleteLoc_mem`, "writes" now says local and memory
writes, the TrustAudit list matches the pins. Build43 (`0b7c2be`)
passed. The storage-to-memory
copier is proved the same way: `loadOK` (structure `LoadOK` over
`loadMem`, `loadElem`, `loadElems`, `loadFields`; storage reads change
nothing, `readAt_keep`, `readLen_keep`, `loadBytes_keep`; `allocRef_mem'`
covers an allocation whose reference is then refused). Not yet done:
proving the same for the other allocation sites (the ABI decoder,
`structNew`, literals, the `abi.encode*` result); carrying `HeapShaped` and `HeapInner` (`MemOK`) through frame restores (`Eval.lean` and
`Semantics.lean` reset the heap or restore a saved one, as for
`HeapOK`). Memory writes keep `HeapInner`, halts included:
`memSet_inner` (it stores a `Data.val` and keeps the other elements;
`DataList.AllVal.setNth`), `writeLoc_memByte_inner`, `heapPut_inner`. Progress for element and
member reads is proved under the element invariant `HeapInner`
(`Data.Inner`: an array's elements and a struct's members are
`Data.val`): `memElem_ok`, `readLoc_mem_ok` (at an array of type `τ`, or
a struct whose member `i` has type `τ`, in a shaped heap with bare-value
elements, not `stuck`: the code reads or panics out of bounds; the value
read agrees; `DataList.nth_val`, `heapObj_get`), witness `arrHeap_read`
(with `arrHeap_inner`), control `inlineHeap_read_stuck` (a well-typed,
shaped heap whose `bytes[]` element is inline: "inline aggregate
element"). Progress for `readLoc .memByte` is proved:
`heapBytes_ok`, `readLoc_memByte_ok` (at a `bytes`/`string` address in a
shaped heap, not `stuck`: the code reads or panics out of bounds),
witness `bytesHeap_byte_read`, control `ptrHeap_byte_read_stuck` (the
unshaped `ptrHeap`: "not a bytes object"). `heapBytes_ok` applies to its
other callers (`bytesOfRV`, the conversion to fixed bytes, the revert
data) once their premise is derived; that is not done.
Progress for element and member writes is proved: `memSet_ok` /
`writeLoc_mem_ok` (at an array of the value's type, or a struct whose
member `i` has it, in a shaped heap, the write is not `stuck`: the code
writes or panics out of bounds; `DataList.setNth_ok`), witness
`arrHeap_write` (on the shaped `arrHeap_shaped`), control
`arrHeap_wrong_elem_stuck` (an `address` written into a `bool[]` is
`stuck`, "element type": the type premise is needed). Callers get the
premise from the location's construction: an index into a `memory`
array reference (`indexLoc`) has `Val.RefOK`, and `memShape` is the
identity on arrays, so the heap type is that array (static arrays
included; `STy.memShape_array`); a struct member (`Eval.lean`, member access) has
`E.fieldTy? d .memory i = some τ`, which is `(E.layout.fields d)[i]?`
for a memory struct. The struct bridge is not stated as a lemma yet, and there is
no struct-member control (`SemanticsExamples.E0` has no structs).

**Review of `HeapInner` preservation and `zeroOK`** (finder and
skeptic, read-only, no blocker): the `zeroOK` docstring overclaimed for
declarations and `delete` (now: only their `zeroVal` step); the
`Hoare.memGrow` docstring was garbled; the witness did not inspect the
object (it now checks both elements are `false`); stale doc lines and the
Handoff row were fixed. Build41 (`dcfedbe`) passed.

**Review of the element-read progress** (finder and skeptic, read-only,
no blocker): `Data.Inner` checked at every array/struct construction
site and `memSet`; the control is stuck for the inline element; fixed: the
"Not yet done" list (now names `HeapInner`), the module docstring's
grammar, the Handoff row, the TrustAudit list; `memElem_ok`'s success
postcondition drops `HeapInner` (the state is unchanged; noted in its
docstring). Build38 (`f9288e5`) passed.

**Review of the byte-read progress** (finder and skeptic, read-only, no
blocker): stale "pending"/"needs" lines, the scope of "byte reads", the
Handoff row and the `memShape_array` docstring were fixed; the element
condition was checked at every site (above). Build37 (`a035e78`) passed.

**Review of `memSet_ok`** (finder and skeptic, read-only, no blocker):
"succeeds or panics" was stronger than the statement (reworded); the
caller bridges were unstated (documented above); the witness lacked a
shaped-heap fact (`arrHeap_shaped` added). Build35 (`ba39d50`) passed. A caller of `writeLoc_memByte_ok` gets its precondition from
a `memory` reference's `Val.RefOK` through `STy.memShape_bytes` and
`StOK.le`. The statement excludes only `stuck` (a timeout is not
excluded by the statement, though the code cannot produce one there).

**Review of the shape invariant** (finder and skeptic, read-only, no
blocker): every allocation site checked shaped; the precondition is
satisfiable and dischargeable from `Val.RefOK` (the `memShape` inversion
lemma was missing: added); "writes or panics" was stronger than the
statement (reworded); `heapObj_pres` had lost its docstring and four new
lemmas had none (added); frame restores were missing from the to-do list
(added). Fixed after build33 (`3aa644e`, passed).

**Review of the location preservation** (finder and skeptic, read-only,
no blocker): the open question about allocations was closed by reading
the code (above); the docstring of `writeLoc_mem_pres` claimed byte writes
and `writeLoc_memByte_pres` had none; the TrustAudit block left out the
helper lemmas and called the control "preservation"; the heading said
"writes" where reads need the shape too. All fixed.

**Not proved**: the triple for every interpreter function (`evalE` …
`dispatch`, deployment, transactions, callbacks). The approach is the one
`Solidity/Source/Horizon.lean` uses for horizons: a structure with one
field per function at horizon `n` and one step lemma per function, as the
progress walk (`NS`/`NSP`, `FragAt`) does; preservation and modifiers need
`Hoare` triples, whose preconditions carry the invariant. The
census below lists, per `stuck` site, the invariant the step lemmas need.
Two facts the invariant must handle, found while setting it up:

- an external call runs the callee in a fresh heap (`enterInstance`) and
  restores the caller's heap afterwards, while `St.fnLocals` keeps the
  caller's modifier locals: the invariant on `fnLocals` must hold only
  for the frame that runs modifiers, not across frames;
- `bytes(s)` of a `string memory` keeps the pointer, so a `bytes memory`
  reference may name a string object: `RefOK` treats `bytes` and
  `string` objects of one location as compatible (`STy.memShape`;
  `refOK_heap` shows both).

## Checkpoint 3: gap-relative progress (partial)

**Value layer** (`Solidity/Source/ValueProgress.lean`). Each pure value
operation is never `stuck` on operands in its domain, and every elaborated
term stays in the domains:

| Theorem | Statement |
|---|---|
| `binVal_ok` | `binVal` is not `stuck` for an operator of `arith` at a numeric type, of `bit` at a bit type, of `logic` at `bool` (`BinOp.FitsAt`) |
| `cmpVal_ok` | `cmpVal` is not `stuck` for a comparison at an ordered type or one with equality (every such value has a key, `Val.key_isSome`) |
| `shiftVal_ok`, `intPow_ok` | shifts at `int`/`bytesN`, powers at `int` |
| `unaryVal_ok`, `incDecVal_ok`, `amount_ok` | `-`, `!`, `~`; `++`/`--` at a numeric type; shift amounts and exponents |
| `intRes_ok`, `fixRes_ok`, `intBin_ok`, `fixBin_ok`, `bytesBin_ok` | the arithmetic below them |
| `binOpName_admits` | the operator `toR` reads off a binary expression is one its rule kind admits (`BinKind.admits`) |
| `Typed.toR_opsOK`, `StmtD.toR_opsOK`, `ItemsD.toR_opsOK` | every operator node of an elaborated expression, statement or block is in its operation's domain (`RExpr.OpsOK`) |
| `Elaborated.body_opsOK`, `Elaborated.inits_opsOK` | so is every body, modifier argument, constant and initializer of an elaborated unit |
| `convVal_ok`, `constVal_ok`, `mkInt_ok`, `mkFix_ok`, `FixTy.scaled_mem`, `Q.toFixed?_mem` | implicit conversions of value-type values and of constants are never `stuck` (integer widening, integer to fixed point within solc's bounds, fixed-point rescaling, `bytesN` padding, enums, user-defined value types, contracts, external function types) |

`RExpr` itself does not tie a `binary` node's operator to its type, so
`OpsOK` is the fact a progress proof needs about the elaborated program
at those nodes; with it, the 30 `stuck` sites of `Value.lean` the census
classifies as `shape` are unreachable from an elaborated program, once the
interpreter walk is done.

**Interpreter, value fragment** (`Solidity/Source/ExprProgress.lean`,
`Solidity/Source/StmtProgress.lean`). `NS m` says `m` never halts `stuck`
from any state; `NSP m Q` adds a postcondition on results. Both compose
through the interpreter's binds, `sub`, `lift`, pipelines and matches.

| Theorem | Statement |
|---|---|
| `evalE_valFrag_ns` | evaluating an expression of the **value fragment** (`RExpr.ValFrag`: literals (not constant state variables), locals of value type, `this`, unary and binary operators including `&&`/`\|\|`, comparisons, shifts and powers, `? :`, implicit conversions from value types and constants; state variables of value types and values of mappings (nested mappings included) with keyable keys, read; and assignment, compound assignment and `++`/`--` to locals, such state variables and such mapping values) that is `OpsOK` is never `stuck`, at any horizon, from any state |
| `exprNSAt` (`ExprNSAt`: `val`, `pair`, `ref`, `loc`, `convArgs`; `val_step`, `pair_step`, `ref_step`, `loc_step`, `convArgs_step`, `exprNSAt_step`) | the induction on the horizon: expressions, operand pairs, mapping references (`RExpr.MapRef`, with the postcondition `RPost`: a storage reference names a path of its type) and lvalues (`RLVal.IsSimple`, with the postcondition `LocOK`: a local, or a storage cell of value type at its own type with a default) |
| `readAt_ns`, `writeAt_ns`, `Storage.read_isSome`, `keyStep_nsp`, `Val.word_isSome`, `cellTy_key`, `pathTy_key`, `Env.pathTy_go`, `storRef_map_nsp` | storage: a cell of value type at its layout type with a default always reads; a write at the layout type succeeds (or reverts in a static frame); a keyable key is a key step; a mapping value's path has the mapping's value type |
| `convRV_ns`, `getV_ns`, `readLoc_ok`, `writeLoc_ok`, `compound_dom` | its other steps |
| `stmtNS`, `itemsNS` (from `StmtNSAt`, `execS_nsStep`, `execItems_nsStep`, `forIter_nsStep`, by induction on the horizon) | executing a statement or block of the **statement value fragment** (`RStmt.ValFrag`: expression statements, declarations of types with a default, blocks, `unchecked`, `if`, `while`, `do`/`while`, `for` with a simple initializer, `break`, `continue`, `return;`, `return e;` and `return (a, b);` of value types: `evalConvArgs_ns`, `setRets_ok`) in a **body frame** (`BodyFrame nps R Γ`: the locals end in the return slots, then the `nps` parameters, as `callInternal` builds them) is never `stuck`, at any horizon, in any modifier context |
| `itemsNSP` (the post `Out.esc`; `Out.close_esc`, `Out.up_esc`) | outside loops (`SCtx.loop = false`) a block of the fragment ends normally or by `return`: no `break`/`continue` escapes it |
| `callInternal_ns` (from `runMods_nil_ns`, `zeroVals_ns`, `retVals_ok`, `Locals.getAt_ok`) | **leaf functions**: an internal call is never `stuck` when virtual dispatch finds a body without modifiers, in the statement fragment (so making no calls, emitting nothing, with value-typed locals) and `OpsOK`, whose locals are the frame the call builds (return slots over parameters, return types with defaults); the frame hypotheses are derived for elaborated programs except the dispatched override's return types and its membership in the unit, `hdec` (the `Elaborated.*` rows) |
| `Elaborated.body_locals` (from `Decl.frame?_lengths`, `Frame.mk?_lengths`, `Syn.tys_params_length`, `Syn.tys_typeName_length`, `Frame.tysOf_locals`) | every elaborated body's locals are its returns over its parameters, last innermost: the frame `callInternal` builds |
| `Glob.dispatchFn_params`, `Elaborated.callInternal_call_ns` | dispatch finds an override with the called declaration's parameter types; for a call node only the override's return types (and membership in the unit) stay open |
| `Elaborated.callInternal_ns`, `Elaborated.callInternal_sig_ns` (from `Elaborated.body_sig`, `Decl.frame?_fnSig`) | in an elaborated program, `callInternal_ns`'s frame hypotheses reduce to dispatch coherence, stated syntactically: the declaration virtual dispatch finds has the call's signature (`fnSig`); when dispatch returns the called declaration itself, that is the call node's own premise |
| `evalE_callFrag_ns`, `stmt_callFrag_ns`, `callInternal_callFrag_ns` (from `fragAt`: the joint induction `FragAt` over expressions, statements, bodies without modifiers and internal calls; `exprNSAt_step`, `stmtNSAt_step`, `mods_step`, `call_step`) | **internal calls inside expressions**: the fragment is parameterized by the callees it allows (`RExpr.ValFragC A`, `RStmt.ValFragC A`; the call-free `ValFrag` is `A = fun _ => False`, so `evalE_valFrag_ns`, `stmtNS`, `itemsNS` and `callInternal_ns` keep their statements, while `exprNSAt`/`stmtNSAt` now state the case `A = fun _ => False`), and for a program whose allowed functions are implemented by fragment bodies in the call's frame (`CallsOK A G c`, per contract `c` whose frames run the call, **assumed**: no lemma derives it for an elaborated program) evaluation is never `stuck`, recursion included |
| `BodyFrame.ext`, `Locals.setAt_ok`, `Locals.setAt_ok'` | declarations keep the frame; writing a return slot is never `stuck` |
| `ItemsD.toR_ns` | so is the elaboration of a typing derivation whose image is in the fragment (`OpsOK` from the derivation) |
| `RStmt.ext`, `RItems.ext`, `Locals.restore_ok`, `Out.close_ok`, `Out.up_ok` | ending a scope is never `stuck`: a statement's output context extends its input |

Controls (`Solidity/Source/SoundnessExamples.lean`; the `*_value` and `*_stuck` controls are kernel `rfl`, the `*_ns` ones ordinary proofs):
`addSub_ns` (S01's own `a + a`), `cond_ns`/`cond_value` (`true ? 1 + 2 : 0`
evaluates to `3`), `cb_ns`/`cb_value` (S05's `x = x + 1;` on a storage
variable is never `stuck` and takes `x` from 3 to 4), `loop_ns`/`loop_value` (`uint8 i; while (i < 3) { i += 1; }`
is never `stuck` and ends with `i = 3`); negative controls
`badBinary_stuck` (a hand-resolved `true + false` evaluates to `stuck`:
`OpsOK` is needed) and `ret_unframed_stuck`/`ret_unframed_no_frame`
(`return 1;` over locals without a return slot is `stuck`, and those
locals are no `BodyFrame`: the frame hypothesis is needed; with the slot,
`ret_framed_ns`); `retPair_ns`/`retPair_unframed_stuck` for `return (1, 2);`. `retLocalPair_ns` for `return (x, x);` over a declared local. Calls inside expressions: `callF_ns` (`f()` with `f` implemented by `return 1;`, through `retOne_callsOK`), `callF_value` (it evaluates to `1`, at horizon 10), `recF_ns`/`recF_timeout` (`f` calling itself, `return f();`: never `stuck`, it times out at horizon 12; the callee's body itself calls) and `callF_badFrame_stuck` (with a body outside the call's frame it is `stuck`: the frame conjunct of `CallsOK` is needed). `callG_ns`/`callG_value` use a program with distinct bodies for `f` and `g` (`g` returns `f()`, which is `1`, at horizon 12; `fg_callsOK`). The declarations (scope `none`, not in `E0`) are dispatched to themselves, so virtual dispatch is not exercised. Function level: `callRetOne_ns` (an internal call of a
`return 1;` body) and `callBadFrame_stuck` (a body whose locals lack the
return slot is `stuck`, "call frame"). Witnesses from S01 typing derivations (through `toR`): `incBody_ns` (the counter's typed
body `count++;`, through `ItemsD.toR_ns`) and `indexMapping_ns` (S01's
`m[o]`, a mapping value read).

The storage side conditions (`E.cellTy d.path = τ`, `E.pathTy d.path =
some τ`, a default for the value type) are checked per expression in the
fragment predicate rather than derived from the elaboration: deriving them
needs the lemma that a resolved state variable is the declaration
`Env.declOf` finds at its path (the census's `stor` class).

**What the fragment leaves out**, in the order a whole-program proof needs
it: modifiers (`runMods` with invocations,
`_`), the coherence of dispatch and elaboration (that the body virtual
dispatch finds has the call's return types and is one of the unit's: the
parameter half is proved, `Glob.dispatchFn_params`), for calls inside
expressions the whole-program hypothesis `CallsOK` (assumed, not derived
for elaborated programs: every allowed callee, dispatched from the
contract whose frame runs the call, is a body without modifiers, in the
fragment and `OpsOK`, in the call's frame, with defaulted return types),
memory (the `heap` invariant, `WellTyped.lean`), arrays and
structs in storage, external calls, `emit`, builtins, and the transaction layer (dispatch,
ABI). Each is listed with its sites in the census below.

### The `stuck` census

A read-only census (finder agent, checked against the code) of all 118
`Halt.stuck` sites (`Value.lean` 30, `Machine.lean` 22, `Eval.lean` 61,
`Semantics.lean` 5), by what rules each out for a well-typed elaborated
program:

| Class | Sites | Ruled out by |
|---|---|---|
| shape | 68 | the value's type index plus the `toR` premises (`OpsOK` above for operators; `callTy`, `lengthTy`, `memberTy`, `copiesTo`, key types, `mkRet` shapes for the others) |
| frame | 18 | program coherence: bodies exist for dispatched functions and overrides (`Elaborated.bodies_typed`), locals end in parameters and returns, `fnLocals` matches the running modifier, constants and initializers at their types, constructor frames |
| heap | 13 | a `memory` reference of type `τ` names a live object of type `τ` (`bytes`/`string` compatible), aggregates hold `Data.val` elements, struct objects have their layout's fields |
| stor | 3 | a `storage` reference of type `τ` names a path of declared type `τ` (`Env.cellTy p = τ.cell`), storage element types are storage-located |
| gap | 12 | not modelled, reachable by well-typed programs (below) |
| typing gap | 3 | well typed by S01, refused by solc, `stuck` at run time (below; all 3 fixed) |
| bug | 1 | fixed (below) |
| dead | 1 | `heapAt` (`Machine.lean`) has no caller in the interpreter |

**Gaps reachable by well-typed programs** (none is on the per-constructor
ledger `semExprGaps`, which lists only constructors S01 does not type):

- dynamic ABI decoding of `calldata` parameters, static arrays, structs
  and external function types (`Eval.lean` `decodeArgs`), and of memory
  arrays of non-value elements (user-defined value types: closed, below);
- ABI encoding of memory arrays and structs (returns, external-call
  arguments, `emit`/error arguments) and of external function values;
- `calldata` references (six sites by the census, two of which name
  calldata explicitly; the other four were not re-checked by the review; all shadowed by the decoder's
  refusal: no `cdRef` is ever built);
- getters of non-value types (`string public s`);
- `fallback` with parameters;
- the default of function-typed variables (a function-typed state
  variable read before written; function-typed locals, fields, returns);
- **storage-pointer and calldata return slots and uninitialised calldata
  locals** (new): `callInternal` zeroes the return slots before the body
  runs, and a `storage`/`calldata` type has no default, so
  `function g() internal view returns (uint[] storage r) { r = a; }` is
  `stuck` at entry although solc accepts it.

**Typing gaps** (S01 types them, solc refuses them, the semantics is
`stuck`), fixed in S01's rules and G13's checker:

- `p = S(1)` (a copy into storage) with `p` a local `storage` pointer
  (solc 7407): `Typed.assignCopy` requires `Γ.namesLocal a = false`
  (`ptrCopy_refused`, which also shows `s = P(x)` and `p = s` typed);
- `delete p` with `p` a local `storage` pointer (solc: "delete cannot be
  applied to storage pointers"): `Typed.delete` requires
  `Γ.deleteRefused τ e = false` (`ptrDelete_refused`, which
  also shows `delete s` and `delete m` typed).
- storage-to-storage assignment of types containing mappings
  (`mapping(uint => uint)[2] a; … a = b;`, `stuck` in `loadMem`; and a
  struct with a mapping member, which ran as a copy of nothing):
  `Typed.assign` requires `Γ.assignRefused τ a = false`: the type contains
  no mapping (`Env.hasMapping`, through arrays and struct members), or `a`
  names a local storage pointer being rebound, solc's exemption
  (`mapAssign_refused`).

Also decided on 2026-10-30: `delete` of a `calldata` reference is refused
(`Ctx.deleteRefused`; `cdDelete_refused`).

**Bug fixed**: `bytes(s)[i] = b` on a `string memory s` was `stuck`
("not bytes"): `convExplicitRV` keeps the pointer, so the object is a
string, and the byte write accepted only `bytes` objects. The write now
updates a string object in place (`Eval.lean` `writeLoc`), as solc does
(`stringByte_write`: `b` reads back `0x78`).

**EIP-214 fixed** (integration review): `callAddr` answered a call with
value from a static frame with `.revert []`, which only failed the call,
so `send` returned `false` and a static frame could continue; it now
halts the calling frame (`static_value_call_halts`, against the same call
from a frame that is not static, which only fails). A callback with value
from the environment's static frame still fails without halting it: the
environment's strategy moves next.

**Review of the work since checkpoint 1** (finder and skeptic, read-only,
on 62379eb..f4eb4e3). Confirmed and fixed: the mapping refusal also
refused rebinding a local storage pointer, which solc exempts (both
reviewers); `Env.hasMapping`'s fuel counted every declaration, which made
a recursive struct (`struct S { S[] a; S[] b; }`) exponential to check:
it now counts struct declarations (`Env.structCount`); `mapAssign_refused`
gained a nested struct and the rebinding neighbours; stale text
(`Typed.delete`'s premise here, `source-s03.md`'s UDVT getter remark,
the vacuity bullet, a duplicated item, the `badFrameBody` docstring,
`cdDelete_refused`'s solc citation); `callInternal_ns` is described as
covering leaf functions. Accepted by both: `itemsNSP` (the `SCtx.loop`
indexing of `brk`/`cont`, `unchecked`, loops), the fuel's sufficiency,
`deleteRefused` against solc, the UDVT decoder, the getter revert, the
pins.

**Final consistency review** (read-only, the whole document against the
code at `1fbea8e`). Fixed: the gate record now covers checkpoints 2-4
("Gates (checkpoints 2-4)"); the checkpoint-1 counts are labelled as of
build9; checkpoint 4 has its own heading; the `callInternal_ns` row,
Handoff row 3 and the coverage-plan row name both open coherence
hypotheses and Panic `0x41`; "Not proved" matches the "Not done" list;
`cbBody.items`; the `heapAt` caveat; the description of the walk's
method; a split list.

**Review of internal calls inside expressions** (finder and skeptic,
read-only, on 3f61cf3..90f4226). No correctness defect; the horizon
bookkeeping of `fragAt` was checked against `Eval.lean` by both. Fixed:
no witness used the mutual part (skeptic): `recF_ns`, `recF_timeout`;
the coverage-plan row and this document now say that `CallsOK` is
assumed, not derived, and what it requires (both); `CallsOK`'s quantifier
over every contract was stronger than needed (finder): it is now per
contract (`CallsOK A G c`, `FragAt A G c n`, `StmtNSAt`'s contract
predicate `Q`); the
witnesses' degenerate program and `fDecl`'s shape are recorded; the
`ExprNSAt` field list, `callF_badFrame_stuck`'s docstring (one conjunct),
the "unchanged theorems" sentence (`exprNSAt`/`stmtNSAt` now state the
call-free case), module-map rows and the TrustAudit list
(`retLocalPair_ns`). Recorded, not changed: the argument orders
`ExprNSAt A G F n` and `StmtNSAt G A Q n` differ.

**Review of the frame, `return (a, b)` and signature work** (finder and
skeptic, read-only, on 481d3ee..b934819). Confirmed and fixed: the doc
said the parameter half of dispatch coherence followed from `Env.fnIn`
without a theorem (both): now `Glob.dispatchFn_params` and
`Elaborated.callInternal_call_ns`; G14's override rule compares returns
only up to locations and against direct bases (finder), and the
membership hypothesis `hdec` is undischarged (skeptic): both listed as
open; no concrete `Elaborated` witness (skeptic): recorded; a stale table
row and Handoff row. Accepted by both: `setRets`/`retVals` slot positions,
the frame order against `callInternal`, `evalConvArgs_ns`,
`Decl.frame?_fnSig` stated for the dispatched declaration, the pins.

## Checkpoint 4: closing gaps (partial)

**Run-time gaps closed**:

- ABI decoding of a user-defined value type argument, as its underlying
  type (`decodeWord`, a wrapper over `decodeElemWord`): `elabW` in
  `ElaborateExamples.lean`, where `f(W w)` with `type W is uint8` runs on
  `7` and reverts on `300` (it was `stuck`), and `g(V v)` with
  `type V is int8` runs on `-1` (a sign-extended word) and reverts on
  `200`.
- Panic `0x41` in the ABI decoder, in part: a length word past the data
  reverts first (solc's `offset + 0x1f < end`), then a `bytes`/`string`
  or dynamic-array argument whose length is `2^64` or more panics with
  `0x41` before the bounds check, as solc's `array_allocation_size` (it
  reverted with no data): `elabB` (`g(bytes)` with length `2^64` panics,
  `2^32` reverts, a length word cut short reverts, `"ab"` runs; legacy
  pipeline, the decoder does not depend on it). solc's
  `finalize_allocation` band just below `2^64` (lower for later arguments
  and under via-IR) still reverts here: a recorded deviation
  (`docs/solc-alignment.md`). `Horizon.lean`'s `tailBytes`/`decodeArg`
  lemmas gained the branches.

  The first version (`3843b17`, marker `d0f8f02`) checked the length
  before the offset and claimed the whole of solc's behaviour; the
  coordinator's review (against solc's generated Yul) found both, and the
  marker was not integrated.

Attempted and reverted: getters of `bytes`/`string` state variables
(`dispatch` encoding a storage reference; the control returned `"ab"`):
the extra branch in `dispatch` makes `Horizon.lean`'s `dispatch_apart`
proofs exceed the heartbeat limit (a full gate run on 8e919d0), and raising it is not
allowed; it needs the branch moved into a helper with its own `_grow`,
`_const` and `_below` lemmas in Horizon's lists.

**Other findings recorded** (not `stuck` sites): `string s = "x";` and
`string constant S = "x";` at contract level do not elaborate (a string
literal does not convert implicitly to `string storage`), so the
`.strLit` arm of `storeRV` is dead; calling an external function that
takes `bytes calldata` with a memory argument has no type (memory to
calldata is not implicit in S01), which solc accepts.

**Not proved**: the gap-relative progress theorem for whole programs,
`noGaps`, and its corollary. The interpreter walk covers the value
fragment of expressions and statements, `return`, and internal calls
(also inside expressions, recursion included) under `CallsOK`; the rest
is listed in the Handoff's "Not done".

## Handoff

Kept current at every checkpoint.

| Checkpoint | Status | Theorems |
|---|---|---|
| 1 Integration | done (gated head: see Gates) | `hasType_iff`, `stmtOK_iff`, `itemsOK_iff`, `wellFormed_iff` over S02's typing; controls `member_checked`, `structNew_checked`, `extCall_checked`, `extCallValue_checked`, `pay_checked`, `abiEncode_checked`, `zero_types`, `hexCall_typed` |
| 2 Preservation | partial | `Hoare` and its rules; `alloc_ok`, `allocRef_ok`, `heapPut_ok`, `heapObj_ok`, `heapAt_ok` (dead code: `heapAt` has no caller), `storRef_ok`, `HeapOK.alloc`, `HeapOK.write`; location reads and writes (`writeLoc_*_pres`, `readLoc_*_pres`, `memSet_pres`, `memElem_pres`); the shape invariant `HeapShaped` and progress of memory byte writes and reads and element/member writes (`writeLoc_memByte_ok`, `memSet_ok`, `writeLoc_mem_ok`, `heapBytes_ok`, `readLoc_memByte_ok`) and, under `HeapInner`, element and member reads (`memElem_ok`, `readLoc_mem_ok`); memory writes keep `HeapInner` (`memSet_inner`, `writeLoc_memByte_inner`); `heapPut_inner`; the zeroing allocator and the storage copier keep `MemOK` (`zeroOK`, `loadOK`, with `allocRef_mem` and `Hoare.memGrow`); writes and non-storage `delete` keep `MemOK` (`writeLoc_*_mem`, `deleteLoc_mem`); no preservation theorem for the walk |
| 3 Gap-relative progress | partial | value layer (`binVal_ok` … `convVal_ok`, `constVal_ok`, `Typed.toR_opsOK`, `Elaborated.body_opsOK`); interpreter on the value fragment (`evalE_valFrag_ns`, `exprNSAt`, `stmtNS`, `itemsNS`, `ItemsD.toR_ns`) with storage, mappings and `return`; no escaping `break`/`continue` (`itemsNSP`); internal calls to modifier-free fragment bodies (`callInternal_ns`, `runMods_nil_ns`), with the frame derived for elaborated programs up to the override's return types and unit membership, `hdec` (`Elaborated.callInternal_call_ns`); internal calls inside expressions under `CallsOK` (`evalE_callFrag_ns`, joint induction `fragAt`); `return (a, b)` (`setRets_ok`); the `stuck` census; typing-gap fixes (`assignCopy`, `delete` of local storage pointers: `ptrCopy_refused`, `ptrDelete_refused`), semantic fixes (`bytes(s)[i] = b` on a string: `stringByte_write`; EIP-214: `static_value_call_halts`) |
| 4 Close gaps | partial | UDVT argument decoding (`elabW`); Panic `0x41` in the decoder (`elabB`); getters of `bytes`/`string` attempted and reverted (Horizon heartbeats) |
| 5 `Failures`, `SourceSpec` | not started | |

**Not done** (also under `limitations:`):

- the whole-program progress theorem (every `stuck` of a well-typed
  elaborated program's transaction or deployment is a ledger gap that
  occurs in it), `noGaps` and its corollary, and the token-like witness:
  the interpreter walk covers the value fragment of expressions and
  statements (with storage, mappings and `return`) and internal calls,
  also inside expressions, to modifier-free fragment bodies under a
  whole-program hypothesis (`CallsOK`: every allowed function's
  dispatched body is a fragment body in the call's frame), not memory,
  arrays and structs, external calls, modifiers, builtins, `emit`, or the transaction layer
  (dispatch, ABI decoding, deployment, callbacks);
- preservation for every interpreter step: proved for the memory
  operations only. For the value fragment preservation of `EMOK` is
  expected (locals receive only value types, the heap is untouched, the
  storage references `MapRef` builds are covered by the progress
  postcondition `RPost`), but no theorem states it;
- vacuity on elaborated programs: two witnesses come from S01 typing
  derivations through `toR` (`incBody_ns`: the counter's typed body
  `count++;`; `indexMapping_ns`: S01's `m[o]`, through `MapRef`), besides
  `addSub_ns`; the derivations are written by hand and checked against
  S01's rules, not produced by `elaborate`. The loop, storage and return
  witnesses (`loopItems`, `cbBody.items`, `condE`) and the function-level one
  (`retOneBody`) are hand-built resolved terms. Which elaborated bodies
  are in the fragment is not characterised; for elaborated programs
  `callInternal_ns`'s frame hypotheses are derived from the elaboration
  (`Elaborated.callInternal_call_ns`) except two: the dispatched override's
  return types are the call's, and the dispatched declaration is one of
  the unit's (`hdec`; "Deriving the frame" below); the program run is the
  elaborated one (`hG : G.prog = el.prog`), and the body conditions of
  `callInternal_ns` (no modifiers, the fragment, `OpsOK`, return types
  with defaults: `hmods`, `hf`, `ho`, `hz`) are kept as hypotheses; no
  concrete elaborated program witnesses them;
- the storage side conditions of the fragment (`E.cellTy d.path = τ`,
  `E.pathTy d.path = some τ`) are checked per expression, not derived
  from the elaboration;
- the run-time gaps not on the ledger
  (storage-pointer and calldata return slots, function-typed defaults,
  getters of non-value types, `fallback` with parameters, dynamic ABI
  decoding and encoding of aggregates, calldata references).

**Deriving the frame for elaborated programs.** `Elaborated.bodies_typed`
gives `b.locals = tysOf f.locals` with `d.frame? E = some f`;
`Decl.frame?_lengths` (by cases on the declaration kind and node: Lean
generates no equation lemmas for `Decl.frame?`'s nested match) and
`Frame.tysOf_locals` turn that into `b.rs.reverse ++ b.ps.reverse`
(`Elaborated.body_locals`), so `Elaborated.callInternal_ns` needs only
the callee's signature to agree with the call's (`b.ps = ps`,
`b.rs = rs`) and the dispatched declaration to be one of the unit's;
`Elaborated.callInternal_sig_ns` states it as the dispatched declaration's
`fnSig` being the call's (`Decl.frame?_fnSig`: a function's frame has its
signature's types). The parameter half is proved: the declaration
dispatch finds has the called declaration's parameter types
(`Glob.dispatchFn_params`: `Env.fnIn` selects overrides by them, through
`STy.eq_of_sameList`, and every fallback is `d` itself), so for a call
node `d(args)` (whose signature is `RExpr.call`'s premise)
`Elaborated.callInternal_call_ns` leaves two hypotheses open:

- the return types of the dispatched override are the call's: G14's
  `OverridesOK.rets` compares them only up to data locations
  (`Decl.sameRets`) and only against direct bases, so it would also need
  location equality (or value-type returns) and transitivity along the
  linearization;
- the dispatched declaration is one of the unit's (`hdec`):
  `Elaborated.bodies_typed` speaks of `res.unit.decls`, and for
  `resolveUnit` the environment's declarations are the unit's, but
  `Elaborated` does not record that, and no lemma ties a call node's `d`
  to the declarations.

No witness applies these theorems to a concrete `Elaborated` program; the
function-level witness (`callRetOne_ns`) uses `callInternal_ns` on a
hand-built body.

**How to continue the walk.** New interpreter functions go into the joint
induction `FragAt` (`StmtProgress.lean`) as fields at horizon `n`, each
with a step lemma from the fields at `n` (as `Horizon.lean`'s `BelowAt`),
and a postcondition that carries what the caller needs (`RPost`,
`LocOK`, `Out.esc`). `simp only [evalE]` unfolds one arm; the heavy
matchers (`convRV`, `convVal`, `keyStep`) are handled by `split` on the
general match or by per-case `rfl` equations, never by
`simp only [convVal]` (whnf timeouts). The next steps, in order:

- modifiers: `runMods` with invocations and the `_` arm read and write
  `St.fnLocals` and check its context at run time, so they need a state
  invariant (the running modifier's frame) in the pre- and postcondition,
  that is, Hoare triples over `NSP`'s "from any state";
- `CallsOK` for elaborated programs: from `Elaborated.callInternal_call_ns`
  per call, given the override return-type and unit-membership lemmas
  above and a characterisation of the bodies in the fragment;
- memory: `WellTyped.lean`'s `EMOK` in the pre- and postconditions (the
  heap typing grows), which also gives preservation;
- external calls, `emit`, builtins and the transaction layer.

**Elaboration.** `ExprProgress.lean` and `StmtProgress.lean` each check
in under a minute with the language server; `SoundnessExamples.lean`
evaluates the loop and storage witnesses in the kernel in seconds.
