# Compiler verification

`Solidity/Evm/` compiles a fragment of the scoped syntax (`Stmt C Γ Γ'`,
`Solidity/Syntax/Scoped.lean`) to an EVM-style stack machine and proves that
the compiled code does what the typed run (`Stmt.run`,
`Solidity/Semantics/Run.lean`) does. It is mini-solkey's
`Ch08_EVM`–`Ch10_Correctness` scaled up to the typed calculus: control flow,
reverts, checked arithmetic (signed too, and `**`), arrays (`push` and `pop`,
copies, aliases into elements), internal calls and `transfer`.
`docs/module-map.md` lists the modules.

`Evm.Compiler.compile` is the checked entry for the core fragment below and
the memory fragment for primitive arrays, primitive struct fields, and
primitive-member struct construction and copies from storage roots. It returns code together with a fragment
certificate; `Compiler.Compilation.correct` (`Main.compiler_checked`) proves
their common source/machine agreement. The selected path determines its
explicit input and output state relation; `inFragP` and `compile_correct`
describe the core path.

## Memory operations

`Compiler.compile` selects one compiler for the whole program: the core path
(no memory) or the memory path. The core path's output relation is `Sim`
only; using it as a prefix to memory compilation needs separate preservation
evidence.

**What the memory path accepts.** Dynamic arrays of primitive values and
structs whose members are primitive (or reference-valued, reserved as one
cell each), through typed pointer locals: element and field reads and
writes, lengths, array reads composed in indices and RHS values (`a[a[0]]`),
checked operators, short-circuit and conditional expressions over memory
operands, primitive storage writes, `require`/`revert`, blocks and
statement-level `if`. Sequential programs may also contain checked loops whose
conditions and bodies belong to this finite memory fragment (below). Allocation: `new T[](n)` with a simple length (the
elaborator captures effects first), a declaration without initializer (the
same as `new T[](0)`), default and literal construction of primitive-member
structs (the elaborator lowers literals to a default declaration and field
writes), and allocating rebinding. Older aliases keep their objects. `delete`
of an element, a field, a whole array local (a fresh empty array) or a whole
struct local (a fresh default object). Numeric `+=` `-=` `*=` `/=` `%=` and
standalone or captured `++`/`−−` on elements, fields and locals (the result
word stays on the stack during the checked bump, so `i = xs[i]++` and
`i = i++` are right). Nested paths through reference-valued fields
(`Evm/MemoryPaths.lean`) for reads, aliases and primitive writes;
reference-field assignment redirects a member to an existing child
(`Evm/MemoryRefWrite.lean`); deleting a reference member allocates a fresh
empty array or primitive-member struct (`Evm/MemoryRefDelete.lean`); copies
of a primitive-member struct from a storage root (`Record memory fresh =
stored;`, `Evm/MemoryStructCopyCode.lean`).

**The representation.** `Memory.StateRepr` extends the core simulation with
an identity-to-base map, disjoint bounded array intervals (length cell then
elements), separated headerless struct intervals (one word per member in
order, `StructHeapRepr`, `StructArraySeparated`), initialized pointer locals,
reference-member words (`RefFieldsRepr`) and a reserved frame limit
(`frameNeedProg`: the largest context anywhere in the program). Arrays and
structs lie above every reserved local cell. Reads and writes revert on the
same out-of-bounds accesses as the typed run. The machine stays
word-addressed: this is no bytecode or gas equivalence claim.

**The allocator.** A bump allocator with its cursor in cell zero and zeroed
free memory (`Evm/MemoryAlloc.lean`). The array-only allocator cannot be
reused once structs exist: a zero-valued struct can sit in the "unused" zero
tail (`legacy_write_breaks_allocator` is the counterexample), so
`StructAllocatorRepr` requires every live struct interval to end before the
cursor. `Memory.GrowingResult` threads the extended map through the program
(`BaseExtends`); `GrowsAllocator` records the exact cursor advance. A struct
reserves `max 1 memberCount` cells, so every reached allocation costs
something. **Capacity is a theorem premise** (`AllocationInput`: an inhabited
allocator, frame base `0 < b`, room for the cost the source run reaches,
`cursor + size + 1 < 2^256`); the generated code does no runtime capacity
check. The cost follows successful source prefixes only: an earlier revert
needs no capacity for an unreachable allocation, and without allocation the
premise is vacuous. solc can panic on an allocation size the typed run
permits, which is why this is evidence and not a check.

**Evaluation order.** Compound updates read their operands in a different
order on the two sides; each evaluator either returns or reverts, so no
other halt can be hidden by the reordering. Reference RHS values are
evaluated before the parent path; a deletion resolves its parent before
allocating.

**Out of the memory path**: reference-element arrays, construction of structs
with reference members, other reference-member default layouts, copies other
than the primitive-member storage-root clause (including memory back to
storage and runtime-length objects, which need iteration), nested loops and
loops beneath enclosing blocks/branches, `assert`,
calls, payments, and compound storage writes in a mixed memory program.

**Regressions** (each runs the actual source program and the public
compiler's code, with an inhabited public input):
`Evm/MemoryCompileExamples.lean`, `Evm/MemoryExprExamples.lean`,
`Evm/MemoryAllocExamples.lean`, `Evm/MemoryAllocSourceExamples.lean`,
`Evm/MemoryStructDefaultExamples.lean`, `Evm/MemoryPathExamples.lean`. The
large computed compiler results there are marked irreducible for
elaboration; kernel checks still unfold them, and the pointer compiler
recurses structurally so acceptance reduces in the kernel (no native
reduction is trusted).

### Checked memory loops and enclosing scopes

`Evm/MemoryLoop.lean` proves an unbounded simulation of `Stmt.loop`
using `Instr.loop`. The condition carries `ValFrag`; the body carries
the existing finite `ProgFrag`, and its output flags must restrict to
the entry flags. Every next turn therefore has the same checked fragment.
`Evm/MemoryLoopCompile.lean` composes those loops with finite statements.

The additive `Evm/MemoryLoopScope.lean` certificates compose these programs
under enclosing typed blocks and statement-level conditionals. The selected
branch alone contributes allocation demands and costs. Scope exit drops local
bindings while retaining the actual heap extension and address map; the join
weakens flags with the existing restrict/meet operations. Both branches must
compile, including an unselected branch. Loop bodies still use the original
finite certificate: a loop inside another loop's BODY remains refused.

`Compiler.compile` tries the core, finite-memory and direct/sequential
`memoryLoops` paths first, then the new `memoryLoopScopes` path. Existing
discriminators retain their meaning; `isMemoryLoopScopes`,
`memoryLoopScopesResult` and `memoryLoopScopes_input` expose the new result
and its premises without normalizing a whole computed certificate.

The input is `StateRepr`, a bound covering every temporary frame in either
branch/body, and reached-prefix `Room`. `LoopPrefix` records actual successful
turns with their exact allocation cost. A reached true-condition turn requires
capacity for allocations before a later revert too. Program demands shift a
reachable suffix by the exact successful prefix cost; unreachable suffixes
contribute nothing. A zero-iteration loop needs no body capacity.
`room_nonallocating` is inhabited even for divergence. Scope helpers preserve
the selected branch's `Room`; an unselected allocating branch needs no capacity.
The result retains `StateRepr`, stack equality, `BaseExtends`, an exact
typed `Cost` witness on success, and `GrowsAllocator`.

`MemoryLoopScopeBudget.prefixBudget` is a sufficient, partial recognizer.
It can bound a finite allocating prefix before a syntactically nonallocating
suffix without evaluating that suffix. It returns `none` at a scope or loop
head it cannot bound; manual checked room lemmas handle allocating turns and
selected/unselected scopes. It is not a termination or universal allocation
oracle. Cost/demand views are kernel eliminators for the typed certificates.

Normal exit, revert and divergence remain distinct. Absent any finite normal or reverting outcome, the certified loop has
source `diverge` and machine `fault`; no iteration fuel or successful
termination premise is added. Continuously allocating divergence generally
cannot inhabit finite-word capacity. Source exhaustion is not reclassified:
The memory-loop certificates continue to refuse exhaustion-producing clauses
such as `assumeFalse`,
including in unselected branches, and `not_exhausted` follows from the full
simulation. Existing layout, copy, reference-array, reference-struct, call,
payment and assembly boundaries are unchanged. This is word-memory compiler
refinement, not raw bytecode/layout/gas refinement or universal source coverage.

`MemoryLoopScopeMeta` and `MemoryLoopScopeCompile` use generalized kernel
recursors with native indexed-match twins and universal kernel equality links.
The compiler's constructor equations share already checked results instead of
normalizing complete certificates twice. No proof, search, node or timing
limit was raised.

The original `MemoryLoopExamples`, `MemoryLoopAllocExamples` and
`MemoryLoopSourceExamples` controls are retained. The additive scope examples
check inhabited public simulation and actual source/compiled observations for
arrays, aliases and primitive structs in legacy and viaIR source orders;
zero iterations with a genuinely reverting body; selected revert; exact
exhaustion with refusal; unsupported nested loop bodies even when unselected;
one reached allocation; allocation before revert; a nontrivial enclosing
local drop (literal `7`, positive scope depth); full temporary-frame
reservation; and a last-word unselected allocating branch with an actual
`StateRepr` and public agreement. Selected divergence, an unreachable revert
suffix, and allocation before nonallocating divergence have kernel-checked
exact outcomes and inhabited room. Their infinite executions are not run by
native evaluation. The allocating divergent prefix is also refused without
its one required cell.

Bare source blocks can flatten during elaboration. Ordinary source regressions
use retained `if` nodes; typed regressions exercise actual `Stmt.block`.
`tests/solc/MemoryCompilerLoops.sol` retains the four original functions and
adds scoped variants. `scripts/memory-loop-evm.mjs` and
`scripts/memory-loop-scope-evm.mjs` actually execute calls through the pinned
EthereumJS adapter in all four legacy/viaIR × optimizer-off/on modes with
published solc 0.8.34. Both sets observe arrays `4`, records `3`,
allocateTurn `0`, and empty-data revert before return. Wrong-value,
wrong-halt and unchanged host instruction-budget refusals remain controls.
These sampled upstream executions complement kernel simulation; they are not
a solc/EVM refinement theorem. No feature inventory status is promoted.

Current validation, batch `solidity-compiler10-20261028`, original base
`f4dee4a29c2e208b36db4a4161a4723c735cd775`:

| Check | Actual result |
|---|---|
| Runtime | Lean 4.24.0, Lake 5.0.0-src+797c613; versions and KeySort build exited 0. |
| All eleven scope modules | Exit 0, 14.39 s in the dedicated multi-target build, including original imported controls. |
| Original/scoped four-mode EVM runners | Each exited 0 (1.54/1.52 s); 32 expected fixture-call observations in total, plus negative controls. |
| Affected script tests | All 22 passed, exit 0. |
| Orphans/layers/classification/complete TestSuite/trust | Each exited 0; 152 core modules, zero elaborator reach; 491 automatic + 61 budgeted, zero manual/pending; 552 derived + 11 refuted + 1 excluded; 753 sources / 250 trust sites / zero findings. |
| Fresh original Derived17 group | All 24 modules freshly checked, exit 0, 262.03 s whole guarded workload, peak group RSS 2,944,225,280 bytes. |
| Public/scope/capacity/divergence axioms | Only `propext`, `Classical.choice`, `Quot.sound`. |
| Documentation paths | Exit 1: the same 20 historical references, byte-identical to the recorded failing baseline. This gate is not passed. |
| Full repository | `./run-lean.sh` exited 0 in 377.01 s: 702 default-build jobs, 282 TestSuite jobs, and all 377 pinned taclets / 131 read-bearing annotations match. Separate final axiom audit exited 0 in 6.97 s. |

The preflight command receipt is `memory-loop-scope-preflight-56`: all
individual terminal codes are recorded, including the failing documentation
baseline; total 26.93 s, peak aggregate RSS 1,139,437,568 bytes.
The complete `memory-loop-scope-full-57` operation (runtime, full script,
axioms) exited 0 in 384.30 s, peak aggregate RSS 2,914,099,200 bytes and
kernel build-group memory peak 3,253,170,176 bytes. The fresh
timing receipt is `memory-loop-scope-derived17-fresh-36`.
The reproducible timing command is
`lake -f lakefile.memory-loops.toml env python3 scripts/check-memory-loop-timing.py --output <new-directory> --results <receipt.json>`,
under one outer 300-second guard. The validator rejects stale, partial,
cached, failed and over-budget group evidence.

These current heavy checks use a working Docker hard build-group scope:
actual `memory.max=12884901888` and `memory.swap.max=0`, independently
verified in each receipt, alongside the unchanged measured guard
(12 GiB per-process address space, 10 GiB sampled group-RSS stop, 12 GiB
current-memory stop, 100 ms samples). The parent VM has a hard 16 GiB cgroup
and disabled swap. Historical worker fallback runs had only that parent
limit plus sampled/per-process guards; they are not relabeled hard 12 GiB.
The writer lock stays held inside the container for the whole workload.
All runs set `LEAN_NUM_THREADS=1`, use explicit Lean `-j1` through an
archived untracked Lake config, keep caches on disk, and run no Lean server.

The before-scope bounded check of the old compile module/public entry/examples
and actual refusal took 8.78 s / peak 868,950,016 bytes. Dedicated new module
checks were approximately 1–2 s for certificate/metadata/soundness/room/budget/
compiler modules, 2–8 s for examples; these are bounded per-file/cache-state
measurements, not clean-build speed ratios. Nontrivial computed-certificate
comparison hit the unchanged 200,000-heartbeat limit. Sharing component
success equations with `Option.some_get` repaired it; automatic compilation
is proved to return the shared certificate, not merely sampled equal code.

Historical resource stops, address-space failures, interrupted runs, 300-second
timeouts and proof-heartbeat failures are retained in the cumulative evidence,
never counted as passes. In particular the earlier 1110.96/965.51-second replay
groups and fresh-31 timeout failed the original timing gate. The standalone
shared repair is commit `082efb3183e66af30d7324a0291a9b45458460d1`, independently
reviewed and exported against published `040e59d30a6726fa4f9fee831695eeaa4027ede1`;
its complete fresh group passed in 288.65 s. The original worktree's separate
fresh 262.03-second pass above includes the same original nine remaining
proofs, 1024-step walk, 903 visits, refusal controls and unchanged bounds.

Independent read-only finder/skeptic reviews used no Lean server. They found
no semantic defect and identified missing nontrivial outer-drop and scoped
divergence controls, which were added and checked. Final source reviews found no outstanding defect after those controls and
wording corrections. The cumulative handoff records the final gate and artifact
verification decisions. Full logs, hashes, exact commits, receipts,
failed attempts and review outcomes accompany the cumulative handoff.

## What is proved

For a program `P : Prog C Γ Γ'` of the fragment (`inFragP F P = some F'`), a
machine `m` representing the typed state `σ` with its frame at base `b` and
every dynamic array below `L` elements (`Sim C L b F σ m`, `L ≤ 2^64`), and room for its pushes:

```lean
theorem compile_correct {P : Solidity.Prog C Γ Γ'} (hP : inFragP F P = some F')
    (hm : Sim C L b F σ m) (hL : L + Prog.pushes P ≤ Lmax) :
    (∃ o m', Solidity.Prog.run σ P = .ok o ∧ run (compileProg b P) m = .ok m' 0 ∧
      m'.stack = m.stack ∧ Sim C (L + Prog.pushes P) b F' o.st m') ∨
    ((Solidity.Prog.run σ P = .error .revert ∨
        (Prog.asserts P = true ∧ Solidity.Prog.run σ P = .error .panic)) ∧
      run (compileProg b P) m = .revert) ∨
    (Prog.pays P = true ∧ run (compileProg b P) m = .revert ∧ ∃ o m',
      Solidity.Prog.run σ P = .ok o ∧
      Sim C (L + Prog.pushes P) b F' o.st m') ∨
    (Solidity.Prog.run σ P = .error .diverge ∧ (run (compileProg b P) m = .fault ∨
      (Prog.pays P = true ∧ run (compileProg b P) m = .revert)))
```

Both succeed, the machine's stack as it was and its storage, locals and
balances representing the run's final state; or both halt, the run by a
revert or a panic (a failed `assert`), the machine by a revert, as solc's
`Panic(0x01)` is one; or the program pays (`Prog.pays`), the world refuses a
payment, and the machine alone reverts. The third is the price of a
`transfer` that books `net` and nothing else (`TRun.transfer`): the
run does not know whether the contract's account covers the amount or
whether the recipient accepts it, and the machine does. So the theorem is for
the box: what the machine does when it succeeds, the run did
(`compile_box`), and a program that pays no one agrees exactly
(`compile_exact`).  The fourth case is a loop no number of turns ends:
the typed run diverges, and the machine has no outcome (`loopRun`'s fault),
or had stopped at a refused payment before the loop. The typed run has no stuck outcome, so no `not_stuck` is
needed, and `inFragP` says only what the compiler covers.

**The ledger is the money that moved.** KeY's `net` is a ghost of the
interpreter: the machine has no ledger, only every account's balance `bal`
(the Yellow Paper's `σ[a].b`), the balances `bal₀` when the transaction
began (a ghost no instruction touches), and the contract's address `self`.
`Sim` ties them: `net(a) = bal₀ a - bal a` at every word `a` but the
contract's own address (what `a`'s account lost), and the contract's own
entry is `0` (`Sim.netSelf`): it is never moved. A payment of `v` to `a`
books `net(a) - v` unless `a` is the contract itself, which books nothing
(`State.pay`, solkey's `\if(sadr = self) \then(net)`), since nothing moves.
So a wrong booking (a `+` for a `-`, the wrong address, a debit the machine
does not make) breaks the proof, where the ledger the machine used to carry
beside the interpreter's would have matched it whatever it was; and so does
dropping the `if`: a payment to the contract itself would then move its own
entry, which `Sim.netSelf` pins. Read off a run that succeeds:

```lean
theorem compile_net {P : Solidity.Prog C Γ Γ'} {m' : Machine} (hP : inFragP F P = some F')
    (hm : Sim C L b F σ m) (hL : L + Prog.pushes P ≤ Lmax)
    (hrun : run (compileProg b P) m = .ok m' 0) :
    ∃ o, Solidity.Prog.run σ P = .ok o ∧
      (∀ a : Nat, a < W → a ≠ m'.self → netAt o.st.net a = (m'.bal₀ a : Int) - m'.bal a) ∧
      netAt o.st.net m'.self = 0
```

`Evm/Examples.lean` runs `owner = 5; owner.transfer(30);` on a contract
holding `100` (`payOwner_run`: `70` left, `30` in `5`'s account), and
`Evm/Interpreter.lean` reads the run's `net(5) = -30` and `net(this) = 0` off
it (`payOwner_interpreter`).

From a fresh contract (`Sim.init`, every slot `0`, `L = 1`, balances agreeing on the contract's funds, at
any address `self < 2^256`, which `address(this)` reads and `ADDRESS`
pushes):

```lean
theorem compile_storage {P : Solidity.Prog C [] Γ'} (hP : inFragP (Frag.init []) P = some F')
    (hL : Prog.pushes P < Lmax) (balance : Nat) (hb : balance < W) (bal : Nat → Nat)
    (self : Nat) (hs : self < W) :
    (∃ o m', Solidity.Prog.run (freshT C balance hb self hs) P = .ok o ∧
        run (compileProg 0 P) (Machine.init bal self) = .ok m' 0 ∧
      ∀ (r : SRef C (.prim .uint)) s (v : PrimTy.uint.Denote),
        PathSlot C false r s →
        o.st.storage.findLive r = some (.prim v) → m'.store s = v.1.toNat) ∨
    ((Solidity.Prog.run (freshT C balance hb self hs) P = .error .revert ∨
        (Prog.asserts P = true ∧
          Solidity.Prog.run (freshT C balance hb self hs) P = .error .panic)) ∧
      run (compileProg 0 P) (Machine.init bal self) = .revert) ∨
    (Prog.pays P = true ∧ run (compileProg 0 P) (Machine.init bal self) = .revert ∧
      ∃ o, Solidity.Prog.run (freshT C balance hb self hs) P = .ok o)
```

every `uint` path the typed storage holds, the machine holds at its slot.
None uses more than `propext`, `Classical.choice` and `Quot.sound`; no
`sorry`, no `native_decide`.

**The bound.** solc's `push` reverts when an array already holds `2^64`
elements (`Panic(0x41)`); the run's arrays are bounded only by `2^256`. The
two agree while no array reaches the limit, and that is the hypothesis: `Sim`
carries a bound `L ≤ 2^64` on every dynamic array's length (`ReprAt.array`),
each `push` raises it by one, and a loop of the fragment pushes nothing
(`inFrag`), so a program raises it by
at most `Prog.pushes P`, its number of `push` statements outside loops. From a fresh contract
the hypothesis is `Prog.pushes P < 2^64`, which `decide` discharges for any
program one can write. The compiled `push` emits solc's check all the same;
under the hypothesis it never fires.

## The machine

Instruction meanings follow the EVM as [EVMYulLean](https://github.com/NethermindEth/EVMYulLean)
formalises it: arithmetic on words below `2^256` wraps, `DIV`/`MOD` by `0` give
`0`, comparisons push `1`/`0`, `SLT`/`SGT`/`SDIV`/`SMOD` read words as two's
complement (`SDIV` truncates, `-2^255 / -1` wraps, `SMOD` takes the dividend's
sign), `JUMPI` jumps on non-zero, `REVERT` aborts, `CALL` with a value the
contract cannot cover, or the recipient refuses, pushes `0`, and one to the
contract itself moves nothing. Deliberately simplified (`Evm/Machine.lean`
says why):

- **slots are terms** — `root o`, `hash k s o` (`keccak256(k ‖ s) + o`),
  `data s o` (`keccak256(s) + o`) — so keccak never collides, solc's assumption
  made structural; an offset added to a slot does not wrap;
- **relative forward jumps** (`exec` carries the instructions still to skip,
  so it is structural; the fragment has no loops (`inFrag` refuses a
  `Stmt.loop`), and the one solc emits for it,
  `checked_exp_helper`'s, is unrolled: it runs at most 255 times);
- **locals in memory cells** addressed by their level in the context (`cell`,
  `lvl`; solc keeps them on the stack); `KECCAK256` takes its inputs from the stack;
- **the world is the accounts' balances** (`bal`, `self`); a recipient's code
  is not run, and whether it accepts a payment is `accepts`, which no
  instruction changes and the theorem quantifies over; `CALL` takes an
  address and a value only, and an address is a word, not cut to 160 bits;
- no gas, no stack limit.

## The layout, and why it is injective

solc's: state variables in declaration order, a struct's members consecutive,
`uint`/`int`/`bool`/dynamic arrays/mappings one slot, an array's length at its
slot and element `i` at `keccak(slot) + i·size(E)`, entry `k` at
`keccak(k ‖ slot)`. A fixed-size array `T[n]` is laid out inline, as a struct
of `n` members: `size (T[n]) = n · size T` (`size_fixed`), element `i` at
`slot + i·size(T)`, no length slot (`Occ.felem`, `ReprAt.fixed`); its bound is
the constant `n` (`fixedCheck`), and the element's slot is an `ADD`
(`fixedSlot`). An `int` is stored as its two's complement word.
`Occ T s x` says slot `x` belongs to a value of type `T` laid out at `s`.
Two members, two mapping entries, two array elements, and an array's length and
its elements occupy disjoint slots: every slot `Occ T s` names descends from
`s` plus an offset below `size T` (`occ_desc`), a slot has one ancestor per
`keccak` depth (`Desc.unique`), and the rest is prefix sums (`offsetIn_disjoint`).
`save_repr` is where it is used: writing one subtree leaves every other
represented. `OccAt.kind_unique` is the same argument once more: the slot of a
primitive is never an array's length slot, whichever state variables the two
paths start from (`len_prim_disjoint`).

## The fragment, and what is out

In (`inFrag`): `uint`, `int` and `bool` values; storage of any shape (structs,
dynamic and fixed-size arrays, mappings keyed by `uint`, nested); literals (a
`uint` below `2^256`, an `int` in `[-2^255, 2^255)`), locals, storage reads,
every operator (`**` at `uint`, `-x` at `int`), `?:`, short-circuit
`&&`/`||`, `.length` of a storage array (a fixed one is folded to its literal
by the elaborator); `=` of a value into storage, a copy of a *static* value
(no dynamic array and no mapping in it: `bob = alice;`, `triple2 = triple;`,
`persons[0] = alice;`), `=` to a local, `uint x = e;`, `T storage p = …;`
through members, keys and indices, `op=`, `x++;`/`total++;`, `v = x++;` and
`v = ++x;`, `push()` of a primitive element, `push(e)`, `push(sp)` of a static
element, `delete` at any type, `pop()`, `transfer`, `if`, `require`,
`assert`, `revert();`, `msg.sender`, `msg.value`, `block.timestamp`,
`address(this)`, a loop (`while`, `for`, `do … while`, lowered to
`Stmt.loop`) whose body pushes, pays (`transfer`) and shrinks (`pop`,
`delete`) nothing and leaves the fragment's flags as it found them, and a
call of an internal function, compiled inlined
(its arguments stored in its parameters' cells, its return variable zeroed,
its body, the result copied: `argsCode`), when its parameters, return variable
and body are in.

Every guard solc emits is emitted: checked `+`/`-`/`*` (the unsigned `*` check
is solc's `a == 0 || (a·b)/a == b`, `mul_ok_iff`; the signed ones are
`checked_add_t_int256` and its siblings, the `*` one dividing the wrapped
product back with `SDIV`, `smul_ok`), `/` and `%` by zero, `-2^255 / -1`,
`-(-2^255)`, `**` on overflow (`checked_exp_unsigned`), array bounds, `pop` on
an empty array, `push` at `2^64` elements, a refused `transfer`.

An alias bound through an array index (`Person storage p = persons[i];`) is
*fragile* (a flag of `Frag Γ`): the run checks the index once, when `p` is
bound, as solc does, and a later `pop` or `delete` could leave `p` naming a
slot past the end, which it still reads and writes. The representation
relates live elements only, so the fragment forgets fragile aliases at every
`pop` and `delete` (`Frag.dropFragile`);
until then no array shrinks, the machine only ever raises a length slot
(`LenSlot`: a primitive write never lands on one, `len_prim_disjoint`), and the
alias's path stays in bounds (carried by `Sim.flags`).

Out, and why:

| Construct | Why |
| --- | --- |
| memory on the core path | The checked entry selects the memory path instead (above). |
| loops whose body pushes, pays or shrinks | A loop is one structured instruction, `LOOP cond body` (`Instr.loop`, `loopRun`: its turns, a fault where none ends it; an assembler writes the `JUMPDEST` and the `JUMP` back), simulated turn by turn (`loop_sim`, `TurnRel`, by induction on the turns). Its body may not push (the bound `L + Prog.pushes P ≤ 2^64` counts each push once), pay (a refused payment stops the machine while the typed run goes on, and the run's later turns are not related), or shrink (the fragile aliases a turn forgets must be forgotten before every turn). |
| storage copies of a value holding a dynamic array (`basketA = basketB;`, `matrix = …`) | solc copies element by element and clears the old tail: a loop over a run-time length; the machine has no loops. Copies of static values (`staticF`) are in. |
| `push()` of a struct or an array element | solc does not clear the slot it grows into (a `pop` cleared it), and the interpreter revives the popped value there (`pushSlot`); the representation does not relate slots past the end (relating them would need `delete` and `pop` to clear them, which for a dynamic array is a loop). `push()` of a primitive (solc writes `0`) and `push(e)`/`push(sp)` (every slot written) are in. |
| a fragile alias used after a `pop` or `delete` | See above: it may name a slot past the end, which the representation does not relate. |
| `address(this).balance` | Transfers debit the typed balance and the machine account together; `Sim.funds` records their agreement. Direct compilation of the balance read remains outside the fragment. |
| mappings keyed by `bool`/`int` | `ReprAt` relates a mapping keyed by `uint` only (`ReprAt.map` claims its entries only when the key type is `uint`): a `bool` key, which the typed run hashes as `0`/`1`, and an `int` key's two's complement are not related yet. |

The run evaluates an `op=`'s right-hand side before its target; the
compiled code resolves the target first. The simulation lemmas are
dichotomies (a value or a revert; the typed run has no stuck outcome), so the two orders agree on
every outcome. A copy loads every word of the source before it resolves the
target and stores; solc interleaves the two member by member. The two agree
whenever source and target do not overlap; loading first is right even when
they do, so the proof needs no argument about it.

## Build cost

`lake build Solidity.Evm.Interpreter` builds the modules. `Evm/Examples.lean`
is the slowest (the `decide +kernel` runs, the unrolled `**` code under a
raised `maxRecDepth`); `Evm/Correct.lean`'s `stmt_sim` dispatches one lemma
per family, held to `maxHeartbeats 11000`.


### Historical review1 evidence (superseded)

These results describe the earlier review1 checkpoint in the same VM/branch.
The failures and incomplete decision are preserved as history; see the
[current validation](#checked-memory-loops-and-enclosing-scopes) for the
complete fresh 262.03-second pass and final full-repository confirmation.

At that checkpoint:

* `node scripts/memory-loop-evm.mjs --output <results.json>` executes actual
  EthereumJS deployment and calls in legacy/viaIR × optimizer-off/on modes.
  `arrays`, `records`, `allocateTurn` return 4, 3, 0; `allocationBeforeRevert`
  actually reverts with empty data. Corrected run exited 0 in 1.52 s,
  sampled aggregate peak 277,245,952 bytes. Wrong-value and wrong-halt controls fail.
  Separate instruction-limit controls stop deployment and a call as BLOCKED;
  these host refusals do not establish source `THalt.exhausted` behavior.
  Bytecode provenance hashes decoded bytes and checks deployed runtime code.
  These sampled upstream observations are separate from kernel simulation;
  they do not establish universal solc compiler refinement.
* The coordinator correction authorizes the measured fallback described above;
  its host-side record is not visible in this VM. The handoff preserves the
  supplied instruction as a labelled transcription. Subsequent local Docker
  checks additionally verify actual `memory.max=12884901888` and
  `memory.swap.max=0`, with the unchanged sampled guard nested inside.
  No earlier fallback run is relabelled as a hard-cgroup run.
* `check-memory-loop-timing.py` and `check-memory-loop-timing.mjs` enforce
  cumulative accounting for the entire original 24-module proof workload.
  The earlier per-stage timing claim was insufficient. Full fresh attempts
  then still stopped at 300 seconds; see `loops.md` and the archived review1 handoff for exact
  command/result records. No timeout, allocation failure or cached partial
  workload is a pass. The original assignment could not be marked complete at that checkpoint.

The review1 terminal checks reported Lean 4.24.0 / Lake 5.0.0-src+797c613,
`lake build Solidity.KeySort`, `./run-lean.sh`, and compiler/replay axiom
queries each exited 0 under the verified hard Docker scope. The warm full
script took 1.05 s; the complete runtime/build/axiom group took 9.29 s with
sampled aggregate peak 1,227,821,056 bytes. These are cached build/audit costs,
not a fresh proof timing pass. The retained-source fresh group stopped at
300.024 s, exit 75, sampled peak 1,591,115,776 bytes; only the helper and
Discover00–03 completed before Discover04 was interrupted. The cumulative
gate and timed automatic gate correctly exited 1 at that checkpoint. All 22 affected script tests,
trust (742 sources / 246 sites / zero findings), layers (152 core / zero
elaborator reach), orphans (728 reachable / zero orphaned) and complete
TestSuite audit passed. Documentation paths remain failed with the same
20 byte-identical baseline findings. Independent finder/skeptic final reviews
confirmed these distinctions and found no further defect; original completion
remained false at that checkpoint. Current validation supersedes that decision.
Full historical commands, resource peaks, failures, reviews and hashes are
preserved in the cumulative evidence.
