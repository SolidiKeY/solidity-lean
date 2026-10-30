# Compiler verification

This document describes the **current fragment compiler and its proved
boundaries**. The target is a complete compiler for all Solidity in the approved
profile, with kernel-checked source-to-executable-EVM correctness. The
[full compiler roadmap](coverage-plan.md) owns the VM groups and final proof
obligations. The fragment restrictions below are implementation/proof work to
remove, not additional user exclusions; this page does not claim that endpoint
has been reached.

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
statement-level `if`. Allocation: `new T[](n)` with a simple length (the
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

**Dynamic reference-element arrays (nonallocating checkpoint).** The public
entry falls back to `Memory.ReferenceArrays.compileProg` when the older paths
refuse a program. `Compilation.isReferenceArray` identifies this path;
`isMemory` continues to identify the older allocating memory variant.
`RefArrayStateRepr` supplements the existing state relation with each dynamic
reference array's bounded header, actual child pointer words, frame separation,
separation from other reference arrays, primitive arrays and structs. Its
fallible pointer certificates admit initialized locals, reference fields and
indexed reference elements with core-fragment indices. The supported statements
are alias rebinding, reference-element assignment, and primitive dynamic-array
writes through these paths; sequences preserve the supplementary relation and
stack. Bounds failures on either a parent or child revert on both runs.
Redirecting a parent retains old child objects and aliases. This path allocates
nothing and makes no allocator-preservation claim.

`Evm/MemoryRefArrayExamples.lean` inhabits the public input with two populated
children and a two-element parent. Indexed rebinding changes an existing local,
parent redirection leaves its old alias intact, and old/new child writes yield
matching source/machine observations. Three bounds controls, a corrupt-pointer
refutation, and explicit allocation/default/fixed-index registration are checked by
the kernel. The new theorem and witness names are in the enforcing axiom audit.
Independent read-only finder and skeptic reviews found no soundness defect;
their requests for observable rebinding, refusal controls and enforced witness
auditing were incorporated.

**Complete object ownership and fixed-array checkpoint.** A further public
fallback, `Memory.Objects.compileProg` (`Compilation.isObject`), accepts
headerless fixed-array indexing as well as dynamic indexing. Its additive
`Objects.StateRepr` requires positive, pairwise disjoint reservations for every
actual typed heap object, typed primitive/child-pointer element words, pointer
locals, primitive struct fields and `RefFieldsRepr`. Existing compiler input
relations retain their earlier premises. Fixed bounds come from the source type;
a model bound at least `2^256` is handled without wrapping it into a zero word.
Indices remain core-fragment values. Primitive value reads compose with existing
checked operators; linear local assignments/declarations and alias declarations
are supported alongside indexed writes and rebinding. No loops or calls are
admitted by this path.

Successful object programs preserve a supplied **complete** allocator, whose live
intervals include reference arrays, fixed arrays, and even empty objects. The
public input/output helpers expose these assumptions without reducing a computed
compiler certificate. Both `Evm/MemoryObjectArrayExamples.lean` and
`Evm/MemoryFixedChildArrayExamples.lean` inhabit the state and allocator premises,
instantiate public allocator preservation, and check source/machine observations
for retained aliases, value reads, alias declarations and three bounds failures.
An overlapping cursor and a corrupt child pointer are rejected. The generic
adoption theorem preserves old typed child identities across heap growth.
`Objects.defaultEmpty_correct` additionally relates the actual source default
copy to empty-array allocation and complete allocator preservation. A populated
input instantiates it with source/machine observations `[40,32,24,0,9]` and
advances the cursor from 40 to 41. These helpers preceded the public construction
path described below.

`tests/memory-reference-arrays/ReferenceArrays.sol` and
`scripts/check-memory-reference-arrays.mjs` provide 92 independent solc 0.8.34 /
EVM executions across legacy/viaIR and optimizer off/on: retained-alias results
11013/17000/13, empty fixed-child arrays, distinct fixed defaults, and bounds
panic `0x32`. These are independent behavior observations; the separately
checked constructor paths are specified below. Reference-bearing struct
constructor setup remains upstream evidence only. The checked compiler's existing
coarse revert observation remains unchanged. Run the script with the published
soljson and an external node_modules directory containing the optional EVM test
dependencies; these are not Lean dependencies.

**Runtime-length reference-array construction checkpoint.** The additive public
`Memory.Construction.compileProg` fallback (`Compilation.isConstruction`) carries
full object state, reserved-frame and reached-capacity premises. It accepts
empty dynamic defaults, ordinary primitive-array allocation, and
`new T[][](n)` when the immediate child is a dynamic array (its element may be
any permitted map-free type). The length is a core-fragment `Simple`, including
a local runtime value. Literal `new T[](0)` also works at any permitted element
type, including fixed-array and struct references, since it invokes no child
constructor. Both declaration and allocating rebinding are checked. These
constructors compose with the full-object linear statements above; source loops,
blocks, branches and other statements remain outside this narrow fallback.

For `n` dynamic-array children, capacity is exactly `n + 1 + n`: one parent
header/element interval and one positive reservation for each distinct empty
child. The target reserves the parent first; the actual source copy appends
children first. `Gap`, the actual typed `childrenCopy` fold and final parent
adoption relate those orders without shared dummy pointers. A finite
`loopIterN` witness proves target termination in `n+1` condition turns, without
fuel or budget assumptions. Successful composition extends bases for old
identities, preserves retained aliases and all unrelated machine fields, and
threads the complete allocator with exact reached cost. A reverted prefix
omits unreachable allocation suffixes from its capacity premise.

`Evm/MemoryObjectConstructionExamples.lean` splices actual source syntax and
inhabits public inputs for empty defaults, local-length construction, primitive
children, alias mutation, and allocating rebinding. Source and actual target
runs yield 11013; the target observation follows from kernel simulation rather
than reducing the noncomputable loop through native execution. Actual default
children have distinct source identities and distinct represented pointers.
Separate public zero-length and fixed-child literal-zero inputs, source/machine
observations, three bounds failures, a `W-1` final-cursor boundary, rejection at
`cursor+cost=W`, and an inhabited reverting prefix before a uint256-max
allocation are checked. The last control consumes only five cells and reverts
before the oversized suffix.

`Evm/MemoryStructArrayInputExamples.lean` supplies a populated fixed parent of
`Holder { uint[] items; }` objects. Its public input includes genuine reference
fields; parent redirection and writes through retained/new field aliases yield
`[48,32,40,40,32,11,13,16,24]` on both runs. Bounds and corrupt-field controls
are checked. Nonempty reference-bearing struct construction remains refused:
it requires the separate constructor API, and this input path does not claim to
implement that API. The source/EVM fixture's constructor setup is independent
behavior evidence, not checked compiler constructor coverage.

**Nonrecursive reference defaults.** `Memory.ReferenceDefaults.compileDefault`
now recursively compiles finite fixed-array type structure, using empty dynamic
objects, headerless primitive fixed objects, and the existing primitive-member
struct default API as leaves. It refuses structs with reference members. The
certificate is indexed by the intrinsic `RefTy`, map-free proof and exact cost;
its result is the actual `Heap.allocDefault`, not a separate arithmetic model.
No intrinsic representation, SolKey rule or dependency boundary changes.

The public construction fallback accepts nonempty runtime arrays of certified
reference children and default declarations of certified fixed reference parents.
Allocating reference-array rebinding is also checked. Child cost `d(R)` is 1 for
an empty dynamic array, `max 1 n` for a primitive fixed child, the padded member
count for a primitive-member struct, and `max 1 n + n*d(R)` for a reference
fixed array. Runtime reference arrays cost exactly `n+1+n*d(R)`. Fixed parents
are headerless; zero-sized intrinsic fixed objects reserve one positive cell.
Each default child receives its actual separately allocated source identity.
Pending parent gaps survive recursively allocated children, old pointer bases
and positive lower memory cells survive growth, and the target loop has a
finite turn witness. Primitive struct fields can be written through indexed
reference paths while retaining the complete allocator and reference fields.

Six additive public fixtures cover `Box[]` defaults, `uint[1][2]`, nonempty
`uint[1][]`, `uint[1][2][2]`, fixed parents of default dynamic children, and
allocating rebinding. Inhabited complete state/allocator inputs yield actual
source and target observations 11013, 13 and 17000 as appropriate. Twelve
bounds cases check exact source/machine reverts. A further exact-capacity control
includes child cost and rejects `cursor+cost=W`. Historical default-struct
fixtures and counterexamples are retained unchanged. The old two fixed-default
refusal names are explicitly replaced by positive registration controls.

The assignment's independent reference-array layout and construction increment
is implemented. Reference-bearing struct construction remains the explicit
other-lane dependency: the populated `Holder` input above proves its meaningful
array/field path without claiming constructor support. Source blocks, branches,
loops and unsupported expressions retain the existing narrow fragment refusal.
No universal source coverage or inventory promotion is claimed.

Validation uses the published Lean 4.24.0 / Lake 5.0.0-src+797c613,
`LEAN_NUM_THREADS=1`, explicit `-j1`, and verified 12 GiB/no-swap cgroups.
The first `./run-lean.sh` passed 691 library and 259 TestSuite jobs and the
377/131 SolKey comparison in 8032.865 seconds. Its whole validation group
peaked at 12 GiB (reclaim pressure, no OOM/kills). Executor reconnects released
its external writer-lock holder; no repository edits occurred during that
build. A protected repeat with the lock held inside the container passed the
official run in 5.492 seconds; its final full validation group took 97.152 seconds
and peaked at 3,199,209,472 bytes with zero limit/OOM events. These are observed
cache states, not a clean-build performance guarantee. The enforcing audit
passed 546 headlines; the new simulation/agreement axioms are exactly
`propext`, `Classical.choice`, `Quot.sound`. Source trust scanned 720 sources
and 240 inventoried sites with zero findings. Orphan, layer, strict automatic
and trust-script test gates passed. Documentation path checking still exits 1:
20 missing references in unchanged existing files were verified unresolved at
base `f4dee4a29c2e208b36db4a4161a4723c735cd775`; no new missing reference was
found. That gate is not reported as passed.

A single warm paired per-file check of the public compiler measured 0.999 s /
164,806,656 bytes before and 1.062 s / 164,990,976 bytes after. The indexed
pointer compiler retains structural recursion over the full endpoint type;
no speed-driven intrinsic representation decision was reversed. Full commands,
terminal logs, hashes, measured cgroups and review outcomes are exported with
the checkpoint handoff.

**Out of the construction fallback**: construction of structs
with reference members, other uncertified reference-member default layouts, copies other
than the primitive-member storage-root clause (including memory back to
storage and runtime-length objects, which need iteration), loops, `assert`,
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
`Panic(0x01)` is one; or the program pays (`Prog.pays`) and the machine
alone reverts. No proof reaches that third case: the typed run checks the
contract's funds and the recipient's `sendKey` response (`TRun.transfer`,
`State.canPay`), and `Sim.funds` and `Sim.oracle` make the machine's `CALL`
agree with it, so `transfer_sim` gives agreement on both success and refusal
and `StmtOut.refused` is only propagated from an inner `refused`, never originated. The third case, and the
refused-payment alternative of the fourth, are a stale weakening of the
statement ([G04 R32](feature-work/roadmap-g04-restrictions.md#27-payments),
owned by G43). What the machine does when it succeeds, the run did
(`compile_box`), and a program that pays no one agrees exactly
(`compile_exact`).  The fourth case is a loop no number of turns ends:
the typed run diverges, and the machine has no outcome (`loopRun`'s fault),
or, as stated, a refused payment before the loop. The typed run has no stuck outcome, so no `not_stuck` is
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
      (∀ a : Fin W, a ≠ m'.self → netAt o.st.net a.1 = (m'.bal₀ a : Int) - m'.bal a) ∧
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
    (hL : Prog.pushes P < Lmax) (balance : Nat) (hb : balance < W) (bal : Fin W → Nat)
    (self : Fin W) (hbalance : balance = bal self) :
    (∃ o m', Solidity.Prog.run (freshT C balance hb self) P = .ok o ∧
        run (compileProg 0 P) (Machine.init bal self) = .ok m' 0 ∧
      ∀ (r : SRef C (.prim .uint)) s (v : PrimTy.uint.Denote),
        PathSlot C false r s →
        o.st.storage.findLive r = some (.prim v) → m'.store s = v.1.toNat) ∨
    ((Solidity.Prog.run (freshT C balance hb self) P = .error .revert ∨
        (Prog.asserts P = true ∧
          Solidity.Prog.run (freshT C balance hb self) P = .error .panic)) ∧
      run (compileProg 0 P) (Machine.init bal self) = .revert) ∨
    (Prog.pays P = true ∧ run (compileProg 0 P) (Machine.init bal self) = .revert ∧
      ∃ o, Solidity.Prog.run (freshT C balance hb self) P = .ok o) ∨
    (Solidity.Prog.run (freshT C balance hb self) P = .error .diverge ∧
      (run (compileProg 0 P) (Machine.init bal self) = .fault ∨ (Prog.pays P = true ∧
        run (compileProg 0 P) (Machine.init bal self) = .revert)))
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
  made structural; an offset added to a slot does not wrap. This is global
  injectivity, which the [user decisions](solidity-scope.md#user-decisions-2026-10-29)
  forbid in the final theorem: there, only a per-run collision premise over
  the preimages a run hashes, extended to hashed regions of length at most
  L (second round), is approved (G04 R34, owned by G27.05/G46.05);
- **relative forward jumps** (`exec` carries the instructions still to skip,
  so it is structural; a source loop is one structured instruction,
  `LOOP cond body` (`Instr.loop`, `loopRun`), and the loop solc emits inside
  `**`, `checked_exp_helper`'s, is unrolled: it runs at most 255 times);
- **locals in memory cells** addressed by their level in the context (`cell`,
  `lvl`; solc keeps them on the stack); `KECCAK256` takes its inputs from the stack;
- **the world is the accounts' balances** (`bal`, `self`); a recipient's code
  is not run, and whether it accepts a payment is `accepts`, which no
  instruction changes and the theorem quantifies over (a fixed, history-free
  oracle; the user decisions require any outcome, depending on history, for
  untyped recipients, and actual execution for typed ones: G04 R33, G43/G47); `CALL` takes an
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
| loops whose body pushes, pays or shrinks | A loop is one structured instruction, `LOOP cond body` (`Instr.loop`, `loopRun`: its turns, a fault where none ends it; an assembler writes the `JUMPDEST` and the `JUMP` back), simulated turn by turn (`loop_sim`, `TurnRel`, by induction on the turns). Its body may not push (the bound `L + Prog.pushes P ≤ 2^64` counts each push once), pay (`StmtOut` keeps the stale `refused` case of the third disjunct, which the turn relation `TurnRel` does not mirror), or shrink (the fragile aliases a turn forgets must be forgotten before every turn). |
| storage copies of a value holding a dynamic array (`basketA = basketB;`, `matrix = …`) | solc copies element by element and clears the old tail: a loop over a run-time length, which the compiler does not emit. Copies of static values (`staticF`) are in. |
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

The fixed-array increment checked its two inhabited public fixtures in 10.439 s /
361,484,288 bytes aggregate peak, generic array adoption in 1.727 s /
191,942,656 bytes, empty-default simulation in 2.172 s / 197,185,536 bytes,
and the 32 upstream fixture runs in 2.568 s / 258,355,200 bytes. All used the
same 12 GiB/no-swap bound with zero limit/OOM events. An initial optional npm
installation stalled and was stopped (exit -15, **blocked**, not a pass); adding
the documented proxy CA and explicit proxy routing completed the dependency
installation in 5.201 s. Independent finder/skeptic reviews requested root/audit
registration, fixed-child/read/alias witnesses and inhabited allocator
preservation; those requests were incorporated. Full milestone gate evidence
is exported separately from the immutable first-checkpoint logs.

The full fixed-array milestone run passed 704 library jobs, 259 TestSuite jobs
and the SolKey comparison in 129.035 s; its 598-headline axiom audit passed in
94.160 s. The complete validation group took 231.556 s and peaked at
2,976,473,088 bytes, with zero limit/OOM events. Orphan, layer, strict automatic,
source-trust (733 sources, 240 inventoried sites, zero findings) and trust-script
tests passed. The documentation-path output was byte-for-byte identical to the
20 historical missing-reference failures recorded above; that gate remains
failed. Adding the inhabited empty-default witness checked in 3.271 s /
343,101,440 bytes before final confirmation.

The construction increment's populated scalar/struct and boundary fixtures
checked in 9.479 s / 316,563,456 bytes; the literal-zero fixed-child public
fixture checked in 5.277 s / 304,128,000 bytes. The 52 upstream source cases
passed in 3.084 s / 275,841,024 bytes, all under the same 12 GiB/no-swap bound.
An initial child-loop proof hit the unchanged 200,000-heartbeat limit and is
recorded as blocked, not passed. Abstracting loop control from concrete evaluator
bodies repaired it: that module checked in 1.350 s / 182,513,664 bytes, and the
strengthened finite simulation in 1.757 s / 198,868,992 bytes. No budget was
raised. Finder and skeptic read-only reviews found no soundness defect; their
zero-length, capacity and unreachable-suffix requests were incorporated.

The complete construction milestone passed the official 715-library/259-TestSuite
build and SolKey comparison in 125.027 s, plus the enforcing 662-headline axiom
audit in 103.401 s. New loop/construction/public-observation theorems use exactly
`propext`, `Classical.choice`, `Quot.sound`; no axiom declaration was added.
Source trust scanned 744 sources and the unchanged 240 inventoried sites with
zero findings. Orphan, layer, strict automatic and trust-script tests passed.
The bounded group took 236.179 s / 2,190,204,928 bytes aggregate peak with no
limit/OOM events. Documentation-path checking still exits 1 with the identical
20 historical missing references; it is not reported as passed. Both independent
reviewers confirmed their findings closed after the public zero-length,
capacity, unreachable-suffix and populated reference-field fixtures were added.

The final nonrecursive-default increment passed `./run-lean.sh` (733 library
and 259 TestSuite jobs, 377/131 SolKey comparison) in 137.829 s. The enforcing
747-headline audit passed in 125.779 s; new default/array simulations and target
observations use exactly `propext`, `Classical.choice`, `Quot.sound`. Source
trust scanned 762 files and 240 inventoried sites with zero findings. Orphan,
layer, strict automatic and trust-script tests passed. The full validation
group took 271.391 s and peaked at 2,199,785,472 bytes under actual
`memory.max=12884901888`, `memory.swap.max=0`, with zero limit/OOM events.
The 92 source/EVM fixtures passed in 3.428 s / 299,343,872 bytes. Logs retain
all failed development attempts as failures; no timeout is counted as a pass.
The documentation-path gate still exits 1 for the same 20 historical missing
references, byte-for-byte identical to the previous checkpoint output.

Independent read-only finder and skeptic reviews used no Lean server. Both
caught an accidental overwrite of the historical struct-default example module;
it was restored exactly and the new fixture moved to an additive module. The
reviewed allocator/source proofs had no remaining soundness findings. Broad
simp cleanup, audit registration and two stale descriptions were corrected.
Full terminal logs, cgroup measurements, review outcomes, cumulative bundle and
SHA256 manifests are exported in the task handoff. No master merge or push was
performed. No source coverage inventory was regenerated or promoted.

### Reference-array integration audit conflict

The merge of `f93e1e981f0eeed1e51b132bea669f92d74955e9` into
`9b6d1c2990209edbe5220a08f30d04d472dfee03` retained both additive
`TrustAudit.lean` headline blocks. Read-only local finder checks against both
index parents found no missing imports, headline entries or axiom prints;
the combined list has 757 unique entries. A local skeptic comparison confirmed
that the standard-axiom whitelist, transitive collection and rejection logic
are identical to both parents. No proof or target predicate changed.
Independent agent review was unavailable because the service could not load
the session rollout. Per-file Lean MCP diagnostics remained partial after
three 30-second polls, with no diagnostics or failed dependencies returned;
this is pending validation, not a passing Lean audit. `git diff --check` passed.
The coordinator must complete the combined audit under its resource scope.


## Memory-storage-copy recovery checkpoint

The recovery base is `8445c3fc203144251b9d1fc9181f7f61a8189522`, branch
`codex/solidity-copy-recovery-20261030/memory-storage-copy`. The isolated
predecessor at `/workspace/memory-storage-copy-preserved` reproduces the exact
original HEAD and porcelain-v1 NUL-delimited index/worktree status. Recovery
archive SHA256 is `5d4432ab8541e9b1669a464c9e1d350921f769a8e996308614971843f51a6f9e`;
all five member size/hash pairs, four untracked files and 381 evidence files
were verified, with safe paths and no links. Original ready inputs and extracted
recovery members are read-only. Other owners' broad staging remains isolated.

Only this task's algorithms, proof/admission changes, controls and additive
root/trust/docs integration were reconciled onto the pinned base. The complete
source and artifact hash inventory is
`/workspace/memory-storage-copy-evidence/restored-source-sha256.json`. Historical
`/workspace/memorycopy-*` log references below map to preserved basenames under
`/workspace/memory-storage-copy-recovery/evidence`; they are not fresh passes.

Fresh runtime: Lean 4.24.0 (797c613), Lake 5.0.0-src+797c613;
`lake -f lakefile.memorycopy-recovery.toml build Solidity.KeySort` exited 0.
The task-only alternate config preserves all proof/search budgets and supplies
explicit Lean `-j1`, with `LEAN_NUM_THREADS=1`. A network-disabled local Docker
container enforces `memory.max=12884901888`, `memory.swap.max=0`; no new VM or
worker is created. The source-host systemd user bus is unavailable, and its
16 GiB cgroup alone is not claimed as the required build cap.

`lake -f lakefile.memorycopy-recovery.toml build
Solidity.Evm.MemoryStorageCopyExamples Solidity.Evm.MemoryFixedCopyExamples
Solidity.Evm.MemoryFixedMixedExamples Solidity.Evm.MemoryStorageLifecycleExamples`
exited 0 (165 jobs, 518 seconds). Peak cgroup memory: 1,153,257,472 bytes;
sampled aggregate RSS: 1,227,550,720 bytes (shared pages may be counted twice).
The headroom monitor observed no reserve stop. Full logs and monitor JSON live
under `/workspace/memory-storage-copy-evidence`. Lean MCP diagnostics are not
available; installed per-file Lean checks are used instead.

Independent read-only finder and skeptic verified recovery bytes/status and
selective task ownership, and found no copy-semantic defect. Both found four
TrustAudit imports appended after commands; they were moved into the import
header before the audit. Current assurance/module-map summaries were corrected.
Neither reviewer used Lean or a server. Fresh audit, per-file, full/import,
TestSuite/corpus/sort, strict/trust/layers/orphans, external modes and exact-base
doc-debt checks remain pending. This is a partial checkpoint, not completion.

### Recovery checkpoint terminal checks

The first full-run attempt was deliberately interrupted (exit 137, not OOM)
after 185.01 seconds to repair missing explicit `-j1` on executable and LeanTeX
sections of the task-only configuration. All library/executable sections now
include it; source and proof budgets are unchanged and caches were retained.
That interrupted attempt is not a pass.

The local recovery/source checkpoint is reviewable and kernel-proved. All
edited/new Evm Lean files have successful installed Lean diagnostics: the first
batch stopped only because `MemoryCompileExamples.olean` had not been produced;
building the five affected legacy examples repaired that dependency, and the
remaining three diagnostics passed (65.05 s, 2,204,811,264-byte cgroup peak).
The failed batch is retained. The five legacy targets passed in 77.36 s.

The independent reference test passed all four legacy/viaIR × optimizer modes,
with exact observations and deliberately wrong-observation rejection saved in
`/workspace/memory-storage-copy-evidence/external-observations.json` (5.54 s,
343,310,336-byte cgroup peak). The task-only transitive audit checks 90 theorem
heads; its printed main axioms are exactly `propext`, `Classical.choice`,
`Quot.sound` (14.33 s). This does not replace the pending combined TrustAudit.

Orphans (915 reachable, 0 orphaned), layers (169 core, 0 elaborator reach),
strict automation (491 automatic, 61 replay budgets, 0 manual, 0 pending),
source trust (930 sources, 0 findings), trust-script tests (2/2), and the
TestSuite inventory all pass. The inventory's first attempt used an activation
snapshot whose sibling pin file was absent; selecting the existing repository
snapshot repaired setup without changing its pin. The unchanged 274-file
snapshot verifies at `473da8944ca7329e6b76819863591407db26e7ec`.

Sort alignment passes: 377 taclets parsed, 131 read-bearing, 131 covered;
annotations match the pinned rules (4.29 s). Exact-base doc checks both fail
with the identical 72 missing/ambiguous findings; zero new or removed findings
(`docs-comparison.json`). These failing historical gates remain failures.

Finder and skeptic re-reviewed the import, documentation, immutable-input and
checkpoint-accuracy fixes and found no remaining confirmed local finding.
Full `./run-lean.sh`, direct full/import/combined audit, TestSuite kernel build
and corpus validation remain mandatory and pending. The entire assignment
remains incomplete.

## Preserved memory-storage-copy recovery history

The following ledger is preserved historical task evidence from original HEAD `0f1039dac4e032c4e2c4030ee0d35b38c8393f80` and its recovered WIP. Its passes and failures describe that predecessor, not validation of the recovery base. Current recovery evidence is recorded separately.

## Certified memory-to-storage copies (2026-10-28)

`MemoryStorageCopyLoop` proves the actual `Instr.loop` traversals for arbitrary
runtime lengths. `MemoryStorageCopyCode.memoryArrayCopy_run` proves their exact
store effect: copy `[0,newLength)`, clear `[newLength,oldLength)`, then replace
the length. `MemoryStorageCopyLaws` connects that effect to the actual
`MVal.copyMToSt` heap snapshot and `Storage.write` overlay, including destination
frames. `MemoryStorageCopySource.assignMemoryArray_correct` and
`MemoryStorageStructCopy.assignMemoryStruct_correct` give the typed statement
simulations used by the checked compiler. No equality between unrelated heaps
or sampled-equivalence premise replaces execution. Neither traversal uses
scratch memory, changes the caller stack, or moves the allocator cursor.

The existing storage representation has a strict length bound `L ≤ 2^64`.
`Compilation.memory_copy_input` exposes `copyBoundProg P σ ≤ L`, separately
from allocation capacity: every reached successful array copy needs
`sourceLength + 1 ≤ L`. Demand is zero after a reverting prefix or failed source
or destination resolution. This is an explicit representation premise; the code
does not emit a new runtime length check. `Compilation.memory_input` retains
the old premise shape for programs with no array copies. Its optional copy-free
proof is explicit in the existing parameterized failure fixtures. Output claims,
halt policies and the source semantics are unchanged. The demand traversals use
generalized `casesOn`, structural recursion and named equations (Gate G0).

The source/target regressions exercise growing, shrinking, empty and recycled
array destinations, primitive signed/Boolean payloads, independent memory
mutation after copying, struct roots/nested fields/mapping entries, destination
bounds reversion, invalid representation bounds, unreachable copies,
reference-element refusal and retained storage outside the copied region.
`tests/solc/MemoryStorageCopies.sol` is also executed by
`scripts/evm-reference/memory-storage-copy.test.mjs` with the unchanged SHA-pinned
0.8.34 compiler in legacy/viaIR × optimizer off/on. All four modes pass; an
intentionally wrong observation fails the adapter. Its exact `Panic(0x32)` check
is independent reference evidence; the typed compiler theorem claims ordinary
reversion, not bytecode/panic-payload equivalence. No source coverage inventory
status is promoted by these compiler refinements.

Read-only finder and skeptic reviews independently found an overly eager
failed-destination length demand and indexed matching in the initial demand
traversal. Both were fixed and re-reviewed; the length-3/L=1 failing-destination
input is inhabited. Neither reviewer used the Lean server. No blocking semantic finding
remained; mandatory global validation remains blocked as recorded below. All proof/search budgets are unchanged. Keeping loop evaluation opaque
to proof unification repaired an intermediate heartbeat timeout; the complete
array-code proof then built in 1.41 seconds at 0.73 GiB aggregate RSS.

Validation uses the installed measured VM guard: inherited per-process
`RLIMIT_AS=12 GiB`, sampled process-group RSS stop at 10 GiB (100 ms), and
whole-VM `memory.current` stop at 12 GiB, inside the existing hard 16 GiB VM
cgroup with actual swap disabled. This is not a 12 GiB cgroup guarantee or a
claim that `MemorySwapMax=0` was set. Final validation commands source the published activation,
then export `LEAN_NUM_THREADS=1`; the untracked task Lake configuration supplies
explicit Lean `-j1`. Logs and resource JSON are exported with the handoff.

| Check | Exit | Elapsed | Peak aggregate RSS | Guard stop |
|---|---:|---:|---:|---|
| KeySort runtime | 0 | 0.30 s | 0.045 GiB | none |
| Baseline compiler dependencies | 0 | 172.70 s | 3.075 GiB | none |
| Compiler after copy integration | 0 | 30.85 s | 1.124 GiB | none |
| New Lean source/target witnesses | 0 | 6.37 s | 0.932 GiB | none |
| Four-mode Solidity reference | 0 | 3.43 s | 0.342 GiB | none |
| First full run (repaired failures below) | 1 | 1931.55 s | 7.141 GiB | none |

The first full run failed on unchanged `Calculus.LinearDecision` and
`Calculus.TermSize` with thread-creation errors, and on legacy fixture input
proof plumbing after the public memory input gained its copy bound. The two
unchanged modules passed with a smaller temporary stack (65536) and
`MALLOC_ARENA_MAX=2`, under the same guard: 33.03 s, 1.278 GiB. Affected legacy
fixtures and new controls then built together in 68.10 s at 1.300 GiB. Their
programs, capacity premises and expected observations did not change. The final
finder caught three further direct input tuples and one overbroad post-rewrite
tuple edit; their repairs passed both the default build and direct per-file
kernel diagnostics.

Two tool-session terminations orphaned intermediate full runs; their task-owned
groups were stopped and are not passing evidence. Another confirmation was
explicitly interrupted for the reviewed fixture repair. Persistent `setsid`
guards and the writer lock were used thereafter. One full attempt stopped at
the 12 GiB whole-VM threshold (exit 75, 2695.41 s, 7.394 GiB peak workload RSS)
during unchanged `Examples/Tactics/OpenLoops.lean`. Reclaimable file cache was
released using per-file `POSIX_FADV_DONTNEED` advice: whole-VM current fell from
4.34 GiB to 0.15 GiB. Disk caches were retained, all limits/budgets stayed the
same, and the isolated target then passed.

The next full attempt passed all 692 default jobs, then unchanged
`TestSuite/Derived7.lean`, `TestSuite/Derived15.lean` and
`TestSuite/Derived17.lean` exited 134 with `std::bad_alloc`. Their 226-file local
import closure has zero changes against the recorded base. A temporary smaller
stack (65536) and `MALLOC_ARENA_MAX=1`, `MALLOC_MMAP_THRESHOLD_=131072`,
`MALLOC_TRIM_THRESHOLD_=131072` made Derived7 and Derived15 pass. Derived17
still failed. A process snapshot showed 44 Lean task threads despite `-j1`,
with the actual inherited 12 GiB address-space limit. A further temporary
32768 stack and `-DElab.async=false` serialized theorem elaboration and kernel
checking. Installed Lean sources and the independent finder confirm this is a
scheduling change, not a trust or search-limit change. It reached the whole-VM
stop; after a second non-destructive cache reclamation (4.11 GiB to 0.16 GiB),
it reached the 10 GiB aggregate-RSS stop instead. No TestSuite source changed.

**Completion decision: the copy implementation and its targeted validation are
proved; original mandatory validation is BLOCKED.** The final unchanged
Derived17/TestSuite attempt stopped at the required aggregate-RSS ceiling.
The full script is not called passed. The next step is an owner-reviewed
performance decomposition/profile of that existing TestSuite replay under the
same limits, rather than raising budgets or changing its claim. This assignment
does not take over corpus work. Default/core build, SolKey rule check, all 15
edited-file kernel diagnostics, explicit axioms and the trust audit passed
independently. Both final read-only reviewers found no new semantic blocker or
scope drift; the skeptic required precisely this blocked validation decision.
Neither reviewer used the Lean server.

| Terminal check/attempt | Exit | Elapsed | Peak aggregate RSS | Guard stop |
|---|---:|---:|---:|---|
| Default/core `lake build` | 0 | 0.61 s | 0.058 GiB | none |
| SolKey rule check | 0 | 0.61 s | 0.211 GiB | none |
| Direct per-file diagnostics (15 edited files) | 0 | 116.26 s | 2.634 GiB | none |
| `TrustAudit.lean` (554 headline theorems) | 0 | 89.37 s | 1.392 GiB | none |
| Explicit `#print axioms` for copy laws/witnesses | 0 | 2.22 s | 0.759 GiB | none |
| Unchanged open-loop target after cache-headroom repair | 0 | 503.53 s | 8.523 GiB | none |
| Full `./run-lean.sh`: default passed; TestSuite failed | 1 | 3023.99 s | 9.046 GiB | none |
| TestSuite: smaller stack/allocator; Derived7/15 passed,17 failed | 1 | 322.34 s | 9.578 GiB | none |
| TestSuite: 32 MiB stack and synchronous elaboration | 75 | 73.66 s | 8.539 GiB | 12GiB-whole-VM-current-guard |
| Same TestSuite after reclaiming file cache | 75 | 87.87 s | 10.011 GiB | 10GiB-aggregate-RSS-guard |

The explicit axiom report gives `[propext, Classical.choice, Quot.sound]` for
the loop, array representation/source correctness, struct source correctness
and inhabited public compiler witnesses; `primitiveStruct_copy_repr` uses
`[propext, Quot.sound]`. There are no added axioms. The four Solidity reference
modes and negative observation control passed as recorded above.

Orphan, import-layer, strict automatic, source trust, trust-script regression
and TestSuite inventory checks pass. The published environment omitted the
sibling snapshot pin; restoring the byte-identical existing tracked pin repaired
inventory validation without changing its revision. The documentation-path
check exits 1 on 20 historical references in unchanged `Solidity/Eqns.lean`,
`tests/upstream/group03-validation.json` and `tests/upstream/group10-validation.json`.
No tracked file was deleted and no new citation is among those failures. This
is retained documentation debt, not a passing gate. Full command logs, resource
JSON, independent reviews and hashes accompany the cumulative committed export.

Resumed prerequisite check (2026-10-29): a successful fresh fetch found
`origin/master` at `127c2ee59de16971e45b08a2def54f4e5fae8e2a`. The shared Derived17
performance repair is owned by `memory-loops`; it is not yet a validated merged
prerequisite at this head. The source blob is still
`e05598503e3aa2700d5e250c47f390da6dfc4743`, identical to this task's blocked
version, and its last source change remains `1f02521bc4be2275f3cc659e3a17ad047dad48bf`.
The only Derived17-named upstream history records the resource stop. No new
Lean retry was run against that unchanged failure. The existing successful
Lean/Lake/KeySort runtime evidence and all independent copy checks remain
preserved. Resume full acceptance after consuming the owner's validated repair
from `origin/master`; do not duplicate the shared repair, import an unmerged
branch, or mark the current full gate passed. The task is not integrated at
this upstream head and the worker has not pushed or merged master.


### Whole-assignment continuation (2026-10-29)

The first checkpoint omitted primitive fixed arrays. The resumed whole-scope
finder/skeptic audit identified that omission and missing meaningful padding and
mixed-family controls; these are now implemented and kernel checked. The earlier
tables are historical checkpoint evidence, not acceptance results for this head.

`MemoryFixedStorageCopy` adds `FixedArrayRepr`, `FixedHeapRepr` and the separate
`FixedStateRepr` refinement. A fixed source has exactly its typed `n` primitive
words at `base..base+n`, no header, a no-wrap extent, and lies above the reserved
frame. Existing `StateRepr` fields and all old memory-input equivalences stay
unchanged. No cross-layout ownership is assumed. Consequently the new route is
memory preserving: initialized local/reference-field source paths, supported
finite storage destinations, copies, guards, branches and scopes are admitted;
fixed allocation, heap mutation, unset sources, array-element reference paths,
reference-element layouts and recursive types remain refused. General memory
loops remain separately owned. This is a copy refinement over represented
inputs, not universal source-program coverage or bytecode refinement.

`MemoryFixedShapeCode` emits actual structured copying/cleanup loops for
same-size fixed copies, fixed-to-larger-fixed padding and fixed-to-dynamic
replacement. `MemoryFixedShapeLaws` and `MemoryFixedShapeSource` connect their
exact stores to `MVal.copyMToSt`, `FixedCopy.apply` and the actual storage overlay.
Fixed destinations clear every padding word and retain slots outside their
inline extent. Dynamic destinations clear the discarded old live tail and
replace the length last. Source pointers precede destination bounds checks;
failed destinations perform no copy and have zero length demand. Successful
fixed-to-dynamic copies require `n+1 <= L`, using the same strict representation
bound as dynamic sources. No emitted length check or weaker premise is invented.

`MemoryFixedMixedCopy` proves that the existing dynamic-array and primitive-struct
copy algorithms preserve the fixed refinement too. `MemoryFixedCompile` composes
all copy families with intrinsic statement/program certificates. Its `FixedResult`
derives successful source heap equality and target memory preservation from
actual executions; neither is an input shortcut. `Compilation.fixed_input`
exposes the additional representation and reached demand. `isMemory` retains
its old legacy-route meaning; `isFixedMemory` identifies the refinement and
`usesMemory` includes both routes. No old input theorem is weakened.

`MemoryStorageCopyExamples.RuntimeLength` runs one compiled program at input
lengths 0, 1 and 3, and a guard failure at 4, including root and mapping copies
and independent later memory mutation. `MemoryFixedCopyExamples` supplies
inhabited public fixed inputs, both branches, root/member/mapping endpoints,
shape conversions, successful-bound refusal, failed-destination demand zero at
L=1, and explicit mutation/reference-element refusals. Padding starts with an
old word 88, so observing zero detects missing cleanup. Dynamic cleanup starts
with a nonzero discarded tail. `MemoryFixedMixedExamples` initializes fixed,
dynamic and primitive-struct objects at 128, 160 and 192, proves the public
fixed-route input/agreement, and observes source `[31,47,2,91,92,77]` together
with the actual compiled copy values and retained memory cells.

The four-mode reference script really deploys and invokes compiled solc bytecode;
it is not compilation-only evidence. The final extended run executes dynamic,
runtime-length, fixed, padded and mixed cases in legacy/viaIR with optimizer
both off/on, with every earlier expected value retained. It also checks bounds
revert data and deliberately wrong replay observations. These executions
supplement the kernel simulations rather than replace them.

The skeptic found indexed matching on `FixedCopy` in the first shape admission
and demand helpers. Generalized `FixedCopy.casesOn` with destination-index motives
repaired it; the remaining kind tests inspect only ordinary types. Both final
read-only reviewers confirmed the nonzero-padding and inhabited mixed-input
repairs and found no remaining confirmed own-scope semantic/admission/control
issue. Neither reviewer ran Lean, a build or a server.

Published compatibility was integrated only into the existing feature branch,
from `cc155f36dc163e221b1f8279c56fb2006113ee7d`, preserving the original
`f4dee4a29c2e208b36db4a4161a4723c735cd775` base and task commits. A further
fresh fetch found `040e59d30a6726fa4f9fee831695eeaa4027ede1`: it changes no
EVM compiler/source semantics or Derived17 file relative to that compatibility
base, so no further compatibility edit is required. No sibling branch, push or
master merge was used. The shared Derived17 performance repair remains owned
by memory-loops. Its unchanged failed full validation was not rerun to fill time.

The original resource guard and all proof/search/test budgets remain unchanged.
One resumed core confirmation was deliberately interrupted after reviewers
required the mixed/padding controls (exit75, reason `interrupted`); its log is
retained and is not a pass. Twelve final edited-file kernel diagnostics all
exited0. The following initial trust-audit attempt failed because the newly
published `Calculus.MemoryWitness.olean` had not yet been built; it is retained
and requires a real prerequisite build before retry, not a false pass.

| Resumed check | Exit | Elapsed | Peak aggregate RSS |
|---|---:|---:|---:|
| Actual Lean/Lake/KeySort runtime | 0 | 0.30 s | 0.045 GiB |
| Published compatibility baseline (117 jobs) | 0 | 237.32 s | 1.096 GiB |
| Fixed payload/source simulation | 0 | 1.71 s | 0.741 GiB |
| Fixed shape loops | 0 | 1.51 s | 0.731 GiB |
| Fixed snapshot/padding laws | 0 | 1.42 s | 0.744 GiB |
| Fixed shape source and demand | 0 | 7.97 s | 0.865 GiB |
| Compiler shape/mixed admission | 0 | 4.13 s | 0.802 GiB |
| G0 repair and source witnesses | 0 | 42.22 s | 1.132 GiB |
| Inhabited mixed and nonzero-padding controls | 0 | 3.43 s | 0.845 GiB |
| Final actual four-mode execution | 0 | 5.44 s | 0.375 GiB |

Final core/trust/gate terminal evidence and the explicit completion decision are recorded below and in the cumulative handoff; a pending or failed gate is never a pass.


#### Terminal checkpoint before the published reference-array integration

Current copy implementation and kernel/source controls pass on compatibility
base `cc155f36`. Fixed copy and padding loop extents must be strictly below
`W = 2^256`; fixed payloads also have the explicit no-wrap/frame assumptions
above. These are represented-input compiler claims, not general fixed-array
allocation/mutation or universal source/bytecode coverage claims.

The first resumed full core attempt stopped at the whole-VM guard during the
unchanged OpenLoops fixture: exit75, 5258.26s, 8428961792-byte aggregate RSS.
It is not a pass. Under the writer lock, `fsync` and `POSIX_FADV_DONTNEED` on
5961 regular generated checkout build files retained every disk artifact and
reduced VM current from4305002496 to2293972992 bytes (zero errors). The same
OpenLoops target then passed under its unchanged600s limit, in577.94s with
9174196224-byte peak RSS. No source, proof/search/test limit or resource ceiling
changed. The recovered default build passed737 jobs, exit0 in2438.42s at
6900506624-byte peak RSS. Its temporary configuration preserves all published
library/executable declarations, including the unaffected optional solcases
runner; default targets are identical. One trailing-space cleanup changed no
terms or expected observations and was kernel rechecked by that full build.

Final diagnostics: twelve edited-file checks exited0; the final trust audit
exited0 in106.70s and checked616 headline theorems. Explicit copy, shape, mixed
and inhabited agreement axioms are only `propext`, `Classical.choice`,
`Quot.sound` (fixed/padded snapshot representation uses just `propext` and
`Quot.sound`). The final audit/axiom/static group exited0 in121.04s with
1816711168-byte peak RSS. Orphans752/0 disallowed, layers156/0 elaborator paths,
strict automatic491/61 budgeted/0 manual/0 pending, source trust767 sources and
241 inventoried sites/0 findings, trust-script regressions, TestSuite inventory
and frozen SolKey377/131 checks all pass. Documentation paths explicitly fail
exit1 with46 missing references, all in the five published files listed in the
handoff; none changed from the compatibility base. Ambiguous citations are also
retained. This is published documentation debt, not a passing path gate.

Fresh fetch now finds `109ba72ac8cf62f4aa4c13ae5590802244400bd0`, whose published
reference-array/object compiler routes change the common entry API. This
checkpoint preserves the proved copy work; integration and its required checks
continue on this same branch. It is not original-assignment completion.

The strict shared-blocker audit also corrects the older closure statement:
current compatibility closure is227 files,26 changed from original base; the
historical226-unchanged figure applies only to the earlier checkpoint.
Derived17 itself remains blob `e05598503e3aa2700d5e250c47f390da6dfc4743`, last
source commit `1f02521bc4be2275f3cc659e3a17ad047dad48bf`. Published recovery
`b7801b00` reports a successful full run, but its11022848000-byte RSS exceeds
this worker's10737418240-byte stop. It is not a validated repair under this
worker policy; its cache-reclamation mechanism was already tried here before
the actual10GiB group-RSS stop. No unchanged failed full replay is run merely
to wait, and memory-loops retains ownership of the needed performance repair.


Published reference-array compatibility integration is in progress on this same feature branch; checkpoint figures above retain their exact baseline.


### Published object ownership and copy lifecycle integration (2026-10-29)

The compatibility union consumes published `109ba72ac8cf62f4aa4c13ae5590802244400bd0`
without importing an unpublished sibling branch. It preserves core, legacy
memory, reference-array, owned-object and construction route priority and every
published discriminated input/output helper. The legacy memory route retains
its necessary reached-copy bound and copy-free helper. The existing read-only
`fixedMemory` route follows the published routes; the new `copyConstruction`
route follows it. Thus earlier initialized-object route observations are stable.

The new owning APIs make a complete fixed lifecycle available. The earlier
checkpoint's allocation/mutation refusal applies specifically to its weaker
read-only route; it is not a global limitation after this integration.
`MemoryStorageObjectCopy.Objects.StateRepr.fixedCopy` derives fixed payloads
from the actual typed full-object array words. `FixedResult.objects` uses
execution-derived unchanged source heap and target memory to restore complete
object ownership and preserve any supplied allocator (`HeapRepr.mem_eq`,
`AllocatorRepr.mem_eq`). Neither equality is assumed as an input. The complete
object relation is retained, not discarded after projecting the old relation.

`MemoryStorageConstructionCompile` composes published construction/mutation
certificates with the copy certificates. Its common `Objects.GrowingResult`
keeps exact source-computed construction cost, allocation capacity, base-map
extension, allocator growth and reached successful-copy bounds. Owner default,
allocation and mutation algorithms are reused unchanged. Public
`Compilation.copyConstruction_input` exposes all these premises; existing route
claims are unchanged. Source/machine run and storage representations remain the
same intrinsic, dependency-free definitions, with no new axioms or proof budgets.

Admission boundary: this new route composes construction and copying in a
top-level sequence. A block/branch containing both construction/mutation and
copies internally remains refused; existing read-only copy blocks/branches
remain supported. Reference-element storage copies, whole reference-bearing
struct copies, recursive-copy layouts and general memory-source loops are not
added. The former fixed-mutation refusal control now explicitly targets
`Fixed.compileProg`, preserving the weaker route's refusal while separately
proving the stronger public lifecycle admission. No earlier source/machine
expected value is changed.

`MemoryStorageLifecycleExamples` supplies an inhabited public owned allocator
input: fixed array default allocation and zero-copy, initialization31/47,
fixed/padded copies, dynamic3 copy followed by fixed2 replacement (discarded88
becomes shadow/tail0), independent source fixed mutation99, primitive struct
copy77 followed by source mutation88. Kernel source observation is
`[31,47,31,47,0,2,31,47,0,77,99,88]`; actual machine observation also checks
free cursor135, sentinel99 and caller stack77. Source allocation cost is7 and
copy demand4. Insufficient storage boundL=3 is refused; a failed destination
still has demand0 and inhabited L=1 input after actual fixed allocation.
The corresponding Solidity lifecycle executes in all four pinned legacy/viaIR
optimizer modes, returning `[31,47,0,2,31,47,77,99,88]`. The complete reference
run passes exit0 in6.55s at401051648-byte peak RSS, retaining all previous
expected values, bounds/revert data and deliberately wrong-observation control.

Finder and skeptic reviewed the ownership projection/restoration, actual-prefix
cost/bound composition and lifecycle inputs read-only, without Lean/server/builds.
Neither found a confirmed semantic bug; both required root/trust registration
and precise documentation of the sequential composition boundary. Those modules
and theorem heads are registered. The source-level kernel checks pass under the
unchanged guard; final integrated global checks and original completion remain
pending until their actual terminal evidence is recorded.
