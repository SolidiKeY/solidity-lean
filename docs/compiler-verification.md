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
`scripts/check-memory-reference-arrays.mjs` provide 52 independent solc 0.8.34 /
EVM executions across legacy/viaIR and optimizer off/on: retained-alias results
11013, empty fixed-child arrays, distinct fixed defaults, and bounds panic `0x32`. Constructor setup and the
distinct-default control are upstream observations, not claims that the checked
compiler already accepts those constructors. The checked compiler's existing
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

This remains **an incomplete original assignment checkpoint**. Nonempty fixed
reference-array defaults and nonempty arrays of fixed-array or primitive-member
struct references remain independent implementation work in this lane; their
named refusals are retained. Reference-bearing struct construction remains the
explicit other-lane dependency. No source-coverage inventory row is promoted.

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

**Out of the construction fallback**: nonempty fixed-array/struct child defaults,
fixed reference-parent defaults, construction of structs
with reference members, other reference-member default layouts, copies other
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
