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
explicit input and output state relation. The original `inFragP` and
`compile_correct` continue to describe the core path.

## Memory operations

The memory path reads and writes dynamic arrays of primitive values through
typed pointer locals, reads their lengths, declares primitive locals with
initializers or defaults, and declares/rebinds aliases. Array reads compose
in indices and RHS values, including `a[a[0]]` and writes whose index or RHS
reads another array. Checked binary/unary operators, short-circuit Boolean
operators and conditional expressions recursively compile memory operands.
Primitive storage writes and `require`/`revert` statements compose with these
operations while preserving the heap and pointer relation. Declarations
`T[] memory xs = new T[](n)` allocate primitive arrays, with a simple length
expression (the source elaborator captures effects before it). Allocating
rebinding `xs = new T[](n)` uses the same allocator and changes only that
local's reference; older aliases retain their previous object and address.

Primitive struct fields also read and write through typed local pointers.
Their values compose with array reads and checked operators in the same
value compiler. Alias declarations and rebinding copy the actual typed
reference and runtime base, including struct aliases. Each field occupies
one word in member order, with no array header; reference-valued members
reserve cells. Checked pointer paths follow those words through existing
structs, supporting nested primitive-field and primitive-array reads/lengths,
and alias declarations/rebinding to the referenced objects. Primitive fields
and array elements also support direct writes, deletion, numeric compound
updates and standalone bumps through such paths. Reference-valued field
assignment redirects that member to an existing typed child reference,
preserving older aliases and child objects. Captured bumps retain the typed syntax's simple
receiver requirement; the elaborator first captures a complex receiver into
an alias.
Default declarations of structs with only primitive members also allocate.
The ordinary elaborator lowers positional/named literals into a default
declaration and field writes, so constructor initializers and allocating
rebinding through such literals use these same checked clauses.

`delete xs[i]` writes the element's typed default through the same checked
index code. `delete r.f` writes a primitive field's typed default through its
runtime struct pointer, preserving aliases and independent fields/objects.
`delete xs` instead rebinds that local to a fresh empty array,
consuming one header cell even when it was already empty. Older aliases
retain their object, including earlier writes and element deletions. The
compiler reuses the default-write and allocating-rebind simulations; its
reached-allocation cost includes these fresh empty headers.

Numeric `+=`, `-=`, `*=`, `/=` and `%=` apply to primitive-array elements,
numeric struct fields and primitive locals, including RHS values read from memory. Their fragment
certificates reuse the checked binary value and ordinary write/assignment
certificates. The source equalities account for the different orders of pure
reads: each evaluator either returns its value or reverts, so no other halt
can be hidden by this reordering. Range and zero-divisor checks remain those
of the existing binary compiler.

`Memory.StateRepr` extends the core simulation with an identity-to-base map,
disjoint bounded array intervals (length cell then elements), separated struct
intervals, initialized pointer locals, reference-member words and a reserved
frame limit. `RefFieldsRepr` maps every such word to its actual typed child
identity under the same address map. Every memory
local on entry must have a represented typed pointer. Arrays and structs lie
above every reserved local cell and outside each other's regions. A primitive-array
or struct-field write preserves the other objects and all
local cells; a local assignment/declaration preserves the heap. Every
accepted statement retains its outer locals; blocks and branches pop their
temporary locals while keeping heap objects and updates to older locals.
The explicit `frameNeedProg` bound reserves the largest context used anywhere
in the program, including either branch, even when the final context is smaller.
Reads and writes
revert on the same out-of-bounds accesses as the typed interpreter. The
machine remains word-addressed; this is not a bytecode/gas equivalence claim.

`Solidity/Evm/MemoryAlloc.lean` supplies the target allocation foundation:
a checked bump sequence using the existing instructions, a cursor in cell
zero, zeroed unused memory, and an identity-map extension for an actual
fresh typed primitive array. The representation is preserved across repeated
allocations and intervening writes, including old aliases and disjoint arrays.
Capacity is explicit: `cursor + size + 1 < 2^256` keeps the next cursor a word.
`Solidity/Evm/MemoryAllocExamples.lean` witnesses the assumptions, writes a nonzero value,
allocates again, and checks the old alias, reserved cell and empty-array bounds.
The public compiler rejects allocating declarations and rebinding at `b = 0`, reserving
cell zero from locals. Programs without allocations retain their earlier
frame-base choices.

`Solidity/Evm/MemoryAllocSource.lean` connects this allocator to the actual
scoped `new T[](n)` declaration run for primitive elements. Its local
simulation evaluates the existing simple length expression, allocates the
fresh typed object, extends the address map, and binds the actual pointer.
Both `StateRepr` and the combined `StructAllocatorRepr` hold afterward. The explicit premises
require `0 < b`, room for the new local and the strict cursor-capacity bound.
`Solidity/Evm/MemoryAllocSourceExamples.lean` supplies a joint inhabited
source/machine witness, with a local length and consecutive int/empty-bool
allocations. It also checks public compilation across alias declaration, a
nonzero write, a length-local assignment and another allocation: the later
array has the updated length, while the old alias retains its written value.
The allocating-rebinding simulation similarly proves the actual source run,
new pointer store and retained old pointers. Its public fixture rebinds twice,
keeping both the old aliased object and an intermediate object that no longer
has a local reference; source and target checks retain their distinct values.
An ordinary `sol{…}` acceptance regression also covers the elaborator's
declaration, alias, write, allocating rebinding and read-guard path.

Blocks and statement-level `if` also compile through this path. A branch's
condition uses the checked value compiler, including memory reads and their
reversion. Each branch drops its temporary locals, and the output fragment
meets the retained core alias flags. Allocations survive scope exit, including
objects referenced by an outer local. Branch costs include only the selected
body; a failed condition contributes no body allocation cost.

`Memory.GrowingResult` threads an extended map through the entire program,
preserving each input reference's address (`BaseExtends`). `GrowsAllocator`
records the exact cursor advance and preserves the separated heap and zeroed
free tail whenever a combined struct/array allocator was supplied. The existing statement results
now preserve an available allocator through local, heap and storage changes.
The compiler's `AllocationInput` requires an inhabited allocator, `0 < b`
and sufficient space when a source execution reaches allocation. Its cost
follows successful source prefixes, counts array headers/elements and struct
member/padding reservations (including empty arrays)
and omits the suffix after an error. A prior revert therefore requires no
capacity for an unreachable allocation. Cost calculation stops interpreting
once the suffix contains no further allocation; rejecting an oversized last
request does not construct its source heap. Capacity is a theorem premise; the
generated code does not perform a runtime capacity check. Without allocation,
the premise reduces to zero cost and does not require an allocator.

`Compiler.compile` selects one compiler for the entire program. The memory
path currently refuses reference-element array access/construction,
construction of structs with reference members, other reference-member
default layouts, copies outside the primitive-member storage-root clause,
loops, `assert`, calls and payments. Deletion is supported for primitive-array
elements, primitive fields and whole primitive-array/primitive-member struct locals. The core path's output relation is `Sim` only;
using it as a prefix to memory compilation needs separate preservation
evidence. `Solidity/Evm/MemoryCompileExamples.lean` checks populated source aliases,
distinct objects, both dispatch paths, declarations/rebinding, nested reads,
composed writes, frame capacity and exact RHS/index-read reversion.
`Solidity/Evm/MemoryExprExamples.lean` checks arithmetic over array reads,
short-circuit and conditional skips of invalid reads, signed negation, checked
underflow/overflow/division failure, true/false guards and a memory-to-storage
write followed by a storage-to-memory write. These run both actual source
programs and code returned by the public compiler.
Compound regressions cover all five operators, a local index, shared aliases,
an independent array, failed operands and unsigned range/divisor failures.
`Solidity/Evm/MemoryAllocSourceExamples.lean` also checks deletion through
computed indices, old aliases after repeated local deletion, signed/Boolean
defaults, empty/nonempty bounds failures, and a failed index that skips later
allocations. Each path has an inhabited public-compiler simulation input.
Signed surface compound updates also test truncating division, negative
remainders, overflow and the minimum-int division edge. Standalone prefix/postfix
increments and decrements reuse the checked addition/subtraction-by-one
certificates for array elements and primitive locals. Tests retain aliases,
computed indices, signed values, range failures and reached allocation capacity.
Captured prefix/postfix results also compile: the result word stays on the
stack while the checked bump runs, then goes into the destination local. This
keeps the original index for `i = xs[i]++` and handles `i = i++` correctly.
Hoisted effects in a larger expression compose in source evaluation order.
Compound storage writes in a mixed memory program remain outside this path.

### Struct fields and shared ownership (M20–M30)

`Solidity/Evm/MemoryStruct.lean` proves local read/write simulations over the
actual typed struct heap. Each member occupies one word, including reserved
reference-member cells; there is no dynamic-array length header. Primitive
members use their own Solidity types, and a bound on the whole interval
prevents address wrap. `StructHeapRepr` uses one base per object identity,
keeps distinct structs apart and reserves the local frame. `StructArraySeparated`
and the framing theorems in `Solidity/Evm/MemoryStructHeap.lean` preserve
structs across array writes and arrays across struct writes.

The array-only allocator cannot safely be reused for these writes. A
zero-valued struct can satisfy `StructRepr` in its purported unused zero tail;
`legacy_allocator`, `legacy_struct_repr` and
`legacy_write_breaks_allocator` give a concrete counterexample.
`Solidity/Evm/MemoryStructAlloc.lean` therefore introduces
`StructAllocatorRepr`: all live struct intervals end before the cursor,
alongside the existing array ownership. Its local, struct and array writes
preserve the cursor, zero tail and both represented layouts. The witnesses
include two populated structs, an independent array, a reserved local,
Boolean and unsigned fields, a negative signed field and a rejected wrapping
base. They establish that the new premises are inhabited.

`Solidity/Evm/MemoryStructGrow.lean` extends this invariant through both typed
primitive-array allocation and headerless struct allocation (M21). Old object
identities keep their bases and fields, and the fresh interval is separated
from every older array and struct. Struct allocation advances the cursor by
the member count, using the existing zero tail for primitive defaults. Its
capacity premise also leaves the next cursor representable without wrapping
to the reserved cursor cell. Reference member cells are reserved; their
pointer values and recursive source construction remain outside this layer.
Mixed witnesses allocate an array, then allocate and write a struct. Separate
continuations reuse an old array reference and allocate an empty array while
retaining all older data.

M22 connects the field instructions to the actual typed statement run in
`Solidity/Evm/MemoryStructSource.lean`. `MemoryCompile` and the public checked
entry now accept primitive field reads/writes, struct alias declarations and
rebinding. The existing array allocations, scopes, local/storage writes and
expression clauses preserve the stronger shared state relation. Allocating
programs require ownership of all live struct intervals too; the old array-only
allocator is retained as a lower-level relation, with an explicit bridge for
heaps containing no structs.

The public mixed witness starts with two aliases, an independent populated
struct and an array. It declares and rebinds a scoped struct alias, combines
field/array reads in arithmetic, writes both layouts, retains the changed heap
after scope exit and allocates a new array. Source and target observations
pin the distinct fields, array contents, result, stack, cursor and reserved
local cells. A failed field RHS divides by zero and reverts on both sides.
The large computed compiler result is marked irreducible for elaboration;
kernel checks still unfold it, while opening the input no longer reruns the
compiler at every unification step.

M23 proves that the actual default-copy fold for a struct with only primitive
members creates exactly one typed heap object. `Solidity/Evm/MemoryStructDefault.lean`
connects its declaration, grown local pointers and allocator to headerless
target allocation. Source allocations reserve `max 1 memberCount` cells:
ordinary nonempty structs use their member count, while zero-field layouts
admitted only by the raw model reserve a padding cell. This keeps every
reached allocation's cost positive and its allocator premise mandatory.

`Solidity/Evm/MemoryStructDefaultExamples.lean` checks ordinary Solidity
positional/named constructors, signed fields, aliases, array allocation and
allocating rebinding to a new literal. The typed run and target retain the
old aliased object, the other struct, the signed words and the array's data.
A failed constructor field RHS charges the object already allocated by its
elaborated prefix; an earlier revert charges no later constructor. Capacity
and frame bounds remain theorem premises, and allocation at frame base zero
is refused.

M24 extends the same field-write certificate to primitive field deletion,
numeric compound updates and standalone/captured prefix/postfix bumps. The
source equalities retain the full typed result, including failure; target
arithmetic and stack capture reuse their existing checked implementations.
The ordinary source fixture checks all five compound operators at unsigned
and signed fields, all four unsigned standalone/captured bump forms, signed
captures, nondefault deletion, aliases, a distinct struct and an array. Seven
inhabited failure programs cover unsigned/signed range edges, zero division/
modulo and signed minimum divided by minus one. This field-update clause
does not add reference-member construction or whole-struct copies.

M25 connects whole-local struct deletion to the interpreter's fresh default
object and compiles its allocation plus destination pointer store. The new
object has the same primitive-member restriction and positive reservation
cost as a declaration; older aliases retain the previous object. The public
fixture checks repeated deletion, retains earlier aliases, scoped
and conditional deletion, an independent struct and array, exact twenty-cell
growth, source identities and target contents. An earlier revert omits the
unreached deletion's cost, and insufficient capacity and frame base zero
are rejected. Capacity remains an input premise, without a generated runtime
capacity check.

M26 accepts primitive-array declarations without an initializer. The full
source result is definitionally the same as `new T[](0)`, so the compiler
reuses its allocation certificate and reserves one header cell. A source
fixture covers `uint[]`, `int[]` and `bool[]` defaults, retained aliases,
allocating rebinding/deletion, a populated struct and scoped/selected-branch
operations. Source/target observations and a reached fourteen-cell cost are
checked with inhabited public inputs. An earlier revert gives zero reached
cost and needs no allocator, even with a zero cursor. Reference-element
arrays and fixed-array defaults remain outside this clause.

M27 adds `Solidity/Evm/MemoryRefs.lean` and `Solidity/Evm/MemoryPaths.lean`.
The former tracks typed child pointer words and preserves them across every
supported state operation and primitive allocation. The latter follows
initialized locals and reference-valued struct fields without losing endpoint
types. Its certificates support nested primitive-field reads, primitive-array
reads/lengths and aliases to existing child objects. The public compiler keeps
its existing direct-local fast paths and adds these checked fallbacks.

`Solidity/Evm/MemoryPathExamples.lean` supplies a populated typed `Prog`
fixture: wrapper, holder, leaf and array with actual pointer words, separated
intervals and allocator ownership. Alias writes update the child objects;
scoped primitive writes and later array/primitive-struct allocations preserve
the pointer relationships. Named observations pin source identities, target
contents, reserved cells and four-cell cursor growth. A wrong pointer word is
refuted, and a nested out-of-bounds read has inhabited public input and exact
source/target reversion. These are typed-program regressions; reference-bearing
source construction and reference-element paths remain outside M27; M28
adds direct primitive writes through its field paths. The pointer compiler recurses structurally over a
variable full endpoint type, so acceptance reduces in the kernel as well as
at runtime; no native reduction is trusted.

M28 compiles assignments, primitive deletion, all five numeric compound
operators and standalone prefix/postfix increments/decrements directly through
these paths. New write lemmas retain the complete source result and emit the
RHS before receiver/index evaluation, reusing the checked field/array writes
and allocator preservation. The existing update/bump source equalities supply
the other clauses. Captured direct nested bumps are not new typed statements:
`Stmt.assignIncDec` requires a simple receiver, supplied by the elaborator's
alias capture.

The typed `PathExamples.Direct` fixture checks all five compound operators
and all four standalone bump forms at a nested unsigned field and array
element, nondefault field/element deletion, retained pointer words and a later
array allocation. Named source/target observations and inhabited public
agreement pin two-cell growth. Three accepted failure programs cover a nested
out-of-bounds write, unsigned maximum increment and zero-divisor RHS. M28
does not add reference-member assignment/deletion; M29 and M30 extend those
cases. Recursive construction and reference-element array paths remain
unsupported.

M29 adds `Solidity/Evm/MemoryRefWrite.lean` and compiles reference-valued
struct-field assignment. The emitted code evaluates the reference RHS before
the parent path and stores the child's existing runtime base in the member
cell. Its source theorem updates the actual typed child reference; it neither
copies nor allocates an object. Primitive values, other pointer words, mixed
ownership, frame cells, stack and an available allocator are preserved.

The typed `PathExamples.ReferenceWrite` fixture redirects a holder's struct
and array members to fresh populated children, modifies them through those
updated paths, self-assigns a nested pointer, and restores its earlier links.
Earlier aliases and the fresh children retain distinct values. A later
allocation checks continued ownership; named public input/agreement and
source/target observations pin child identities, pointer words and six-cell
growth. M29 itself covers assignment; M30 adds selected reference-member
deletion. M31 below adds primitive-member storage-root copies. Recursive
reference-bearing construction and reference-element array paths remain
unsupported.

M30 adds `Solidity/Evm/MemoryRefDelete.lean`. Deleting a reference-valued
struct member allocates a fresh empty primitive array or a default struct
whose members are all primitive. The source resolves its parent before
allocation, then weakens that reference into the grown heap and installs the
fresh child. The target retains the parent pointer on the stack across
allocation, swaps the two pointers and writes the member. Older aliases
retain their objects; the strengthened heap relation and exact cursor growth
hold afterward. Other default child layouts remain unsupported.

The checked allocation cost charges only a successfully resolved parent:
one array header or the struct's positive member/padding reservation. The
public entry still requires a nonzero frame base and sufficient reached
capacity. Typed regressions cover repeated/scoped struct and array member
deletion, retained older and earlier-fresh aliases, an old-alias write and a
later array allocation. Named public input/agreement and source/target
observations pin fresh identities, defaults, pointer words and eleven-cell
growth. Insufficient capacity is refuted. An unset parent has zero cost and
reverts, and its public input is refuted; a prior revert has valid public
agreement with zero cost and an unusable zero cursor.

M31 adds checked storage-root copies of primitive-member structs:
`Record memory fresh = stored;` and allocating rebinding `fresh = stored;`.
The source creates one independent object with the stored values at their
actual types. `Solidity/Evm/MemoryStructCopyCode.lean` checks each member
lookup and load, loads all values before allocation, then emits stores that
retain the fresh pointer and the caller's stack. The populated reservation
preserves old objects, typed reference words, separated intervals, reserved
frame cells and the zero tail beyond its exact new cursor. Empty raw-model
layouts still reserve their one padding cell.

The ordinary Solidity fixture proves inhabited public input/agreement and
checks populated unsigned, Boolean and signed copies, retained old aliases,
independent changes, allocating rebinding, scoped copying, deletion and a
later primitive array allocation. Named source/target observations pin twenty
cells of growth and storage independence. Insufficient capacity is refuted;
a prior revert has zero copy cost and valid input at a zero allocator cursor.
This clause does not copy other storage paths, reference-bearing objects or
runtime-length arrays, or copy memory back into storage.

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
| memory on the core path | The checked entry also selects the separate memory certificate/relation, including primitive arrays, primitive struct fields/construction, reference-field paths and primitive-member storage-root copies as described above. The original core predicate still excludes memory. Unbounded runtime allocation needs explicit reached-capacity evidence: solc can panic on allocation size while the typed interpreter permits any representable length. Copies of runtime-length dynamic objects require iteration, which the forward-only machine does not yet support. |
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
per family, held to `maxHeartbeats 11000` (10000 until O8).
