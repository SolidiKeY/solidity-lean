# Compiler verification

`Solidity/Evm/` compiles a fragment of the typed syntax (`Stmt C`,
`Solidity/Syntax.lean`) to an EVM-style stack machine and proves that the
compiled code does what the interpreter (`Stmt.run`, `Solidity/Semantics.lean`)
does. It is mini-solkey's `Ch08_EVM`–`Ch10_Correctness` scaled up to the typed
calculus: control flow, reverts, checked arithmetic (signed too, and `**`),
arrays (`push` and `pop`, copies, aliases into elements) and `transfer`.
(The untyped compiler it replaces is at commit `9721af1`.)

## What is proved

For a program `P` of the fragment (`wtProg Γ P = some Γ'`), a machine `m`
representing the interpreter state `σ` with every dynamic array below `L`
elements (`Sim C L Γ σ m`, `L ≤ 2^64`), and room for its pushes:

```lean
theorem compile_correct (hP : wtProg Γ P = some Γ') (hm : Sim C L Γ σ m)
    (hL : L + pushesP P ≤ Lmax) :
    (∃ σ' m', Prog.run σ P = .ok σ' ∧ run (compileProg P) m = .ok m' 0 ∧
      m'.stack = m.stack ∧ Sim C (L + pushesP P) Γ' σ' m') ∨
    (Prog.run σ P = .error .revert ∧ run (compileProg P) m = .revert)
```

Both succeed, the machine's stack as it was and its storage, locals, funds and
ledger representing the interpreter's final state; or both revert. The
interpreter is never stuck on the fragment (`not_stuck`), so `wtProg` is a type
system for it. From a fresh contract (`Sim.init`, every slot `0`, `L = 1`):

```lean
theorem compile_storage (hP : wtProg (fun _ => none) P = some Γ')
    (hL : pushesP P < Lmax) (balance : Nat) :
    (∃ σ' m', Prog.run (State.fresh C balance) P = .ok σ' ∧
      run (compileProg P) (Machine.init balance) = .ok m' 0 ∧
      ∀ r segs s n, PathSlot C false r segs (.prim .uint) s →
        σ'.findLive r segs = .ok (.prim (.int n)) → m'.store s = n.toNat) ∨
    (Prog.run (State.fresh C balance) P = .error .revert ∧
      run (compileProg P) (Machine.init balance) = .revert)
```

every `uint` path the interpreter reads, the machine holds at its slot.
`#print axioms` of all three: `propext`, `Classical.choice`, `Quot.sound`. No
`sorry`, no `native_decide`.

**The bound.** solc's `push` reverts when an array already holds `2^64`
elements (`Panic(0x41)`); the interpreter's arrays are unbounded. The two
agree while no array reaches the limit, and that is the hypothesis: `Sim`
carries a bound `L ≤ 2^64` on every dynamic array's length (`ReprAt.array`),
each `push` raises it by one, and a program has no loops, so it raises it by
at most `pushesP P`, its number of `push` statements. From a fresh contract
the hypothesis is `pushesP P < 2^64`, which `decide` discharges for any
program one can write. The compiled `push` emits solc's check all the same;
under the hypothesis it never fires.

## The modules

| Module | Content |
| --- | --- |
| `Evm/Machine.lean` | Words, two's complement (`sgn`, `toWord`), slots, instructions (`SLT`/`SGT`/`SDIV`/`SMOD`/`AND` beside the unsigned ones), `Instr.step`, `exec`/`run`; running code in pieces (`exec_append`, `run_append_ok`, …). |
| `Evm/Compile.lean` | The layout (`size`, `offset`, `rootSlot`), what a value occupies (`Occ`) and its disjointness lemmas, static types (`staticF`), the fragment (`wtStmt`, `wtProg`, fragile aliases), the compiler (`compileVal`, `compileLoc`, `compileStmt`, `compileProg`), the guard sequences (`uTail`, `sTail`, `negCode`, `expCode`, `pushSlotCode`), `pushesP`. |
| `Evm/Repr.lean` | `ReprAt`/`ReprStore` (with the bound `L`); `PathSlot`; `find_repr`, `save_repr`, `zero_repr` (`delete`), `pop_repr`, `push_repr`, `move_repr`/`overlay_repr` (copies), `OccAt.kind_unique` and `live_mono` (fragile aliases stay in bounds), `initStorage_repr`. |
| `Evm/Signed.lean` | The signed guard sequences exact: `sadd_tail`, `ssub_tail`, `smul_tail` (solc's `sdiv(product, x) == y` check, `smul_ok`), `sdiv_tail`, `smod_tail`, `scmp_tail`, `neg_run`. |
| `Evm/Exp.lean` | `**`: one round of solc's `checked_exp_helper` (`expBody_run`), the unrolled loop (`expLoop_run`), `exp_tail`. |
| `Evm/Correctness.lean` | The unsigned guard sequences, `tail_sim`/`stail_sim`, `Sim`, the simulation lemmas `spath_sim`/`loc_sim`/`val_sim`, the statement lemmas (`copy_sim`, `push_sim`, `assignBumpStore_sim`, …), `stmt_sim`/`prog_sim`, the headline theorems. |
| `Evm/Examples.lean` | Compiled code printed, runs checked by `decide` for every feature, and the headline applied: `setAge_interpreter` reads the interpreter's `alice.age` off the machine, `overflow_interpreter` proves the interpreter reverts because the machine does. |

## The machine

Instruction meanings follow the EVM as [EVMYulLean](https://github.com/NethermindEth/EVMYulLean)
formalises it: arithmetic on words below `2^256` wraps, `DIV`/`MOD` by `0` give
`0`, comparisons push `1`/`0`, `SLT`/`SGT`/`SDIV`/`SMOD` read words as two's
complement (`SDIV` truncates, `-2^255 / -1` wraps, `SMOD` takes the dividend's
sign), `JUMPI` jumps on non-zero, `REVERT` aborts, `CALL` with a value the
contract cannot cover pushes `0`. Deliberately simplified (`Evm/Machine.lean`
says why):

- **slots are terms** — `root o`, `hash k s o` (`keccak256(k ‖ s) + o`),
  `data s o` (`keccak256(s) + o`) — so keccak never collides, solc's assumption
  made structural; an offset added to a slot does not wrap;
- **relative forward jumps** (`exec` carries the instructions still to skip,
  so it is structural; the fragment has no loops, and the one solc emits for it,
  `checked_exp_helper`'s, is unrolled: it runs at most 255 times);
- **locals in memory cells** addressed by the variable (solc keeps them on the
  stack); `KECCAK256` takes its inputs from the stack;
- **one ledger for the world**: `balance` and `net`, which is KeY's `net`;
  `CALL` takes an address and a value only;
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

In (`wtStmt`): `uint`, `int` and `bool` values; storage of any shape (structs,
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
`assert`, `revert();`, and a call of an internal function, compiled inlined
(its arguments stored in its parameters' cells, its return variable zeroed,
its body, the result copied: `argsCode`), when its parameters, return variable
and body are in.

Every guard solc emits is emitted: checked `+`/`-`/`*` (the unsigned `*` check
is solc's `a == 0 || (a·b)/a == b`, `mul_ok_iff`; the signed ones are
`checked_add_t_int256` and its siblings, the `*` one dividing the wrapped
product back with `SDIV`, `smul_ok`), `/` and `%` by zero, `-2^255 / -1`,
`-(-2^255)`, `**` on overflow (`checked_exp_unsigned`), array bounds, `pop` on
an empty array, `push` at `2^64` elements, an unfunded `transfer`.

An alias bound through an array index (`Person storage p = persons[i];`) is
*fragile* (`LTy.falias`): the interpreter checks the index once, when `p` is
bound, as solc does, and a later `pop` or `delete` could leave `p` naming a
slot past the end, which it still reads and writes (the interpreter's
`shadow`). The representation relates live elements only, so the fragment
forgets fragile aliases at every `pop` and `delete` (`TyCtx.dropFragile`);
until then no array shrinks, the machine only ever raises a length slot
(`LenSlot`: a primitive write never lands on one, `len_prim_disjoint`), and the
alias's path stays in bounds (`live_mono`, carried by `Sim.fragile`).

Out, and why:

| Construct | Why |
| --- | --- |
| memory (`T memory m`, reads and writes, `new T[](n)`, `delete m`, copies storage↔memory) | The machine's memory holds the locals, one cell per variable; there is no heap. Laying one out means a word-addressed heap with solc's free-memory pointer, an injective map from the interpreter's object identities to addresses with the objects disjoint below the pointer and zero above it, and a heap typing (an object's layout depends on its type, and aliases share objects), all carried by `Sim` and preserved by every write. Two parts cannot agree with the interpreter at all: `new T[](n)` with a run-time `n` (solc's `allocate_memory` panics once the free pointer passes `2^64`, `Panic(0x41)`, the interpreter allocates any size, and unlike `push` the size is not bounded by the program text), and a copy of a dynamic array or an allocation of an array of structs (a loop over a run-time length). The part that could — structs of primitives, `new` of a literal size, copies of static values — is not built. |
| storage copies of a value holding a dynamic array (`basketA = basketB;`, `matrix = …`) | solc copies element by element and clears the old tail: a loop over a run-time length; the machine has no loops. Copies of static values (`staticF`) are in. |
| `push()` of a struct or an array element | solc does not clear the slot it grows into (a `pop` cleared it), and the interpreter revives the popped value there (`pushSlot`); the representation does not relate slots past the end (relating them would need `delete` and `pop` to clear them, which for a dynamic array is a loop). `push()` of a primitive (solc writes `0`) and `push(e)`/`push(sp)` (every slot written) are in. |
| a fragile alias used after a `pop` or `delete` | See above: it may name a slot past the end, which the representation does not relate. |
| mappings keyed by `bool`/`int` | `ReprAt` claims nothing for them (the interpreter indexes by `Int`, and reads a `bool` key as stuck). |

The interpreter evaluates an `op=`'s right-hand side before its target; the
compiled code resolves the target first. The simulation lemmas are
dichotomies (a value or a revert, never stuck), so the two orders agree on
every outcome. A copy loads every word of the source before it resolves the
target and stores; solc interleaves the two member by member. The two agree
whenever source and target do not overlap; loading first is right even when
they do, so the proof needs no argument about it.

## Elaboration

`lake build Solidity.Evm.Examples` builds the seven modules. `Correctness`
is the slow one (a few minutes: `stmt_sim` is one mutual declaration);
`Examples` runs the unrolled `**` code under `decide` with a raised
`maxRecDepth`.
