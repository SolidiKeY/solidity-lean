# Compiler verification

`Solidity/Evm/` compiles a fragment of the typed syntax (`Stmt C`,
`Solidity/Syntax.lean`) to an EVM-style stack machine and proves that the
compiled code does what the interpreter (`Stmt.run`, `Solidity/Semantics.lean`)
does. It is mini-solkey's `Ch08_EVM`–`Ch10_Correctness` scaled up to the typed
calculus: control flow, reverts, checked arithmetic, arrays and `transfer`.
(The untyped compiler it replaces is at commit `9721af1`.)

## What is proved

For a program `P` of the fragment (`wtProg Γ P = some Γ'`) and a machine `m`
representing the interpreter state `σ` (`Sim C Γ σ m`):

```lean
theorem compile_correct (hP : wtProg Γ P = some Γ') (hm : Sim C Γ σ m) :
    (∃ σ' m', Prog.run σ P = .ok σ' ∧ run (compileProg P) m = .ok m' 0 ∧
      m'.stack = m.stack ∧ Sim C Γ' σ' m') ∨
    (Prog.run σ P = .error .revert ∧ run (compileProg P) m = .revert)
```

Both succeed, the machine's stack as it was and its storage, locals, funds and
ledger representing the interpreter's final state; or both revert. The
interpreter is never stuck on the fragment (`not_stuck`), so `wtProg` is a type
system for it. From a fresh contract (`Sim.init`, every slot `0`):

```lean
theorem compile_storage (hP : wtProg (fun _ => none) P = some Γ') (balance : Nat) :
    (∃ σ' m', Prog.run (State.fresh C balance) P = .ok σ' ∧
      run (compileProg P) (Machine.init balance) = .ok m' 0 ∧
      ∀ r segs s n, PathSlot C false r segs (.prim .uint) s →
        σ'.findStorage r segs = .ok (.prim (.int n)) → m'.store s = n.toNat) ∨
    (Prog.run (State.fresh C balance) P = .error .revert ∧
      run (compileProg P) (Machine.init balance) = .revert)
```

every `uint` path the interpreter reads, the machine holds at its slot.
`#print axioms` of all three: `propext`, `Classical.choice`, `Quot.sound`. No
`sorry`, no `native_decide`.

## The modules

| Module | Content |
| --- | --- |
| `Evm/Machine.lean` | Words, slots, instructions, `Instr.step`, `exec`/`run`; `exec_append`, `exec_skip`. |
| `Evm/Compile.lean` | The layout (`size`, `offset`, `rootSlot`), what a value occupies (`Occ`) and its disjointness lemmas, the fragment (`wtStmt`, `wtProg`), the compiler (`compileVal`, `compileLoc`, `compileStmt`, `compileProg`). |
| `Evm/Repr.lean` | `ReprAt`/`ReprStore`: the machine storage represents the storage tree; `PathSlot`; `find_repr`, `save_repr` (a write of a subtree is a write of the slots it occupies), `zero_repr` (`delete`), `pop_repr`, `initStorage_repr`. |
| `Evm/Correctness.lean` | The guard sequences (`add_tail`, `sub_tail`, `mul_tail`, …, `tail_sim`), `Sim`, the simulation lemmas `spath_sim`/`loc_sim`/`val_sim` and `stmt_sim`/`prog_sim`, the headline theorems. |
| `Evm/Examples.lean` | Compiled code printed, runs checked by `decide`, and the headline applied: `setAge_interpreter` reads the interpreter's `alice.age` off the machine, `overflow_interpreter` proves the interpreter reverts because the machine does. |

## The machine

Instruction meanings follow the EVM as [EVMYulLean](https://github.com/NethermindEth/EVMYulLean)
formalises it: arithmetic on words below `2^256` wraps, `DIV`/`MOD` by `0` give
`0`, comparisons push `1`/`0`, `JUMPI` jumps on non-zero, `REVERT` aborts,
`CALL` with a value the contract cannot cover pushes `0`. Deliberately
simplified (`Evm/Machine.lean` says why):

- **slots are terms** — `root o`, `hash k s o` (`keccak256(k ‖ s) + o`),
  `data s o` (`keccak256(s) + o`) — so keccak never collides, solc's assumption
  made structural; an offset added to a slot does not wrap;
- **relative forward jumps** (`exec` carries the instructions still to skip,
  so it is structural; the fragment has no loops);
- **locals in memory cells** addressed by the variable (solc keeps them on the
  stack); `KECCAK256` takes its inputs from the stack;
- **one ledger for the world**: `balance` and `net`, which is KeY's `net`;
  `CALL` takes an address and a value only;
- no gas, no stack limit.

## The layout, and why it is injective

solc's: state variables in declaration order, a struct's members consecutive,
`uint`/`bool`/dynamic arrays/mappings one slot, an array's length at its slot
and element `i` at `keccak(slot) + i·size(E)`, entry `k` at `keccak(k ‖ slot)`.
A fixed-size array `T[n]` is laid out inline, as a struct of `n` members:
`size (T[n]) = n · size T` (`size_fixed`), element `i` at `slot + i·size(T)`,
no length slot (`Occ.felem`, `ReprAt.fixed`); its bound is the constant `n`
(`fixedCheck`), and the element's slot is an `ADD` (`fixedSlot`).
`Occ T s x` says slot `x` belongs to a value of type `T` laid out at `s`.
Two members, two mapping entries, two array elements, and an array's length and
its elements occupy disjoint slots: every slot `Occ T s` names descends from
`s` plus an offset below `size T` (`occ_desc`), a slot has one ancestor per
`keccak` depth (`Desc.unique`), and the rest is prefix sums (`offsetIn_disjoint`).
`save_repr` is where it is used: writing one subtree leaves every other
represented.

## The fragment, and what is out

In (`wtStmt`): `uint` and `bool` values; storage of any shape (structs,
dynamic and fixed-size arrays, mappings keyed by `uint`, nested); literals below `2^256`, locals,
storage reads, every operator but `**` and unary minus, `?:`, short-circuit
`&&`/`||`; `=` of a value into storage, `=` to a local, `uint x = e;`,
`T storage p = …;`, `op=`, `x++;`/`total++;`, `delete` at any type, `pop()`,
`transfer`, `if`, `require`, `assert`, `revert();`, and a call of an
internal function, compiled inlined (its arguments stored in its parameters'
cells, its return variable zeroed, its body, the result copied: `argsCode`),
when its parameters, return variable and body are in.

Every guard solc emits is emitted: checked `+`/`-`/`*` (the `*` check is solc's
`a == 0 || (a·b)/a == b`, `mul_ok_iff`), `/` and `%` by zero, array bounds,
`pop` on an empty array, an unfunded `transfer`.

Out, and why:

| Construct | Why |
| --- | --- |
| `int` | Signed arithmetic and its guards are not compiled; `ReprV` has no `int` case. |
| `**`, unary `-` | `**` (checked, `uint` only; the interpreter has it) needs solc's `checked_exp` loop or an unbounded unrolling, and the machine has no loops; `-x` is `int`-only in solc. |
| memory (`T memory m`, reads and writes, copies) | The machine's memory holds the locals; the heap and `copySt`/`copyMem` are not laid out. |
| storage-to-storage copies (`alice = bob;`) | A copy is a loop over the type's leaves plus a bound check on nested arrays; not compiled. |
| `push` | The interpreter's arrays are unbounded, solc's stop at `2^64` elements (`Panic(0x41)`): the two would disagree at that boundary, so the theorem as stated would be false. |
| an alias bound to a path through an array (`Person storage p = persons[0];`) | The interpreter checks the index once, when `p` is bound, as solc does, and a later `pop` leaves `p` naming a slot past the end, which it still writes. The representation (`Evm/Repr.lean`) relates the live elements only (`SVal.findLive`), so such an alias is not compiled. Aliases to paths through structs and mappings are in. |
| `v = x++;` | Not compiled (needs the old value kept beside the write); `x++;` is in. |
| mappings keyed by `bool`/`int` | `ReprAt` claims nothing for them (the interpreter indexes by `Int`). |

The interpreter evaluates an `op=`'s right-hand side before its target; the
compiled code resolves the target first. The simulation lemmas are
dichotomies (a value or a revert, never stuck), so the two orders agree on
every outcome.

## Elaboration

`lake build Solidity.Evm.Examples` builds the five modules; per file:
`Machine` 0.7 s, `Compile` 1.1 s, `Repr` 0.7 s, `Correctness` 6.9 s, `Examples`
3.0 s.
