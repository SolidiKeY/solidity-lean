# Semantic gaps

What of Solidity's semantics the model leaves open, and what is out of
scope. The goal is that nothing of the language's semantics stays open
without a stated reason. A program that uses a gap is refused by the
elaborator or the solc import (an `unsupported` row); a claim the model
cannot prove is `pending` with a reason (`scripts/test-solidity.test.mjs`
pins them). `docs/solc-alignment.md` is where the model follows solc over
KeY; this file is the work list.

## Out of scope: the EVM inside Solidity

The model is Solidity's semantics, not the machine's. These are left out on
purpose, and a program using them is refused:

- inline assembly (`assembly { … }`, Yul), `address.code`, `extcodesize`,
  `gasleft()`, gas stipends beyond `transfer`/`send`'s `noCallback`
  reading, `selfdestruct`, `create2` salts;
- raw calldata and returndata (`msg.data`, `msg.sig`, low-level
  `call(data)` with arbitrary bytes), and expectations on them;
- block and transaction fields other than those the model reads
  (`block.timestamp`; not `block.number`, `tx.origin`, `block.basefee`, …);
- storage layout (slot numbers, packing): `Evm/` compiles a fragment and
  proves it against the model, it does not expose slots to programs.

A fact about the chain that a proof needs is stated as an assumption where
the proof uses it (address `0` has no code, `docs/solc-alignment.md`; see
"Chain facts" below), never derived from a machine model.

## Chain facts, as premises

Functional correctness is proved of a deployed contract called by a
transaction, so what every such call guarantees is a premise of the
obligation (`Problem.callPre`, `Frontend/Problems.lean`), not something to
prove: a non-payable function's `msg.value == 0`, a parameter in its ABI
range, `address(this)` at a harness address when the test pins one
(`--self-address`). Bounds that hold of every reachable state belong in the
contract's invariant.

## Open

| Gap | Kind | Status |
|---|---|---|
| recursion (`functionsRecursiveUnbounded`) | semantics: a call is inlined | open |
| a `catch` goal when the callee cannot fail (`tryCatchExactReturn`) | calculus | open |
| a value call to `this` runs `receive` (`callRunsReceive`) | semantics | open |
| `msg.value` bounded by the ether supply (`msgValueArith`) | chain fact | open |
| literal types in `c ? 63 : 255` (`ternaryLiteralOverflow`, false on the EVM) | elaborator | open |
| narrow types inside types (`uint8[]`, `mapping(uint8 => …)`, struct members) | semantics | open |
| signed `**` in `unchecked`; `-128 / -1`, `-(-128)` wrap in `unchecked` | semantics | open |
| `type(T).max`/`min` in `sol{}` (the import folds them) | elaborator | open |
| a narrow operation under `&&`/`||` or a ternary branch | elaborator | open |
| `super` calls; base constructor arguments | semantics | open |
| loops past the search budget (`SolcLoopsOpen`) | search cost | open (branch `open-loops`) |
