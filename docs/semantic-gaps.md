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
prove: a non-payable function's `msg.value == 0`, a payable one's
`msg.value < 2^128` where its body reads `msg.value` (the total ether supply
is below `2^128` wei, so no transaction carries more; `etherBound`, also in
the specified obligation, `Calculus/SurfaceSpec.lean`), a parameter in its
ABI range, `address(this)` at a harness address when the test pins one
(`--self-address`). Bounds that hold of every reachable state belong in the
contract's invariant.

## Open

| Gap | Kind | Status |
|---|---|---|
| recursion (`functionsRecursiveUnbounded`) | semantics, calculus | closed: `Stmt.callRec`, unrolled to the EVM's 1024 frames, proved by contract over the frames (`docs/kernel-port.md`, "Recursion"); the runner proves it with the contract `true`/`true` (`rec_auto`); several or reference returns refused |
| a `catch` goal when the callee cannot fail (`tryCatchExactReturn`) | calculus | closed: each self-call `catch` goal assumes `fails(call)`, the walks prove the callee's diamond instead (`notLeft`; `docs/options.md` O8) |
| a value call to `this` runs `receive` (`callRunsReceive`) | semantics | closed: a self-call `try` of `receive` behind `r == address(this)` (`elabValueCall`, O8); `callKeepsStorageUnsound` stays pending, false on the EVM |
| `msg.value` bounded by the ether supply (`msgValueArith`) | chain fact | closed: `msg.value < 2^128` (`Problem.callPre`) |
| literal types in `c ? 63 : 255` (`ternaryLiteralOverflow`, false on the EVM) | elaborator | closed: solc's mobile type (`mobileTy`); the run reverts (`SolcOpen.ternaryLiteralOverflow` refutes the diamond), the row stays `pending` |
| narrow types inside types (`uint8[]`, `mapping(uint8 => …)`, struct members) | semantics | closed: a state variable's narrow element, key and value (`expandStateTyW`), a struct's narrow member (`structWidths`), a storage alias's, a memory local's and a reference parameter's narrow positions (`LocalTy.shape`, `shapeCheck`), a modifier's narrow parameter (`Checked.lean` §2, `tests/solc/NarrowNested.sol`, `docs/solc-alignment.md`) |
| signed `**` in `unchecked`; `-128 / -1`, `-(-128)` wrap in `unchecked` | semantics | closed: on the words (`narrowWrapNode`, `Examples/Tactics/SignedCasts.lean`), at `int256` too |
| `type(T).max`/`min` in `sol{}` (the import folds them) | elaborator | closed: a value of `T` (`typeBoundExpr`), an enum's members |
| a narrow operation under `&&`/`||` or a ternary branch | elaborator | closed: a conditional capture (`hoist`, `Examples/Tactics/Checked.lean`) |
| `super` calls; base constructor arguments | semantics | closed in the solc import (`readContract`, `Frontend/SolcJson.lean`): `super.f` names the next implementation after its declaration's contract in the most-derived C3 order; the base constructors compose into one constructor in solc's legacy order (`docs/solc-alignment.md`, "Constructors"); a base's contract clauses are inherited; a constructor's modifiers wrap its own body after its bases, and a base's `return` ends its own body (`solcCtorBody<id>`, `tests/solc/InheritanceCtors.sol`); `super` in a modifier's arguments or body names the next implementation after the contract writing it (`SuperMod*`; `super.m` as a modifier name solc refuses); a base's private variable of a later one's name is its own root (`stateRenames`), refused only where a specification names it |
| the four `SolcLoopsOpen` functions | search and closer limits, not semantic gaps | open: `pushNoArgs2dLoop` is false under the default `.solc` tails and holds under `ValidTail .clean` (O6); the others are closer cost (exposed recycled slots, unshared memory terms); `docs/loops.md`, "Open loops lane" |
| a quotient `x / k` of a parameter left open (constructors and functions alike) | closer | closed: `sol_close`'s arithmetic reads a quotient of a nonnegative dividend as `div` (`Int.tdiv_eq_ediv_of_nonneg`, solkey's `sdiv_axiom`; `Calculus/Close.lean`, `tests/solc/CtorDivision.sol`) |
| narrow leftovers: push arithmetic on a narrow element, whole uses in a conditional of references or a struct constructor's argument, a modifier's reference parameter | elaborator | closed: the appended slot checked (`pushedSlot`), the branches and members shape-checked (`narrowWholeAt?`), a modifier's reference parameter a local at its location (`ModApp.locs`, `rawTyW`); `tests/solc/NarrowNested.sol`, `tests/solc/Modifiers.sol`, `Examples/Tactics/Checked.lean`.  A tuple of references stays refused whatever its types (`elabTuple`) |
| a public function's memory array of narrow elements: ABI decoding reverts on one out of range | chain fact | closed: the obligation assumes each element in range (`Problem.callPre`, `SolcFun.elemRanges`), and `sol_leaf` instantiates the quantified premise at the literal indices the leaf reads (`allLeftHide`, `Calculus/AllLeft.lean`; `NarrowNested.abiElementInRange`).  An index that is not a literal (a parameter, a loop counter) is not offered |
| push arithmetic inside `unchecked` (`small.push() -= 1`, `small.push()--`) | elaborator | closed: the appended slot starts at `0`, so the statement pushes `0 op r` wrapped at the element's width (`r` for `+=`, `0` for `*=`, `r`'s negation modulo `2^N` for `-=`, a signed minimum itself; a literal folded), `r` evaluated once before the push (`elabStmtP`, `Syntax/Elab.lean`; `tests/solc/NarrowNested.sol`) |
| the narrow shape error names a capture (`mv1`) | elaborator | closed: a reference argument's shape is checked as written, before `hoistCallArgs` captures it (`Examples/Tactics/Checked.lean`) |
