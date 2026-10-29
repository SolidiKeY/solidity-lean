# G04 — compiler theorems and restrictions audit

Roadmap group G04 ([coverage-plan.md](../coverage-plan.md), wave 0): audit the
current compiler theorems and every fragment/input restriction, and assign each
restriction to the group that must discharge it. This is a read-only audit: no
Lean module, generated file or TestSuite file changed. It records what the base
revision proves. It does not claim that any final obligation is met.

- **Base revision:** `127c2ee59de16971e45b08a2def54f4e5fae8e2a` ("Refresh
  integration"). Every `file:line` below refers to that revision.
- **Method:** ranged reads of `Solidity/Evm/*.lean`, `Solidity/Theorems.lean`,
  `TrustAudit.lean`, `Bridge/SolidityBridge/{Evm,CompilerSimulation,ExternalEvm}.lean`
  and `Bridge/SolidityBridge/ExternalEvm/Obstructions.lean`; `git grep` for every
  cited declaration and for every constructor of the core leaf result
  (`StmtOut.refused`); the documents named in the assignment. No Lean server and
  no build were used, and no `#print axioms` was added: the axiom pins already
  present (`Solidity/Theorems.lean:350–357`,
  `Bridge/SolidityBridge/CompilerSimulation.lean:74–77`, `TrustAudit.lean:385–476`)
  are cited and were not re-run.
- **In-flight lanes:** the Codex lanes listed in [§5](#5-in-flight-lanes-to-re-check)
  edit `Solidity/Evm/`, the frontend and the semantics. Facts marked **⟳lane**
  are pinned to the base and must be re-checked after that lane merges.

## 1. Theorem inventory

Notation for the shared premises:

- **CoreIn** = `inFragP F P = some F'` (fragment certificate), `Sim C L b F σ m`
  (core state relation), `L + Prog.pushes P ≤ Lmax` (`Lmax = 2^64`).
- **MemIn** = `Memory.StateRepr L b frame F σ base m`,
  `b + Memory.frameNeedProg P ≤ frame`, and
  `Memory.AllocationInput b frame cost σ base m`.
- **4-way** = the outcome disjunction of `compile_correct`: (i) both succeed and
  `Sim` holds afterwards; (ii) source revert, or (`Prog.asserts P` and source
  panic), and machine revert; (iii) `Prog.pays P`, machine revert, source
  success; (iv) source `diverge`, and machine `fault` or (`pays` and revert).

| # | Declaration | Location | Statement | Premises beyond the notation |
|---|---|---|---|---|
| T1 | `Solidity.Evm.compile_correct` | `Solidity/Evm/Correct.lean:1089` | Core compiler, 4-way, final stack equals the initial stack. | CoreIn. |
| T2 | `Solidity.Evm.compile_exact` | `Solidity/Evm/Correct.lean:1115` | Exact 3-way agreement (success / revert or panic / diverge with fault). | CoreIn, `Prog.pays P = false`. |
| T3 | `Solidity.Evm.compile_box` | `Solidity/Evm/Correct.lean:1137` | Machine success implies source success with `Sim`. | CoreIn, machine `run … = .ok m' 0`. |
| T4 | `Solidity.Evm.compile_net` | `Solidity/Evm/Correct.lean:1157` | Machine success implies source success, and `net(a) = bal₀ a − bal a` for `a ≠ self`, `net(self) = 0`. | As T3. |
| T5 | `Solidity.Evm.Sim.init` | `Solidity/Evm/Correct.lean:1181` | Fresh typed state `freshT` and `Machine.init` satisfy `Sim C 1 0 (Frag.init [])`. | `balance < W`, `balance = bal self`. |
| T6 | `Solidity.Evm.compile_storage` | `Solidity/Evm/Correct.lean:1197` | From a fresh contract, 4-way with success reading as: every live `uint` storage path value equals the machine slot. | `inFragP (Frag.init []) P = some F'`, `Prog.pushes P < Lmax`, `balance < W`, `balance = bal self`. |
| T7 | `Solidity.Evm.Memory.ValFrag.correct` | `Solidity/Evm/MemoryCompile.lean:140` | Memory-path expression code: value agreement or both revert. | `ValFrag` certificate, `StateRepr`. |
| T8 | `Solidity.Evm.Memory.StmtFrag.correct` | `Solidity/Evm/MemoryCompile.lean:1221` | One memory-path statement: `GrowingResult` (success with extended base map and exact allocator growth, or both revert). | `StmtFrag` certificate, MemIn with `frameNeedStmt`. |
| T9 | `Solidity.Evm.Memory.ProgFrag.correct` | `Solidity/Evm/MemoryCompile.lean:1230` | As T8 for programs. | `ProgFrag` certificate, MemIn. |
| T10 | `Solidity.Evm.Memory.compile_correct` | `Solidity/Evm/MemoryCompile.lean:1245` | `compileProg b F P = some result` gives `GrowingResult` (success or revert only). | MemIn with `result.cert.cost σ`. |
| T11 | `Solidity.Evm.Compiler.Compilation.memory_input` | `Solidity/Evm/Compiler.lean:53` | Opens the memory input without reducing the compiler result. | `isMemory = true`. |
| T12 | `Solidity.Evm.Compiler.Compilation.correct` | `Solidity/Evm/Compiler.lean:86` | Unified entry: for either path, `Input → Agrees` (4-way with the path's `Rep`). | `Input`: CoreIn (core path) or MemIn (memory path). |
| T13 | `Solidity.Main.compiler_correct` | `Solidity/Theorems.lean:269` | Notation restatement of T1, without the stack clause. | CoreIn. |
| T14 | `Solidity.Main.compiler_net` | `Solidity/Theorems.lean:285` | Restatement of T4. | As T4. |
| T15 | `Solidity.Main.compiler_checked` | `Solidity/Theorems.lean:297` | Restatement of T12 (the "public" checked entry). | As T12. |
| T16 | `Solidity.Evm.compile_trace_sound` | `Bridge/SolidityBridge/Evm.lean:144` | A successful CSLib trace of compiled code has a source success with `Sim`. | CoreIn. |
| T17 | `Solidity.Evm.compile_trace_complete` | `Bridge/SolidityBridge/Evm.lean:153` | A source success has a successful trace. | CoreIn, `Prog.pays P = false`. |
| T18 | `Solidity.Evm.compile_terminates_iff` | `Bridge/SolidityBridge/Evm.lean:171` | Successful trace exists iff the source succeeds. | CoreIn, `pays = false`. |
| T19 | `Solidity.Evm.Compiler.bisimulation`, `.simulation`, `.trace_equivalence` | `Bridge/SolidityBridge/CompilerSimulation.lean:45,61,67` | Bisimulation and trace equivalence of the source and target LTSs over successful program boundaries only. | Each transition requires `inFragP`, the `Lmax` bound and `pays = false`; `Represents` is core `Sim` with fixed `b`. |
| T20 | `Solidity.Evm.External.simulation`, `.upstream_step` | `Bridge/SolidityBridge/ExternalEvm.lean:198,226` | Numeric stack opcodes (ADD…XOR) against EVMYulLean's word operations. | Arithmetic stack only. Storage, jumps, calls, memory and gas are excluded (module docstring, lines 6–15). |
| T21 | `Solidity.Evm.External.no_injective_slot_encoding`, `.slot_add_wrap_mismatch` (+ `call_/revert_/jump_/jumpi_/mload_/mstore_arity_mismatch`) | `Bridge/SolidityBridge/ExternalEvm/Obstructions.lean:15,65` (24–58) | Negative results: no injective `Slot → Fin W` exists, symbolic slot offsets do not wrap, and the macro instructions do not match the opcodes' arity. | — |

These are **fixed-program instances, not general theorems**:
`Solidity.Evm.Examples.{setAge,overflow,payOwner,callTwice}_interpreter`
(`Solidity/Evm/Interpreter.lean:35,65,88,116`), `Solidity.Evm.Examples.rejected`
(`Solidity/Evm/Examples.lean:354`) and `loop_push_rejected` (`:386`),
`selfBalance_out` (`:287`) and `transfer_refused` (`:268`), plus the memory
regression families listed in [compiler-verification.md](../compiler-verification.md#memory-operations).
`Solidity/Tools/DiffTest.lean` is random testing, not a theorem.

**Axioms.** T1, T12, T13–T15, T8–T10 and T19 are pinned to
`[propext, Classical.choice, Quot.sound]` by existing `#guard_msgs` or
`TrustAudit.lean`. Not re-run here.

**What no theorem states at the base.** There is no compilability or coverage
theorem: `Compiler.compile` returns `Option`, and `none` carries no statement.
There is no contract, dispatch, ABI, deployment or transaction-sequence
theorem, and no theorem connecting `Machine` to byte-encoded EVM code or to a
pinned EVM beyond T20's word operations. There is no memory-path counterpart of
T16–T19.

## 2. Restriction ledger

Kinds: **N** = a final-theorem narrowing that the roadmap forbids
(see "Final proof obligations" 3–5 and "Done when" in coverage-plan.md);
**O** = an intermediate organizer or representation premise that may remain
inside proofs; **S** = a stale weakening, meaning the stated theorem is weaker
than what the leaf lemmas prove; **P** = an environment, crypto or resource
premise whose exact form needs G01/G06 definition or user approval.

Examples marked ✓ are kernel-checked rejections at the base. Unmarked examples
were checked by reading the code against `inFrag`/`StmtFrag`, not by running
them.

### 2.1 Core/memory split and public shape

| ID | Restriction (where) | Excludes | In-profile example | Kind | Discharging group(s) |
|---|---|---|---|---|---|
| R01 | One compiler per whole program: `Compiler.compile` tries `inFragP`, then the memory compiler (`Solidity/Evm/Compiler.lean:21–25`). | Any program that needs both a core-only construct (loop, `assert`, call, `transfer`, `push`/`pop`, compound storage write) and a memory construct. | `uint[] memory xs = new uint[](2); owner.transfer(1);` or a memory array with a `for` loop. | N | G24 (unified entry), G49.01, G49.03. ⟳ memory-loops, memory-internal-calls |
| R02 | The core output relation is `Sim` only, and the memory relation is `StateRepr` + `GrowsAllocator` (`Compiler.lean:63–70`). A core prefix cannot feed a memory suffix. | Sequential composition across paths. | Same as R01. | O, and N while R01 holds | G24 |
| R03 | Rejection is `none` with no theorem (`Compiler.lean:21`). | Nothing provably: coverage is unstated. | Every rejected program in R05–R33. | N | G49.03 (coverage and non-vacuity), G48 |
| R04 | The theorems are about `Prog C Γ Γ'` from an arbitrary represented state, with no contract, dispatch, ABI, constructor or transaction. | Whole contracts, deployment, transaction sequences. | Any contract with an external function. | N | G40, G41, G44, G49.02, G50 |
| R05 | The target is the word-level `Machine` with macro `Instr`s, not EVM bytes (T20/T21; `Solidity/Evm/Machine.lean:1–66`). | Any bytecode-level claim. | — (target property) | N | G45, G46, G47, G49.02. ⟳ evm-control-flow, evm-byte-memory, evm-storage-slots |

### 2.2 Core fragment (`inFrag`, `Solidity/Evm/Compile.lean:274–326`)

| ID | Restriction (where) | Excludes | In-profile example | Kind | Discharging group(s) |
|---|---|---|---|---|---|
| R06 | `send` out (`.send => none`, `:313`), although `Stmt.pays` counts it (`:254`). | `send` and value calls. | `bool ok = payable(a).send(1);`; `(bool ok, ) = a.call{value: v}("");` | N | G43, G42.02 |
| R07 | `tryCall`, `revertData`, `catchData` out (`:315`; `inFrag_tryCall`, `Correct.lean:945`). | External calls, try/catch, revert with data. | `try this.f() {} catch {}`; `revert E(1);` | N | G42, G38, G21, G41. ⟳ diamond-try, revert-outcome-specs, readonly-external |
| R08 | `callRec` out (`:319`). At the source level, recursion is unrolled to `recDepth = 1024` with an `exhausted` bottom (`Solidity/Syntax/Scoped.lean:469`; [solc-alignment.md](../solc-alignment.md#where-the-interpreter-follows-solc-not-key), "Recursion depth"). | Recursive internal calls. The source depth bound is a fixed-fuel semantics. | `function fact(uint n) internal returns (uint) { return n == 0 ? 1 : n * fact(n - 1); }` | N (compiler) and N (source fuel) | G37.02, S03.03 (no fixed inlining or fuel), S03.04 |
| R09 | Internal calls are compiled inline (`Stmt.call` carries its body). Value arguments only (`argsIn`, `:146–149`). Return shape `.none`/`.val` only (`CallRetIn`, `:153–159`). `callReceiver(Push)` out (`:316–317`). | Storage/memory reference arguments, tuple/reference returns, receiver-style library calls, runtime call frames. | `function g(uint[] storage a) internal {…} g(arr);`; `function h() internal returns (uint, uint)` | N | G37.01, G37.03, G20. ⟳ memory-internal-calls, function-ref-args |
| R10 | `valIn` refuses `readMem`, `mlen`, `modular`, `hash` (`:127`). | Memory reads on the core path, `addmod`/`mulmod`, `keccak256`/`sha256`/`ripemd160` values. | `x = addmod(a, b, m);`; `h = uint(keccak256(abi.encode(a)));` | N | G25 (modular), G31 + G46.05 (hashes), G23 |
| R11 | `simpleIn` refuses the `selfBalance` environment read (`:104–106`). | `address(this).balance`. | ✓ `total = address(this).balance;` (`selfBalance_out`) | N | G31, G46.04 |
| R12 | Operator tables `binInFrag`/`unInFrag` (`Solidity/Evm/Layout.lean:410,422`): bitwise and shift operators, `**` and the wrapping (`unchecked`) operators only at `uint`. | Signed bitwise/shift operators, signed `**`, `unchecked` signed arithmetic. | `int c = a & b;`, `int d = a >> 1;`, `unchecked { int e = a + b; }` | N | G25 |
| R13 | `PrimTy` is only `bool`/`uint`/`int` (`Solidity/AST.lean:30–45`). Narrow widths, `address`, enums and `bytesN` reach the compiler as `uint` after elaboration. `bytesN` is right-aligned, unlike solc ([semantic-gaps.md](../semantic-gaps.md#bytes-and-strings)). | Nothing at the compiler interface. Width and representation correctness rests on lowering. | `uint8 x = 200; x += 100;` is correct only via the elaborated guard. | O (representation), checked by lowering | G16, G25, G27.01 |
| R14 | Mapping keys `uint` only (`locIn`, `:116`; `ReprAt.map` relates only `K = .uint`, `Solidity/Evm/Repr.lean:85`). | `bool`/`int`/`string`/`bytes` keys (the last are hashed). | `mapping(bool => uint) m; m[true] = 1;`; `mapping(string => uint)` | N | G27.02 |
| R15 | Layout size side conditions: `leavesFit` (`:101`), field `offset < W` (`:115`), fixed `n < W` (`:118–119`). | Storage types with more than `2^256` slots. | None found. solc refuses storage types that are too large; that claim is unverified here, so G13/G18.01 must prove admission implies these. | O | G27.05, G18.01 |
| R16 | Unset storage aliases are `dead` (`declStorageIn`, `:220`) and unreadable until rebound. | Reads of an uninitialized storage pointer. | None expected: solc rejects such reads at compile time (claim not verified here). | O | G28 (confirm via G13 admission) |

### 2.3 Copies

| ID | Restriction (where) | Excludes | In-profile example | Kind | Discharging group(s) |
|---|---|---|---|---|---|
| R17 | Storage-to-storage `=` only for `static` types (`assignIn`, `Compile.lean:211–216`; `static`, `Layout.lean:440`). | Copies of a value that holds a dynamic array, `bytes` or `string`. These need a runtime-length loop. | ✓ `basketA = basketB;` (`rejected`); `names = otherNames;` (`string[]`) | N | G29.01–G29.03 |
| R18 | `push` shapes (`pushIn`, `:167–174`): `push()` only of a primitive, and `push(sp)` only of a static element. | `push()` of a struct or array, which revives the popped slot (`pushSlot`); pushes of dynamic or memory values. | ✓ `persons.push();` (`rejected`); `rows.push(memRow);` | N | G30, G35.02, G27.03 |
| R19 | `copyMem`, `fixedCopy`, `fixedCopyMem` sources out of the core path (`:216`, `:174`). | Memory-to-storage and fixed-array copies. | `stored = memRecord;`; `fixedArr = otherFixed;` with memory/fixed sources | N | G35.02, G35.04. ⟳ memory-storage-copy |
| R20 | Memory path copies: only primitive-member storage-root struct → memory (`StmtFrag.copyStruct`/`rebindCopyStruct`, `MemoryCompile.lean:203,211`; M31 in [assurance.md](../assurance.md)). | Storage arrays → memory, memory → storage, deep memory → memory, calldata → memory, runtime-length objects. | `uint[] memory c = storedArr;`; `Record memory r = stored.nested;` | N | G35.01–G35.06, G18.05. ⟳ memory-storage-copy, abi-lazy-calldata |

### 2.4 Loops and control flow

| ID | Restriction (where) | Excludes | In-profile example | Kind | Discharging group(s) |
|---|---|---|---|---|---|
| R21 | A core loop body must not push, pay or shrink, and must leave the fragment flags unchanged (`Compile.lean:307–312`). `Prog.pushes` counts a loop as `0` (`:243`). | Loops that grow, pay, pop/delete, or rebind aliases. | ✓ `while (age < 3) { values.push(1); age = age + 1; }` (`loop_push_rejected`); `for (…) { a.transfer(1); }`; `for (…) arr.pop();` | N | G36.02, G36.03 (after G43), G19. ⟳ memory-loops |
| R22 | No loops on the memory path (`StmtFrag` has no loop constructor, `MemoryCompile.lean:162–360`). | Any loop in a memory program. | `for (uint i; i < xs.length; i++) xs[i] = i;` with `xs` in memory | N | G36.02, G24. ⟳ memory-loops |
| R23 | Structured `LOOP` and relative forward jumps. `checked_exp_helper` is unrolled 255 times (`Machine.lean:34–43`; `expLoop`, `Layout.lean:480`). | Absolute-jump bytecode. | — (target property) | O now, N for the final target | G45.03. ⟳ evm-control-flow |

### 2.5 Capacities and resources

| ID | Restriction (where) | Excludes | In-profile example | Kind | Discharging group(s) |
|---|---|---|---|---|---|
| R24 | `L + Prog.pushes P ≤ Lmax` (`2^64`), with `Sim.bound` and every array length `≤ L` (`Sim.lean:213`; `Machine.lean:93`). The typed run caps lengths at `2^256` (`Storage.full`, `Solidity/Semantics/Storage/Ops.lean:916`) and has no `Panic(0x41)` at `2^64` ([solc-alignment.md](../solc-alignment.md#remaining-deltas-documented-intentionally-out-of-scope)). | States with an array near `2^64`; with R21, pushes inside loops. | A storage array of length `2^64` followed by `push`: the run succeeds where solc panics. | N (initial-state premise that hides a source/solc mismatch) | S04.01 / S02 (source length bound and `0x41`), G30, G38 |
| R25 | Memory capacity is a premise (`AllocationInput`, `MemoryGrowResult.lean:36`: `cost = 0 ∨ (0 < b ∧ ∃ cursor, … ∧ cursor + cost < W)`). The generated code has no capacity check. | Allocations whose reached cost exceeds the word space. solc panics instead. | `uint[] memory x = new uint[](2**255);`: the typed run allocates, no input satisfies the premise, and the theorem says nothing. | N | G33, G38 (`0x41`). ⟳ evm-byte-memory |
| R26 | Frame: `b + frameNeedProg P ≤ frame` (peak context, `MemoryCompile.lean:51`), `0 < b` when allocating, and locals held in memory cells by level (`Compile.lean:44–55`). | Nothing at the source, as long as a frame exists. | — | O | G32, G37.01, G45.02 |
| R27 | Idealized machine: no gas, no stack limit, memory `Nat → Word`, addresses as 256-bit words not truncated to 160 bits, and `CALL` takes only address and value (`Machine.lean:56–66,323–344`). | Resource-indexed behaviour and the 160-bit address domain. | Recursion or loops that exhaust gas on chain. | P (resource abstraction) | G01/G06 (definition), G46.04, G46.06, G47 |

### 2.6 Memory-path admission (`StmtFrag`, `MemoryCompile.lean:162–360`)

| ID | Restriction (where) | Excludes | In-profile example | Kind | Discharging group(s) |
|---|---|---|---|---|---|
| R28 | Primitive-element arrays and primitive- or reference-member structs only. No reference-element arrays, no construction or defaults of reference-member structs, no fixed memory arrays ([compiler-verification.md](../compiler-verification.md#memory-operations), "Out of the memory path"). | Nested memory aggregates. | `uint[][] memory m = new uint[][](2);`; `Wrapper memory w = Wrapper(inner);`; `uint[3] memory f;` | N | G18.03, G33, G34. ⟳ memory-reference-arrays, memory-reference-structs |
| R29 | The only storage statement is a primitive `storageWrite` (`:347`). No `assert`, call, payment, `push`/`pop`/`delete` of storage, or compound storage update in a memory program. | Mixed storage/memory programs. | `uint[] memory xs = new uint[](1); total += xs[0];` | N | G24, G28, G37, G38, G43. ⟳ memory-internal-calls |
| R30 | `HeapRepr` relates only primitive-element arrays (`MemoryHeap.lean:16–23`). `PointerRepr` requires every memory local to be initialized (`MemorySource.lean:20`). | Initial states holding other heap objects or unset pointers. | — (input premise) | O | G32 |
| R31 | Word-addressed memory, one word per member, headerless structs (`StructRepr`, [compiler-verification.md](../compiler-verification.md#memory-operations), "The representation"). | Byte-addressed EVM memory. | — | O now, N for the final target | G32, G46.02. ⟳ evm-byte-memory |

### 2.7 Payments

| ID | Restriction (where) | Excludes | In-profile example | Kind | Discharging group(s) |
|---|---|---|---|---|---|
| R32 | **Payment asymmetry.** Disjunct (iii) of T1/T6/T12/T13 (`Prog.pays P = true ∧ machine revert ∧ source ok`), and the `pays ∧ revert` alternative in (iv). The Bridge results T17–T19 require `pays = false`. **Finding:** at the base, the only leaf for payments, `transfer_sim` (`Solidity/Evm/Stmt.lean:892`), returns `.inl` or `.inr` only. Exact agreement on refusal comes from `Sim.funds`/`Sim.oracle` (`Sim.lean:223–228`; fields `funds` and `oracle`). `StmtOut.refused` (`Stmt.lean:107`) is only propagated (`Correct.lean:79,95,111,168,504,583,922,933,937`), never constructed. The disjunct therefore appears unreachable. That is not proved here. | As stated, the theorem lets a compiler revert every paying program. | Any `owner.transfer(1);`: the theorem allows the machine to revert where the source succeeds. | S + N | G43 (discharge the asymmetry). G36.03 then relies on it. ⟳ diamond-payments |
| R33 | Recipient code is not run. Acceptance is the oracle `Machine.accepts` (`Machine.lean:336`), tied to the source `tx.ext` `sendKey` table by `Sim.oracle`. The world is balances only. | Reentrant or state-changing recipients, stipend gas. | A `transfer` to a contract whose `receive()` writes storage. | P | G22.02, G42.03, G43, G47 |

### 2.8 Hashes and storage representation

| ID | Restriction (where) | Excludes | In-profile example | Kind | Discharging group(s) |
|---|---|---|---|---|---|
| R34 | Storage slots are symbolic terms (`Slot.root/hash/data`, `Machine.lean:99`). Distinct terms never collide, and offsets do not wrap (`Slot.add`, `:106`). That is global keccak injectivity built into the type, which the roadmap forbids. T21 proves that no injective numeric encoding exists. | Collisions and wrap-around; any numeric storage claim. | Every mapping or dynamic-array access is related only symbolically. | N (premise in disguise) | G27.05, G46.03, G46.05. ⟳ evm-storage-slots |
| R35 | `KECCAK256` takes its inputs from the stack (`keccakMap`/`keccakArr`, `Machine.lean:45–46`), not from memory. | Byte-level hashing of memory. | — | O now, N for the final target | G46.02, G46.05 |

### 2.9 Alias liveness

| ID | Restriction (where) | Excludes | In-profile example | Kind | Discharging group(s) |
|---|---|---|---|---|---|
| R36 | An alias bound through an array index is `fragile` (`bindFl`, `Compile.lean:161`). It is forgotten at every `pop`/`delete` (`Frag.dropFragile`, `:87`), including in branches (`meet`) and callee bodies (`Stmt.shrinks`). Later use is rejected. `ReprAt` relates live elements only. | Use of a storage alias after a shrink: dangling, compiler-specific behaviour ([solc-alignment.md](../solc-alignment.md#arrays-past-their-end)). | ✓ `Person storage p = persons[0]; persons.pop(); p.age = 1;` and the branch variant (`rejected`) | N, or a scope decision (Q2) | G28, G30, G27.03 |

### 2.10 Failures, observations, divergence

| ID | Restriction (where) | Excludes | In-profile example | Kind | Discharging group(s) |
|---|---|---|---|---|---|
| R37 | Revert data is erased. `Out.revert` carries no bytes, and a failed `assert` (source `panic`) matches a plain machine revert. Every other source failure is `.revert` ([solc-alignment.md](../solc-alignment.md#remaining-deltas-documented-intentionally-out-of-scope), "Error classification"). | Panic codes, `Error(string)`, custom-error payloads. | `require(x > 0, "neg");` reason bytes; `revert E(1);` | N (observation loss) | G38, G21, G41. ⟳ revert-outcome-specs |
| R38 | Divergence is matched classically. Source `diverge` corresponds to machine `.fault` through `loopRun`'s `Classical.choose` (`Machine.lean:435`). `.fault` also covers stack underflow and malformed code (`Instr.step`, `:476ff`). There is no finite-prefix, resource-indexed statement. | A faithful finite-prefix/divergence correspondence. | `while (true) {}`: the theorem gives a machine "fault", not a gas-bounded prefix family. | N | G01 (definition), G36.03, G47, G49.03 |
| R39 | Source `exhausted` (a push at `2^256`, the recursion bottom, `assumeFalse`) never appears in the theorem. It is excluded through R08/R24 and `assumeFalse ⇒ none` (`Compile.lean:298`). | Programs that reach the source resource bound. | Recursion deeper than 1024 frames (see R08). | O while R08/R24 hold | S03.04, G01/G06 resource abstraction |
| R40 | The Bridge LTS (T19) relates successful boundaries only (module docstring, `CompilerSimulation.lean:4–10`). | Halting and diverging traces in the CSLib bisimulation. | Any reverting program. | N for a final trace theorem | G49.03, G50.02 |
| R41 | Observation at success is `Sim`: storage representation, locals, balances, ledger and four environment words (`EnvSim`, `SimLemmas.lean:610`). There are no return values or returndata. | Function results as observations. | `function f() external returns (uint)`, whose result has no theorem | N | G41, G49.02 |

## 3. Ownership gaps

Every restriction above maps to at least one G/S row. These items are owned
only **implicitly**: the owning row's text does not name the specific defect.
G03 should record them explicitly.

1. **Payment disjunct as a stale weakening (R32).** G43 owns the asymmetry, but
   nobody owns re-stating T1/T12/T13/T15 now, before G43. A statement-only
   strengthening of the existing results may be possible, and no group is
   assigned that interim strengthening.
2. **Machine `fault` conflates divergence with malformed code (R38).** This is
   implied by G49.03 ("matching progress/traces") and G47, but no row names it.
3. **Source fixed depth `recDepth = 1024` (R08).** This is source semantics, not
   compiler. S03.03 forbids "fixed inlining/fuel limits", and G37.02 forbids
   depth admission limits, but neither names the existing `recUnroll` encoding.
4. **The source has no `2^64` length bound or `Panic(0x41)` (R24).** S04.01
   and S02 own state and value semantics, and G30/G38 own the compiled check. No
   row names this solc divergence, which is the reason for the `Lmax` premise.
5. **Stale public documentation** (see [§4](#4-other-findings-at-the-base)). Only
   G55 ("public claims") covers it.

No restriction was found with no plausible owner at all.

## 4. Other findings at the base

These are facts found during the audit. None is fixed here, because this group
edits no Lean and the documents are owned elsewhere.

- [compiler-verification.md](../compiler-verification.md#what-is-proved):
  - Its `compile_storage` block omits the divergence disjunct (iv) that the
    code has (`Correct.lean:1211–1213`).
  - It writes `bal : Nat → Nat`, `self : Nat`, `hs : self < W` and, in
    `compile_net`, `∀ a : Nat, a < W`. The code uses `Fin W` and adds
    `hbalance : balance = bal self`.
  - It describes the payment disjunct as reachable ("the world refuses a
    payment, and the machine alone reverts").
- `Solidity/Evm/Compile.lean:24–25` (module docstring) still says the fragment
  has "no `send`/`try`/loop". Loops are admitted at `:307`.
- These still say that a refused payment "reverts the machine alone":
  - [solc-alignment.md](../solc-alignment.md#where-the-interpreter-follows-solc-not-key), `transfer` row;
  - `Solidity/Calculus/Rules.lean:1061`;
  - `Solidity/Examples/Tactics/Payment.lean:16`.

  This contradicts [solc-alignment.md](../solc-alignment.md#transfer) ("agree on
  both success and refusal") and `transfer_sim`.
- [assurance.md](../assurance.md) gives the memory capacity as
  `cursor + size + 1 < 2^256`. The definition (`AllocationInput`,
  `MemoryGrowResult.lean:36`) states `cursor.val + cost < W` over the
  accumulated cost.
- `Stmt.pays` counts `callRec` as paying (`Compile.lean:260`). That is harmless
  while `callRec` is out of the fragment, but it must be revisited by G37.02.

## 5. In-flight lanes to re-check

Facts here are pinned to `127c2ee`. Re-audit them after the lane merges.

| Codex lane | Restrictions likely changed |
|---|---|
| memory-loops | R01, R21, R22 (and possibly R24 if memory pushes are added) |
| memory-storage-copy | R19, R20, R29 |
| memory-reference-arrays | R28, R30 |
| memory-reference-structs | R28, R30 |
| memory-internal-calls | R01, R09, R29 |
| function-ref-args | R09 |
| readonly-external | R07 |
| evm-byte-memory | R05, R25, R31, R35 |
| evm-storage-slots | R05, R34 (and T21) |
| evm-control-flow | R05, R23, R38 |
| revert-outcome-specs | R07, R37 |
| diamond-try | R07 (calculus side; compiler status unchanged unless `inFrag` changes) |
| diamond-payments | R32, R33 (calculus side; check `LeanTaclet.transferDiamond` and the T1 disjunct) |
| abi-lazy-calldata | R20 (calldata copies), R04 (ABI) |

## 6. Open scope questions

These do not block this audit. They need a user decision; evidence is given.

- **Q1 — Hash/slot premise.** R34 is a global injectivity assumption, and the
  roadmap rejects it. Collision freedom for symbolic storage slots
  (`Machine.lean:30–34`) is unprovable as a global fact
  (`no_injective_slot_encoding`). Which exact cryptographic premise, if any, is
  approved for G27.05/G46.05: for example, collision freedom restricted to the
  slots reached by a finite execution, stated as an explicit hypothesis?
- **Q2 — Dangling storage aliases (R36).** solc-alignment classifies writes
  through an alias to a popped element as "compiler-specific/undefined".
  G28 compiles them "under the selected source semantics". Are such programs in
  profile with solc's slot behaviour, or should G00 record an exclusion? Until
  decided, R36 is a narrowing.
- **Q3 — Payment acceptance oracle (R33).** An oracle over recipients is
  existing behaviour. The roadmap (G47) replaces it with actual execution
  "where typed code is in scope". The exact quantification over untyped
  recipients must be stated as an approved environment premise.

## 7. Handoff

- **Base/patch:** base `127c2ee`. The patch adds this file, one line in
  `docs/coverage-plan.md` and one line in `docs/README.md`.
- **Checked:** the theorem statements (T1–T21) read from source; each `inFrag`
  arm, `StmtFrag` constructor, `Sim`/`StateRepr` field and machine
  simplification read; cited declarations confirmed with `git grep` at the
  head; `StmtOut.refused` construction sites enumerated.
- **Not checked:** no Lean elaboration, no axiom re-run, no build. The R32
  unreachability is an observation, not a theorem.
- **Remaining child obligations:**
  - every R-row's discharging group;
  - the five implicit ownerships in §3 for G03;
  - the stale-document fixes in §4;
  - Q1–Q3 for the user/G00;
  - lane re-checks in §5.
- **Elapsed:** about 1.5 h of agent time on a 4-core VM; no Lean process run.

## Review

Separate read-only finder and skeptic reviews (subagents, no Lean server) of
this document. Results and fixes are recorded below.
