# Inline assembly VY3: Yul compilation combinators

`Yul/Compilation/**`, from the vy3-compilation lane. Target-side combinators
over the existing backend stack model (`Backend/Scalar/Heights`,
`Backend/Control`, `Backend/Passes/Stack`); no Yul AST or VY1 semantics is
consumed, so this is not yet the P20 state relation.

- Stack slots and scopes (`Allocation`, `Slices`, `SlotSemantics`,
  `ScopeSemantics`, `NestedWrites`): slot allocation, arity slices, DUP/SWAP
  writes, push/pop of prefixes; general over locals, newer values and tails.
- Expression and statement lowering (`PureLowering`, `ArgumentLowering`,
  `ResultAssignment`, `ResultFrame`, `LocalScopeLowering`): `LoweredExpr n
  value` is indexed by an arbitrary Lean function; the relation is the stack
  layout `newer ++ locals ++ tail`.
- Opcode lowering (`OpcodeLowering`, `ClzLowering`, `ClzBounds`,
  `ByteLowering`): selection and CLZ/BYTE expansions with bounds.
- Control (`ControlLowering`, `MachineControl`, `Relocation`): branch and loop
  `Block` emission and relocation; `lowerBranch_slices` gives the runs of the
  parts, not of the whole block, and `lowerWhile` has no execution theorem.
- `MachineAdapter`: transport to `Evm.Machine` for stack-only code
  (`stackCode` covers PUSH/DUP/SWAP/POP only). `NumericMachine`,
  `WordMachine`, `SignedMachine`, `WordControl` are selectors without run
  theorems. `MemoryHarness`, `PhysicalCombination`: a byte-materialization
  harness and an unproved storage/transient suffix.
- `*Controls`: kernel controls.

Open: a Yul AST/semantics relation (P20), run theorems for arithmetic and
control code, whole-block execution.

## Expression, statement and machine slices (sched 2026-11-03)

Core `Yul/Compilation/` modules (each `*Machine`/`*Branch`/`*Placement` with a
`*Controls` module) over the original VY1 AST and evaluator; none adds an AST,
word semantics, state or calling convention.

- Expression compilers: `WordExpressions`, `QuotientExpressions` (unsigned
  DIV/MOD with zero divisors), `SignedExpressions`, `BitExpressions`,
  `ModularExpressions`, `PureExpressions`, `ProducerExpressions`,
  `RemainingWordBridges`, `OpenExpressions` (raw external cells through the VY1
  `WordAdapter`).
- Statements and control: `ProducerStatements`, `PureStatements`,
  `OpenStatements`, `ScopedStatements`, `ScopedRawStatements`, `NormalControl`,
  `NormalStackTransport`.
- Compiler-model execution: `ArithmeticMachine` (ADD/MUL), `ShiftSubMachine`,
  `BitMachineExecution`, `QuotientMachine`, `UnaryMachine`, `ComparisonMachine`;
  concrete branches `UnaryBranch`, `ComparisonBranch`.
- Physical memory: `PhysicalStore` (constant-operand stores on the VY2 byte
  view), `PhysicalHash` (Keccak over the canonical `withKeccak` field).

Bridge `SolidityBridge/Yul/`: `ChargedQuotients`, `ChargedQuotientPrefix`,
`QuotientPlacement`, `QuotientSuffix`, `SignedPlacement`, `BinaryPlacement`,
`SignextendPlacement` — compiler-origin sites with the charged P10 producers
at arbitrary encoded offsets.

Open: native/G24 closure, general branches, finite-code transport,
source-update pairing.

