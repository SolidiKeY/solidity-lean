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
