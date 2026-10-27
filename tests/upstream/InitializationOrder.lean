import Solidity.Tools.Upstream

/-! Pipeline-specific source construction schedules, pinned to solc 0.8.38.
Concrete deployment theorems are checked by the kernel. They are controls for
lowering, not a universal source/compiler equivalence theorem. -/
namespace InitializationOrder
open Solidity Solidity.Semantics Solidity.Frontend Solidity.Tools.Upstream Lean

solc_import "InitializationOrder.ast.json" hash 0x6ad0eccb73e4d898
  as Legacy.ArgumentOrder testing entrypoints
solc_import "InitializationOrderIR.ast.json" hash 0x96fed26695f0ddbb
  as IR.ArgumentOrder testing entrypoints
solc_import "InitializationOrder.ast.json" hash 0x6ad0eccb73e4d898
  as Legacy.StageLeaf testing entrypoints
solc_import "InitializationOrderIR.ast.json" hash 0x96fed26695f0ddbb
  as IR.StageLeaf testing entrypoints

private def argumentLegacyStorage : Storage Legacy.ArgumentOrder :=
  .cons (.prim ⟨4, rfl⟩) .nil
private def argumentIRStorage : Storage IR.ArgumentOrder :=
  .cons (.prim ⟨2, rfl⟩) .nil

/-- Legacy initializes x before evaluating the effectful base argument. -/
theorem argument_legacy :
    (Contract.deployT Legacy.ArgumentOrder
      sol[Legacy.ArgumentOrder]{ constructor(); } {}).toOption.map
        (·.storage.beq argumentLegacyStorage) = some true := by
  decide +kernel

/-- IR evaluates the argument first; the base initializer overwrites its write. -/
theorem argument_ir :
    (Contract.deployT IR.ArgumentOrder
      sol[IR.ArgumentOrder]{ constructor(); } {}).toOption.map
        (·.storage.beq argumentIRStorage) = some true := by
  decide +kernel

/-- The legacy observation is false in IR; pipeline selection is observable. -/
theorem argument_ir_refutes_legacy :
    (Contract.deployT IR.ArgumentOrder
      sol[IR.ArgumentOrder]{ constructor(); } {}).toOption.map
        (·.storage.beq (.cons (.prim ⟨4, rfl⟩) .nil)) = some false := by
  decide +kernel

-- a, b, c, middle, d, e, snapshot, last, in source declaration order.
private def stageLegacyStorage : Storage Legacy.StageLeaf :=
  .cons (.prim ⟨17, rfl⟩) (.cons (.prim ⟨42, rfl⟩) (.cons (.prim ⟨131, rfl⟩)
    (.cons (.prim ⟨23, rfl⟩) (.cons (.prim ⟨23, rfl⟩) (.cons (.prim ⟨0, rfl⟩)
      (.cons (.prim ⟨126, rfl⟩) (.cons (.prim ⟨127, rfl⟩) .nil)))))))
private def stageIRStorage : Storage IR.StageLeaf :=
  .cons (.prim ⟨17, rfl⟩) (.cons (.prim ⟨42, rfl⟩) (.cons (.prim ⟨56, rfl⟩)
    (.cons (.prim ⟨23, rfl⟩) (.cons (.prim ⟨23, rfl⟩) (.cons (.prim ⟨42, rfl⟩)
      (.cons (.prim ⟨51, rfl⟩) (.cons (.prim ⟨57, rfl⟩) .nil)))))))

/-- Legacy runs all field initializers before any base constructor body. -/
theorem stages_legacy :
    (Contract.deployT Legacy.StageLeaf
      sol[Legacy.StageLeaf]{ constructor(); } {}).toOption.map
        (·.storage.beq stageLegacyStorage) = some true := by
  decide +kernel

/-- IR interleaves each owner's initializers/body, including implicit owners. -/
theorem stages_ir :
    (Contract.deployT IR.StageLeaf
      sol[IR.StageLeaf]{ constructor(); } {}).toOption.map
        (·.storage.beq stageIRStorage) = some true := by
  decide +kernel

solc_import "InitializationOrder.ast.json" hash 0x6ad0eccb73e4d898
  as Legacy.ReturnLeaf testing entrypoints
solc_import "InitializationOrderIR.ast.json" hash 0x96fed26695f0ddbb
  as IR.ReturnLeaf testing entrypoints
solc_import "InitializationOrder.ast.json" hash 0x6ad0eccb73e4d898
  as Legacy.NarrowLeaf testing entrypoints
solc_import "InitializationOrderIR.ast.json" hash 0x96fed26695f0ddbb
  as IR.NarrowLeaf testing entrypoints
solc_import "InitializationOrder.ast.json" hash 0x6ad0eccb73e4d898
  as Legacy.FailingLeaf testing entrypoints
solc_import "InitializationOrderIR.ast.json" hash 0x96fed26695f0ddbb
  as IR.FailingLeaf testing entrypoints

/-- Legacy initializes the derived field before the base modifier/body returns. -/
theorem modifier_return_legacy :
    (Contract.deployT Legacy.ReturnLeaf
      sol[Legacy.ReturnLeaf]{ constructor(); } {}).toOption.map
        (·.storage.beq (.cons (.prim ⟨113, rfl⟩) (.cons (.prim ⟨2, rfl⟩) .nil))) = some true := by
  decide +kernel

/-- IR initializes the derived field after the helper's return and modifier suffix. -/
theorem modifier_return_ir :
    (Contract.deployT IR.ReturnLeaf
      sol[IR.ReturnLeaf]{ constructor(); } {}).toOption.map
        (·.storage.beq (.cons (.prim ⟨113, rfl⟩) (.cons (.prim ⟨113, rfl⟩) .nil))) = some true := by
  decide +kernel

/-- The existing narrow-assignment guard rejects legacy overflow before the base body.
This model guard is an empty revert; it does not certify the EVM Panic(0x11) payload. -/
theorem narrow_legacy_guard_reverts :
    Contract.deployT Legacy.NarrowLeaf
      sol[Legacy.NarrowLeaf]{ constructor(); } {} = .error .revert := by
  rfl

/-- IR uses the reset uint8 value and retains its checked assignment widths. -/
theorem narrow_ir :
    (Contract.deployT IR.NarrowLeaf
      sol[IR.NarrowLeaf]{ constructor(); } {}).toOption.map
        (·.storage.beq (.cons (.prim ⟨1, rfl⟩) (.cons (.prim ⟨2, rfl⟩) .nil))) = some true := by
  decide +kernel

/-- Legacy reaches the derived initializer's panic before the base body. -/
theorem failure_legacy :
    Contract.deployT Legacy.FailingLeaf
      sol[Legacy.FailingLeaf]{ constructor(); } {} = .error .panic := by
  rfl

/-- Failed base construction in IR stops later initializers; no state is committed. -/
theorem failure_ir :
    Contract.deployT IR.FailingLeaf
      sol[IR.FailingLeaf]{ constructor(); } {} = .error .revert := by
  rfl

private def check (C : Contract) (rows : List ImportRow) (signature value status : String) : IO Unit := do
  let data := Json.mkObj [("vectors", toJson [Json.mkObj [
    ("signature", toJson signature), ("args", toJson ([] : List String)),
    ("failure", toJson false), ("expected", toJson [value])]])]
  let actual := replay C rows data
  unless (actual.getObjValAs? String "status").toOption == some status do
    throw (IO.userError actual.pretty)

-- Getter observations independently pin both schedules and refusal of swapped expectations.
#eval check Legacy.StageLeaf Legacy.StageLeaf.report "snapshot()" "126" "working"
#eval check IR.StageLeaf IR.StageLeaf.report "snapshot()" "51" "working"
#eval check IR.StageLeaf IR.StageLeaf.report "snapshot()" "126" "broken"
#eval check Legacy.StageLeaf Legacy.StageLeaf.report "snapshot()" "51" "broken"

#print axioms argument_legacy
#print axioms argument_ir
#print axioms argument_ir_refutes_legacy
#print axioms stages_legacy
#print axioms stages_ir
#print axioms modifier_return_legacy
#print axioms modifier_return_ir
#print axioms narrow_legacy_guard_reverts
#print axioms narrow_ir
#print axioms failure_legacy
#print axioms failure_ir
end InitializationOrder
