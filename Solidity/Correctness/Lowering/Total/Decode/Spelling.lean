import Solidity.Correctness.Lowering.Total.Spells

/-! Compatibility import for versioned spelling. The single implementation
and its original-table specializations live in `Total.Spells`. -/
namespace Solidity.Correctness.Lowering.Total

/-- Original request spelling is definitionally the original-table instance. -/
theorem spellsT_tables1 {r : Request} {s : SourceProgram} :
    SpellsT Decode.tables1 r s ↔ Spells r s := Iff.rfl

end Solidity.Correctness.Lowering.Total
