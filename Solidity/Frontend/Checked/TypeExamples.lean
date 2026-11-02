import Solidity.Frontend.Checked.TypeNameExamples
import Solidity.Frontend.Checked.TypeCorpusExamples
import Solidity.Frontend.Checked.TypeDeclarationExamples
import Solidity.Frontend.Checked.TypePrintExamples

/-!
# Type and declaration controls (G09)

Kernel-checked witnesses for the parse of type names and declarations:
trees (`rfl`), attribute orders as layouts, recursive declaration
references through S00's declaration graph, printing round trips, the
constructor coverage of the type and declaration constructors, and negative
controls.
-/

/-! Compatibility entry point; the controls are split only for bounded checking. -/


/-- info: 'Solidity.Frontend.Checked.parseType_derives' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.Checked.parseType_derives
/-- info: 'Solidity.Frontend.Checked.declCtors_covered' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Frontend.Checked.declCtors_covered
