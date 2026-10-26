import Solidity.Frontend.Import
import Solidity.Tools.Run
import Solidity.Calculus.Close
import Solidity.Calculus.Closers
import Solidity.Calculus.Surface

/-! Compiler-validated Solidity 0.8.38 input, including its ERC-7201 builtin.
The fixture is independent of the frozen SolKeY compiler pin. -/
namespace Solidity.Examples.Tactics.AbiFeaturesImport
solc_import "../../../tests/abi-0.8.38/Features.ast.json" hash 0x03800b34a8b6f3ac as Imported.ABIConformance testing
def Source : Contract := _root_.Imported.ABIConformance

/-- info: ok
returns 37439836327923360225337895871394760624280537466773280374265222508165906222592 -/
#guard_msgs in #run Source.constantRoot()
/-- info: ok
returns 89080316084849266924113458916420441381095493738250323500559816430735688691456 -/
#guard_msgs in #run Source.runtimeRoot("abc")
/-- info: ok
returns (36, 97, 98, 0) -/
#guard_msgs in #run Source.fixedLiteral()
/-- info: ok
returns true -/
#guard_msgs in #run Source.externalValue()
/-- info: ok
returns (78, 69, 207, 137, true) -/
#guard_msgs in #run Source.unicodeSelector()
/-- info: ok
returns (196, 64, 7) -/
#guard_msgs in #run Source.nestedPrefix()
/-- info: revert -/
#guard_msgs in #run Source.hugeNestedHead()
/-- info: ok
returns 0 -/
#guard_msgs in #run Source.unaligned()
/-- info: ok
returns 0 -/
#guard_msgs in #run Source.overlapping()
/-- info: panic (an `assert` failed) -/
#guard_msgs in #run Source.falseProperty()
/-- info: ok
returns 721457446580647751014191829380889690493307935711 -/
#guard_msgs in #run Source.recovery(0, 27,
  0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,
  0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798)
/-- info: ok
returns 30348469548119976384149824193117947667795829812057172845188107037932402691072 -/
#guard_msgs in #run Source.runtimeRoot("")
/-- info: ok
returns 57861545570621347113984716387450989072831671086294251435296248171547464265216 -/
#guard_msgs in #run Source.runtimeRoot("a b")
/-- info: ok
returns 58817168841818429821822861410436174112975048784383205212621391405482053771264 -/
#guard_msgs in #run Source.runtimeRoot("é")
open scoped Scoped
local instance : InContract := ⟨Source⟩

/-- The source compiler's constant declaration reaches the proved obligation. -/
theorem namespace_property : ⊨ᶠ spec!{trueProperty} := by
  sol_symex
  sol_decide

end Solidity.Examples.Tactics.AbiFeaturesImport
