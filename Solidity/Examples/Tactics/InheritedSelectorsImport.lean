import Solidity.Frontend.Import
import Solidity.Tools.Run

/-! ABI identity of inherited and renamed function values (lane CF1 backfill,
`docs/feature-work/abi-hashes.md`). The importer renames the inherited `h` to a
generated name (`solcFunction31`) and keeps overridden `f`/`g` under the
derived declaration; every selector and encoding below is still the source
declaration's, as pinned solc 0.8.38 computes it in legacy and via-IR with
the optimizer off and on (`scripts/abi-entry-probe.mjs` machinery; outcomes
in the doc). A `bytes4` returns as its compact `uint32`. Calling through an
external function value stays refused for inherited and own functions alike:
that is the function-value dispatch boundary, not an identity gap. -/
namespace Solidity.Examples.Tactics.InheritedSelectorsImport
solc_import "../../../tests/abi-0.8.38/InheritedSelectors.ast.json" hash 0x7c13e65704819ffd as Imported.Derived testing
def Source : Contract := _root_.Imported.Derived

-- Base.f.selector, this.f.selector (override), this.h.selector (inherited, renamed)
/-- info: ok
returns 3017696395 -/
#guard_msgs in #run Source.baseSelector()
/-- info: ok
returns 3017696395 -/
#guard_msgs in #run Source.derivedSelector()
/-- info: ok
returns 94394398 -/
#guard_msgs in #run Source.inheritedSelector()
-- abi.encodeCall of an override and of an inherited, renamed function: selector, length, argument byte
/-- info: ok
returns (2869465021, 36, 9) -/
#guard_msgs in #run Source.encodeOverrideHead()
/-- info: ok
returns (94394398, 36, 1) -/
#guard_msgs in #run Source.encodeInheritedHead()
-- external function values: their selector, and abi.encode of the value (address ++ selector)
/-- info: ok
returns 3017696395 -/
#guard_msgs in #run Source.valueSelector()
/-- info: ok
returns 94394398 -/
#guard_msgs in #run Source.inheritedValueSelector()
/-- info: ok
returns (94394398, 32) -/
#guard_msgs in #run Source.encodeValue()
-- inherited overloads (both renamed) and super
/-- info: ok
returns (3, true) -/
#guard_msgs in #run Source.overloadCalls()
/-- info: ok
returns 4 -/
#guard_msgs in #run Source.superCall()

-- Negative controls: calls through external function values keep their named
-- refusal, the same for the inherited `h` and the derived `f`.
/-- info: [("callValue",
    "InheritedSelectors.sol:47: solidity.functionDispatch: this call needs a finite set of typed dispatch targets"),
  ("callOwnValue",
    "InheritedSelectors.sol:51: solidity.functionDispatch: this call needs a finite set of typed dispatch targets")] -/
#guard_msgs in
#eval (Imported.Derived.report.filter (·.status != .elaborated)).map fun r => (r.name, r.reason)

end Solidity.Examples.Tactics.InheritedSelectorsImport
