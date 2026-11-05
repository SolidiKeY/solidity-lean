import Solidity.Backend.Passes.MachineSar

namespace Solidity.Backend.Passes.MachineSar
/-- info: 'Solidity.Backend.Passes.MachineSar.sarCode_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sarCode_run
/-- info: 'Solidity.Backend.Passes.MachineSar.sarCode_simT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sarCode_simT
/-- info: 'Solidity.Backend.Passes.MachineSar.machine_agrees_intShr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms machine_agrees_intShr
/-- info: 'Solidity.Backend.Passes.MachineSar.raw_sar_differs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms raw_sar_differs
/-- info: 'Solidity.Backend.Passes.MachineSar.saturated_fill' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms saturated_fill

end Solidity.Backend.Passes.MachineSar
