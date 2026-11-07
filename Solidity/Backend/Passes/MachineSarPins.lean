import Solidity.Backend.Passes.MachineSar

namespace Solidity.Backend.Passes.MachineSar
/-- info: 'Solidity.Evm.sarCode_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Evm.sarCode_run
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
/-- info: 'Solidity.Evm.sar_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Evm.sar_tail
/-- info: 'Solidity.Backend.Passes.MachineSar.shr_int_inFrag' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms shr_int_inFrag
/-- info: 'Solidity.Backend.Passes.MachineSar.evalT_shr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalT_shr

end Solidity.Backend.Passes.MachineSar
