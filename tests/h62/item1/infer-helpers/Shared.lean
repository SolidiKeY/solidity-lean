import Solidity.Source.InferHelpers

/-!
Guarded regression: the helper test namespace must import the production definitions
rather than introduce a second copy after the canonical extraction.
-/

#print axioms Solidity.H62.InferHelpers.Shared.isMapping_rule
#print axioms Solidity.H62.InferHelpers.Shared.payableArg_rule
#print axioms Solidity.H62.InferHelpers.Shared.convLoc_rule
