import Solidity.Stipend.Rule

-- Full printed types for all explicitly named original declarations.
set_option pp.all true
#check @Solidity.Stipend.CostModel
#check @Solidity.Stipend.osakaCold
#check @Solidity.Stipend.addC
#check @Solidity.Stipend.maxC
#check @Solidity.Stipend.valCost
#check @Solidity.Stipend.argsCost
#check @Solidity.Stipend.revPartCost
#check @Solidity.Stipend.revListCost
#check @Solidity.Stipend.retOk
#check @Solidity.Stipend.stmtCost
#check @Solidity.Stipend.progCost
#check @Solidity.Stipend.Body
#check @Solidity.Stipend.fitsWith
#check @Solidity.Stipend.rule
#check @Solidity.Stipend.Enforced
#check @Solidity.Stipend.Obligation
#check @Solidity.Stipend.fits_iff
#check @Solidity.Stipend.not_fits_cons
#check @Solidity.Stipend.empty_fits
#check @Solidity.Stipend.requireValue
#check @Solidity.Stipend.requireValue_fits
#check @Solidity.Stipend.transfer_not_fits
#check @Solidity.Stipend.loop_not_fits
#check @Solidity.Stipend.assign_not_fits
#check @Solidity.Stipend.read_not_fits
#check @Solidity.Stipend.requires
#check @Solidity.Stipend.requires_cost
#check @Solidity.Stipend.requires_ten_fits
#check @Solidity.Stipend.requires_eleven_not_fits
#check @Solidity.Stipend.pow_not_fits

section
variable {C : Solidity.Contract} (b : Solidity.Stipend.Body C)
#synth Decidable ((Solidity.Stipend.rule C).fits b)
end
