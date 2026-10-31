import Solidity.Evm.Compile

/-! Reproductions against the published compiler, not replacement proofs for
reserved components. Refusals remain unchanged and are never admissions. -/
namespace Solidity.Backend.InternalFlow

variable {C : Contract} {Γ Δ ps rs : Ctx}

/-- Reference arguments cannot use the existing value-only inline compiler. -/
theorem storage_argument_refused (frame : Evm.Frag Γ) (args : Args C Γ ps)
    (R : RefTy) (name : Var) (path : SPath C Γ (.ref R)) :
    Evm.argsIn frame (.snocStorage args R name path) = false := rfl

/-- The existing core compiler refuses memory arguments as well. -/
theorem memory_argument_refused (frame : Evm.Frag Γ) (args : Args C Γ ps)
    (R : RefTy) (name : Var) (path : MPath C Γ (.ref R)) :
    Evm.argsIn frame (.snocMemory args R name path) = false := rfl

/-- Storage reference results require a new runtime frame target theorem. -/
theorem storage_result_refused (frame : Evm.Frag Γ) (R : RefTy) (name : Var) :
    Evm.CallRetIn frame (.storage R name) = none := rfl

/-- Every recursive call remains outside the existing core fragment. -/
theorem recursive_call_refused (frame : Evm.Frag Γ) (name : Name) (depth : Nat)
    (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (body : Unit → Prog C (rs ++ ps) (rs ++ ps)) :
    Evm.inFrag frame (.callRec name depth args ret body) = none := rfl

end Solidity.Backend.InternalFlow
