import Solidity.Source.Eval

/-!
# Caller mode at the internal-call boundary

Guards propagation of a caller's unchecked flag across the actual Source
internal-call boundary. Arguments have already been evaluated here: their
caller-mode arithmetic is not changed by this law. It compares whole EM
computations, retaining every failure and poststate, not only normal returns.
Caller-mode independence alone does not establish which callee mode is selected.
This is a Source ingredient, not raw-output or model-call certification.
-/
namespace Solidity.Correctness.Lowering.Unchecked

/-- The actual internal call can canonicalize its caller's checkedness to
`true` after argument evaluation. The published Source interpreter enters
`runMods` with a checked frame; this law leaves its body, dispatch, arguments,
return slots, failure plan and calldata mode intact. No callee success or
no-panic premise is required. -/
theorem internalCall_checkedCaller {E : Source.Env}
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat) (d : Source.Decl)
    {ps : List Source.STy} (values : Source.Vals E.layout ps) (rs : List Source.STy)
    (plan : Source.FailureExecution.RuntimePlan) (calldataKnown : Bool) :
    Source.callInternal G F horizon d values rs (plan := plan) (calldataKnown := calldataKnown) =
      Source.callInternal G { F with checked := true } horizon d values rs
        (plan := plan) (calldataKnown := calldataKnown) := by
  cases horizon <;> rfl

#print axioms internalCall_checkedCaller

end Solidity.Correctness.Lowering.Unchecked
