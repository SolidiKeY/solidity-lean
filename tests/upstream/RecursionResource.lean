import Solidity.Tools.Upstream

/-!
Recursion boundary controls. The depth annotation is quotation metadata, not an
EVM stack counter. The abstract bottom frame remains inconclusive for replay.
These kernel equalities do not assert a machine stack-overflow theorem.
-/
namespace Solidity.Upstream.RecursionResource

variable {C : Contract} {Γ Γ' ps rs : Ctx}

/-- The abstract bottom is exhausted for every loop-fuel value and typed state. -/
theorem bottom_exhausted (fuel : Nat) (σ : State C Γ) :
    Prog.runF fuel Prog.recBase σ = .error .exhausted := rfl

/-- Exhaustion cannot be an explicit source revert. -/
theorem bottom_not_revert (fuel : Nat) (σ : State C Γ) :
    Prog.runF fuel Prog.recBase σ ≠ .error .revert := by
  rw [bottom_exhausted]
  intro h
  cases h

/-- The depth label itself cannot implement machine stack accounting. -/
theorem depth_annotation_irrelevant (f : Name) (d e : Nat)
    (args : Args C Γ ps) (ret : CallRet Γ rs Γ')
    (body : Unit → Prog C (rs ++ ps) (rs ++ ps)) (σ : State C Γ) :
    Stmt.run σ (.callRec f d args ret body) =
      Stmt.run σ (.callRec f e args ret body) := rfl

/-- Recursive calls use the same typed call implementation as ordinary calls. -/
theorem recursive_call_is_call (f : Name) (d : Nat)
    (args : Args C Γ ps) (ret : CallRet Γ rs Γ')
    (body : Unit → Prog C (rs ++ ps) (rs ++ ps)) (σ : State C Γ) :
    Stmt.run σ (.callRec f d args ret body) =
      Stmt.run σ (.call f args ret (body ())) := Stmt.run_callRec σ f d args ret body

/-- The existing boundary is unchanged. -/
example : recDepth = 1024 := rfl

#print axioms bottom_exhausted
#print axioms bottom_not_revert
#print axioms depth_annotation_irrelevant
#print axioms recursive_call_is_call
end Solidity.Upstream.RecursionResource
