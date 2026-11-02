import Solidity.Calculus.CallFunctionTable
import Solidity.Calculus.TermSize

/-! # Intrinsic partial-call composition graph
The oldNet locals are typed finite function tables. Both input and returned
argument are universally quantified at fresh intrinsic UInt positions.
This is a definition clause, not yet a source-call expansion rule.
-/
namespace Solidity.CallFunctionGraph
open CallFunctionTable
variable {C : Contract} {Γ : Ctx}

/-- KeY integer equality uses the existing Boolean comparison symbol. -/
def equalZ (a b : Tm C Γ .kint) : Fml C Γ :=
  .eq (.app2 (.zcmp .eqB rfl) a b) (.app0 (.lit true))

/-- The second lookup is read at the first returning argument; a first failure
is propagated separately. All positions refer to the original context. -/
def compose (inputName resultName : Var) (first second next : Idx Γ .oldNet) : Fml C Γ :=
  .all inputName .uint
    (.and
      (.imp
        (equalZ (.netOf first.there (.pvV .here)) (.app0 (.zlit (-1))))
        (equalZ (.netOf next.there (.pvV .here)) (.app0 (.zlit (-1)))))
      (.all resultName .uint
        (.imp
          (equalZ (.netOf first.there.there (.pvV (.there .here)))
            (.app1 .toInt (.pvV .here)))
          (equalZ (.netOf next.there.there (.pvV (.there .here)))
            (.netOf second.there.there (.pvV .here))))))

/-- The actual intrinsic clause has the exact pointwise sequential semantics. -/
theorem holds_compose (inputName resultName : Var) (first second next : Idx Γ .oldNet)
    (σ : State C Γ) : holds σ (compose inputName resultName first second next) ↔
    Composes (TEnv.get first σ.env) (TEnv.get second σ.env) (TEnv.get next σ.env) := by
  change (∀ x : Key,
    ((some (decide ((TEnv.get first σ.env).at x = -1)) : Option Bool) = some true →
      (some (decide ((TEnv.get next σ.env).at x = -1)) : Option Bool) = some true) ∧
    ∀ r : Key, (some (decide ((TEnv.get first σ.env).at x = r.val)) : Option Bool) = some true →
      (some (decide ((TEnv.get next σ.env).at x = (TEnv.get second σ.env).at r)) : Option Bool) = some true) ↔ _
  simp only [Composes, Option.some.injEq, decide_eq_true_eq]

/-- Count all quantifiers, connectives and lookup/argument terms. -/
theorem compose_size (inputName resultName : Var) (first second next : Idx Γ .oldNet) :
    (compose (C := C) inputName resultName first second next).tmSize = 31 := rfl

end Solidity.CallFunctionGraph
