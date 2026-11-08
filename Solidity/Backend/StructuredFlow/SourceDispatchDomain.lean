import Solidity.Backend.StructuredFlow.SourceDispatchViews
import Solidity.Lowering.G19.AssignmentBlocks
import Solidity.Lowering.G19.ConditionalSequence
import Solidity.Lowering.G19.ConditionalReturnContinuation
import Solidity.Lowering.G19.ReturnPair
import Solidity.Lowering.G19.AssignmentForBreak
import Solidity.Lowering.G19.AssignmentForContinue
import Solidity.Lowering.G19.AssignmentForReturn
import Solidity.Lowering.G19.AssignmentWhileContinue
import Solidity.Lowering.G19.WhileReturn
import Solidity.Lowering.G19.AssignmentDoWhileBreak
import Solidity.Lowering.G19.AssignmentDoWhileContinue
import Solidity.Lowering.G19.AssignmentDoWhileReturn

/-!
# Exact union of the published structured Source compiler templates

Guards silently broadening a dispatcher's domain to arbitrary expressions,
recursive loops or reachable suffixes. `Plan` is indexed by the existing Source
term and lists precisely the sixteen source families with compiler theorems.
It is extraction provenance, with no evaluator or alternative Source syntax.
Arbitrary tails and posts occur only where the existing theorems skip them.
-/
namespace Solidity.Backend.StructuredFlow.SourceDispatch
open Solidity.Lowering.G19

inductive Plan (E : Source.Env) (M : Bool) :
    {R : List Source.STy} → {k : Source.SCtx} → {Γ Δ : Source.RCtx} →
    Source.RStmt E R M k Γ Δ → Type where
  | blocks {R k Γ} (steps : List (Source.Idx Γ .bool × Source.Idx Γ .bool)) :
      Plan E M (AssignmentBlocks.statement (E := E) (R := R) (M := M) (k := k) steps)
  | conditional {R k Γ τ} (ci ca : Source.Idx Γ .bool) (i a j b : Source.Idx Γ τ) :
      Plan E M (ConditionalStatement.statement (E := E) (R := R) (M := M) (k := k) ci ca i a j b)
  | sequence {R k Γ τ σ} (ci ca : Source.Idx Γ .bool) (i a j b : Source.Idx Γ τ)
      (dest donor : Source.Idx Γ σ) :
      Plan E M (ConditionalSequence.statement (E := E) (R := R) (M := M) (k := k) ci ca i a j b dest donor)
  | returning {k Γ τ} (ci ca : Source.Idx Γ .bool) (i a j b : Source.Idx Γ τ) :
      Plan E M (ConditionalReturn.statement (E := E) (M := M) (k := k) ci ca i a j b)
  | continuation {k Γ tailΓ τ} (ci ca : Source.Idx Γ .bool) (i a j b : Source.Idx Γ τ)
      (tail : Source.RItems E [] M k Γ tailΓ) :
      Plan E M (ConditionalReturnContinuation.statement (M := M) (k := k) ci ca i a j b tail)
  | returnTail {k Γ σ} (ci ca : Source.Idx Γ .bool) (dest donor : Source.Idx Γ σ) :
      Plan E M (ReturnTail.statement (E := E) (M := M) (k := k) ci ca dest donor)
  | returnPair {k Γ τ σ} (ci ca : Source.Idx Γ .bool) (i a : Source.Idx Γ τ)
      (dest donor : Source.Idx Γ σ) :
      Plan E M (ReturnPair.statement (E := E) (M := M) (k := k) ci ca i a dest donor)
  | whileBreak {R Γ l u} (i a : Source.Idx Γ .bool) :
      Plan E M (Source.RStmt.whileLoop (R := R) (l := l) (u := u)
        (.assign (.local i) (.local a)) .brk)
  | whileContinue {R Γ tailΓ l u} (i a : Source.Idx Γ .bool)
      (tail : Source.RItems E R M ⟨true,u⟩ Γ tailΓ) :
      Plan E M (AssignmentWhileContinue.statement (l := l) i a tail)
  | whileReturn {Γ l u} (i a : Source.Idx Γ .bool) :
      Plan E M (Source.RStmt.whileLoop (R := []) (l := l) (u := u)
        (.assign (.local i) (.local a)) (.ret rfl))
  | forBreak {R Γ l u} (i a : Source.Idx Γ .bool) (post : Source.ROptExpr E Γ) :
      Plan E M (AssignmentForBreak.statement (R := R) (M := M) (l := l) (u := u) i a post)
  | forContinue {R Γ tailΓ l u} (i a : Source.Idx Γ .bool)
      (tail : Source.RItems E R M ⟨true,u⟩ Γ tailΓ) :
      Plan E M (AssignmentForContinue.statement (l := l) i a tail)
  | forReturn {Γ l u} (i a : Source.Idx Γ .bool) (post : Source.ROptExpr E Γ) :
      Plan E M (AssignmentForReturn.statement (M := M) (l := l) (u := u) i a post)
  | doBreak {R Γ l u} (i a : Source.Idx Γ .bool) (condition : Source.RExpr E Γ .bool) :
      Plan E M (Source.RStmt.doWhile (R := R) (l := l) (u := u)
        (AssignmentDoWhileBreak.body i a) condition)
  | doContinue {R Γ tailΓ l u} (i a : Source.Idx Γ .bool)
      (tail : Source.RItems E R M ⟨true,u⟩ Γ tailΓ) :
      Plan E M (Source.RStmt.doWhile (R := R) (l := l) (u := u)
        (AssignmentDoWhileContinue.body i a tail) (.bool false))
  | doReturn {Γ l u} (i a : Source.Idx Γ .bool) (condition : Source.RExpr E Γ .bool) :
      Plan E M (Source.RStmt.doWhile (R := []) (l := l) (u := u)
        (AssignmentDoWhileReturn.body i a) condition)

/-- Exactly the union above, not arbitrary control flow with the same outer tag. -/
def Supported {E : Source.Env} {M : Bool} {R : List Source.STy}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) : Prop :=
  Nonempty (Plan E M s)

/-- Every covered statement restores its caller's Source context. -/
theorem Plan.context_same {E : Source.Env} {M : Bool} {R : List Source.STy}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} {s : Source.RStmt E R M k Γ Δ}
    (plan : Plan E M s) : Δ = Γ := by
  cases plan <;> rfl

end Solidity.Backend.StructuredFlow.SourceDispatch
