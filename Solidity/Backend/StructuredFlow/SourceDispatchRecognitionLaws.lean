import Solidity.Backend.StructuredFlow.SourceDispatchRecognize

/-!
# Completeness of exact Source template extraction

Guards a reject-all recognizer or accidental finite block-length cap satisfying
only extraction soundness. These laws concern the existing Source syntax;
operational correctness remains with the per-construct compiler theorems.
-/
namespace Solidity.Backend.StructuredFlow.SourceDispatch
open Solidity.Lowering.G19

@[simp] theorem conditional_exact {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ : Source.RCtx} {τ : Source.STy}
    (ci ca : Source.Idx Γ .bool) (i a j b : Source.Idx Γ τ) :
    conditional? (ConditionalStatement.statement (E := E) (R := R) (M := M) (k := k)
      ci ca i a j b) = some (.branch ci ca i a j b) := by
  simp [conditional?,ConditionalStatement.statement,localCopy_copy,copyStatement_copy]

@[simp] theorem itemSpine_sourceItems {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ : Source.RCtx}
    (steps : List (Source.Idx Γ .bool × Source.Idx Γ .bool)) :
    itemSpine (AssignmentBlocks.sourceItems (E := E) (R := R) (M := M) (k := k) steps) =
      steps.length := by
  induction steps with
  | nil => rfl
  | cons step rest ih =>
    cases step
    exact congrArg (fun n => n + 1) ih

theorem copyItemsAux_complete {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ : Source.RCtx}
    (steps : List (Source.Idx Γ .bool × Source.Idx Γ .bool)) (spare : Nat) :
    copyItemsAux (steps.length + spare + 1)
      (AssignmentBlocks.sourceItems (E := E) (R := R) (M := M) (k := k) steps) =
      some (.copies steps) := by
  induction steps with
  | nil => simp [copyItemsAux,AssignmentBlocks.sourceItems]
  | cons step rest ih =>
    cases step with
    | mk i a =>
      simpa [List.length_cons,Nat.add_right_comm,copyItemsAux,AssignmentBlocks.sourceItems,
        boolCopyStatement_copy] using congrArg (Option.map (prependCopy i a
          (AssignmentBlocks.sourceItems (E := E) (R := R) (M := M) (k := k) rest))) ih

@[simp] theorem copyItems_complete {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ : Source.RCtx}
    (steps : List (Source.Idx Γ .bool × Source.Idx Γ .bool)) :
    copyItems? (AssignmentBlocks.sourceItems (E := E) (R := R) (M := M) (k := k) steps) =
      some (.copies steps) := by
  simpa [copyItems?,itemSpine_sourceItems] using
    (copyItemsAux_complete (E := E) (R := R) (M := M) (k := k) steps 0)

@[simp] theorem returning_exact {E : Source.Env} {M : Bool}
    {k : Source.SCtx} {Γ : Source.RCtx} {τ : Source.STy}
    (ci ca : Source.Idx Γ .bool) (i a j b : Source.Idx Γ τ) :
    returning? (ConditionalReturn.statement (E := E) (M := M) (k := k) ci ca i a j b) =
      some (.returns ci ca i a j b) := by
  simp [returning?,ConditionalReturn.statement,blockStatement?,twoItems?,
    emptyItems?,returnStatement?,conditional_exact]

@[simp] theorem returnTail_exact {E : Source.Env} {M : Bool}
    {k : Source.SCtx} {Γ : Source.RCtx} {τ : Source.STy}
    (ci ca : Source.Idx Γ .bool) (i a : Source.Idx Γ τ) :
    returnTail? (ReturnTail.statement (E := E) (M := M) (k := k) ci ca i a) =
      some (.tail ci ca i a) := by
  simp [returnTail?,ReturnTail.statement,blockStatement?,twoItems?,
    emptyItems?,ifReturn?,returnStatement?,localCopy_copy,copyStatement_copy]

@[simp] theorem sequencePlan_exact {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ : Source.RCtx} {τ σ : Source.STy}
    (ci ca : Source.Idx Γ .bool) (i a j b : Source.Idx Γ τ) (dest donor : Source.Idx Γ σ) :
    sequencePlan? (ConditionalSequence.statement (E := E) (R := R) (M := M) (k := k)
      ci ca i a j b dest donor) = some (.sequence ci ca i a j b dest donor) := by
  simp [sequencePlan?,ConditionalSequence.statement,blockStatement?,twoItems?,
    emptyItems?,conditional_exact,copyStatement_copy]

@[simp] theorem pairPlan_exact {E : Source.Env} {M : Bool}
    {k : Source.SCtx} {Γ : Source.RCtx} {τ σ : Source.STy}
    (ci ca : Source.Idx Γ .bool) (i a : Source.Idx Γ τ) (dest donor : Source.Idx Γ σ) :
    pairPlan? (ReturnPair.statement (E := E) (M := M) (k := k) ci ca i a dest donor) =
      some (.returnPair ci ca i a dest donor) := by
  simp [pairPlan?,ReturnPair.statement,blockStatement?,twoItems?,
    emptyItems?,returnTail_exact,copyStatement_copy]

@[simp] theorem continuationPlan_exact {E : Source.Env} {M : Bool}
    {k : Source.SCtx} {Γ tailΓ : Source.RCtx} {τ : Source.STy}
    (ci ca : Source.Idx Γ .bool) (i a j b : Source.Idx Γ τ)
    (tail : Source.RItems E [] M k Γ tailΓ) :
    continuationPlan? (ConditionalReturnContinuation.statement (E := E) (M := M) (k := k)
      ci ca i a j b tail) = some (.continuation ci ca i a j b tail) := by
  simp [continuationPlan?,ConditionalReturnContinuation.statement,blockStatement?,
    itemHead?,returning_exact]

@[simp] theorem whileBreakPlan_exact {E : Source.Env} {R : List Source.STy} {M l u : Bool}
    {Γ : Source.RCtx} (i a : Source.Idx Γ .bool) :
    whilePlan? (Source.RStmt.whileLoop (E := E) (R := R) (M := M) (l := l) (u := u)
      (.assign (.local i) (.local a)) .brk) = some (.whileBreak i a) := by
  simp [whilePlan?,localCopy_copy,breakStatement?]

@[simp] theorem whileReturnPlan_exact {E : Source.Env} {M l u : Bool}
    {Γ : Source.RCtx} (i a : Source.Idx Γ .bool) :
    whilePlan? (Source.RStmt.whileLoop (E := E) (R := []) (M := M) (l := l) (u := u)
      (.assign (.local i) (.local a)) (.ret rfl)) = some (.whileReturn i a) := by
  simp [whilePlan?,localCopy_copy,breakStatement?,returnStatement?]

@[simp] theorem whileContinuePlan_exact {E : Source.Env} {R : List Source.STy} {M l u : Bool}
    {Γ tailΓ : Source.RCtx} (i a : Source.Idx Γ .bool)
    (tail : Source.RItems E R M ⟨true,u⟩ Γ tailΓ) :
    whilePlan? (AssignmentWhileContinue.statement (l := l) i a tail) =
      some (.whileContinue i a tail) := by
  simp [whilePlan?,AssignmentWhileContinue.statement,AssignmentWhileContinue.body,localCopy_copy,breakStatement?,
    returnStatement?,resetContinue?,blockStatement?,itemHead?,boolWriteStatement_set,
    continueStatement?]

@[simp] theorem forBreakPlan_exact {E : Source.Env} {R : List Source.STy} {M l u : Bool}
    {Γ : Source.RCtx} (i a : Source.Idx Γ .bool) (post : Source.ROptExpr E Γ) :
    forBreakPlan? (AssignmentForBreak.statement (R := R) (M := M) (l := l) (u := u) i a post) =
      some (.forBreak i a post) := by
  simp [forBreakPlan?,AssignmentForBreak.statement,boolCopyStatement_copy,breakStatement?]

@[simp] theorem forReturnPlan_exact {E : Source.Env} {M l u : Bool}
    {Γ : Source.RCtx} (i a : Source.Idx Γ .bool) (post : Source.ROptExpr E Γ) :
    forRestPlan? (AssignmentForReturn.statement (M := M) (l := l) (u := u) i a post) =
      some (.forReturn i a post) := by
  simp [forRestPlan?,AssignmentForReturn.statement,skipStatement?,localCopy_copy,returnStatement?]

@[simp] theorem forContinuePlan_exact {E : Source.Env} {R : List Source.STy} {M l u : Bool}
    {Γ tailΓ : Source.RCtx} (i a : Source.Idx Γ .bool)
    (tail : Source.RItems E R M ⟨true,u⟩ Γ tailΓ) :
    forRestPlan? (AssignmentForContinue.statement (l := l) i a tail) =
      some (.forContinue i a tail) := by
  simp [forRestPlan?,AssignmentForContinue.statement,AssignmentForContinue.body,skipStatement?,localCopy_copy,
    returnStatement?,continueBlock?,blockStatement?,itemHead?,continueStatement?,boolWriteStatement_set]

@[simp] theorem doBreakPlan_exact {E : Source.Env} {R : List Source.STy} {M l u : Bool}
    {Γ : Source.RCtx} (i a : Source.Idx Γ .bool) (condition : Source.RExpr E Γ .bool) :
    doPlan? (Source.RStmt.doWhile (R := R) (M := M) (l := l) (u := u)
      (AssignmentDoWhileBreak.body i a) condition) = some (.doBreak i a condition) := by
  simp [doPlan?,AssignmentDoWhileBreak.body,blockStatement?,itemHead?,boolCopyStatement_copy,
    breakStatement?,emptyItems?]

@[simp] theorem doReturnPlan_exact {E : Source.Env} {M l u : Bool}
    {Γ : Source.RCtx} (i a : Source.Idx Γ .bool) (condition : Source.RExpr E Γ .bool) :
    doPlan? (Source.RStmt.doWhile (R := []) (M := M) (l := l) (u := u)
      (AssignmentDoWhileReturn.body i a) condition) = some (.doReturn i a condition) := by
  simp [doPlan?,AssignmentDoWhileReturn.body,blockStatement?,itemHead?,boolCopyStatement_copy,
    breakStatement?,returnStatement?,emptyItems?]

@[simp] theorem doContinuePlan_exact {E : Source.Env} {R : List Source.STy} {M l u : Bool}
    {Γ tailΓ : Source.RCtx} (i a : Source.Idx Γ .bool)
    (tail : Source.RItems E R M ⟨true,u⟩ Γ tailΓ) :
    doPlan? (Source.RStmt.doWhile (R := R) (M := M) (l := l) (u := u)
      (AssignmentDoWhileContinue.body i a tail) (.bool false)) = some (.doContinue i a tail) := by
  simp [doPlan?,AssignmentDoWhileContinue.body,blockStatement?,itemHead?,boolCopyStatement_copy,
    breakStatement?,returnStatement?,continueStatement?,literal?]

@[simp] theorem blocksPlan_exact {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ : Source.RCtx}
    (steps : List (Source.Idx Γ .bool × Source.Idx Γ .bool)) :
    blocksPlan? (AssignmentBlocks.statement (E := E) (R := R) (M := M) (k := k) steps) =
      some (.blocks steps) := by
  simp [blocksPlan?,AssignmentBlocks.statement,blockStatement?,copyItems_complete]

private theorem recognizeCase_blocksPlan_exact {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ : Source.RCtx}
    (steps : List (Source.Idx Γ .bool × Source.Idx Γ .bool)) :
    recognize (AssignmentBlocks.statement (E := E) (R := R) (M := M) (k := k) steps) =
      some (.blocks steps) := by
  let input := (AssignmentBlocks.statement (E := E) (R := R) (M := M) (k := k) steps)
  change (blocksPlan? input).orElse (fun _ =>
    ((returning? input).map Returning.plan).orElse (fun _ =>
    ((returnTail? input).map ReturnTailView.plan).orElse (fun _ =>
    (sequencePlan? input).orElse (fun _ =>
    (pairPlan? input).orElse (fun _ => continuationPlan? input))))) = _
  have yes : blocksPlan? input = some (.blocks steps) := blocksPlan_exact steps
  rw [yes]
  rfl

private theorem recognizeCase_conditional_exact {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ : Source.RCtx} {τ : Source.STy}
    (ci ca : Source.Idx Γ .bool) (i a j b : Source.Idx Γ τ) :
    recognize (ConditionalStatement.statement (E := E) (R := R) (M := M) (k := k)
      ci ca i a j b) = some (.conditional ci ca i a j b) := by
  let input := (ConditionalStatement.statement (E := E) (R := R) (M := M) (k := k)
      ci ca i a j b)
  change (conditional? input).map Conditional.plan = _
  have yes : conditional? input = some (.branch ci ca i a j b) := conditional_exact ci ca i a j b
  rw [yes]
  rfl

private theorem recognizeCase_sequencePlan_exact {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ : Source.RCtx} {τ σ : Source.STy}
    (ci ca : Source.Idx Γ .bool) (i a j b : Source.Idx Γ τ) (dest donor : Source.Idx Γ σ) :
    recognize (ConditionalSequence.statement (E := E) (R := R) (M := M) (k := k)
      ci ca i a j b dest donor) = some (.sequence ci ca i a j b dest donor) := by
  let input := (ConditionalSequence.statement (E := E) (R := R) (M := M) (k := k)
      ci ca i a j b dest donor)
  change (blocksPlan? input).orElse (fun _ =>
    ((returning? input).map Returning.plan).orElse (fun _ =>
    ((returnTail? input).map ReturnTailView.plan).orElse (fun _ =>
    (sequencePlan? input).orElse (fun _ =>
    (pairPlan? input).orElse (fun _ => continuationPlan? input))))) = _
  have no0 : blocksPlan? input = none := rfl
  have no1 : returning? input = none := by
    simp [input,returning?,ConditionalSequence.statement,blockStatement?,twoItems?,emptyItems?,conditional_exact,returnStatement?]
  have no2 : returnTail? input = none := rfl
  have yes : sequencePlan? input = some (.sequence ci ca i a j b dest donor) := sequencePlan_exact ci ca i a j b dest donor
  rw [no0,no1,no2,yes]
  rfl

private theorem recognizeCase_returning_exact {E : Source.Env} {M : Bool}
    {k : Source.SCtx} {Γ : Source.RCtx} {τ : Source.STy}
    (ci ca : Source.Idx Γ .bool) (i a j b : Source.Idx Γ τ) :
    recognize (ConditionalReturn.statement (E := E) (M := M) (k := k) ci ca i a j b) =
      some (.returning ci ca i a j b) := by
  let input := (ConditionalReturn.statement (E := E) (M := M) (k := k) ci ca i a j b)
  change (blocksPlan? input).orElse (fun _ =>
    ((returning? input).map Returning.plan).orElse (fun _ =>
    ((returnTail? input).map ReturnTailView.plan).orElse (fun _ =>
    (sequencePlan? input).orElse (fun _ =>
    (pairPlan? input).orElse (fun _ => continuationPlan? input))))) = _
  have no0 : blocksPlan? input = none := rfl
  have yes : returning? input = some (.returns ci ca i a j b) := returning_exact ci ca i a j b
  rw [no0,yes]
  rfl

private theorem recognizeCase_continuationPlan_exact {E : Source.Env} {M : Bool}
    {k : Source.SCtx} {Γ tailΓ : Source.RCtx} {τ : Source.STy}
    (ci ca : Source.Idx Γ .bool) (i a j b : Source.Idx Γ τ)
    (tail : Source.RItems E [] M k Γ tailΓ) :
    recognize (ConditionalReturnContinuation.statement (E := E) (M := M) (k := k)
      ci ca i a j b tail) = some (.continuation ci ca i a j b tail) := by
  let input := (ConditionalReturnContinuation.statement (E := E) (M := M) (k := k)
      ci ca i a j b tail)
  change (blocksPlan? input).orElse (fun _ =>
    ((returning? input).map Returning.plan).orElse (fun _ =>
    ((returnTail? input).map ReturnTailView.plan).orElse (fun _ =>
    (sequencePlan? input).orElse (fun _ =>
    (pairPlan? input).orElse (fun _ => continuationPlan? input))))) = _
  have no0 : blocksPlan? input = none := rfl
  have no1 : returning? input = none := by
    cases tail
    case stmt second ending => cases ending <;> rfl
    all_goals rfl
  have no2 : returnTail? input = none := by
    cases tail
    case stmt second ending => cases ending <;> rfl
    all_goals rfl
  have no3 : sequencePlan? input = none := by
    cases tail
    case stmt second ending => cases ending <;> rfl
    all_goals rfl
  have no4 : pairPlan? input = none := by
    cases tail
    case stmt second ending => cases ending <;> rfl
    all_goals rfl
  have yes : continuationPlan? input = some (.continuation ci ca i a j b tail) := continuationPlan_exact ci ca i a j b tail
  rw [no0,no1,no2,no3,no4,yes]
  rfl

private theorem recognizeCase_returnTail_exact {E : Source.Env} {M : Bool}
    {k : Source.SCtx} {Γ : Source.RCtx} {τ : Source.STy}
    (ci ca : Source.Idx Γ .bool) (i a : Source.Idx Γ τ) :
    recognize (ReturnTail.statement (E := E) (M := M) (k := k) ci ca i a) =
      some (.returnTail ci ca i a) := by
  let input := (ReturnTail.statement (E := E) (M := M) (k := k) ci ca i a)
  change (blocksPlan? input).orElse (fun _ =>
    ((returning? input).map Returning.plan).orElse (fun _ =>
    ((returnTail? input).map ReturnTailView.plan).orElse (fun _ =>
    (sequencePlan? input).orElse (fun _ =>
    (pairPlan? input).orElse (fun _ => continuationPlan? input))))) = _
  have no0 : blocksPlan? input = none := rfl
  have no1 : returning? input = none := rfl
  have yes : returnTail? input = some (.tail ci ca i a) := returnTail_exact ci ca i a
  rw [no0,no1,yes]
  rfl

private theorem recognizeCase_pairPlan_exact {E : Source.Env} {M : Bool}
    {k : Source.SCtx} {Γ : Source.RCtx} {τ σ : Source.STy}
    (ci ca : Source.Idx Γ .bool) (i a : Source.Idx Γ τ) (dest donor : Source.Idx Γ σ) :
    recognize (ReturnPair.statement (E := E) (M := M) (k := k) ci ca i a dest donor) =
      some (.returnPair ci ca i a dest donor) := by
  let input := (ReturnPair.statement (E := E) (M := M) (k := k) ci ca i a dest donor)
  change (blocksPlan? input).orElse (fun _ =>
    ((returning? input).map Returning.plan).orElse (fun _ =>
    ((returnTail? input).map ReturnTailView.plan).orElse (fun _ =>
    (sequencePlan? input).orElse (fun _ =>
    (pairPlan? input).orElse (fun _ => continuationPlan? input))))) = _
  have no0 : blocksPlan? input = none := rfl
  have no1 : returning? input = none := rfl
  have no2 : returnTail? input = none := rfl
  have no3 : sequencePlan? input = none := rfl
  have yes : pairPlan? input = some (.returnPair ci ca i a dest donor) := pairPlan_exact ci ca i a dest donor
  rw [no0,no1,no2,no3,yes]
  rfl

private theorem recognizeCase_whileBreakPlan_exact {E : Source.Env} {R : List Source.STy} {M l u : Bool}
    {Γ : Source.RCtx} (i a : Source.Idx Γ .bool) :
    recognize (Source.RStmt.whileLoop (E := E) (R := R) (M := M) (l := l) (u := u)
      (.assign (.local i) (.local a)) .brk) = some (.whileBreak i a) := by
  let input := (Source.RStmt.whileLoop (E := E) (R := R) (M := M) (l := l) (u := u)
      (.assign (.local i) (.local a)) .brk)
  change whilePlan? input = _
  exact whileBreakPlan_exact i a

private theorem recognizeCase_whileContinuePlan_exact {E : Source.Env} {R : List Source.STy} {M l u : Bool}
    {Γ tailΓ : Source.RCtx} (i a : Source.Idx Γ .bool)
    (tail : Source.RItems E R M ⟨true,u⟩ Γ tailΓ) :
    recognize (AssignmentWhileContinue.statement (l := l) i a tail) =
      some (.whileContinue i a tail) := by
  let input := (AssignmentWhileContinue.statement (l := l) i a tail)
  change whilePlan? input = _
  exact whileContinuePlan_exact i a tail

private theorem recognizeCase_whileReturnPlan_exact {E : Source.Env} {M l u : Bool}
    {Γ : Source.RCtx} (i a : Source.Idx Γ .bool) :
    recognize (Source.RStmt.whileLoop (E := E) (R := []) (M := M) (l := l) (u := u)
      (.assign (.local i) (.local a)) (.ret rfl)) = some (.whileReturn i a) := by
  let input := (Source.RStmt.whileLoop (E := E) (R := []) (M := M) (l := l) (u := u)
      (.assign (.local i) (.local a)) (.ret rfl))
  change whilePlan? input = _
  exact whileReturnPlan_exact i a

private theorem recognizeCase_forBreakPlan_exact {E : Source.Env} {R : List Source.STy} {M l u : Bool}
    {Γ : Source.RCtx} (i a : Source.Idx Γ .bool) (post : Source.ROptExpr E Γ) :
    recognize (AssignmentForBreak.statement (R := R) (M := M) (l := l) (u := u) i a post) =
      some (.forBreak i a post) := by
  let input := (AssignmentForBreak.statement (R := R) (M := M) (l := l) (u := u) i a post)
  change (forBreakPlan? input).orElse (fun _ => forRestPlan? input) = _
  have yes : forBreakPlan? input = some (.forBreak i a post) := forBreakPlan_exact i a post
  rw [yes]
  rfl

private theorem recognizeCase_forContinuePlan_exact {E : Source.Env} {R : List Source.STy} {M l u : Bool}
    {Γ tailΓ : Source.RCtx} (i a : Source.Idx Γ .bool)
    (tail : Source.RItems E R M ⟨true,u⟩ Γ tailΓ) :
    recognize (AssignmentForContinue.statement (l := l) i a tail) =
      some (.forContinue i a tail) := by
  let input := (AssignmentForContinue.statement (l := l) i a tail)
  change (forBreakPlan? input).orElse (fun _ => forRestPlan? input) = _
  have no : forBreakPlan? input = none := rfl
  have yes : forRestPlan? input = some (.forContinue i a tail) := forContinuePlan_exact i a tail
  rw [no]
  exact yes

private theorem recognizeCase_forReturnPlan_exact {E : Source.Env} {M l u : Bool}
    {Γ : Source.RCtx} (i a : Source.Idx Γ .bool) (post : Source.ROptExpr E Γ) :
    recognize (AssignmentForReturn.statement (M := M) (l := l) (u := u) i a post) =
      some (.forReturn i a post) := by
  let input := (AssignmentForReturn.statement (M := M) (l := l) (u := u) i a post)
  change (forBreakPlan? input).orElse (fun _ => forRestPlan? input) = _
  have no : forBreakPlan? input = none := rfl
  have yes : forRestPlan? input = some (.forReturn i a post) := forReturnPlan_exact i a post
  rw [no]
  exact yes

private theorem recognizeCase_doBreakPlan_exact {E : Source.Env} {R : List Source.STy} {M l u : Bool}
    {Γ : Source.RCtx} (i a : Source.Idx Γ .bool) (condition : Source.RExpr E Γ .bool) :
    recognize (Source.RStmt.doWhile (R := R) (M := M) (l := l) (u := u)
      (AssignmentDoWhileBreak.body i a) condition) = some (.doBreak i a condition) := by
  let input := (Source.RStmt.doWhile (R := R) (M := M) (l := l) (u := u)
      (AssignmentDoWhileBreak.body i a) condition)
  change doPlan? input = _
  exact doBreakPlan_exact i a condition

private theorem recognizeCase_doContinuePlan_exact {E : Source.Env} {R : List Source.STy} {M l u : Bool}
    {Γ tailΓ : Source.RCtx} (i a : Source.Idx Γ .bool)
    (tail : Source.RItems E R M ⟨true,u⟩ Γ tailΓ) :
    recognize (Source.RStmt.doWhile (R := R) (M := M) (l := l) (u := u)
      (AssignmentDoWhileContinue.body i a tail) (.bool false)) = some (.doContinue i a tail) := by
  let input := (Source.RStmt.doWhile (R := R) (M := M) (l := l) (u := u)
      (AssignmentDoWhileContinue.body i a tail) (.bool false))
  change doPlan? input = _
  exact doContinuePlan_exact i a tail

private theorem recognizeCase_doReturnPlan_exact {E : Source.Env} {M l u : Bool}
    {Γ : Source.RCtx} (i a : Source.Idx Γ .bool) (condition : Source.RExpr E Γ .bool) :
    recognize (Source.RStmt.doWhile (R := []) (M := M) (l := l) (u := u)
      (AssignmentDoWhileReturn.body i a) condition) = some (.doReturn i a condition) := by
  let input := (Source.RStmt.doWhile (R := []) (M := M) (l := l) (u := u)
      (AssignmentDoWhileReturn.body i a) condition)
  change doPlan? input = _
  exact doReturnPlan_exact i a condition

/-- Recognition returns the original plan, not merely some inhabited plan. -/
theorem recognize_plan_exact {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} {s : Source.RStmt E R M k Γ Δ}
    (plan : Plan E M s) : recognize s = some plan := by
  cases plan
  case blocks steps => exact recognizeCase_blocksPlan_exact steps
  case conditional ci ca i a j b => exact recognizeCase_conditional_exact ci ca i a j b
  case sequence ci ca i a j b dest donor => exact recognizeCase_sequencePlan_exact ci ca i a j b dest donor
  case returning ci ca i a j b => exact recognizeCase_returning_exact ci ca i a j b
  case continuation ci ca i a j b tail => exact recognizeCase_continuationPlan_exact ci ca i a j b tail
  case returnTail ci ca dest donor => exact recognizeCase_returnTail_exact ci ca dest donor
  case returnPair ci ca i a dest donor => exact recognizeCase_pairPlan_exact ci ca i a dest donor
  case whileBreak i a => exact recognizeCase_whileBreakPlan_exact i a
  case whileContinue i a tail => exact recognizeCase_whileContinuePlan_exact i a tail
  case whileReturn i a => exact recognizeCase_whileReturnPlan_exact i a
  case forBreak i a post => exact recognizeCase_forBreakPlan_exact i a post
  case forContinue i a tail => exact recognizeCase_forContinuePlan_exact i a tail
  case forReturn i a post => exact recognizeCase_forReturnPlan_exact i a post
  case doBreak i a condition => exact recognizeCase_doBreakPlan_exact i a condition
  case doContinue i a tail => exact recognizeCase_doContinuePlan_exact i a tail
  case doReturn i a condition => exact recognizeCase_doReturnPlan_exact i a condition

/-- No supported template is lost to recognition precedence or block length. -/
theorem recognize_complete {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} {s : Source.RStmt E R M k Γ Δ}
    (plan : Plan E M s) : (recognize s).isSome = true := by
  rw [recognize_plan_exact plan]
  rfl

/-- Exact domain equivalence, including an explicit refusal outside the union. -/
theorem recognize_none_iff {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    recognize s = none ↔ ¬ Supported s := by
  constructor
  · intro refused ⟨plan⟩
    have accepted := recognize_complete plan
    rw [refused] at accepted
    contradiction
  · exact recognize_refuses s

/-- Captured-return extraction is selected before any later alternatives. -/
theorem recognize_returning_exact {E : Source.Env} {M : Bool}
    {k : Source.SCtx} {Γ : Source.RCtx} {τ : Source.STy}
    (ci ca : Source.Idx Γ .bool) (i a j b : Source.Idx Γ τ) :
    recognize (ConditionalReturn.statement (E := E) (M := M) (k := k) ci ca i a j b) =
      some (.returning ci ca i a j b) := by
  exact recognize_plan_exact (.returning ci ca i a j b)

end Solidity.Backend.StructuredFlow.SourceDispatch
