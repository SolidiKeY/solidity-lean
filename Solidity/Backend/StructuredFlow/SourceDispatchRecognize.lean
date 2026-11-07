import Solidity.Backend.StructuredFlow.SourceDispatchDomain
import Solidity.Lowering.V07.IntegerLocalFamily

/-!
# Exact recognition for the structured Source compiler

Guards accepting an if/else whose branches merely resemble the supported
local-copy template. Successful extraction is indexed by the original Source
statement, including both branch types and all local indices.
-/
namespace Solidity.Backend.StructuredFlow.SourceDispatch
open Solidity.Lowering.G19

inductive Conditional {E : Source.Env} {R : List Source.STy} {M : Bool} :
    {k : Source.SCtx} → {Γ Δ : Source.RCtx} → Source.RStmt E R M k Γ Δ → Type where
  | branch {k Γ τ} (ci ca : Source.Idx Γ .bool) (i a j b : Source.Idx Γ τ) :
      Conditional (ConditionalStatement.statement (E := E) (R := R) (M := M) (k := k) ci ca i a j b)

def conditional? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (Conditional s) := by
  cases s
  case ifElse condition yes no =>
    refine (localCopy? condition).bind ?_
    intro guard
    refine (copyStatement? yes).bind ?_
    intro left
    refine (copyStatement? no).bind ?_
    intro right
    cases guard with
    | mk ci ca eq =>
      cases left with
      | @copy τ i a =>
        cases right with
        | @copy σ j b =>
          if same : σ = τ then
            cases same
            cases eq
            exact some (.branch ci ca i a j b)
          else exact none
  all_goals exact none

inductive CopyItems {E : Source.Env} {R : List Source.STy} {M : Bool} :
    {k : Source.SCtx} → {Γ Δ : Source.RCtx} → Source.RItems E R M k Γ Δ → Type where
  | copies {k Γ} (steps : List (Source.Idx Γ .bool × Source.Idx Γ .bool)) :
      CopyItems (AssignmentBlocks.sourceItems (E := E) (R := R) (M := M) (k := k) steps)

def prependCopy {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (i a : Source.Idx Γ .bool)
    (items : Source.RItems E R M k Γ Δ) (rest : CopyItems items) :
    CopyItems (.stmt (.expr (.assign (.local i) (.local a))) items) := by
  cases rest with
  | copies steps => exact .copies ((i,a) :: steps)

/-- Structural traversal budget: derived from the statement spine by `copyItems?`,
not a bound on Source execution or supported block length. -/
def copyItemsAux {E : Source.Env} {R : List Source.STy} {M : Bool} (fuel : Nat) :
    {k : Source.SCtx} → {Γ Δ : Source.RCtx} →
    (items : Source.RItems E R M k Γ Δ) → Option (CopyItems items) :=
  Nat.rec (motive := fun _ => {k : Source.SCtx} → {Γ Δ : Source.RCtx} →
      (items : Source.RItems E R M k Γ Δ) → Option (CopyItems items))
    (fun {_} {_} {_} _ => none)
    (fun _ ih {_} {_} {_} items => by
      cases items
      case nil => exact some (.copies [])
      case stmt head tail =>
        refine (boolCopyStatement? head).bind ?_
        intro headCopy
        cases headCopy with
        | copy i a =>
          exact (ih tail).map (prependCopy i a tail)
      all_goals exact none) fuel

/-- Length of the ordinary statement spine. Unchecked groups are refused. -/
def itemSpine {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (items : Source.RItems E R M k Γ Δ) : Nat :=
  Source.RItems.casesOn (motive_2 := fun _ _ _ _ => Nat) items
    0 (fun _ tail => itemSpine tail + 1) (fun _ _ => 0)
termination_by structural items

def copyItems? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (items : Source.RItems E R M k Γ Δ) :
    Option (CopyItems items) := copyItemsAux (itemSpine items + 1) items

inductive IfReturn {E : Source.Env} {M : Bool} :
    {R : List Source.STy} → {k : Source.SCtx} → {Γ Δ : Source.RCtx} →
    Source.RStmt E R M k Γ Δ → Type where
  | branch {k Γ} (ci ca : Source.Idx Γ .bool) :
      IfReturn (Source.RStmt.ifThen (E := E) (M := M) (k := k)
        (.assign (.local ci) (.local ca)) (.ret rfl))

def ifReturn? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (IfReturn s) := by
  cases s
  case ifThen condition body =>
    refine (localCopy? condition).bind ?_
    intro guard
    refine (returnStatement? body).bind ?_
    intro returned
    cases guard with
    | mk ci ca eq =>
      cases returned with
      | ret empty =>
        cases empty
        cases eq
        exact some (.branch ci ca)
  all_goals exact none

inductive TwoItems {E : Source.Env} {R : List Source.STy} {M : Bool} :
    {k : Source.SCtx} → {Γ Δ : Source.RCtx} → Source.RItems E R M k Γ Δ → Type where
  | pair {k Γ mid Δ} (first : Source.RStmt E R M k Γ mid)
      (second : Source.RStmt E R M k mid Δ) :
      TwoItems (.stmt first (.stmt second .nil))

def twoItems? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (items : Source.RItems E R M k Γ Δ) :
    Option (TwoItems items) := by
  cases items
  case stmt first rest =>
    cases rest
    case stmt second ending =>
      refine (emptyItems? ending).map ?_
      intro empty
      cases empty
      exact .pair first second
    all_goals exact none
  all_goals exact none

inductive ReturnTailView {E : Source.Env} {M : Bool} :
    {R : List Source.STy} → {k : Source.SCtx} → {Γ Δ : Source.RCtx} →
    Source.RStmt E R M k Γ Δ → Type where
  | tail {k Γ τ} (ci ca : Source.Idx Γ .bool) (i a : Source.Idx Γ τ) :
      ReturnTailView (ReturnTail.statement (E := E) (M := M) (k := k) ci ca i a)

def returnTail? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (ReturnTailView s) := by
  refine (blockStatement? s).bind ?_
  intro block
  cases block with
  | block items =>
    refine (twoItems? items).bind ?_
    intro pair
    cases pair with
    | pair first second =>
      refine (ifReturn? first).bind ?_
      intro cond
      cases cond with
      | branch ci ca =>
        refine (copyStatement? second).map ?_
        intro copy
        cases copy with
        | copy i a => exact .tail ci ca i a

inductive Returning {E : Source.Env} {M : Bool} :
    {R : List Source.STy} → {k : Source.SCtx} → {Γ Δ : Source.RCtx} →
    Source.RStmt E R M k Γ Δ → Type where
  | returns {k Γ τ} (ci ca : Source.Idx Γ .bool) (i a j b : Source.Idx Γ τ) :
      Returning (ConditionalReturn.statement (E := E) (M := M) (k := k) ci ca i a j b)

def returning? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (Returning s) := by
  refine (blockStatement? s).bind ?_
  intro block
  cases block with
  | block items =>
    refine (twoItems? items).bind ?_
    intro pair
    cases pair with
    | pair first second =>
      refine (conditional? first).bind ?_
      intro cond
      cases cond with
      | branch ci ca i a j b =>
        refine (returnStatement? second).map ?_
        intro ret
        cases ret with
        | ret empty =>
          cases empty
          exact .returns ci ca i a j b

def sequencePlan? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (Plan E M s) := by
  refine (blockStatement? s).bind ?_
  intro block
  cases block with
  | block items =>
    refine (twoItems? items).bind ?_
    intro pair
    cases pair with
    | pair first second =>
      refine (conditional? first).bind ?_
      intro cond
      cases cond with
      | branch ci ca i a j b =>
        refine (copyStatement? second).map ?_
        intro copy
        cases copy with
        | copy dest donor => exact .sequence ci ca i a j b dest donor

def pairPlan? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (Plan E M s) := by
  refine (blockStatement? s).bind ?_
  intro block
  cases block with
  | block items =>
    refine (twoItems? items).bind ?_
    intro pair
    cases pair with
    | pair first second =>
      refine (returnTail? first).bind ?_
      intro tail
      cases tail with
      | tail ci ca i a =>
        refine (copyStatement? second).map ?_
        intro copy
        cases copy with
        | copy dest donor => exact .returnPair ci ca i a dest donor

def continuationPlan? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (Plan E M s) := by
  refine (blockStatement? s).bind ?_
  intro block
  cases block with
  | block items =>
    refine (itemHead? items).bind ?_
    intro head
    cases head with
    | stmt first tail =>
      refine (returning? first).map ?_
      intro returned
      cases returned with
      | returns ci ca i a j b => exact .continuation ci ca i a j b tail

inductive ContinueBlock {E : Source.Env} {R : List Source.STy} {M : Bool} :
    {k : Source.SCtx} → {Γ Δ : Source.RCtx} → Source.RStmt E R M k Γ Δ → Type where
  | body {u Γ tailΓ} (tail : Source.RItems E R M ⟨true,u⟩ Γ tailΓ) :
      ContinueBlock (Source.RStmt.block (.stmt .cont tail))

def continueBlock? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (ContinueBlock s) := by
  refine (blockStatement? s).bind ?_
  intro block
  cases block with
  | block items =>
    refine (itemHead? items).bind ?_
    intro head
    cases head with
    | stmt first tail =>
      refine (continueStatement? first).map ?_
      intro cont
      cases cont
      exact .body tail

inductive ResetContinue {E : Source.Env} {R : List Source.STy} {M : Bool} :
    {k : Source.SCtx} → {Γ Δ : Source.RCtx} → Source.RStmt E R M k Γ Δ → Type where
  | body {u Γ tailΓ} (donor : Source.Idx Γ .bool)
      (tail : Source.RItems E R M ⟨true,u⟩ Γ tailΓ) :
      ResetContinue (Source.RStmt.block (.stmt (.expr (.assign (.local donor) (.bool false)))
        (.stmt .cont tail)))

def resetContinue? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (ResetContinue s) := by
  refine (blockStatement? s).bind ?_
  intro block
  cases block with
  | block items =>
    refine (itemHead? items).bind ?_
    intro head
    cases head with
    | stmt first rest =>
      refine (boolWriteStatement? first).bind ?_
      intro write
      cases write with
      | set donor value =>
        cases value
        case true => exact none
        case false =>
          refine (itemHead? rest).bind ?_
          intro next
          cases next with
          | stmt second tail =>
            refine (continueStatement? second).map ?_
            intro cont
            cases cont
            exact .body donor tail

def whilePlan? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (Plan E M s) := by
  cases s
  case whileLoop condition body =>
    refine (localCopy? condition).bind ?_
    intro guard
    cases guard with
    | mk ci ca eq =>
      cases eq
      exact ((breakStatement? body).map (fun exit => by
        cases exit
        exact .whileBreak ci ca)).orElse (fun _ =>
          ((returnStatement? body).map (fun exit => by
            cases exit with
            | ret empty =>
              cases empty
              exact .whileReturn ci ca)).orElse (fun _ => by
                refine (resetContinue? body).bind ?_
                intro reset
                cases reset with
                | body donor tail =>
                  if same : donor.toNat = ca.toNat then
                    have eq := Solidity.Lowering.V07.source_idx_injective donor ca same
                    cases eq
                    exact some (.whileContinue ci ca tail)
                  else exact none))
  all_goals exact none

def doPlan? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (Plan E M s) := by
  cases s
  case doWhile body condition =>
    refine (blockStatement? body).bind ?_
    intro block
    cases block with
    | block items =>
      refine (itemHead? items).bind ?_
      intro head
      cases head with
      | stmt first rest =>
        refine (boolCopyStatement? first).bind ?_
        intro copy
        cases copy with
        | copy ci ca =>
          refine (itemHead? rest).bind ?_
          intro next
          cases next with
          | stmt second tail =>
            exact ((breakStatement? second).bind (fun exit => by
              cases exit
              refine (emptyItems? tail).map ?_
              intro empty
              cases empty
              exact .doBreak ci ca condition)).orElse (fun _ =>
                ((returnStatement? second).bind (fun exit => by
                  cases exit with
                  | ret emptyR =>
                    cases emptyR
                    refine (emptyItems? tail).map ?_
                    intro empty
                    cases empty
                    exact .doReturn ci ca condition)).orElse (fun _ => by
                      refine (continueStatement? second).bind ?_
                      intro cont
                      cases cont
                      refine (literal? condition).bind ?_
                      intro lit
                      cases lit with
                      | bool value =>
                        cases value
                        case false => exact some (.doContinue ci ca tail)
                        case true => exact none))
  all_goals exact none

def forBreakPlan? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (Plan E M s) := by
  cases s
  case forLoop condition post body initial =>
    refine (boolCopyStatement? initial).bind ?_
    intro copy
    cases copy with
    | copy ci ca =>
      cases condition
      case none =>
        refine (breakStatement? body).map ?_
        intro exit
        cases exit
        exact .forBreak ci ca post
      all_goals exact none
  all_goals exact none

def forRestPlan? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (Plan E M s) := by
  cases s
  case forLoop condition post body initial =>
    refine (skipStatement? initial).bind ?_
    intro skipped
    cases skipped
    cases condition
    case some condition =>
      refine (localCopy? condition).bind ?_
      intro guard
      cases guard with
      | mk ci ca eq =>
        cases eq
        exact ((returnStatement? body).map (fun exit => by
          cases exit with
          | ret empty =>
            cases empty
            exact .forReturn ci ca post)).orElse (fun _ => by
              refine (continueBlock? body).bind ?_
              intro cont
              cases cont with
              | body tail =>
                cases post
                case some expression =>
                  refine (boolWriteStatement? (Source.RStmt.expr (R := R) (M := M)
                    (k := ⟨false,false⟩) expression)).bind ?_
                  intro write
                  cases write with
                  | set donor value =>
                    cases value
                    case false =>
                      if same : donor.toNat = ca.toNat then
                        have eq := Solidity.Lowering.V07.source_idx_injective donor ca same
                        cases eq
                        exact some (.forContinue ci ca tail)
                      else exact none
                    case true => exact none
                all_goals exact none)
    all_goals exact none
  all_goals exact none

def blocksPlan? {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (Plan E M s) := by
  refine (blockStatement? s).bind ?_
  intro block
  cases block with
  | block items =>
    refine (copyItems? items).map ?_
    intro copies
    cases copies with
    | copies steps => exact .blocks steps

def Conditional.plan {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} {s : Source.RStmt E R M k Γ Δ}
    (found : Conditional s) : Plan E M s := by
  cases found with
  | branch ci ca i a j b => exact .conditional ci ca i a j b

def Returning.plan {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} {s : Source.RStmt E R M k Γ Δ}
    (found : Returning s) : Plan E M s := by
  cases found with
  | returns ci ca i a j b => exact .returning ci ca i a j b

def ReturnTailView.plan {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} {s : Source.RStmt E R M k Γ Δ}
    (found : ReturnTailView s) : Plan E M s := by
  cases found with
  | tail ci ca i a => exact .returnTail ci ca i a

/-- Executable extraction, first split by the real Source constructor. Exact
block-copy extraction precedes other block templates, without length bounds. -/
def recognize {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ) :
    Option (Plan E M s) := by
  let input := s
  cases s
  case ifElse =>
    exact (conditional? input).map Conditional.plan
  case block =>
    exact (blocksPlan? input).orElse (fun _ =>
      ((returning? input).map Returning.plan).orElse (fun _ =>
      ((returnTail? input).map ReturnTailView.plan).orElse (fun _ =>
      (sequencePlan? input).orElse (fun _ =>
      (pairPlan? input).orElse (fun _ => continuationPlan? input)))))
  case whileLoop => exact whilePlan? input
  case forLoop => exact (forBreakPlan? input).orElse (fun _ => forRestPlan? input)
  case doWhile => exact doPlan? input
  all_goals exact none

/-- Recognition cannot fabricate support for any other Source term. -/
theorem recognize_sound {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} {s : Source.RStmt E R M k Γ Δ}
    {plan : Plan E M s} (_accepted : recognize s = some plan) : Supported s := ⟨plan⟩

/-- Every Source term outside the stated union is explicitly refused. -/
theorem recognize_refuses {E : Source.Env} {R : List Source.STy} {M : Bool}
    {k : Source.SCtx} {Γ Δ : Source.RCtx} (s : Source.RStmt E R M k Γ Δ)
    (outside : ¬ Supported s) : recognize s = none := by
  cases h : recognize s with
  | none => rfl
  | some plan => exact False.elim (outside ⟨plan⟩)

end Solidity.Backend.StructuredFlow.SourceDispatch
