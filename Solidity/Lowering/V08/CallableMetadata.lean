import Solidity.Source.Resolved
import Solidity.Semantics.ContractWorld

/-!
# Resolved callable metadata and argument order

Adapters over the published resolved terms, not another expression evaluator.
Source expressions keep their type indices and explicit conversion proofs.
The target name check concerns labels and frame order only: it does not certify
source expression evaluation, type representation, body selection or lowering.
-/
namespace Solidity.Lowering.V08.CallableMetadata
open Solidity
open Source

/-- Expose the explicit implicit-conversion nodes already justified by S01. -/
def convertedArgs {E : Source.Env} {Γ : RCtx} : {ps : List STy} →
    RConvArgs E Γ ps → RArgs E Γ ps
  | _, .nil => .nil
  | _, .cons expression conversion rest =>
    .cons (.conv expression (.inl conversion)) (convertedArgs rest)

/-- Original expression types, in source argument order, before conversion. -/
def originTypes {E : Source.Env} {Γ : RCtx} : {ps : List STy} →
    RConvArgs E Γ ps → List STy
  | _, .nil => []
  | _, @RConvArgs.cons _ _ σ _ _ _ _ rest => σ :: originTypes rest

/-- The fitting test enforces exact arity, including nonempty argument lists. -/
theorem argsFit_length {B : DeclName → DeclName → Bool} {σs ps : List STy}
    (fits : argsFit B σs ps = true) : σs.length = ps.length := by
  simp only [argsFit, Bool.and_eq_true, beq_iff_eq] at fits
  exact fits.1

/-- S01 argument conversion retains the original types in their original order. -/
theorem convert_originTypes {E : Source.Env} {Γ : RCtx} {σs : List STy}
    (arguments : RArgs E Γ σs) (ps : List STy)
    (fits : argsFit E.isBase σs ps = true) :
    originTypes (arguments.convert ps fits) = σs := by
  cases arguments with
  | nil =>
    cases ps with
    | nil => rfl
    | cons p ps => have impossible := argsFit_length fits; cases impossible
  | cons expression rest =>
    cases ps with
    | nil => have impossible := argsFit_length fits; cases impossible
    | cons p ps =>
      simp only [RArgs.convert, originTypes]
      exact congrArg (_ :: ·) (convert_originTypes rest _ _)
termination_by σs.length

/-- The source-selected event/error parameter list is unique, not chosen by
an adapter consumer to make an unrelated signature fit. -/
theorem paramsOf_unique (E : Source.Env) (B : DeclName → DeclName → Bool)
    (σs : List STy) (declaration : Decl)
    (fits : declaration.fitsParams E B σs = true) (ps : List STy)
    (declared : declaration.paramTys E = some ps) :
    (paramsOf E B σs declaration fits).1 = ps := by
  exact Option.some.inj ((paramsOf E B σs declaration fits).2.1.symm.trans declared)

/-- A selected function fixes both parameter and result lists simultaneously. -/
theorem function_signature_unique (E : Source.Env) (declaration : Decl)
    {ps rs ps' rs' : List STy}
    (one : declaration.fnSig E = some (ps, rs))
    (two : declaration.fnSig E = some (ps', rs')) : ps = ps' ∧ rs = rs' := by
  exact Prod.mk.inj (Option.some.inj (one.symm.trans two))

/-- Names at a function declaration, using the existing source projection. -/
def parameterNames (declaration : Decl) : List (Option String) :=
  match declaration.kind, declaration.top, declaration.node with
  | .function, _, .function _ ps _ _ _ _ _ _ _ => ps.paramNames
  | _, _, _ => []

/-- User labels retain source spelling; generated labels represent anonymous
parameters, independently of the printer's configurable FreshNames table.
All generated identities collapse to none: this projection cannot detect
permutations of anonymous parameters or distinguish repeated source labels. -/
def sourceLabel : Var → Option String
  | .user name => some name
  | .fresh _ _ => none

/-- Check source-order names against the actual target frame's innermost-first
labels. This check deliberately supplies no type/body preservation premise. -/
def namesMatch {C : Contract} {Γ ps : Solidity.Ctx} (declaration : Decl)
    (arguments : Args C Γ ps) : Bool :=
  decide (parameterNames declaration = arguments.names.reverse.map sourceLabel)

/-- Accepted names agree in source order, with the target frame reversed. -/
theorem namesMatch_iff {C : Contract} {Γ ps : Solidity.Ctx} (declaration : Decl)
    (arguments : Args C Γ ps) : namesMatch declaration arguments = true ↔
    parameterNames declaration = arguments.names.reverse.map sourceLabel := by
  simp only [namesMatch, decide_eq_true_eq]

/-- Each primitive, storage or memory argument binds exactly one frame slot. -/
theorem target_names_length {C : Contract} {Γ ps : Solidity.Ctx}
    (arguments : Args C Γ ps) : arguments.names.length = ps.length := by
  induction arguments with
  | nil => rfl
  | snoc arguments p x expression ih => exact congrArg Nat.succ ih
  | snocStorage arguments R x expression ih => exact congrArg Nat.succ ih
  | snocMemory arguments R x expression ih => exact congrArg Nat.succ ih

/-- The checked source labels retain target arity across all three argument kinds. -/
theorem matched_names_length {C : Contract} {Γ ps : Solidity.Ctx}
    (declaration : Decl) (arguments : Args C Γ ps)
    (matched : namesMatch declaration arguments = true) :
    (parameterNames declaration).length = ps.length := by
  rw [(namesMatch_iff declaration arguments).mp matched, List.length_map,
    List.length_reverse, target_names_length]

#print axioms argsFit_length
#print axioms convert_originTypes
#print axioms paramsOf_unique
#print axioms function_signature_unique
#print axioms namesMatch_iff
#print axioms target_names_length
#print axioms matched_names_length
end Solidity.Lowering.V08.CallableMetadata
