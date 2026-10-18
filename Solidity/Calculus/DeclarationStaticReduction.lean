import Solidity.Calculus.DeclarationReduction
import Solidity.Calculus.CheckedLinear
import Solidity.Calculus.ParameterReduction
import Solidity.Calculus.InputReduction
import Solidity.Calculus.TraceReduction
import Solidity.Calculus.DependentReduction

/-!
# Declaration certificates before complete typed-input decisions

The normalizer may remove only independently certified declaration facts.
Its per-state equivalence composes with the complete static-read pipeline,
so both verdicts still refer to the original formula with its premises.
-/

namespace Solidity.DeclarationReduction

open Decide

variable {C : Contract} {φ : Fml C []}

def withCompiler (d : DeclarationReduction φ)
    (compile : (ψ : Fml C []) → Option (StaticReduction ψ)) : Option (StaticReduction φ) :=
  (compile d.formula).map fun r =>
    ⟨r.refs, r.distinct, r.arithmetic, fun σ => (r.meaning σ).trans (d.correct σ)⟩

def static? (d : DeclarationReduction φ) : Option (StaticReduction φ) := d.withCompiler staticReduction?
def checked? (d : DeclarationReduction φ) : Option (StaticReduction φ) := d.withCompiler checkedReduction?

def parameter? (d : DeclarationReduction φ) : Option (ParameterReduction φ) :=
  (parameterReduction? d.formula).map fun r =>
    ⟨r.parameters, r.distinctParameters, r.refs, r.distinctRefs, r.arithmetic,
      fun σ => (r.meaning σ).trans (d.correct σ)⟩

def input? (d : DeclarationReduction φ) : Option (InputReduction φ) :=
  (inputReduction? d.formula).map fun r =>
    ⟨r.environment, r.distinctEnvironment, r.parameters, r.distinctParameters,
      r.refs, r.distinctRefs, r.arithmetic, fun σ => (r.meaning σ).trans (d.correct σ)⟩

def trace? (d : DeclarationReduction φ) : Option (TraceReduction φ) :=
  (traceReduction? d.formula).map fun r =>
    ⟨⟨r.normalization.formula, fun σ => (r.normalization.correct σ).trans (d.correct σ)⟩,
      r.source, r.sentence⟩

def dependent? (d : DeclarationReduction φ) : Option (DependentReduction φ) :=
  (dependentReduction? d.formula).map fun r =>
    ⟨⟨r.normalization.formula, fun σ => (r.normalization.correct σ).trans (d.correct σ)⟩,
      r.source, r.sentence, r.body, r.covered⟩

open Lean Meta Elab

syntax (name := declarationStaticReductionTerm) "declaration_static_reduce[" term "]" : term
syntax (name := declarationCheckedReductionTerm) "declaration_checked_reduce[" term "]" : term
syntax (name := declarationParameterReductionTerm) "declaration_parameter_reduce[" term "]" : term
syntax (name := declarationInputReductionTerm) "declaration_input_reduce[" term "]" : term
syntax (name := declarationTraceReductionTerm) "declaration_trace_reduce[" term "]" : term
syntax (name := declarationDependentReductionTerm) "declaration_dependent_reduce[" term "]" : term

private def compileReduced (compiler : Lean.Name) (label : String) (d : Expr) : MetaM Expr := do
  let result ← mkAppM compiler #[d]
  let some ← mkAppM ``Option.isSome #[result]
  let eq ← mkEq some (mkConst ``Bool.true)
  -- Run recognition as compiled code; the returned proof is checked by the
  -- kernel. Meta reduction through a deep program can exhaust recursion.
  unless ← withCurrHeartbeats (unsafe evalExpr Bool (mkConst ``Bool) some) do
    throwError "{label}: normalized formula is outside the exact supported storage fragment"
  let proof := mkExpectedPropHint (← mkEqRefl (mkConst ``Bool.true)) eq
  mkAppM ``Option.get #[result, proof]

private def elaborate (compiler : Lean.Name) (label : String) (stx : Syntax) : TermElabM Expr := do
  let φ ← Term.elabTerm stx[1] none
  let d ← withCurrHeartbeats (DeclarationReduction.reduce φ)
  compileReduced compiler label d

/-- The shared bounded declaration and source-input compiler, for tactics
and commands as well as the term elaborator. -/
def compileInput (φ : Expr) : MetaM Expr := do
  let d ← withCurrHeartbeats (DeclarationReduction.reduce φ)
  compileReduced ``input? "declaration_input_reduce" d

def compileDependent (φ : Expr) : MetaM Expr := do
  let d ← withCurrHeartbeats (DeclarationReduction.reduce φ)
  compileReduced ``dependent? "declaration_dependent_reduce" d

@[term_elab declarationStaticReductionTerm]
def elabDeclarationStaticReduction : Term.TermElab := fun stx _ =>
  elaborate ``static? "declaration_static_reduce" stx

@[term_elab declarationCheckedReductionTerm]
def elabDeclarationCheckedReduction : Term.TermElab := fun stx _ =>
  elaborate ``checked? "declaration_checked_reduce" stx

@[term_elab declarationParameterReductionTerm]
def elabDeclarationParameterReduction : Term.TermElab := fun stx _ =>
  elaborate ``parameter? "declaration_parameter_reduce" stx

@[term_elab declarationInputReductionTerm]
def elabDeclarationInputReduction : Term.TermElab := fun stx _ => do
  compileInput (← Term.elabTerm stx[1] none)

@[term_elab declarationTraceReductionTerm]
def elabDeclarationTraceReduction : Term.TermElab := fun stx _ =>
  elaborate ``trace? "declaration_trace_reduce" stx

@[term_elab declarationDependentReductionTerm]
def elabDeclarationDependentReduction : Term.TermElab := fun stx _ => do
  compileDependent (← Term.elabTerm stx[1] none)

end Solidity.DeclarationReduction
