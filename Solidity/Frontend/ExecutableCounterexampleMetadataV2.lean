import Solidity.Tools.DirectRuntime

/-! # Internal executable-goal reification for V2 intake

Prevents the regression of quoting the importer contract instead of the actual
executable contract: source declarations, operand schedules and every other
field remain literal data. Generic derived quotations reuse the existing raw
constructors; no parser, normalizer, builder or verifier is copied or rerun.

The resulting expressions are UNCHECKED until independently kernel checked.
This is not capture authentication, compiler adequacy, candidate failure or
metadata ingress. No certificate or source location is published here.
-/
namespace Solidity.Frontend.ExecutableMetadataV2.Internal
open Lean Solidity

-- Use Lean's generator, changing only its instance registration to local.
-- Its constructor quoting implementation and the shared source types stay unchanged.
section
run_cmd do
  let localKind ← `(Lean.Parser.Term.attrKind| local)
  for type in [``RawTy, ``RawExpr, ``RawInv, ``RawLoopSpec, ``OFMode,
      ``RawStmt, ``SpecExpr, ``SpecLoc, ``FunSpec, ``ModApp, ``FunDecl, ``EvalOrder] do
    let commands ← withFreshMacroScope <| Lean.Elab.Command.liftTermElabM <|
      Lean.Elab.Deriving.ToExpr.mkToExprInstanceCmds #[type]
    for command in commands do
      let localized := command.rewriteBottomUp fun node =>
        if node.isOfKind ``Lean.Parser.Command.instance then node.setArg 0 localKind else node
      Lean.Elab.Command.elabCommand localized

/-- Full literal constructor, including all proof fields. The existing Boolean
side conditions must reduce in the kernel; no proof is trusted by this quoter. -/
def quoteContract (C : Contract) : Expr :=
  mkAppN (mkConst ``Contract.mk) #[toExpr C.vars, toExpr C.transientRoots,
    rflTrue, toExpr C.funs, toExpr C.enums, toExpr C.inv, toExpr C.widths,
    toExpr C.ctor, toExpr C.inits, toExpr C.structs, toExpr C.errors,
    toExpr C.evalOrder, rflTrue, rflTrue]

/-- Reify the actual captured intrinsic target without rebuilding it. This may
be a listing or unsupported-to-certify capture: callers must independently
validate invocation ownership, branch, source and certificate admission. -/
def quoteGoal (goal : Tools.DirectRuntime.RequestGoalCaptureV2) : Expr × Expr :=
  let contract := quoteContract goal.contract
  (contract, Fml.quote contract goal.formula)

end

end Solidity.Frontend.ExecutableMetadataV2.Internal
