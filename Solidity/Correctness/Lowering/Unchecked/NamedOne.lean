import Solidity.Correctness.Lowering.Unchecked.RawOne
import Solidity.Correctness.Lowering.Unchecked.WordOne
import Solidity.Syntax.Elab.Context

/-!
# Named raw/output/program association for one updates

Guards checking a correctly shaped assignment to the wrong named slot. The
total boundary composes actual raw-tree checks, supplied-program checks, and
the production newest-binding resolver in the supplied typed incoming
context. Merely finding that name at the slot is insufficient under shadowing.
It does not certify
that this context is the producer's context or the Source typing context;
NCtx also erases original integer widths. Those provenance, width, Source-mode,
state and resource obligations remain unproved.
-/
namespace Solidity.Correctness.Lowering.Unchecked
open Solidity.Lowering.V07

/-- Static association of all three supplied boundary objects. -/
structure NamedOneAssociation {C : Contract} [FreshNames] (context : NCtx)
    (input output : RawStmt) (program : Prog C context.ctx context.ctx) where
  raw : RawOneAssociation input output
  typed : WordOneAssociation raw.source.inc program
  binding : ((context.find (Var.ofName raw.source.name) (.val .uint)).toOption.map Subtype.val) =
    some typed.target.slot

/-- A total association checker; it accepts no execution equations. Explicit
rejections remain coverage gaps. This is the initial named uint256/local
boundary, not the complete uncheckStmts validator or a PassCorrect factory. -/
def checkNamedOne {C : Contract} [FreshNames] (context : NCtx) (input output : RawStmt)
    (program : Prog C context.ctx context.ctx) : Option (NamedOneAssociation context input output program) := do
  let raw ← checkRawOne input output
  let typed ← checkWordOne raw.source.inc program
  if binding : ((context.find (Var.ofName raw.source.name) (.val .uint)).toOption.map Subtype.val) =
      some typed.target.slot then
    some ⟨raw, typed, binding⟩
  else none

/-- Static boundary evidence derives the actual supplied model-program run
and Source arithmetic result from one initial local observation. This does
not replace the missing Source statement/context or failure/resource bridge. -/
theorem namedOne_run {D : Source.Layout} {C : Contract} [FreshNames] (context : NCtx)
    (input output : RawStmt) (program : Prog C context.ctx context.ctx)
    (certificate : NamedOneAssociation context input output program)
    (target : State C context.ctx) (x : Int)
    (range : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (read : TEnv.get certificate.typed.target.slot target.env = integerValue Source.IntTy.u256 x range) :
    ∃ (sourceResult : Source.Val D (.int Source.IntTy.u256)) (modelResult : PrimTy.uint.Denote),
      Source.binVal false (if certificate.raw.source.inc then .add else .sub)
        (.int x range) (.int 1 (integerOne_range Source.IntTy.u256)) = .ok sourceResult ∧
      IntValueRel Source.IntTy.u256 sourceResult modelResult ∧
      program.run target = .ok (⟨target.setLocal certificate.typed.target.slot modelResult,
        List.prefix_refl _⟩ : Out C target.H context.ctx) := by
  exact wordOne_run target certificate.raw.source.inc program certificate.typed x range read

#print axioms namedOne_run

end Solidity.Correctness.Lowering.Unchecked
