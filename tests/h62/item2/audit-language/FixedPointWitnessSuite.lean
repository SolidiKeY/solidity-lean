import tests.h62.item2.«audit-language».FixedPointWitness
import tests.h62.item2.«audit-language».FixedPointLawWitness
import tests.h62.item2.«audit-language».FixedPointAbiWitness
import tests.h62.item2.«audit-language».FixedPointStorageWitness
import tests.h62.item2.«audit-language».FixedPointLiteralWitness

/-!
Guarded regression: separately checked feasibility families must coexist without
namespace or imported-signature conflicts. This import suite checks composition;
family_coverage.py separately rejects duplicate target/witness credit. The suite
keeps closed counterexamples separate from positive input-tuple certificates.
The original expected telescope-mismatch control remains a negative test. No
whole-audit or compiler-success claim is made.
-/

-- Closed statements have no leading input tuple; do not invent a positive case.
example : fixed_hypotheses_of% Solidity.Language.FixedPoint.Fx.solc_lossy := True.intro

-- Retain the concrete lossy-solc counterexample, not a global conversion equality.
example :
    Solidity.Language.FixedPoint.FxTy.solcImplicit
      Solidity.Language.FixedPoint.Fx.fixed8x3 Solidity.Language.FixedPoint.Fx.ufixed8x3 = true ∧
    Solidity.Language.FixedPoint.FxTy.subsumes
      Solidity.Language.FixedPoint.Fx.fixed8x3 Solidity.Language.FixedPoint.Fx.ufixed8x3 = false ∧
    Solidity.Language.FixedPoint.FxTy.solcImplicit
      Solidity.Language.FixedPoint.Fx.ufixed8x3 Solidity.Language.FixedPoint.Fx.ufixed8x4 = true ∧
    Solidity.Language.FixedPoint.FxTy.subsumes
      Solidity.Language.FixedPoint.Fx.ufixed8x3 Solidity.Language.FixedPoint.Fx.ufixed8x4 = false :=
  Solidity.Language.FixedPoint.Fx.solc_lossy

open Lean Meta Elab Term

elab "#verify_closed_theorem " target:ident : command => do
  Lean.Elab.Command.liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo target
    let info ← getConstInfo name
    match info with
    | .thmInfo _ => pure ()
    | _ => throwError "closed theorem must be a theorem"
    unless (← isProp info.type) do
      throwError "closed theorem must have a proposition type"
    unless info.levelParams.isEmpty do
      throwError "closed theorem must be monomorphic"
    let type ← whnf info.type
    if type.isForall then
      throwError "closed theorem still has leading parameters"
    logInfo m!"H62_CLOSED_THEOREM {name}"

#verify_closed_theorem Solidity.Language.FixedPoint.Fx.solc_lossy

/-- error: closed theorem still has leading parameters -/
#guard_msgs in
#verify_closed_theorem Solidity.Language.FixedPoint.Fx.div_eq

/-- error: closed theorem must be a theorem -/
#guard_msgs in
#verify_closed_theorem Solidity.H62.AuditLanguage.FixedWitness.ty

#print axioms Solidity.Language.FixedPoint.Fx.solc_lossy
