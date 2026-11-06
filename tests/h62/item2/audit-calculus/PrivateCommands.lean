import tests.h62.item2.«audit-calculus».KernelCensus

/-! Resolve imported private constants by their actual numeric Lean names.
Delegated joint commands retain the existing exact telescope/verifier.
The term form uses universe-zero specialization for one closed audit instance;
ordinary kernel checking and the witness axiom gate remain in force. -/
namespace H62.AuditCalculus.PrivateCommands
open Lean Elab Command

private def resolvePrivate (module original : Name) : CoreM Name := do
  let actual := mkPrivateNameCore module original
  let _ ← getConstInfo actual
  let env ← getEnv
  let some idx := env.getModuleIdxFor? actual
    | throwError "private constant has no imported module"
  unless env.header.moduleNames[idx.toNat]! == module do
    throwError "private constant belongs to a different module"
  return actual

elab "#joint_private_premises " module:ident original:ident " as " target:ident : command => do
  let actual ← liftCoreM <| resolvePrivate module.getId original.getId
  let id := mkIdent actual
  elabCommand (← `(command| #joint_premises $id:ident as $target:ident))

elab "#verify_private_joint " module:ident original:ident " with " witness:ident : command => do
  let actual ← liftCoreM <| resolvePrivate module.getId original.getId
  let id := mkIdent actual
  elabCommand (← `(command| #verify_joint $id:ident with $witness:ident))

elab "private_const% " module:ident original:ident : term => do
  let actual ← liftM <| resolvePrivate module.getId original.getId
  let info ← getConstInfo actual
  return mkConst actual (info.levelParams.map (fun _ => Level.zero))

end H62.AuditCalculus.PrivateCommands
