import Lean

namespace Solidity.Goal

open Lean Meta Elab Command

opaque Unstated : Prop

structure Entry where
  decl : Name
  proof : Name
  deps : Array Name
  plan : Option String
deriving Inhabited

initialize goalExt : SimplePersistentEnvExtension Entry (Array Entry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[] }

syntax (name := goal) "goal " ident (ppSpace str)? (" ← " ident+)? : attr

initialize registerBuiltinAttribute {
  name := `goal
  descr := "a roadmap goal: a `Prop` definition and the theorem name expected to prove it"
  applicationTime := .afterTypeChecking
  add := fun decl stx kind => do
    unless kind == .global do throwError "goal: global attribute only"
    let ci ← getConstInfo decl
    unless ci.type == .sort .zero do throwError "goal: {decl} must be a definition of type Prop"
    let proof := stx[1].getId
    let step := stx[2].getOptional?.bind (·.isStrLit?)
    let deps ← match stx[3].getOptional? with
      | some g => g[1].getArgs.mapM fun d => realizeGlobalConstNoOverloadWithInfo d
      | none => pure #[]
    modifyEnv (goalExt.addEntry · { decl, proof, deps, plan := step })
}

inductive Status where
  | proved | open | unstated | mismatch | sorried
deriving BEq, Inhabited

def Status.label : Status → String
  | .proved => "proved"
  | .open => "open"
  | .unstated => "unstated"
  | .mismatch => "mismatch"
  | .sorried => "sorry"

def status (e : Entry) : MetaM Status := do
  let env ← getEnv
  if let some (.defnInfo d) := env.find? e.decl then
    if d.value.isConstOf ``Unstated then return .unstated
  let some pi := env.find? e.proof | return .open
  let us := pi.levelParams.map Level.param
  let ty := pi.instantiateTypeLevelParams us
  unless ← withoutModifyingState (isDefEq ty (mkConst e.decl)) do return .mismatch
  if (← collectAxioms e.proof).contains ``sorryAx then return .sorried
  return .proved

def statuses : MetaM (Array (Entry × Status)) := do
  let es := goalExt.getState (← getEnv)
  es.mapM fun e => return (e, ← status e)

def report (rs : Array (Entry × Status)) : String :=
  let proved (n : Name) := rs.any fun (e, s) => e.decl == n && s == .proved
  let line := fun ((e, s) : Entry × Status) =>
    let blocked := if s == .proved then [] else e.deps.toList.filter (! proved ·)
    let tail := (if blocked.isEmpty then "" else s!" blocked by {blocked}") ++
      (e.plan.map (s!" plan {·}") |>.getD "")
    s!"{s.label} {e.decl} ← {e.proof}{tail}"
  "\n".intercalate (rs.toList.map line)

elab "#roadmap" : command => do
  let rs ← liftTermElabM statuses
  logInfo (report rs)

end Solidity.Goal
