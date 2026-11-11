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
    -- `(" ← " ident+)?` parses to a null node holding the arrow and the identifiers:
    -- two children, so `getOptional?` (one child) would silently drop every dependency.
    let deps ← match stx[3].getArgs with
      | #[_, ids] => ids.getArgs.mapM fun d => realizeGlobalConstNoOverloadWithInfo d
      | #[] => pure #[]
      | _ => throwError "goal: malformed dependency list"
    modifyEnv (goalExt.addEntry · { decl, proof, deps, plan := step })
}

inductive Status where
  | proved | open | unstated | mismatch | sorried | assumed
deriving BEq, Inhabited

def Status.label : Status → String
  | .proved => "proved"
  | .open => "open"
  | .unstated => "unstated"
  | .mismatch => "mismatch"
  | .sorried => r"sorry"
  | .assumed => "assumed"

def status (e : Entry) : MetaM Status := do
  let env ← getEnv
  if let some (.defnInfo d) := env.find? e.decl then
    if d.value.isConstOf ``Unstated then return .unstated
  let some pi := env.find? e.proof | return .open
  let us := pi.levelParams.map Level.param
  let ty := pi.instantiateTypeLevelParams us
  unless ← withoutModifyingState (isDefEq ty (mkConst e.decl)) do return .mismatch
  let axioms ← collectAxioms e.proof
  if axioms.any (fun a => (mkConst a).isSorry) then return .sorried
  if pi matches .axiomInfo _ then return .assumed
  if axioms.any (fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound) then
    return .assumed
  return .proved

def statuses : MetaM (Array (Entry × Status)) := do
  let es := goalExt.getState (← getEnv)
  es.mapM fun e => return (e, ← status e)

/-- One line per goal selected by `only`; dependencies are looked up among all of `rs`. -/
def report (rs : Array (Entry × Status)) (only : Name → Bool := fun _ => true) : String :=
  let proved (n : Name) := rs.any fun (e, s) => e.decl == n && s == .proved
  let line := fun ((e, s) : Entry × Status) =>
    -- Even a proved goal lists its unproved dependencies: its theorem alone does not
    -- discharge them.
    let blocked := e.deps.toList.filter (! proved ·)
    let tail := (if blocked.isEmpty then "" else s!" blocked by {blocked}") ++
      (e.plan.map (s!" plan {·}") |>.getD "")
    s!"{s.label} {e.decl} ← {e.proof}{tail}"
  "\n".intercalate ((rs.toList.filter (only ·.1.decl)).map line)

elab "#roadmap" : command => do
  let rs ← liftTermElabM statuses
  logInfo (report rs)

/-- `#roadmap_goal g₁ … gₙ`: the `#roadmap` lines of the named goals only, so each goal
module pins its own status. -/
elab "#roadmap_goal " ids:ident+ : command => do
  let names ← ids.mapM fun i => liftCoreM <| realizeGlobalConstNoOverloadWithInfo i
  let rs ← liftTermElabM statuses
  for n in names do
    unless rs.any (·.1.decl == n) do throwError "#roadmap_goal: {n} carries no @[goal]"
  logInfo (report rs names.contains)

end Solidity.Goal
