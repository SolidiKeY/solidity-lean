import Solidity.Calculus.Core.Delab

/-!
# Every scoped rule prints as its old twin

`Calculus/Core/Rules.lean`'s lines are `Rules.lean`'s, copied verbatim
(`scripts/core-rules.mjs`, `scripts/check-rule-text.sh`); this module checks
that what they elaborate to prints back as the same text: for each
constructor of today's `Taclet`, its scoped twin of the same name, both
conclusions printed with the notation on (`Rules.lean`'s delaborator for
today's, `Calculus/Core/Delab.lean`'s for the scoped one), the two strings
compared.  A line the scoped printer does not render as today's is listed,
with both texts.
-/

namespace Solidity.Core.RuleText

open Lean Meta Elab Command

/-- The rule line of a constructor: its conclusion, printed on one line with
the notation on, its binders and side conditions left out. -/
def ruleLine (c : Lean.Name) : MetaM String := do
  forallTelescope (← getConstInfo c).type fun _ body =>
    withOptions (fun o => o.setBool `pp.sol.dl true) do
      return (← Lean.Meta.ppExpr body).pretty 100000

/-- Today's text of the rule `r` and its scoped twin's, if both exist. -/
def texts (r : String) : MetaM (Option (String × String)) := do
  let c := ``Solidity.Taclet ++ Lean.Name.mkSimple r
  let c' := ``Solidity.Core.Taclet ++ Lean.Name.mkSimple r
  unless (← getEnv).contains c && (← getEnv).contains c' do return none
  return some (← ruleLine c, ← ruleLine c')

/-- The rules of today's `Taclet` whose scoped twin is missing or prints
otherwise, and how many there are in all. -/
def mismatches : MetaM (Nat × Array String) := do
  let some (.inductInfo old) := (← getEnv).find? ``Solidity.Taclet | throwError "no `Taclet`"
  let mut bad := #[]
  for c in old.ctors do
    let r := c.getString!
    match ← texts r with
    | some (a, b) => if a != b then bad := bad.push r
    | none => bad := bad.push r
  return (old.ctors.length, bad)

/-- Every rule line the scoped table does not print as today's, by name. -/
elab "#check_rule_text" : command => liftTermElabM do
  let (n, bad) ← mismatches
  if bad.isEmpty then logInfo m!"all {n} rules of `Taclet` print as their scoped twins"
  else
    logInfo m!"{n - bad.size} of {n} rules of `Taclet` print as their scoped twins; not these:\n\
      {"\n".intercalate bad.toList}"

/-- The rule `r`, as today's table prints it and as the scoped one does. -/
elab "#rule_text " r:ident : command => liftTermElabM do
  match ← texts r.getId.toString with
  | some (a, b) => logInfo m!"today:  {a}\nscoped: {b}"
  | none => throwError "no rule `{r.getId}` in both tables"

/-! The lines the scoped printer does not render yet (`docs/intrinsic.md`,
W1 "rules"): a hole's statement (`lhs = …`, `tgt = mv`), `⊕⊕`'s value
(`Term.bumped`), a call's inlining (`Premise.expandCall`) and a `try`'s
binders, which `Calculus/Core/Delab.lean` does not translate. -/

/--
info: 140 of 158 rules of `Taclet` print as their scoped twins; not these:
storageFieldRead_unfold_rightFst
storageIndexRead_unfold_rightFst
storageIndexRead_unfold_rightSndIndex
ternaryToIf
ternaryCaptureCond
localAssignIncrement
storageRootIncrementAssignment
storageFieldIncrementAssignment
storageIndexIncrementAssignment
memoryFieldIncrementAssignment
memoryIndexArrayIncrementAssignment
memoryFieldRead_unfold_rightFst
memoryIndexRead_unfold_rightFst
memoryIndexRead_unfold_rightSndIndex
newArrayCapture
functionBodyExpand
internalCallExpand
tryCallNoCallbackBox
-/
#guard_msgs in
#check_rule_text

end Solidity.Core.RuleText
