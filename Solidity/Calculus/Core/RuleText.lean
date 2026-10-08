import Solidity.Calculus.Rules
import Solidity.Calculus.Core.DelabLean

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
      -- the judgement as each namespace names it: `dl[LeanTaclet C k]{ … }`
      let t := (← Lean.Meta.ppExpr body).pretty 100000
      return (t.replace "dl[Solidity.Core." "dl[").replace "dl[Solidity." "dl[" |>.replace "dl[Core." "dl["

/-- The judgements compared: today's and the scoped one of the same name. -/
def judgements : List Lean.Name := [`Taclet, `LeanTaclet]

/-- Today's text of the rule `J.r` and its scoped twin's, if both exist. -/
def texts (J : Lean.Name) (r : String) : MetaM (Option (String × String)) := do
  let c := `Solidity ++ J ++ Lean.Name.mkSimple r
  let c' := `Solidity.Core ++ J ++ Lean.Name.mkSimple r
  unless (← getEnv).contains c && (← getEnv).contains c' do return none
  return some (← ruleLine c, ← ruleLine c')

/-- The rules of today's judgement `J` whose scoped twin is missing or
prints otherwise, and how many there are in all. -/
def mismatches (J : Lean.Name) : MetaM (Nat × Array String) := do
  let some (.inductInfo old) := (← getEnv).find? (`Solidity ++ J) | throwError "no `{J}`"
  let mut bad := #[]
  for c in old.ctors do
    let r := c.getString!
    match ← texts J r with
    | some (a, b) => if a != b then bad := bad.push r
    | none => bad := bad.push r
  return (old.ctors.length, bad)

/-- Every rule line the scoped tables do not print as today's, by name. -/
elab "#check_rule_text" : command => liftTermElabM do
  for J in judgements do
    let (n, bad) ← mismatches J
    if bad.isEmpty then logInfo m!"all {n} rules of `{J}` print as their scoped twins"
    else
      logInfo m!"{n - bad.size} of {n} rules of `{J}` print as their scoped twins; not these:\n\
        {"\n".intercalate bad.toList}"

/-- The rule `J.r`, as today's table prints it and as the scoped one does. -/
elab "#rule_text " J:ident r:ident : command => liftTermElabM do
  match ← texts J.getId r.getId.toString with
  | some (a, b) => logInfo m!"today:  {a}\nscoped: {b}"
  | none => throwError "no rule `{J.getId}.{r.getId}` in both tables"

/-! The lines the scoped printer does not render yet (`docs/intrinsic.md`,
W1 "rules"): a hole's statement (`lhs = …`, `tgt = mv`: `SHole.fill` and
its kin), `⊕⊕`'s value (`Tms.Term.bumped`), a call's inlining
(`Premise.expandCall`), a `try` with schema binders (`rets`, `code`), and a
block weakened inside a premise's program (`Prog.up`, which
`Calculus/Core/Delab.lean`'s `progPieces` unfolds before it looks for `up`).
`functionCallArgCapture` is stated without a line: today's escapes to the
untyped call (`‹.call f args hsep ret body›`). -/

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
---
info: 7 of 9 rules of `LeanTaclet` print as their scoped twins; not these:
functionCallArgCapture
tryCallDiamond
-/
#guard_msgs in
#check_rule_text

end Solidity.Core.RuleText
