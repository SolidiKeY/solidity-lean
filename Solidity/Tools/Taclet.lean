import Solidity.Calculus.Core.PrintedRules
import Solidity.Calculus.Core.Callback
import Solidity.Calculus.Core.DelabLean
import Solidity.Tools.Common

/-!
# `#taclet`: a rule of the calculus

```
#taclet storageFieldWriteSave
#taclet "storageFieldWriteCaptureSrc"
```

`#taclet r` prints a rule: its statement (the delaborator shows it as
`dl{ ⟨[ s; ]⟩ ⇝ p }`, `Calculus/Core/Delab.lean`), the solkey taclets it
transcribes and their `\heuristics`, the printed rule, and what makes it
sound.  `r` is a constructor of the scoped `Core.Taclet`, `Core.LeanTaclet`
or `Core.CallbackTaclet`, or a KeY taclet's name (an identifier or a
string), looked up backwards in the scoped table
(`Core.RuleShapes.tacletOrigins`, `Calculus/Core/RuleShapes.lean`).  A
scoped taclet is sound as its premise is the one `Stmt.step` builds
(`Core.Taclet.toStep`), which `Core.Stmt.Sound` makes sound.
-/

namespace Solidity.Tools

open Semantics

open Lean Elab Command Term Meta

/-! ## `#taclet` -/

/-- A `\heuristics` rule set as the `.key` files spell it. -/
def Heuristic.keyName : Heuristic → String
  | .simplifyProg => "simplify_prog"
  | .simplifyExpression => "simplify_expression"
  | .concreteSolidity => "concrete_solidity"
  | .simplifyProgExpensive => "simplify_prog_expensive"

/-- A KeY taclet with its rule set: `storageFieldWriteSave (simplify_prog)`. -/
def KeyTaclet.fmt (t : KeyTaclet) : String := s!"{t.name} ({Heuristic.keyName t.heuristic})"

/-- The scoped callback rows: today's (`RuleShapes.callbackOrigins`,
`PrintedRules.callbackPrintedOrigins`) under the scoped names. -/
def callbackRows {α : Type} (rows : List (Lean.Name × α)) : List (Lean.Name × α) :=
  rows.map fun (n, o) => (Core.RuleShapes.scopedName n, o)

/-- The KeY taclets of a constructor, one line. -/
def keyLine (n : Lean.Name) : String :=
  match lookupBy n (Core.RuleShapes.tacletOrigins ++ callbackRows RuleShapes.callbackOrigins) with
  | some (.taclet t) => s!"solkey: {KeyTaclet.fmt t}"
  | some (.merged ts) => "solkey (merged): " ++ ", ".intercalate (ts.map KeyTaclet.fmt)
  | none =>
    -- solkey's taclets past the pinned checkout (`ed7849d5b6`), unwinding bounded here
    if n == ``Core.LeanTaclet.whileUnwind then "solkey: whileUnwind (loop_expand), past the pin"
    else if n == ``Core.LeanTaclet.whileInvariantBox then
      "solkey: whileInvariantBox (loop_inv), past the pin"
    else if n == ``Core.LeanTaclet.whileInvariantDiamond then
      "solkey: whileInvariantDiamond (loop_inv), past the pin"
    else "solkey: none (a rule solkey does not have)"

/-- The printed rule of a constructor, one line. -/
def texLine (n : Lean.Name) : String :=
  let rows := Core.PrintedRules.printedOrigins ++ Core.PrintedRules.leanPrintedOrigins ++
    callbackRows PrintedRules.callbackPrintedOrigins
  match lookupBy n rows with
  | some (.printed p) => s!"printed: {p.name}"
  | some (.merged ps) => "printed (merged): " ++ ", ".intercalate (ps.map PrintedRule.name)
  | some (.leanOnly .keyTier) => "printed: none (a solkey taclet not printed)"
  | some (.leanOnly .calculus) => "printed: none (theory only Lean has)"
  | none => "printed: not tabled"

/-- What makes the constructor `n` sound: its premise is the one `Stmt.step`
builds (`toStep`), which `Core.Stmt.Sound` makes sound; a callback rule's
reading is `Core.ProvesC.sound_of`'s. -/
def soundLine (n : Lean.Name) : String :=
  let family := n.getPrefix
  if family == ``Core.CallbackTaclet then
    s!"sound: {family}.toStep (the premise is Stmt.step's; Core.Stmt.Sound, Core.ProvesC.sound_of)"
  else s!"sound: {family}.toStep (the premise is Stmt.step's; Core.Stmt.Sound)"

/-- Everything `#taclet` says of the constructor `n`. -/
def tacletInfo (n : Lean.Name) : MetaM MessageData := do
  let info ← getConstInfo n
  return m!"{n} : {info.type}\n{keyLine n}\n{texLine n}\n{soundLine n}"

/-- The rule families, in the order a bare name is looked up. -/
def ruleFamilies : List Lean.Name :=
  [``Core.Taclet, ``Core.LeanTaclet, ``Core.CallbackTaclet]

/-- The constructor a name denotes: `storageFieldWriteSave`,
`Taclet.storageFieldWriteSave`, `Core.Taclet.storageFieldWriteSave`, or a
full name. -/
def resolveRule (id : Lean.Name) : MetaM (Option Lean.Name) := do
  let env ← getEnv
  let cands := id :: (`Solidity ++ id) :: (`Solidity.Core ++ id) :: ruleFamilies.map (· ++ id)
  return cands.find? fun c => env.contains c && ruleFamilies.contains c.getPrefix &&
    (env.find? c).any (·.isCtor)

/-- `#taclet r`, for a KeY taclet's name: the constructors that transcribe it. -/
def keyTacletInfo (s : String) : MetaM MessageData := do
  let rows := (Core.RuleShapes.tacletOrigins ++ callbackRows RuleShapes.callbackOrigins).filter
    fun r => r.2.taclets.any (·.name == s)
  match KeyTaclet.all.find? (·.name == s) with
  | none => throwError "#taclet: {s} is neither a rule of the calculus nor a solkey taclet"
  | some t =>
    if rows.isEmpty then
      return m!"solkey: {KeyTaclet.fmt t}\nno Lean rule claims it \
        (`Core.RuleShapes.unclaimedTaclets` says why)"
    let mut out := m!"solkey: {KeyTaclet.fmt t}, transcribed by"
    for (n, _) in rows do
      out := out ++ m!"\n\n" ++ (← tacletInfo n)
    return out

/-- `#taclet r`: a rule of the calculus, or a solkey taclet by its `.key`
name (as an identifier or a string). -/
syntax (name := tacletCmd) "#taclet " (ident <|> str) : command

/-- `#taclet` prints a rule in KeY's long forms (`pp.sol.key`): `consr(sp, fld)`,
`find(storage, consr(sp, size))`. -/
def withKeyForms {α : Type} (x : TermElabM α) : TermElabM α :=
  withOptions (fun o => pp.sol.key.set o true) x

@[command_elab tacletCmd] def elabTaclet : CommandElab
  | `(#taclet $s:str) => liftTermElabM <| withKeyForms do logInfo (← keyTacletInfo s.getString)
  | `(#taclet $id:ident) => liftTermElabM <| withKeyForms do
    match ← resolveRule id.getId with
    | some n => logInfo (← tacletInfo n)
    | none => logInfo (← keyTacletInfo id.getId.toString)
  | _ => throwUnsupportedSyntax


end Solidity.Tools
