import Solidity.Calculus.Callback
import Solidity.Calculus.PrintedRules
import Solidity.Calculus.RuleSoundness
import Solidity.Calculus.SoundUpdate
import Solidity.Tools.Common

/-!
# `#taclet`: a rule of the calculus

```
#taclet storageFieldWriteSave
#taclet "storageFieldWriteCaptureSrc"
```

`#taclet r` prints a rule: its statement (the delaborator shows it as
`dl{ ⟨[ s; ]⟩ ⇝ p }`), the solkey taclets it transcribes and their
`\heuristics`, the printed rule, and the theorem that makes it sound.  `r` is a
constructor of `Taclet`, `LeanTaclet` or `CallbackTaclet` (or of the scoped
`Core.Taclet`, printed where `Calculus/Core/Delab.lean` is imported), or a KeY taclet's
name (an identifier or a string), looked up backwards in
`RuleShapes.tacletOrigins`.

It reads today's rule tables (`RuleShapes`, `PrintedRules`) and names
today's constructors and soundness theorems first, so it stays on today's
calculus until W4 deletes it (`docs/intrinsic.md`, W4): a switch to the
scoped families prints `Core.Taclet.*`, a change of pins W5 allows.
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

/-- A scoped taclet (`Calculus/Core/Taclet.lean`) is looked up as today's
of the same name: it transcribes the same solkey taclets. -/
def coreTwin (n : Lean.Name) : Lean.Name :=
  if (`Solidity.Core.Taclet).isPrefixOf n then n.replacePrefix `Solidity.Core `Solidity else n

/-- The KeY taclets of a constructor, one line. -/
def keyLine (n : Lean.Name) : String :=
  let n := coreTwin n
  match lookupBy n (RuleShapes.tacletOrigins ++ RuleShapes.callbackOrigins) with
  | some (.taclet t) => s!"solkey: {KeyTaclet.fmt t}"
  | some (.merged ts) => "solkey (merged): " ++ ", ".intercalate (ts.map KeyTaclet.fmt)
  | none =>
    -- solkey's taclets past the pinned checkout (`ed7849d5b6`), unwinding bounded here
    if n == ``LeanTaclet.whileUnwind then "solkey: whileUnwind (loop_expand), past the pin"
    else if n == ``LeanTaclet.whileInvariantBox then
      "solkey: whileInvariantBox (loop_inv), past the pin"
    else if n == ``LeanTaclet.whileInvariantDiamond then
      "solkey: whileInvariantDiamond (loop_inv), past the pin"
    else "solkey: none (a rule solkey does not have)"

/-- The printed rule of a constructor, one line. -/
def texLine (n : Lean.Name) : String :=
  let n := coreTwin n
  let rows := PrintedRules.printedOrigins ++ PrintedRules.leanPrintedOrigins ++
    PrintedRules.callbackPrintedOrigins
  match lookupBy n rows with
  | some (.printed p) => s!"printed: {p.name}"
  | some (.merged ps) => "printed (merged): " ++ ", ".intercalate (ps.map PrintedRule.name)
  | some (.leanOnly .keyTier) => "printed: none (a solkey taclet not printed)"
  | some (.leanOnly .calculus) => "printed: none (theory only Lean has)"
  | none => "printed: not tabled"

/-- The theorem that makes the constructor `n` sound: by its family, and for
a `Taclet` by its premise's kind; with the per-rule update lemma
`Solidity.upd_<n>` when there is one (`upd_send_cases` for a send's). -/
def soundLine (n : Lean.Name) (ty : Lean.Expr) : MetaM String := do
  let env ← getEnv
  let family := n.getPrefix
  -- a scoped taclet: its premise is `Stmt.step`'s, which `Core.Stmt.Sound` makes sound
  if family == `Solidity.Core.Taclet || family == `Solidity.Core.LeanTaclet then
    return s!"sound: {family}.toStep (the premise is Stmt.step's; Core.Stmt.Sound)"
  let thm ← if n == ``CallbackTaclet.tryCallWithCallbackBox then pure ``CallbackTaclet.sound_branches
    else if n == ``CallbackTaclet.sendWithCallbackBox then pure ``CallbackTaclet.sound_send
    else if family == ``CallbackTaclet then pure ``CallbackTaclet.sound
    else if family == ``LeanTaclet then pure ``LeanTaclet.sound
    else forallTelescopeReducing ty fun _ concl => do
      let p := concl.getAppArgs.back?.getD concl
      pure <| match p.getAppFn.constName? with
        | some ``Premise.update => ``Taclet.sound_update
        | some ``Premise.unfold => ``Taclet.sound_unfold
        | some ``Premise.split => ``Taclet.sound_split
        | some ``Premise.check => ``Taclet.sound_check
        | some ``Premise.done => ``Taclet.sound_done
        | some ``Premise.branches => ``Taclet.sound_branches
        | some ``Premise.cases => ``Taclet.sound_cases
        | _ => ``Taclet.sound
  let upd := Name.mkStr `Solidity ("upd_" ++ n.getString!)
  -- a send's two outcomes are one lemma for both modalities
  let upd := if thm == ``Taclet.sound_cases then ``upd_send_cases else upd
  let extra := if env.contains upd then s!", {upd}" else ""
  return s!"sound: {thm}{extra}"

/-- Everything `#taclet` says of the constructor `n`. -/
def tacletInfo (n : Lean.Name) : MetaM MessageData := do
  let info ← getConstInfo n
  let snd ← soundLine n info.type
  return m!"{n} : {info.type}\n{keyLine n}\n{texLine n}\n{snd}"

/-- The rule families, in the order a bare name is looked up. -/
def ruleFamilies : List Lean.Name :=
  [``Taclet, ``LeanTaclet, ``CallbackTaclet, `Solidity.Core.Taclet]

/-- The constructor a name denotes: `storageFieldWriteSave`,
`Taclet.storageFieldWriteSave`, or a full name. -/
def resolveRule (id : Lean.Name) : MetaM (Option Lean.Name) := do
  let env ← getEnv
  let cands := id :: (`Solidity ++ id) :: ruleFamilies.map (· ++ id)
  return cands.find? fun c => env.contains c && ruleFamilies.contains c.getPrefix &&
    (env.find? c).any (·.isCtor)

/-- `#taclet r`, for a KeY taclet's name: the constructors that transcribe it. -/
def keyTacletInfo (s : String) : MetaM MessageData := do
  let rows := (RuleShapes.tacletOrigins ++ RuleShapes.callbackOrigins).filter fun r =>
    r.2.taclets.any (·.name == s)
  match KeyTaclet.all.find? (·.name == s) with
  | none => throwError "#taclet: {s} is neither a rule of the calculus nor a solkey taclet"
  | some t =>
    if rows.isEmpty then
      return m!"solkey: {KeyTaclet.fmt t}\nno Lean rule claims it \
        (`RuleShapes.unclaimedTaclets` says why)"
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
