import Solidity.Calculus.PrintedRules
import Solidity.Calculus.Callback
import Solidity.Calculus.DelabLean
import Solidity.Tools.Common

/-!
# `#taclet`: a rule of the calculus

```
#taclet storageFieldWriteSave
#taclet "storageFieldWriteCaptureSrc"
```

`#taclet r` prints a rule: its statement (the delaborator shows it as
`dl{ ⟨[ s; ]⟩ ⇝ p }`, `Calculus/Delab.lean`), the solkey taclets it
transcribes and their `\heuristics`, the printed rule, and what makes it
sound.  `r` is a constructor of the scoped `Taclet`, `LeanTaclet`
or `CallbackTaclet`, or a KeY taclet's name (an identifier or a
string), looked up backwards in the table
(`RuleShapes.tacletOrigins`, `Calculus/RuleShapes.lean`).  A
scoped taclet is sound as its premise is the one `Stmt.step` builds
(`Taclet.toStep`), which `Stmt.Sound` makes sound.

`#check_rule_text` checks that every rule prints as a rule line.
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

/-- The KeY taclets of a constructor, one line. -/
def keyLine (n : Lean.Name) : String :=
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
  let rows := PrintedRules.printedOrigins ++ PrintedRules.leanPrintedOrigins ++
    PrintedRules.callbackPrintedOrigins
  match lookupBy n rows with
  | some (.printed p) => s!"printed: {p.name}"
  | some (.merged ps) => "printed (merged): " ++ ", ".intercalate (ps.map PrintedRule.name)
  | some (.leanOnly .keyTier) => "printed: none (a solkey taclet not printed)"
  | some (.leanOnly .calculus) => "printed: none (theory only Lean has)"
  | none => "printed: not tabled"

/-- What makes the constructor `n` sound: its premise is the one `Stmt.step`
builds (`toStep`), which `Stmt.Sound` makes sound; a callback rule's
reading is `ProvesC.sound_of`'s. -/
def soundLine (n : Lean.Name) : String :=
  let family := n.getPrefix
  if family == ``CallbackTaclet then
    s!"sound: {family}.toStep (the premise is Stmt.step's; Stmt.Sound, ProvesC.sound_of)"
  else s!"sound: {family}.toStep (the premise is Stmt.step's; Stmt.Sound)"

/-- Everything `#taclet` says of the constructor `n`. -/
def tacletInfo (n : Lean.Name) : MetaM MessageData := do
  let info ← getConstInfo n
  return m!"{n} : {info.type}\n{keyLine n}\n{texLine n}\n{soundLine n}"

/-- The rule families, in the order a bare name is looked up. -/
def ruleFamilies : List Lean.Name :=
  [``Taclet, ``LeanTaclet, ``CallbackTaclet]

/-- The constructor a name denotes: `storageFieldWriteSave`,
`Taclet.storageFieldWriteSave`, or a full name. -/
def resolveRule (id : Lean.Name) : MetaM (Option Lean.Name) := do
  let env ← getEnv
  let cands := id :: (`Solidity ++ id) :: ruleFamilies.map (· ++ id)
  return cands.find? fun c => env.contains c && ruleFamilies.contains c.getPrefix &&
    (env.find? c).any (·.isCtor)

/-- `#taclet r`, for a KeY taclet's name: the constructors that transcribe it. -/
def keyTacletInfo (s : String) : MetaM MessageData := do
  let rows := (RuleShapes.tacletOrigins ++ RuleShapes.callbackOrigins).filter
    fun r => r.2.taclets.any (·.name == s)
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

/-! ## `#check_rule_text`

Every rule prints as a rule line: for each constructor of the three
families, its conclusion, printed with the notation on (`pp.sol.dl`, and
`pp.sol.ic` where its side condition makes the call KeY's `ic`), is a
`dl{ … }` (or `dl[J C k]{ … }`) line in today's KeY text, with no scoped
term left escaped: no escape `‹…›` names a scoped constant, printed with
full names (`‹Solidity.Val.…›`, `‹(Solidity.Upd.…).snd›`,
`‹@Solidity.Val.…›`, `‹Solidity.Ext.push …›`, `‹Solidity.Tms.STerm.save …›`;
`‹Solidity.Stmt.call …›`, `functionCallArgCapture`'s call, which has no
line of KeY's: `Calculus/DelabLean.lean`).  The constructors whose line does not print
are listed.  Today's rule table, which the scoped lines were once diffed
against (`docs/intrinsic.md`, decision 35), is gone; the lines are pinned
where each rule is shown (`#taclet`, `#check`). -/

/-- The rule line of a constructor: its conclusion, printed on one line
(with full names when `full`). -/
def ruleLine (c : Lean.Name) (full : Bool := false) : MetaM String := do
  let ty := (← getConstInfo c).type
  let ic := (Delab.callSide ty).any (·.isConstOf ``Bool.false)
  forallTelescope ty fun _ body =>
    withOptions (fun o => ((o.setBool `pp.sol.dl true).setBool `pp.sol.ic ic).setBool
        `pp.fullNames full) do
      return (← Meta.ppExpr body).pretty 100000

/-- The scoped families and namespaces besides `Delab.isScopedFamily`'s (the
ones that never had an erased twin), which the prefix `Solidity.Core` once
kept apart: the program's (`Stmt`, `Val`, …,
the holes, `Premise`), and every root of a type or a namespace that was
declared under it, but the shared vocabulary that only gained lemmas there
(`Contract`, `PrimTy`, `BinOp`, `Op0`–`Op3`, `Srt`, `Binds`, `Res`, `Value`,
`Delab`). -/
def scopedOnlyRoots : List Lean.Name :=
  [``Solidity.Stmt, ``Solidity.Prog, ``Solidity.Simple, ``Solidity.SPath, ``Solidity.Loc,
   ``Solidity.MPath, ``Solidity.MLoc, ``Solidity.Val, ``Solidity.Src, ``Solidity.ARhs,
   ``Solidity.MRhs, ``Solidity.NewLhs, ``Solidity.MSrc, ``Solidity.OpLoc, ``Solidity.CallRet,
   ``Solidity.ExtCall, ``Solidity.LoopAnn, ``Solidity.Args, ``Solidity.Binders,
   ``Solidity.CodeBinder, ``Solidity.SHole, ``Solidity.MHole, ``Solidity.VHole,
   ``Solidity.Frames, ``Solidity.Premise, ``Solidity.LTy,
   ``Solidity.ArrView, ``Solidity.BlockKind, ``Solidity.Branch,
   ``Solidity.CallbackTaclet, ``Solidity.COut, ``Solidity.Ctx,
   ``Solidity.ExecF, ``Solidity.ExecP, ``Solidity.ExecS, ``Solidity.Ext,
   ``Solidity.Fold, ``Solidity.FShape, ``Solidity.Grew,
   ``Solidity.Grown, ``Solidity.Heap, ``Solidity.Held, ``Solidity.HRef, ``Solidity.HTy,
   ``Solidity.Hyps, ``Solidity.LeanTaclet, ``Solidity.MFields, ``Solidity.MObj,
   ``Solidity.MVal, ``Solidity.NCtx, ``Solidity.Objs,
   ``Solidity.Out, ``Solidity.Path, ``Solidity.Proves, ``Solidity.ProvesC, ``Solidity.RemOk,
   ``Solidity.Rhs, ``Solidity.Rule, ``Solidity.RunInv,
   ``Solidity.SFields, ``Solidity.Shape, ``Solidity.SList, ``Solidity.SMap, ``Solidity.SRef,
   ``Solidity.StateInv, ``Solidity.Storage, ``Solidity.Subst,
   ``Solidity.SVal, ``Solidity.SVec, ``Solidity.Taclet, ``Solidity.TEnv, ``Solidity.TGFrame,
   ``Solidity.THalt, ``Solidity.Thin, ``Solidity.TLocAgree, `Solidity.TLoop, ``Solidity.TRes,
   `Solidity.TRun, ``Solidity.TStep, ``Solidity.TTx, ``Solidity.TWkRel, ``Solidity.TyLe,
   ``Solidity.TyLt, `Solidity.Tms, ``Solidity.VShape]

/-- Whether a full name printed in an escape is a scoped constant: it, or a
namespace it is in, is a scoped family (`Delab.isScopedFamily`) or one of
`scopedOnlyRoots`. -/
def isScopedName (tok : String) : Bool :=
  let rec go : Lean.Name → Bool
    | .anonymous => false
    | n@(.str p _) => n != `Solidity &&
        (Delab.isScopedFamily n || scopedOnlyRoots.contains n || go p)
    | .num p _ => go p
  tok.startsWith "Solidity." && tok != "Solidity.Stmt.call" && go tok.toName

/-- Whether a conclusion printed with full names is a rule line: the
judgement's delaborator wrote it, and no escape `‹…›` in it names a scoped
constant (a scoped term, however parenthesized or explicit). -/
def isRuleLine (t : String) : Bool :=
  t.startsWith "dl" && !((t.splitOn "‹").drop 1).any fun s =>
    (((s.splitOn "›").headD "").split fun c =>
      !(c.isAlphanum || c == '_' || c == '.' || c == '\'' || c == '?' || c == '!' ||
        c.toNat > 127)).any isScopedName

/-- The constructors of the family `J` whose line does not print, and how
many there are in all. -/
def unprinted (J : Lean.Name) : MetaM (Nat × Array Lean.Name) := do
  let some (.inductInfo i) := (← getEnv).find? J | throwError "no `{J}`"
  let mut bad := #[]
  for c in i.ctors do
    unless isRuleLine (← ruleLine c (full := true)) do bad := bad.push c
  return (i.ctors.length, bad)

/-- `#check_rule_text`: every rule of the three families prints as a rule
line; the ones that do not, by name. -/
elab "#check_rule_text" : command => liftTermElabM do
  for J in ruleFamilies do
    let (n, bad) ← unprinted J
    if bad.isEmpty then logInfo m!"all {n} rules of `{J}` print as rule lines"
    else
      logInfo m!"{n - bad.size} of {n} rules of `{J}` print as rule lines; not these:\n\
        {"\n".intercalate (bad.toList.map (·.getString!))}"

end Solidity.Tools
