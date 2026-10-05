import Solidity.Calculus.Chains
import Solidity.Calculus.Decide
import Solidity.Calculus.Callback
import Solidity.Calculus.PrintedRules
import Solidity.Tools.Common

/-!
# `#wp`, `#step`, `#taclet`: looking inside the calculus

```
#wp dl!{ [ alice.age = 42; uint x = alice.age; ] x == 42 }
#step dl!{ [ alice.age = 42; uint x = alice.age; ] x == 42 }
#taclet storageFieldWriteSave
#taclet "storageFieldWriteCaptureSrc"
```

* `#wp φ` runs the strategy to the end (`symex 200`, what `sol_symex` does)
  and prints what is left, the first-order formula whose validity is `φ`'s.
  When that formula is in `sol_decide`'s fragment (`Fml.inL`) it also prints
  its reduction (`Fml.reduce`): the updates pushed in and every read of a
  write eliminated, a formula over the initial state alone, printed by
  `LFml.fmt` (`find(storage, alice.age)`, `save(s, p, w)`, `∧`, `→`, `¬`).
* `#step φ` takes one step and names the rule, as a line of `#derivation`.
* `#taclet r` prints a rule: its statement (the delaborator shows it as
  `dl{ ⟨[ s; ]⟩ ⇝ p }`), the solkey taclets it transcribes and their
  `\heuristics`, the printed rule, and the theorem that makes it sound.  `r` is a
  constructor of `Taclet`, `LeanTaclet` or `CallbackTaclet`, or a KeY taclet's
  name (an identifier or a string), looked up backwards in
  `RuleShapes.tacletOrigins`.

`φ` must be a closed formula of a named contract (`elabFormula`), as for
`#derivation`: the strategy runs as compiled code (`unsafe evalExpr`) and
its result is quoted back against the contract's name.
-/

namespace Solidity.Tools

open Semantics Decide

/-! ## The reduced formula, printed -/

/-- A key shape as its test is named. -/
def KShape.fmt : KShape → String
  | .map => "isMap"
  | .fixed => "isFixed"

/-- A path whose keys are integer literals. -/
def LPath.total : LPath → Bool
  | .root _ => true
  | .field q _ => LPath.total q
  | .at q (.lit (.int _)) => LPath.total q
  | .at _ _ => false

/-- A guard that always returns, and is not printed: a literal, or the keys
of a path with literal keys (`ok(alice.age)`). -/
def LTerm.total : LTerm → Bool
  | .lit _ | .env _ => true
  | .pok q => LPath.total q
  | _ => false

/-- The guards of a sequence and the value it returns: `seq d a` returns
`a` where `d` returns, and a guard that is itself a sequence contributes its
guards and its value. -/
def LTerm.guards : LTerm → List LTerm × LTerm
  | .seq d a =>
    let (gd, vd) := LTerm.guards d
    let (ga, va) := LTerm.guards a
    (gd ++ [vd] ++ ga, va)
  | t => ([], t)

/-- A memory name, its root ordinal and its literal path: `#0.account`. -/
def LId.fmt (i : LId) : String :=
  i.path.foldl (fun acc a => match a with
    | .field f => s!"{acc}.{f}"
    | .at k => s!"{acc}[{k}]") s!"#{i.root}"

mutual
/-- A term of the target language. -/
partial def LTerm.fmt [FreshNames] : LTerm → String
  | .lit v => Value.fmt v
  | .var x => toString x
  | .binop op _ a b => s!"{LTerm.fmtArg a} {BinOp.sym op} {LTerm.fmtArg b}"
  | .unop op _ a => s!"{UnOp.sym op}{LTerm.fmtArg a}"
  | .ite c a b => s!"{LTerm.fmtArg c} ? {LTerm.fmtArg a} : {LTerm.fmtArg b}"
  | .find s q => s!"find({LStor.fmt s}, {LPath.fmt q})"
  | .has s q => s!"has({LStor.fmt s}, {LPath.fmt q})"
  | .kmap sh s q => s!"{KShape.fmt sh}({LStor.fmt s}, {LPath.fmt q})"
  | .len s q => s!"length({LStor.fmt s}, {LPath.fmt q})"
  | .sok s => s!"ok({LStor.fmt s})"
  | .pok q => s!"ok({LPath.fmt q})"
  | t@(.seq ..) =>
    let (gs, v) := LTerm.guards t
    let gs := (gs.filter (!LTerm.total ·)).map LTerm.fmt |>.eraseDups
    if gs.isEmpty then LTerm.fmt v else s!"({", ".intercalate gs}; {LTerm.fmt v})"
  | .orElse a b => s!"orElse({LTerm.fmt a}, {LTerm.fmt b})"
  | .kite a b t e => s!"({LTerm.fmt a} ≡ {LTerm.fmt b} ? {LTerm.fmt t} : {LTerm.fmt e})"
  | .zero a => s!"zero({LTerm.fmt a})"
  | .err => "err"
  | .env k => k.toStr
  | .findP s q => s!"find({LStor.fmt s}, {LPath.fmt q})"
  | .cpok s q => s!"copyOk({LStor.fmt s}, {LPath.fmt q})"

/-- A term as an operand: parenthesised unless it is atomic. -/
partial def LTerm.fmtArg [FreshNames] : LTerm → String
  | t@(.binop ..) | t@(.ite ..) => s!"({LTerm.fmt t})"
  | t => LTerm.fmt t

/-- A path, the root first: `alice.account.balance`, `balances[k]`. -/
partial def LPath.fmt [FreshNames] : LPath → String
  | .root r => r
  | .field q f => s!"{LPath.fmt q}.{f}"
  | .at q k => s!"{LPath.fmt q}[{LTerm.fmt k}]"

/-- A storage: `storage`, and the writes on top of it. -/
partial def LStor.fmt [FreshNames] : LStor → String
  | .init => "storage"
  | .save s q w => s!"save({LStor.fmt s}, {LPath.fmt q}, {LTerm.fmt w})"
  | .del s q => s!"del({LStor.fmt s}, {LPath.fmt q})"
  | .arr .push s q w => s!"push({LStor.fmt s}, {LPath.fmt q}, {LTerm.fmt w})"
  | .arr (.slot _) s q _ => s!"pushSlot({LStor.fmt s}, {LPath.fmt q})"
  | .arr (.pop _) s q _ => s!"pop({LStor.fmt s}, {LPath.fmt q})"
  | .copy s q src sq => s!"copy({LStor.fmt s}, {LPath.fmt q}, {LStor.fmt src}, {LPath.fmt sq})"
  | .view m i => s!"copyMem({LMem.fmt m}, {LId.fmt i})"

/-- A memory: `memory`, and the allocations and writes on top of it. -/
partial def LMem.fmt [FreshNames] : LMem → String
  | .init => "memory"
  | .addM m k _ => s!"addM({LMem.fmt m}, #{k})"
  | .newArr m k _ n => s!"newArr({LMem.fmt m}, #{k}, {LTerm.fmt n})"
  | .copySt m k s q => s!"copySt({LMem.fmt m}, #{k}, {LStor.fmt s}, {LPath.fmt q})"
  | .write m i a v => s!"write({LMem.fmt m}, {LId.fmt i}{LSel.fmt a}, {LMV.fmt v})"

/-- A selector: `.f`, `[t]`, `.size`. -/
partial def LSel.fmt [FreshNames] : LSel → String
  | .fld f => s!".{f}"
  | .idx t => s!"[{LTerm.fmt t}]"
  | .size => ".size"

/-- A memory value: a word, or a name. -/
partial def LMV.fmt [FreshNames] : LMV → String
  | .word t => LTerm.fmt t
  | .ref i => LId.fmt i
end

/-- A reduced formula: `∧` binds tighter than `→`, which associates to the
right. -/
partial def LFml.fmt [FreshNames] : LFml → String
  | .tt => "true"
  | .eq a b => s!"{LTerm.fmtArg a} == {LTerm.fmtArg b}"
  | .not φ => s!"¬{atom φ}"
  | .and φ ψ => s!"{conj φ} ∧ {conj ψ}"
  | .imp φ ψ => s!"{atom' φ} → {LFml.fmt ψ}"
  | .all x p φ => s!"∀ {p.toStr} {x}, {LFml.fmt φ}"
where
  atom : LFml → String
    | φ@(.tt) | φ@(.not _) => LFml.fmt φ
    | φ => s!"({LFml.fmt φ})"
  conj : LFml → String
    | φ@(.imp ..) => s!"({LFml.fmt φ})"
    | φ => LFml.fmt φ
  atom' : LFml → String
    | φ@(.imp ..) => s!"({LFml.fmt φ})"
    | φ => LFml.fmt φ

/-! ## What the commands evaluate -/

variable {C : Contract}

/-- What `#wp` shows of `φ`: the formula symbolic execution leaves, quoted
against the contract `c`, and its reduction when it is in the fragment. -/
def wpQuoted [FreshNames] (c : Lean.Expr) (φ : Fml C) : Lean.Expr × Option String :=
  let ψ := symex 200 φ
  (ψ.quote c, if ψ.inL Sym.empty then some (LFml.fmt ψ.reduce) else none)

/-- What `#step` shows of `φ`: the formula one step leaves, quoted. -/
def stepQuoted (c : Lean.Expr) (φ : Fml C) : Option Lean.Expr :=
  φ.step.map (·.quote c)

open Lean Elab Command Term Meta

/-- `#wp φ`: what symbolic execution leaves of `φ`, and, in `sol_decide`'s
fragment, its reduction to the initial state. -/
elab "#wp " t:term : command => liftTermElabM do
  let (φ, _, c) ← elabFormula "#wp" t
  let e ← mkAppM ``wpQuoted #[c, φ]
  let ty ← inferType e
  let (ψ, red) ← unsafe evalExpr (Lean.Expr × Option String) ty e
  let tail := match red with
    | some r => m!"\nupdate-free:\n    {r}"
    | none => m!"\noutside `sol_decide`'s fragment (`Fml.inL`): no reduction"
  logInfo (m!"symbolic execution leaves:\n    {ψ}" ++ tail)

/-- `#step φ`: one step of the strategy on `φ`, and the rule it fires. -/
elab "#step " t:term : command => liftTermElabM do
  let (φ, _, c) ← elabFormula "#step" t
  let e ← mkAppM ``stepQuoted #[c, φ]
  let ty ← inferType e
  match ← unsafe evalExpr (Option Lean.Expr) ty e with
  | none => logInfo "no modality left: `close`"
  | some ψ =>
    let r := match ← Chain.ruleOfLine φ with
      | some (_, n) => toString n
      | none => "?"
    logInfo m!"  ~[{r}]~>\n    {ψ}"

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
  | none => "solkey: none (a rule solkey does not have)"

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

/-- The theorem that makes the constructor `n` sound: by its family, and for
a `Taclet` by its premise's kind; with the per-rule update lemma
`Solidity.upd_<n>` when there is one. -/
def soundLine (n : Lean.Name) (ty : Lean.Expr) : MetaM String := do
  let env ← getEnv
  let family := n.getPrefix
  let thm ← if n == ``CallbackTaclet.tryCallWithCallbackBox then pure ``CallbackTaclet.sound_branches
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
        | _ => ``Taclet.sound
  let upd := Name.mkStr `Solidity ("upd_" ++ n.getString!)
  let extra := if env.contains upd then s!", {upd}" else ""
  return s!"sound: {thm}{extra}"

/-- Everything `#taclet` says of the constructor `n`. -/
def tacletInfo (n : Lean.Name) : MetaM MessageData := do
  let info ← getConstInfo n
  let snd ← soundLine n info.type
  return m!"{n} : {info.type}\n{keyLine n}\n{texLine n}\n{snd}"

/-- The rule families, in the order a bare name is looked up. -/
def ruleFamilies : List Lean.Name := [``Taclet, ``LeanTaclet, ``CallbackTaclet]

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

@[command_elab tacletCmd] def elabTaclet : CommandElab
  | `(#taclet $s:str) => liftTermElabM do logInfo (← keyTacletInfo s.getString)
  | `(#taclet $id:ident) => liftTermElabM do
    match ← resolveRule id.getId with
    | some n => logInfo (← tacletInfo n)
    | none => logInfo (← keyTacletInfo id.getId.toString)
  | _ => throwUnsupportedSyntax

end Solidity.Tools

