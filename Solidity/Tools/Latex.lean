import Solidity.Tools.LatexTerm

/-!
# The calculus's notation as LaTeX

LeanTeX's `#latex` composes ordinary mathematics with the scoped calculus.
`Solidity.Latex.exprLatex` returns a math fragment in `MetaM`; `declLatex`
exports a declaration's statement (hypotheses retained; parameters implicit
by default).  A scoped formula, `Fml.Valid`, a sequent (`Proves`) and a chain
(`Fml.Via`, `Fml.StepBy`, …) are read from their `Expr` by
`Tools/LatexTerm.lean`; a chain or a derivation (`derivationLatex`) is an
`aligned` environment, one line a row, a long line broken onto `\qquad` rows.

**A derivation's presentation** (`Options`): runs of bookkeeping steps
collapse into one `\rightsquigarrow^{*}` (`collapse`, `groups`); a leading
premise `A → ψ` is stated once as `\Gamma = \{A\}` (`premise`); an arrow
shows its rule over it, as a tag, or not (`labels`); a law's rewrite is
preceded by its instance and side conditions (`sides`).  A chain written as
a theorem keeps its links as written: only a generated derivation is
filtered.

The commands take options before their argument (`latexOpt`); the defaults
come from `set_option latex.sol.macros` and `latex.sol.width`.  The output is
for display, not a serialization to re-import as a proof.
-/

namespace Solidity.Latex

open Lean Meta Elab LeanTeX

/-! ## Layout -/

/-- A line as a fragment: one line, or an `aligned` environment of its rows. -/
def lineLatex (o : Options) (d : Doc) : String :=
  match d.lines o.width with
  | #[l] => l
  | ls => "\\begin{aligned}\n&" ++ " \\\\\n&\\qquad ".intercalate ls.toList ++ "\n\\end{aligned}"

/-- Rows of an `aligned` environment. -/
def alignedLatex (rows : Array String) : String :=
  "\\begin{aligned}\n" ++ " \\\\\n".intercalate rows.toList ++ "\n\\end{aligned}"

/-- A rule's name as a label. -/
def ruleLabel (o : Options) (r : String) : String :=
  if o.macros then "\\ruleName{" ++ escape r ++ "}" else "\\mathsf{" ++ escape r ++ "}"

/-! ## Side lines -/

/-- A step of a derivation: the rule that reached the line (`""` for one
unnamed step, `"~*>"` for several), the line, and the rewrite (`FmlRw`) it
was, if a rewrite. -/
structure Step where
  rule : String
  line : Expr
  rw? : Option Expr := none
  deriving Inhabited

/-- The first application of a law (`TermTaclet`, `EvalLaw`, `LitLaw`, or a
constant stating one) in a rewrite's `Expr`. -/
partial def findLawApp (e : Expr) : MetaM (Option Expr) := do
  let e := e.consumeMData
  match e with
  | .app .. =>
    if let some c := e.getAppFn.constName? then
      if (← Chain.lawKind? c).isSome then return some e
    for a in e.getAppArgs do
      if let some r ← findLawApp a then return some r
    return none
  | .lam _ _ b _ => findLawApp b
  | _ => return none

/-- The names of the scopes of the updates along a line's spine, outermost
first: where a law past the program applies (`Fml.spineScopes`, through
quantifiers, hidden binders and updates; here also a premise's consequent). -/
partial def spineScopes (ns : List Expr) (e : Expr) : RM (Array (List Expr)) := do
  let (ns, e) ← pr (Delab.viewF ns e)
  match_expr e with
  | Fml.upd _ _ _ _ U φ =>
    let (_, ms) ← Delab.updPiecesS ns U
    return #[ns] ++ (← spineScopes ms φ)
  | Fml.imp _ _ _ b => spineScopes ns b
  | Fml.all _ _ x _ φ => spineScopes (x.consumeMData :: ns) φ
  | _ => return #[]

/-- The last component of a name, as text. -/
def lastText (n : Lean.Name) : String :=
  match n with
  | .str _ s => s
  | .num _ k => toString k
  | .anonymous => ""

mutual

/-- A side condition's argument: a scoped term, a literal, a name. -/
partial def condArg (ns : List Expr) (a : Expr) : RM Doc := do
  let a ← instantiateMVars a
  let ty ← whnfR (← inferType a)
  if ty.isAppOf ``Tm then return ← tm ns a
  if let some n ← fvarName? a then return .ident n
  let a' := (← whnf a).consumeMData
  match a' with
  | .lit (.strVal s) => return .ident s
  | .lit (.natVal n) => return .tx (toString n) (toString n).length
  | _ => pure ()
  if a'.isConstOf ``Bool.true then return .kw "true"
  if a'.isConstOf ``Bool.false then return .kw "false"
  -- a member or root name, `"alice"`
  if (← whnfR ty).isConstOf ``Lean.Name then
    if let some n := a'.name? then return .ident n.toString
  condApp ns a

/-- `f(args)`, its explicit arguments, by the function's last name. -/
partial def condApp (ns : List Expr) (a : Expr) : RM Doc := do
  let some f := a.getAppFn.constName? | do
    let s := toString (← ppExpr a)
    return .tx ("\\text{" ++ escape s ++ "}") s.length
  let info ← getFunInfo a.getAppFn
  let args := a.getAppArgs
  let mut out := #[]
  for h : i in [0:args.size] do
    let explicit := match info.paramInfo[i]? with
      | some p => p.binderInfo.isExplicit
      | none => true
    if explicit then out := out.push (← condArg ns args[i])
  let n := lastText f
  if out.isEmpty then return .tx (identIt n) n.length
  return .app (.tx (identIt n) n.length) out

end

/-- A side condition (`p.diverges q = true`) read at `ns`. -/
def condDoc (ns : List Expr) (c : Expr) : RM Doc := do
  let c ← instantiateMVars c
  if let some (_, l, r) := c.eq? then
    if (← whnf r).isConstOf ``Bool.true then return ← condApp ns l
    if (← whnf r).isConstOf ``Bool.false then return .cat #[.tx "\\lnot " 1, ← condApp ns l]
    return .bin (← condArg ns l) "=" 1 (← condArg ns r)
  if c.isAppOfArity ``Ne 3 then
    return .bin (← condArg ns c.appFn!.appArg!) "\\ne" 1 (← condArg ns c.appArg!)
  if c.isAppOfArity ``Not 1 then
    if let some (_, l, r) := c.appArg!.eq? then
      return .bin (← condArg ns l) "\\ne" 1 (← condArg ns r)
    return .cat #[.tx "\\lnot " 1, ← condApp ns c.appArg!]
  condApp ns c

/-- A side condition not worth a reader's eye: a computation on values the
law's instance closes by evaluation (`… = some v` with no term of the
calculus in it: a literal fold, a length), or a test of a term against
itself (`sameSegs(p, p)`). -/
def condTrivial (c : Expr) : MetaM Bool := do
  let c ← instantiateMVars c
  let some (_, l, r) := c.eq? | return false
  -- a term of the calculus among the arguments: what the law reads, kept
  let readsTm ← l.getAppArgs.anyM fun a => return (← whnfR (← inferType a)).isAppOf ``Tm
  if (← whnf r).isAppOf ``Option.some then return !readsTm
  if (← whnf r).isConstOf ``Bool.true then
    let info ← getFunInfo l.getAppFn
    let args := l.getAppArgs
    let explicit := (List.range args.size).filterMap fun i =>
      if (info.paramInfo[i]?.map (·.binderInfo.isExplicit)).getD true then some args[i]! else none
    if let [a, b] := explicit then return a == b
  return false

/-- The side line of a law's rewrite: its instance `t ⇝ t'` and its side
conditions (`condTrivial` ones left out), the terms read at the scope of the
line before (`before`) whose length is the law's. -/
def sideDoc (rw : Expr) (before : List Expr × Expr) : RM (Option Doc) := do
  let some app ← findLawApp rw | return none
  let ty ← whnfR (← instantiateMVars (← inferType app))
  let some (t, t') := Chain.lawSides? ty | return none
  let tty ← whnfR (← inferType t)
  let n? ← if tty.isAppOfArity ``Tm 3 then Delab.ctxLength? (tty.getArg! 1) else pure none
  let scopes ← spineScopes before.1 before.2
  let ns := (n?.bind fun n => scopes.find? (·.length == n)).getD
    (List.replicate (n?.getD 0) Delab.unknownVar)
  -- the hypotheses of the law's constructor, instantiated
  let mut conds : Array Doc := #[]
  let mut fty ← inferType app.getAppFn
  for a in app.getAppArgs do
    unless fty.isForall do fty ← whnf fty
    let .forallE _ d b _ := fty | break
    if (← isProp d) && !(← condTrivial d.cleanupAnnotations) then
      conds := conds.push (← condDoc ns d.cleanupAnnotations)
    fty := b.instantiate1 a
  let core := Doc.bin (← tm ns t) "\\rightsquigarrow" 1 (← tm ns t')
  if conds.isEmpty then return some core
  return some (.cat #[core, .tx "\\qquad " 2, .paren (.sepBy (.tx ",\\ " 2) conds)])

/-! ## Derivations -/

/-- A line, its leading premise stripped where it is `hyp`. -/
def stripPremise (hyp? : Option (List Expr × Expr)) (e : Expr) : RM (List Expr × Expr) := do
  return (← stripPremise? hyp? e).1
where
  stripPremise? (hyp? : Option (List Expr × Expr)) (e : Expr) :
      RM ((List Expr × Expr) × Bool) := do
    let some (hns, hyp) := hyp? | return (([], e), false)
    let (ns, v) ← pr (Delab.viewF [] e)
    let_expr Fml.imp _ _ a ψ := v | return (([], e), false)
    let a ← instantiateMVars a
    -- the same premise where it prints the same: a line's is often unfolded
    if a == hyp || (← fml ns a).flat == (← fml hns hyp).flat then return ((ns, ψ), true)
    return (([], e), false)

/-- Whether a step is bookkeeping, to collapse. -/
def Options.collapses (o : Options) (s : Step) : Bool :=
  (o.groups && s.rule == "~*>") || o.collapse.contains s.rule

/-- Consecutive bookkeeping steps as one `~*>` (`"*"`), the last line kept. -/
def collapseSteps (o : Options) (steps : Array Step) : Array Step := Id.run do
  let mut out : Array Step := #[]
  let mut run : Option Step := none
  for s in steps do
    if o.collapses s then
      run := some { rule := "*", line := s.line }
    else
      if let some r := run then out := out.push r
      run := none
      out := out.push s
  if let some r := run then out := out.push r
  return out

/-- The arrow of a step, and its tag. -/
def arrowOf (o : Options) (rule : String) : String × String :=
  if rule.isEmpty then ("\\rightsquigarrow", "")
  else if rule == "~*>" || rule == "*" then ("\\rightsquigarrow^{*}", "")
  else match o.labelsOr with
    | .none => ("\\rightsquigarrow", "")
    | .over => ("\\overset{" ++ ruleLabel o rule ++ "}{\\rightsquigarrow}", "")
    | .tag => ("\\rightsquigarrow", " && (" ++ ruleLabel o rule ++ ")")

/-- A derivation from `first` through `steps`: its rows, the bookkeeping
collapsed when `filter`, the leading premise stated as `\Gamma` when the
options say so. -/
def derivationRows (first : Expr) (steps : Array Step) (filter : Bool) : RM (Array String) := do
  let o ← read
  let first ← instantiateMVars first
  -- the leading premise
  let hyp? ← if !(filter && o.premise) then pure none else do
    let (ns, v) ← pr (Delab.viewF [] first)
    let_expr Fml.imp _ _ a _ := v | pure none
    pure (some (ns, ← instantiateMVars a))
  let steps := if filter then collapseSteps o steps else steps
  let mut rows : Array String := #[]
  let (ns0, f0) ← stripPremise hyp? first
  let ls := (← fml ns0 f0).lines o.width
  rows := rows ++ ls.mapIdx fun i l => (if i == 0 then "&" else "&\\qquad ") ++ l
  let mut before := (ns0, f0)
  let mut last := (← fml ns0 f0).flat
  let mut held := hyp?.isSome
  for s in steps do
    let ((ns, e), has) ← stripPremise.stripPremise? hyp? (← instantiateMVars s.line)
    -- the step that drops the premise stated as `\Gamma` (`A → φ ⇝ φ`, a
    -- fold) prints as the line before it: left out
    let flat := (← fml ns e).flat
    let dropsPremise := held && !has
    held := has
    if dropsPremise && flat == last then continue
    last := flat
    if o.sidesOr then
      if let some rw := s.rw? then
        if let some d ← sideDoc rw before then
          rows := rows ++ (d.lines o.width 1).mapIdx fun i l =>
            (if i == 0 then "&" else "&\\qquad ") ++ l
    let (arrow, tag) := arrowOf o s.rule
    let ls := (← fml ns e).lines o.width 3
    rows := rows ++ ls.mapIdx fun i l =>
      if i == 0 then "&" ++ arrow ++ "\\ " ++ l ++ tag else "&\\qquad " ++ l
    before := (ns, e)
  if let some (hns, h) := hyp? then
    -- `\Gamma` above the chain, apart from it
    return #["&\\Gamma = \\{" ++ (← fml hns h).flat ++ "\\}\\\\[4pt]\n" ++ rows[0]!] ++
      rows.extract 1 rows.size
  return rows

/-! ## Judgements and chains -/

/-- A chain's links, from its statement: `Fml.Via` and the relations of one link. -/
def chainSteps? (e : Expr) : MetaM (Option (Expr × Array Step)) := do
  let e ← instantiateMVars e
  let some h := e.getAppFn.constName? | return none
  let args := e.getAppArgs
  let one (rule : String) (n : Nat) (rw? : Option Expr := none) : Option (Expr × Array Step) :=
    if args.size == n then some (args[n - 2]!, #[{ rule, line := args[n - 1]!, rw? }]) else none
  match h with
  | ``Fml.OneStep => return one "" 4
  | ``Fml.Steps => return one "~*>" 4
  | ``Fml.Leads => return one "~*>" 4
  | ``Fml.LeadsK => return one "~*>" 3
  | ``Fml.MergeBy => return one "sequentialToParallel" 6
  | ``Fml.StepBy =>
    if args.size != 5 then return none
    let n := ((← Chain.ruleName? args[2]!).map (·.toString)).getD ""
    return one n 5
  | ``Fml.RwBy =>
    if args.size != 6 then return none
    let .lit (.strVal n) := args[2]!.consumeMData | return none
    return one n 6 (some args[3]!)
  | ``Fml.Via =>
    if args.size != 4 then return none
    let some ws ← listElems? args[3]! | return none
    let mut out := #[]
    for w in ws do
      let w ← whnfR w
      unless w.isAppOfArity ``Prod.mk 4 do return none
      let l ← whnfR (w.getArg! 2)
      let line := w.getArg! 3
      let step : Step ←
        if l.isAppOf ``Link.one then pure { rule := "", line }
        else if l.isAppOf ``Link.many then pure { rule := "~*>", line }
        else if l.isAppOf ``Link.merge then pure { rule := "sequentialToParallel", line }
        else if l.isAppOf ``Link.rw then
          let .lit (.strVal n) := (l.getArg! 1).consumeMData | return none
          pure { rule := n, line, rw? := some (l.getArg! 2) }
        else if l.isAppOf ``Link.rule then
          pure { rule := ((← Chain.ruleName? l.appArg!).map (·.toString)).getD "", line }
        else return none
      out := out.push step
    return some (args[2]!, out)
  | _ => return none

/-- A sequent's antecedent, read from its `Hyps`, and the names it leaves. -/
partial def hypsDoc (H : Expr) : RM (Array Doc × List Expr) := do
  let H := (← instantiateMVars H).consumeMData
  let unknown (Γ : Expr) : MetaM (List Expr) := do
    return List.replicate ((← Delab.ctxLength? Γ).getD 0) Delab.unknownVar
  if let .fvar fv := H then
    let ty ← whnfR (← fv.getType)
    return (#[.ident (← fv.getUserName).eraseMacroScopes.toString], ← unknown (ty.getArg! 2))
  let H ← whnf H
  let args := H.getAppArgs
  match H.getAppFn.constName? with
  | some ``Hyps.nil => return (#[], ← unknown args[1]!)
  | some ``Hyps.pre =>
    let (hs, ns) ← hypsDoc args[3]!
    return (hs.push (← fml ns args[4]!), ns)
  | some ``Hyps.upd =>
    let (hs, ns) ← hypsDoc args[4]!
    let (u, ms) ← updDoc ns args[6]!
    return (match u with | some u => hs.push u | none => hs, ms)
  | some ``Hyps.havoc =>
    let (hs, ns) ← hypsDoc args[3]!
    return (hs.push (.cat #[.tx "\\{" 1, .tx (← spell "havoc" "\\havoc") 5, .tx "\\}" 1]), ns)
  | some ``Hyps.all =>
    let (hs, ns) ← hypsDoc args[3]!
    let x := args[4]!
    let xn := ((← ppVar? x).map (·.getId.toString)).getD "_"
    let T := (← primName? args[5]!).getD "T"
    return (hs.push (.cat #[.tx "\\forall " 1, .tx ("\\mathsf{" ++ T ++ "}") T.length, .tx "\\," 1,
      .ident xn]), x :: ns)
  | some ``Hyps.bind =>
    let (hs, ns) ← hypsDoc args[3]!
    return (hs, args[5]! :: ns)
  | some ``Hyps.anon =>
    let (hs, ns) ← hypsDoc args[3]!
    return (hs.push (.kw "anon"), ns)
  | _ => return (#[← unknownFml H], [])

/-- What a calculus expression renders as: one line, or the rows of a chain. -/
inductive Out where
  | line (d : Doc)
  | rows (rs : Array String)

/-- A scoped formula, `Fml.Valid`, a sequent or a chain; `none` for anything else. -/
def calculusOut? (e : Expr) : RM (Option Out) := do
  let e ← instantiateMVars e
  let ty ← whnfR (← inferType e)
  if ty.isAppOf ``Fml then return some (.line (← fml [] e))
  if e.isAppOfArity ``Fml.Valid 2 then
    return some (.line (.cat #[.tx "\\models " 2, ← fml [] e.appArg!]))
  if e.isAppOfArity ``Proves 6 then
    let (hs, ns) ← hypsDoc (e.getArg! 4)
    let φ ← fml ns (e.getArg! 5)
    let ante : Doc := .sepBy (.tx ",\\ " 2) hs
    return some (.line (.cat #[ante, .tx (if hs.isEmpty then "" else " ") 1, .brk,
      .tx "\\Longrightarrow " 2, φ]))
  if let some (first, steps) ← chainSteps? e then
    return some (.rows (← derivationRows first steps false))
  return none

/-- Run a renderer, logging the warnings it collected. -/
def runRM {α : Type} (o : Options) (k : RM α) : MetaM α := do
  let (a, ws) ← RM.run' o k
  for w in ws do logWarning m!"LaTeX export: {w}"
  return a

/-- A calculus expression as a fragment, `none` if it is none. -/
def calculusLatex? (o : Options) (e : Expr) : MetaM (Option String) := runRM o do
  match ← calculusOut? e with
  | some (.line d) => return some (lineLatex o d)
  | some (.rows rs) => return some (alignedLatex rs)
  | none => return none

/-- Scoped formula, chain or judgement, in the calculus's notation, at the
options `set_option latex.sol.*` gives. -/
def calculusLatex (e : Expr) : MetaM String := do
  let o := Options.ofCore (← getOptions)
  if let some s ← calculusLatex? o e then return s
  run_latexPP e {}

/-- A derivation from `φ` through its steps, as an `aligned` environment,
presented as the options say (`collapse`, `premise`, `labels`, `sides`). -/
def derivationLatex (φ : Expr) (steps : Array Step) (o : Options := {}) : MetaM String :=
  runRM o do return alignedLatex (← derivationRows φ steps true)

-- LeanTeX falls back to the root key, so register each head explicitly.
@[latex_pp app.Solidity.Fml.tt, latex_pp app.Solidity.Fml.eq,
  latex_pp app.Solidity.Fml.wellFormed, latex_pp app.Solidity.Fml.not,
  latex_pp app.Solidity.Fml.and, latex_pp app.Solidity.Fml.imp,
  latex_pp app.Solidity.Fml.all, latex_pp app.Solidity.Fml.upd,
  latex_pp app.Solidity.Fml.modal, latex_pp app.Solidity.Fml.havoc,
  latex_pp app.Solidity.Fml.anon, latex_pp app.Solidity.Fml.bind,
  latex_pp app.Solidity.Fml.OneStep,
  latex_pp app.Solidity.Fml.Steps, latex_pp app.Solidity.Fml.StepBy,
  latex_pp app.Solidity.Fml.RwBy, latex_pp app.Solidity.Fml.MergeBy,
  latex_pp app.Solidity.Fml.Via, latex_pp app.Solidity.Fml.LeadsK,
  latex_pp app.Solidity.Fml.Leads, latex_pp app.Solidity.Fml.Valid, latex_pp app.Solidity.Proves]
def ppCalculus : LatexPrinter := fun e => do
  return LatexData.atomString (← calculusLatex e)

/-- LaTeX string of an elaborated expression; also composes with LeanTeX's
ordinary mathematical printers. -/
def exprLatex (e : Expr) (o : Options := {}) : MetaM String := do
  if let some s ← calculusLatex? o e then return s
  -- a calculus term nested in ordinary mathematics (`ppCalculus`) reads the
  -- presentation options from the caller, including explicit map overrides.
  withOptions (fun co => latex.sol.definitions.set
    (latex.sol.width.set (latex.sol.macros.set co o.macros) o.width)
    (Lean.toJson o.definitions).compress)
    (run_latexPP e {})

/-- Export a declaration's statement, retaining hypotheses. As in fm-04,
schema parameters are implicit in print; `binders := true` prints their types. -/
def declLatex (n : Lean.Name) (binders : Bool := false) (o : Options := {}) : MetaM String := do
  forallTelescope (← getConstInfo n).type fun xs body => do
    let mut result ← exprLatex body o
    for x in xs.reverse do
      let d ← x.fvarId!.getDecl
      if ← isProp d.type then
        result := s!"({← exprLatex d.type o}) \\implies {result}"
      else if binders then
        result := s!"\\forall {identLatex d.userName.toString} : {← exprLatex d.type o},\\ {result}"
    return result

/-! ## Commands -/

/-- An option of the export commands: `(macros := true)`, `(width := 70)`,
`(labels := none | over | tag)`, `(collapse := [r, …])`, `(groups := b)`,
`(premise := b)`, `(sides := b)`, `(sorts := b)`, `(past := b)`. -/
syntax latexOpt := atomic("(" ident " := ") term ")"

/-- A document's explicit symbol-to-destination map. These identifiers are
renderer keys, not names resolved in the current Lean namespace. -/
def elabDefinitionTargets (v : Term) : CoreM (List (String × String)) := do
  let `([$xs,*]) := v |
    throwErrorAt v "expected [(find, \"destination\"), (select, \"destination\"), ...]"
  let mut targets : List (String × String) := []
  for x in xs.getElems do
    let `(($key:ident, $target:str)) := x |
      throwErrorAt x "expected (symbol, \"destination\")"
    let keyName := key.getId.toString
    unless definitionKeys.contains keyName do
      throwErrorAt key "unknown definition symbol {keyName}; available: {definitionKeys}"
    if targets.any (·.1 == keyName) then
      throwErrorAt key "duplicate definition symbol {keyName}"
    unless validDefinitionTarget target.getString do
      throwErrorAt target "definition destination must be nonempty and contain only ASCII letters, digits, :, _, ., / or -"
    targets := targets ++ [(keyName, target.getString)]
  return targets

/-- Set the default definition map in the current section or namespace.
An export's `(definitions := ...)` replaces this map; `[]` disables links. -/
elab "#latex_definition_targets " targets:term : command => do
  let targets ← Command.liftCoreM (elabDefinitionTargets targets)
  Command.modifyScope fun s =>
    { s with opts := latex.sol.definitions.set s.opts (Lean.toJson targets).compress }

/-- The options of a command, over those `set_option latex.sol.*` gives. -/
def elabOpts (opts : Array (TSyntax ``latexOpt)) : CoreM Options := do
  let mut o := Options.ofCore (← getOptions)
  for opt in opts do
    let `(latexOpt| ($k:ident := $v)) := opt | throwErrorAt opt "malformed option"
    let bool : CoreM Bool := match v with
      | `(true) => pure true
      | `(false) => pure false
      | _ => throwErrorAt v "expected true or false"
    match k.getId.toString with
    | "macros" => o := { o with backend := if ← bool then .macros else .plain }
    | "width" =>
      let some n := v.raw.isNatLit? | throwErrorAt v "expected a number"
      o := { o with width := n }
    | "labels" =>
      let l ← match v with
        | `(none) => pure Labels.none
        | `(over) => pure Labels.over
        | `(tag) => pure Labels.tag
        | _ => throwErrorAt v "expected none, over or tag"
      o := { o with labels := some l }
    | "collapse" =>
      let `([$xs,*]) := v | throwErrorAt v "expected a list of rule names, [r, …]"
      let names ← xs.getElems.mapM fun x => match x with
        | `($x:ident) => pure x.getId.toString
        | _ => throwErrorAt x "expected a rule name"
      o := { o with collapse := names.toList }
    | "groups" => o := { o with groups := ← bool }
    | "premise" => o := { o with premise := ← bool }
    | "sides" => o := { o with sides := some (← bool) }
    | "sorts" => o := { o with sorts := ← bool }
    | "past" => o := { o with past := ← bool }
    | "definitions" => o := { o with definitions := ← elabDefinitionTargets v }
    | s => throwErrorAt k "unknown option {s}: macros, width, labels, collapse, groups, premise, \
        sides, sorts, past, definitions"
  return o

/-- `#latex_decl (opts) n`: a declaration's statement. -/
elab "#latex_decl " opts:latexOpt* id:ident : command => do
  let o ← Command.liftCoreM (elabOpts opts)
  let result ← Command.runTermElabM fun _ => do
    declLatex (← realizeGlobalConstNoOverloadWithInfo id) (o := o)
  logInfo result

/-- `#latex_file "path" (opts) t`: write a math fragment from an elaborated term. -/
elab "#latex_file " path:str opts:latexOpt* t:term : command => do
  let o ← Command.liftCoreM (elabOpts opts)
  let result ← Command.runTermElabM fun _ => do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    exprLatex e o
  IO.FS.writeFile path.getString (result ++ "\n")

/-- `#latex_decl_file "path" (opts) n`: write a declaration's statement. -/
elab "#latex_decl_file " path:str opts:latexOpt* id:ident : command => do
  let o ← Command.liftCoreM (elabOpts opts)
  let result ← Command.runTermElabM fun _ => do
    declLatex (← realizeGlobalConstNoOverloadWithInfo id) (o := o)
  IO.FS.writeFile path.getString (result ++ "\n")

/-- The chains proved under the namespace `ns` (a theorem whose statement is
a chain, `chainSteps?`), each with its path below it: `ns.A.chain` is `A`,
`ns.A.box` is `A/box`, `ns.storageRootWrite` is `storageRootWrite`. -/
def chainsUnder (ns : Lean.Name) : MetaM (Array (Lean.Name × String)) := do
  let cands := (← getEnv).constants.fold (init := #[]) fun acc n c =>
    if c matches .thmInfo _ && ns.isPrefixOf n && n != ns then acc.push (n, c.type) else acc
  let mut out := #[]
  for (n, ty) in cands do
    let isChain ← forallTelescope ty fun _ b => return (← chainSteps? b).isSome
    unless isChain do continue
    let parts := (n.componentsRev.take (n.getNumParts - ns.getNumParts)).reverse.filterMap
      fun | .str _ x => some x | _ => none
    let parts := if parts.length > 1 && parts.getLast? == some "chain" then parts.dropLast
      else parts
    out := out.push (n, "/".intercalate parts)
  return out.qsort (·.2 < ·.2)

/-- `#latex_chains_files "dir" (opts) N`: every chain proved under the
namespace `N` (a worked chain, kernel-checked), its statement written to
`dir/<path>.tex` (`N.A.chain` to `dir/A.tex`, `N.A.box` to `dir/A/box.tex`);
the files it wrote logged. -/
elab "#latex_chains_files " path:str opts:latexOpt* ns:ident : command => do
  let o ← Command.liftCoreM (elabOpts opts)
  let cs ← Command.liftTermElabM (chainsUnder ns.getId)
  if cs.isEmpty then
    logWarningAt ns m!"no chain proved under {ns.getId}"
    return
  let mut wrote := #[]
  for (n, rel) in cs do
    let result ← Command.runTermElabM fun _ => declLatex n (o := o)
    let file : System.FilePath := path.getString / (rel ++ ".tex")
    if let some d := file.parent then IO.FS.createDirAll d
    IO.FS.writeFile file (result ++ "\n")
    wrote := wrote.push file.toString
  logInfo m!"{wrote.size} fragments:\n{"\n".intercalate wrote.toList}"

/-- `#latex_expr (opts) t`: a term as a fragment, with options (`#latex`
takes none: it reads `set_option latex.sol.*`). -/
elab "#latex_expr " opts:latexOpt* t:term : command => do
  let o ← Command.liftCoreM (elabOpts opts)
  let result ← Command.runTermElabM fun _ => do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    exprLatex e o
  logInfo result

end Solidity.Latex
