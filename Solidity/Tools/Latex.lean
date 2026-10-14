import LeanTeX
import Solidity.Calculus.Chains

/-!
# Paper notation as LaTeX

LeanTeX's `#latex` composes ordinary mathematics with the scoped calculus.
`Solidity.Latex.exprLatex` returns a string in `MetaM`; `declLatex` exports a
declaration's statement (hypotheses retained; parameters implicit by default). The commands
`#latex_decl` and `#latex_file "path.tex" term` expose these APIs to Lean files.

The renderer reads the syntax produced by the calculus's existing printers,
so the scopes, parentheses, fresh names and written chain links are shared.
It does not run symbolic execution or alter the proof. The export API rejects
unsupported Lean escapes; upstream `#latex` uses best-effort fallback instead.
The output is a math fragment using LaTeX, amsmath and amssymb commands.
-/

namespace Solidity.Latex

open Lean Meta Elab LeanTeX

/-- Escape literal text for a LaTeX text or identifier argument. -/
def escape (s : String) : String :=
  String.join <| s.toList.map fun c => match c with
    | '\\' => "\\textbackslash{}"
    | '{' => "\\{" | '}' => "\\}"
    | '_' => "\\_" | '%' => "\\%" | '#' => "\\#" | '&' => "\\&"
    | '$' => "\\$" | '^' => "\\textasciicircum{}" | '~' => "\\textasciitilde{}"
    | _ => String.singleton c

/-- Preserve LeanTeX's Greek/subscript spelling while escaping TeX specials. -/
def identLatex (s : String) : String :=
  go s.toList ""
where
  sub (s : String) : String := if s.isEmpty then "" else "_{" ++ s ++ "}"
  go : List Char → String → String
    | [], acc => sub acc
    | c :: cs, acc =>
      let t := if "%&#$\\^~_{}".contains c then escape (String.singleton c)
        else c.toLatex
      if t.startsWith "_" then go cs (acc ++ String.mk (t.toList.drop 1))
      else
        let delim := if t.startsWith "\\" && t.toList.all (fun c => c == '\\' || c.isAlpha)
            && cs.head?.any Char.isAlpha then "{}" else ""
        sub acc ++ t ++ delim ++ go cs ""

/-- A notation token; modal delimiters differ from arithmetic comparisons. -/
def token (s : String) : String :=
  match s.trim with
  | "⟨" => "\\langle" | "⟩" => "\\rangle"
  | "⟨[" => "\\langle[" | "]⟩" => "]\\rangle"
  | "{" => "\\{" | "}" => "\\}"
  | "∧" => "\\land" | "∨" => "\\lor" | "¬" => "\\neg"
  | "→" => "\\rightarrow" | "↔" => "\\leftrightarrow"
  | "∀" => "\\forall" | "∃" => "\\exists"
  | "⊢" => "\\vdash" | "⊨" => "\\models" | "⟹" => "\\Longrightarrow"
  | "≐" | "==" => "=" | "!=" => "\\ne"
  | "<=" | "≤" => "\\le" | ">=" | "≥" => "\\ge"
  | "‖" => "\\parallel"
  | "~>" => "\\rightsquigarrow" | "~*>" | "~~>" => "\\rightsquigarrow^{*}"
  | "true" => "\\mathit{true}" | "false" => "\\mathit{false}"
  | "−" => "-"
  | t => escape t

/-- Render the scoped notation tree, dropping only its Lean quotation wrapper. -/
partial def syntaxLatex (s : Syntax) : MetaM String := do
  if s.isOfKind ``chainStx then
    let first ← syntaxLatex s[0]
    let links ← s[1].getArgs.mapM fun link => do
      return s!" &{← syntaxLatex link[0]} {← syntaxLatex link[1]}"
    return "\\begin{aligned} &" ++ first ++ " \\\\ " ++
      " \\\\ ".intercalate links.toList ++ " \\end{aligned}"
  if let `(chain_arrow| ~[$n:ident]~>) := s then
    return "\\overset{\\mathrm{" ++ escape n.getId.toString ++ "}}{\\rightsquigarrow}"
  -- The wrapper adds a contract/modality to Lean syntax, not to the formula.
  if let `(dl{ $f:dl_fml }) := s then return ← syntaxLatex f
  if let `(dl!{ $f:dl_fml }) := s then return ← syntaxLatex f
  if let `(dl![$_:term]{ $f:dl_fml }) := s then return ← syntaxLatex f
  -- Sequents use the same quotation wrapper, with hypotheses inside it.
  if s[0].isAtom && s[0].getAtomVal.trim == "dl{" then
    let args := s.getArgs
    return " ".intercalate ((← (args.extract 1 (args.size - 1)).mapM syntaxLatex).toList)
  match s with
  | .missing => return ""
  | .ident _ _ n _ => return identLatex n.toString
  | .atom _ "‹" | .atom _ "›" =>
    throwError "LaTeX export needs a notation printer for this Lean escape"
  | .atom _ t => return token t
  | .node _ _ args =>
    return " ".intercalate ((← args.mapM syntaxLatex).toList.filter (!·.isEmpty))

/-- Scoped formula, chain or judgement, in the calculus's notation. -/
def calculusLatex (e : Expr) : MetaM String := do
  let e ← instantiateMVars e
  let ty ← whnf (← inferType e)
  if ty.isAppOf ``Fml then
    return ← syntaxLatex (← Chain.ppCoreLine e)
  if e.isAppOf ``Valid then
    return "\\models " ++ (← syntaxLatex (← Chain.ppCoreLine e.appArg!))
  return ← syntaxLatex (← PrettyPrinter.delab e)

-- LeanTeX falls back to the root key, so register each head explicitly.
@[latex_pp app.Solidity.Fml.tt, latex_pp app.Solidity.Fml.eq,
  latex_pp app.Solidity.Fml.defined, latex_pp app.Solidity.Fml.not,
  latex_pp app.Solidity.Fml.and, latex_pp app.Solidity.Fml.imp,
  latex_pp app.Solidity.Fml.all, latex_pp app.Solidity.Fml.upd,
  latex_pp app.Solidity.Fml.modal, latex_pp app.Solidity.Fml.havoc,
  latex_pp app.Solidity.Fml.anon, latex_pp app.Solidity.Fml.bind,
  latex_pp app.Solidity.Fml.OneStep,
  latex_pp app.Solidity.Fml.Steps, latex_pp app.Solidity.Fml.StepBy,
  latex_pp app.Solidity.Fml.RwBy, latex_pp app.Solidity.Fml.MergeBy,
  latex_pp app.Solidity.Fml.Via, latex_pp app.Solidity.Fml.LeadsK,
  latex_pp app.Solidity.Fml.Leads]
def ppFormula : LatexPrinter := fun e => do
  return LatexData.atomString (← calculusLatex e)

@[latex_pp app.Solidity.Valid, latex_pp app.Solidity.Proves]
def ppJudgement : LatexPrinter := fun e => do
  return LatexData.atomString (← calculusLatex e)

/-- LaTeX string of an elaborated expression; also composes with LeanTeX's
ordinary mathematical printers. -/
def exprLatex (e : Expr) : MetaM String := do
  let e ← instantiateMVars e
  let ty ← whnf (← inferType e)
  if ty.isAppOf ``Fml then return ← calculusLatex e
  -- Bypass LeanTeX's best-effort dispatch for calculus relations: it catches
  -- printer failures, whereas the export API must report unsupported escapes.
  let head := e.getAppFn.constName?
  if head.any (fun n => n.getPrefix == ``Fml || n == ``Valid || n == ``Proves) then
    return ← calculusLatex e
  return ← run_latexPP e {}

/-- Export a declaration's statement, retaining hypotheses. As in fm-04,
schema parameters are implicit on paper; `binders := true` prints their types. -/
def declLatex (n : Lean.Name) (binders : Bool := false) : MetaM String := do
  forallTelescope (← getConstInfo n).type fun xs body => do
    let mut result ← exprLatex body
    for x in xs.reverse do
      let d ← x.fvarId!.getDecl
      if ← isProp d.type then
        result := s!"({← exprLatex d.type}) \\implies {result}"
      else if binders then
        result := s!"\\forall {identLatex d.userName.toString} : {← exprLatex d.type},\\ {result}"
    return result

elab "#latex_decl " id:ident : command => do
  let result ← Command.runTermElabM fun _ => do
    declLatex (← realizeGlobalConstNoOverloadWithInfo id)
  logInfo result

/-- Write a math fragment directly from an elaborated Lean term. -/
elab "#latex_file " path:str t:term : command => do
  let result ← Command.runTermElabM fun _ => do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    exprLatex e
  IO.FS.writeFile path.getString (result ++ "\n")

/-- Write a declaration's statement as a math fragment. -/
elab "#latex_decl_file " path:str id:ident : command => do
  let result ← Command.runTermElabM fun _ => do
    declLatex (← realizeGlobalConstNoOverloadWithInfo id)
  IO.FS.writeFile path.getString (result ++ "\n")

end Solidity.Latex
