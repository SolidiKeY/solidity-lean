import Solidity.Calculus.RuleSyntax
import Solidity.Calculus.KeyTaclets

/-!
# What a rule is made of

What the printers and the tools keep of a taclet: solkey's branch labels
(`Taclet.branchLabels`, `Taclet.labelledBy`) and the printer of a taclet's
binders (`delabTacletBinders`, which `Calculus/Delab.lean`'s `#taclet`
uses).  Moved out of `Rules.lean` (`docs/intrinsic.md`, W4 item 11), which
keeps the rule table and its delaborators.
-/

namespace Solidity

/-! ## solkey's branch labels -/

/-- solkey's labels of a taclet's goals, in order, as the rules above write
them (`"Holds": …`; the macro drops them): the two goals of a split or a
check, the outcomes of `branches`.  `Examples/ProofTree.lean` checks them
against this file's source. -/
def Taclet.branchLabels : List (String × List String) := [
  ("ifElseSplit", ["if s#se true", "if s#se false"]),
  ("requireSimple", ["Holds", "Reverts"]),
  ("assertSimple", ["Holds", "Violated"]),
  ("tryCallNoCallbackBox",
    ["call succeeded", "Error caught", "Panic caught", "other failure caught"]),
  ("sendNoCallbackBox", ["send succeeded", "send failed"]),
  ("sendNoCallbackDiamond", ["non-negative amount", "send succeeded", "send failed"]),
  ("loopExit", ["loop exited", "unwound to the end"]),
  ("whileInvariantBox", ["invariant initially valid", "invariant preserved and used"]),
  ("whileInvariantDiamond", ["invariant initially valid", "invariant preserved and used"])]

/-- The taclet whose goals a premise for the statement of head `c` labels:
an `if` splits by `ifElseSplit`, a `require` by `requireSimple`, an `assert`
by `assertSimple`, a `try` by `tryCallNoCallbackBox` (and
`CallbackTaclet.tryCallWithCallbackBox`, labelled alike), a send by
`sendNoCallbackBox`, or under the diamond (`diamond`) `sendNoCallbackDiamond`;
a loop by `loopExit`, the one rule of a loop with goals to label. -/
def Taclet.labelledBy (c : Lean.Name) (diamond : Bool := false) : Option String :=
  if c == ``Stmt.ite then some "ifElseSplit"
  else if c == ``Stmt.require then some "requireSimple"
  else if c == ``Stmt.assert then some "assertSimple"
  else if c == ``Stmt.tryCall then some "tryCallNoCallbackBox"
  else if c == ``Stmt.send then
    some (if diamond then "sendNoCallbackDiamond" else "sendNoCallbackBox")
  else if c == ``Stmt.loop then some "loopExit"
  else none

section Print
open Lean Meta PrettyPrinter Delaborator SubExpr
set_option hygiene false

/-- The type without its `autoParam` hypotheses (a taclet's side conditions),
which nothing after them depends on. -/
partial def dropSide : Lean.Expr → Lean.Expr
  | .forallE n t b bi =>
    let b' := dropSide b
    if t.isAppOfArity ``autoParam 2 && !b'.hasLooseBVar 0 then b'.lowerLooseBVars 1 1
    else .forallE n t b' bi
  | e => e

/-- Whether a binder type of the telescope `e` mentions the bound variable `i`. -/
def usedInBinders : Lean.Expr → Nat → Bool
  | .forallE _ t b _, i => t.hasLooseBVar i || usedInBinders b (i + 1)
  | _, _ => false

/-- The binders of a taclet's type and its line.  The proof a name carries
(`hfld : C.fieldType R fld = …` for `fld`, `hgsp` for `gsp`, `hop` for `op`;
`hsep` for the arguments of a call `fbs`) stays out of sight, unless another
binder's type names it, the line saying it; binders of one type are
grouped, as Lean groups them. -/
partial def delabTacletBinders (names : Array Lean.Name)
    (acc : Array (Lean.Ident × Lean.Term × BinderInfo)) : DelabM Lean.Term := do
  let .forallE n t rest bi := ← getExpr | do
    let body ← delab
    -- consecutive binders of one type and kind, grouped
    let mut groups : Array (Array Lean.Ident × Lean.Term × BinderInfo) := #[]
    for (x, ty, bi) in acc do
      match groups.back? with
      | some (xs, ty', bi') =>
        if bi == bi' && ty.raw.structEq ty'.raw && bi != .instImplicit then
          groups := groups.pop.push (xs.push x, ty', bi')
        else groups := groups.push (#[x], ty, bi)
      | none => groups := groups.push (#[x], ty, bi)
    if groups.isEmpty then return body
    let bs ← groups.mapM fun (xs, ty, bi) => match bi with
      | .implicit => `(Lean.Parser.Term.bracketedBinderF| {$xs* : $ty})
      | .strictImplicit => `(Lean.Parser.Term.bracketedBinderF| ⦃$xs* : $ty⦄)
      | .instImplicit => `(Lean.Parser.Term.bracketedBinderF| [$(xs[0]!) : $ty])
      | .default => `(Lean.Parser.Term.bracketedBinderF| ($xs* : $ty))
    `(∀ $bs*, $body)
  -- `hx`, of a fact about the binder `x` before it
  let s := n.eraseMacroScopes.toString
  let carried ← if s == "hsep" then pure true else if !s.startsWith "h" then pure false else
    match (← getLCtx).findFromUserName? (Lean.Name.mkSimple (s.drop 1)) with
    | some d => pure (names.contains d.userName && t.containsFVar d.fvarId)
    | none => pure false
  let hide := bi == .implicit && carried && !(usedInBinders rest 0) && (← isProp t)
  let ty ← withBindingDomain delab
  withBindingBodyUnusedName fun x => do
    let x : Lean.Ident := ⟨x⟩
    let names := names.push x.getId
    if hide then return ← delabTacletBinders names acc
    delabTacletBinders names (acc.push (x, ty, bi))

end Print

end Solidity
