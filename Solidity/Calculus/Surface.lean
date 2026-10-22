import Solidity.Calculus.Notation
import Solidity.Calculus.Spec
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Logic
import Solidity.Calculus.Proves
import Solidity.Calculus.SequentNotation

/-!
# The flip switch: `open scoped Solidity.Scoped`

With the scope open, today's notation reads the scoped calculus
(`docs/intrinsic.md`, W2 `tree`): the same text, a scoped term.  Since W9.4
every formula reads scoped without it too (`elabDlAuto`, decision 11), so
the switch decides only how a parameter is bound, by `∀` (`cdl!`) or by a
hidden binder printing as nothing (`dl!` outside the scope):

* `dl!{ φ }`, `dl![m]{ φ }`, `dl[C]{ φ }`, `dl[C, m]{ φ }` and their sequent
  lines (`dl!{ Γ ⟹ φ }`) are `cdl…`'s (`Calculus/Notation.lean`): a
  `Fml C []`, with or without a modality;
* `spec!{f}`, `spec[C]{f}` are `cspec…`'s, `problem!{constructor}` is
  `cproblem…`'s (`Calculus/Spec.lean`);
* `⊨ᶠ φ` is `Fml.Valid φ` (`Calculus/RuleSyntax.lean`, either side); under the
  scope `valid% φ`, which reads the closer's `Fml.Valid` of a formula that is
  no `Fml` (a chain's line past the program, `Calculus/RewriteChains.lean`);
  `⊢ φ` is the scoped sequent with nothing assumed,
  `Proves C .all [] .nil φ`;
* the commands of `Tools/Inspect.lean` (`#wp`, `#step`, `#proof_tree`,
  `#proof_node`, `#proof_tree_json`) read `dl!{ … }` as scoped
  (`surfaceOn`).

The rule lines `dl{ ⟨[ s; ]⟩ ⇝ p }` are not this switch's: they read scoped
under `open scoped Solidity.Schema` (`Calculus/Rules.lean`).
Tactics dispatch on the goal's head constant, so `sol_…` are the same text
on either side.

Each reading is a macro (`scoped macro_rules`), tried before today's
elaborator, so a file that opens the scope reads every formula scoped.
-/

namespace Solidity

open Lean Elab Term Meta

/-- `core_surface%`: `true` where `open scoped Solidity.Scoped` is in
effect, `false` elsewhere. -/
syntax (name := coreSurfaceFlag) "core_surface%" : term

macro_rules | `(core_surface%) => `(false)

/-- Whether `open scoped Solidity.Scoped` is in effect here. -/
def surfaceOn : TermElabM Bool := do
  let some stx ← liftMacroM (expandMacro? (← `(core_surface%))) | return false
  return stx.isIdent && stx.getId.eraseMacroScopes == `true

/-- `valid% φ`: `Fml.Valid φ` of a scoped formula. -/
syntax (name := validDispatch) "valid% " term:max : term

@[term_elab validDispatch]
def elabValidDispatch : TermElab := fun stx _ => do
  let φ ← elabTerm stx[1] none
  synthesizeSyntheticMVarsNoPostponing
  let φ ← instantiateMVars φ
  let ty ← whnf (← inferType φ)
  unless ty.isAppOfArity ``Fml 2 do throwError "valid%: not a scoped formula{indentExpr φ}"
  mkAppM ``Fml.Valid #[φ]

/-- `Fml.Valid φ` prints as `⊨ᶠ φ`. -/
@[app_unexpander Fml.Valid]
def unexpandValid : PrettyPrinter.Unexpander
  | `($_ $φ) => `(⊨ᶠ $φ)
  | _ => throw ()

/-- `holds σ φ` prints as `σ ⊧ φ`. -/
@[app_unexpander holds]
def unexpandHolds : PrettyPrinter.Unexpander
  | `($_ $σ $φ) => `($σ ⊧ $φ)
  | _ => throw ()

namespace Scoped

scoped macro_rules | `(core_surface%) => `(true)

scoped macro_rules
  | `(dl!{ $φ:dl_fml }) => `(cdl!{ $φ })
  | `(dl![ $m ]{ $φ:dl_fml }) => `(cdl![$m]{ $φ })
  | `(dl[ $c ]{ $φ:dl_fml }) => `(cdl[$c]{ $φ })
  | `(dl[ $c, $m ]{ $φ:dl_fml }) => `(cdl[$c, $m]{ $φ })
  | `(dl!{ $[$as:dl_fml],* ⟹ $φ:dl_fml }) => `(cdl!{ $[$as],* ⟹ $φ })
  | `(dl![ $m ]{ $[$as:dl_fml],* ⟹ $φ:dl_fml }) => `(cdl![$m]{ $[$as],* ⟹ $φ })
  | `(dl[ $c ]{ $[$as:dl_fml],* ⟹ $φ:dl_fml }) => `(cdl[$c]{ $[$as],* ⟹ $φ })
  | `(dl[ $c, $m ]{ $[$as:dl_fml],* ⟹ $φ:dl_fml }) => `(cdl[$c, $m]{ $[$as],* ⟹ $φ })

scoped macro_rules
  | `(spec!{ $f:ident }) => `(cspec!{ $f })
  | `(spec[ $c:term ]{ $f:ident }) => `(cspec[$c]{ $f })
  | `(problem!{ constructor }) => `(cproblem!{ constructor })
  | `(problem[ $c:term ]{ constructor }) => `(cproblem[$c]{ constructor })

scoped macro_rules
  | `(⊨ᶠ $φ:term) => `(valid% $φ)

/-- `⊢ φ`: the scoped sequent with nothing assumed. -/
scoped notation:25 "⊢ " φ:26 => Proves _ RuleSet.all [] Hyps.nil φ

end Scoped

end Solidity
