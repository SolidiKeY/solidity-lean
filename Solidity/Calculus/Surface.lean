import Solidity.Calculus.Notation
import Solidity.Calculus.Spec
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Logic
import Solidity.Calculus.Proves

/-!
# The flip switch: `open scoped Solidity.Scoped`

With the scope open, today's notation reads the scoped calculus
(`docs/intrinsic.md`, W2 `tree`): the same text, a scoped term.  A formula
with a modality reads scoped without it (`elabDlAuto`, decision 11), so the
switch matters only for one with none, which reads as the closer's `NFml`
when it is off:

* `dl!{ φ }`, `dl![m]{ φ }`, `dl[C]{ φ }`, `dl[C, m]{ φ }` and their sequent
  lines (`dl!{ Γ ⟹ φ }`) are `cdl…`'s (`Calculus/Notation.lean`): a
  `Fml C []`, with or without a modality;
* `spec!{f}`, `spec[C]{f}` are `cspec…`'s, `problem!{constructor}` is
  `cproblem…`'s (`Calculus/Spec.lean`);
* `⊨ φ` is `Valid φ` for a scoped `φ`, and today's `Valid φ` for any
  other (`valid% φ`); `⊢ φ` is the scoped sequent with nothing assumed,
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

/-- `valid% φ`: `Valid φ` for a scoped formula, `Solidity.Valid φ`
for any other. -/
syntax (name := validDispatch) "valid% " term:max : term

@[term_elab validDispatch]
def elabValidDispatch : TermElab := fun stx _ => do
  let φ ← elabTerm stx[1] none
  synthesizeSyntheticMVarsNoPostponing
  let φ ← instantiateMVars φ
  let ty ← whnf (← inferType φ)
  if ty.isAppOfArity ``Fml 2 then return ← mkAppM ``Valid #[φ]
  mkAppM ``NFml.Valid #[φ]

/-- `Valid φ` prints as `⊨ φ`. -/
@[app_unexpander Valid]
def unexpandValid : PrettyPrinter.Unexpander
  | `($_ $φ) => `(⊨ $φ)
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
  | `(⊨ $φ:term) => `(valid% $φ)

/-- `⊢ φ`: the scoped sequent with nothing assumed. -/
scoped notation:25 "⊢ " φ:26 => Proves _ RuleSet.all [] Hyps.nil φ

end Scoped

end Solidity
