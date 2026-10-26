import Solidity.Update
import Solidity.Syntax.PushSource

/-!
# The rule syntax: grammar and schemas

The grammar of `dl{ … }` and `tm{ … }`, the side conditions' syntax, and
the first part of reading schemas (macros).

A piece of `Calculus/RuleSyntax.lean`, whose docstring describes the whole.
-/

namespace Solidity

/-! ## Grammar -/

/-- Terms of the logic.  `f(…)` is read by its head: `find`, `save`,
`delAt`, `select`, `write`, `read`, `addM`, `copySt`, `copyMem`, `freshId`,
`delValue`, `lit`; at a state variable `store` and `select` (the older
spellings of `save` and `find`).  KeY's long forms are read as well:
`consr(p, f)` for `p.f`, `consr(p, at(i))` for `p[i]`, `find(s, consr(p,
size))` for `find(s, p.length)`, `read(m, i, f)` and `write(m, i, f, v)` for a
memory member or element (`at(k)`, `size`), `storeSt`/`selectSt`/`self` in the
ledger's update; `pp.sol.key` prints them. -/
declare_syntax_cat dl_term
syntax:max num : dl_term
syntax:max ident : dl_term
syntax:max dl_term:max "." ident : dl_term
syntax:max dl_term:max "[" dl_term "]" : dl_term
/-- `p[i]@S`: the index `p[i]` checked in the storage `S` instead of the
state's, what `p[i]` becomes merged under a storage write; `p[p.length]@S`
is the slot past the end, its length read in `S`. -/
syntax:max dl_term:max "[" dl_term "]" "@" dl_term:max : dl_term
/-- `T[]`: a dynamic array type, where a term names what an allocation makes
(`addM(m, uint[])`, `newArr(Person[], n)`); `uint[3]` is the index form. -/
syntax:max dl_term:max "[" "]" : dl_term
syntax:max ident noWs "(" dl_term,* ")" : dl_term
syntax:65 dl_term:65 " ⊕ " dl_term:66 : dl_term
syntax:65 dl_term:65 " + " dl_term:66 : dl_term
/-- A unary operator schema variable `op`, applied. -/
syntax:80 "⊖" dl_term:80 : dl_term
/-- `!t`: the negation of a `bool`. -/
syntax:80 "!" dl_term:80 : dl_term
/-- `t ± 1`: the increment or decrement schema variable `op`, as arithmetic. -/
syntax:65 dl_term:65 " ± " dl_term:66 : dl_term
/-- The value `t⊕⊕` has: the new one for `++t`, the old one for `t++`. -/
syntax:max dl_term:max "⊕⊕" : dl_term
syntax:65 dl_term:65 " - " dl_term:66 : dl_term
/-- `a / b`: a quotion, truncated, as Solidity divides. -/
syntax:70 dl_term:70 " / " dl_term:71 : dl_term
/-- `a * b`: a product (KeY's `mul`), checked as Solidity multiplies. -/
syntax:70 dl_term:70 " * " dl_term:71 : dl_term
syntax:70 dl_term:70 " % " dl_term:71 : dl_term
/-- `a && b`, `a || b`: the `bool` operators of a value, short-circuiting. -/
syntax:30 dl_term:30 " && " dl_term:31 : dl_term
syntax:25 dl_term:25 " || " dl_term:26 : dl_term
/-- `at(r)`: the ledger's key for the address `r` (`net := store(net, at(r), …)`). -/
syntax:max "at" noWs "(" dl_term ")" : dl_term
/-- Historical conditional-payment text is recognized for a migration
diagnostic; a payment is written `pay(r, a)`. -/
syntax:max "if" noWs "(" dl_term " = " dl_term ")" " then " dl_term " else " dl_term : dl_term
syntax:max "(" dl_term ")" : dl_term
/-- `(a == b)`: a comparison as a `bool` term. Parenthesised, since a bare `==`
after `:=` is the update `x := a == b`. -/
syntax:max "(" dl_term " == " dl_term ")" : dl_term
/-- `(c ? a : b)`: a conditional value, `a` where `c` holds and `b` where it
fails (KeY's `\if (c) \then (a) \else (b)`), what a joined `if` sets a local
to (`ifElseJoin`). -/
syntax:max "(" dl_term " ? " dl_term " : " dl_term ")" : dl_term
syntax:max "‹" term "›" : dl_term

/-- One elementary update `x := t`.  The funds and the ledger are written
`selfBalance := selfBalance - a` and `net := store(net, at(r), net(r) - a)`
(`+` as well), their arithmetic KeY's `int`; a payment
`pay(r, a)`, which also debits the balance. -/
declare_syntax_cat dl_upd_elem (behavior := both)
syntax dl_term " := " dl_term : dl_upd_elem
syntax (priority := high) "pay" "(" dl_term "," dl_term ")" : dl_upd_elem
/-- `x := a <= b`, `x := a < b` (and `>`, `>=`): a comparison captured.  A comparison has
no term spelling of its own (`a <= b` standing alone is a formula), so the
element carries it. -/
syntax dl_term " := " dl_term:56 " <= " dl_term:56 : dl_upd_elem
syntax dl_term " := " dl_term:56 " < " dl_term:56 : dl_upd_elem
syntax dl_term " := " dl_term:56 " > " dl_term:56 : dl_upd_elem
syntax dl_term " := " dl_term:56 " >= " dl_term:56 : dl_upd_elem
/-- `x := a == b`, `x := a != b`: an equality of two `uint`s captured, as the
comparisons are. -/
syntax dl_term " := " dl_term:56 " == " dl_term:56 : dl_upd_elem
syntax dl_term " := " dl_term:56 " != " dl_term:56 : dl_upd_elem
/-- `u`: an update schema variable, its elements in place (KeY's `{u}`). -/
syntax ident : dl_upd_elem
/-- `{u}u2`: the update `u2` with `u` applied to its right-hand sides, KeY's `{u}u2` in `{u ‖ {u}u2}`. -/
syntax "{" ident "}" ident : dl_upd_elem

/-- A parallel update `{ a ‖ b }`. -/
declare_syntax_cat dl_upd (behavior := both)
syntax "{ " sepBy1(dl_upd_elem, " ‖ ") " }" : dl_upd
syntax "‹" term "›" : dl_upd

declare_syntax_cat dl_fml (behavior := both)
syntax:max &"true" : dl_fml
syntax:max &"false" : dl_fml
/-- `a = b`: KeY's `=`, the total equation `Fml.eq` (what the sides denote
in the Theory), in a taclet and against a contract alike. -/
syntax:50 dl_term:51 " = " dl_term:51 : dl_fml
/-- `wt(s)`: the storage `s` is well-formed (`Fml.wellFormed`), KeY's
`wellFormed(heap)`. -/
syntax:max &"wt" "(" dl_term ")" : dl_fml
syntax:max "¬" dl_fml:50 : dl_fml
syntax:35 dl_fml:36 " ∧ " dl_fml:35 : dl_fml
syntax:25 dl_fml:26 " → " dl_fml:25 : dl_fml
syntax:max dl_upd ppSpace dl_fml:50 : dl_fml
/-- `{ havoc } φ`: `φ` after any storage and ledger a callee may leave.
Above an update schema variable named `havoc`, which it also reads as. -/
syntax:max (priority := high) "{ " &"havoc" " } " dl_fml:50 : dl_fml
/-- `{ anon(i, s) } φ`: `φ` whatever the locals `i`, `s` hold (`Fml.anon`),
the anonymising update of a loop's frame. -/
syntax:max (priority := high) "{ " &"anon" "(" sepBy(ident, ", ") ")" " } " dl_fml:50 : dl_fml
/-- The diamond: `P` runs to the end, and `φ` holds after. -/
syntax:max "⟨ " (sol_stmt "; ")* "⟩ " dl_fml:50 : dl_fml
/-- The box: if `P` runs to the end, `φ` holds after. -/
syntax:max "[ " (sol_stmt "; ")* "] " dl_fml:50 : dl_fml
/-- Either modality, `⟨[ P ]⟩ φ` (solkey's `#mod`), in a taclet. -/
syntax:max "⟨" "[ " (sol_stmt "; ")* "]" "⟩ " dl_fml:50 : dl_fml
/-- `⟨[ s; ..ω ]⟩ φ`: statements in front of the rest `ω` of the program
(KeY's `c# s #c`), `s :: ω`; a program schema variable `P; ..ω` is `P ++ ω`. -/
syntax:max "⟨" "[ " (sol_stmt "; ")* ".." term:max " ]" "⟩ " dl_fml:50 : dl_fml
/-- `[ s; ..ω ] φ`, `⟨ s; ..ω ⟩ φ`: the same at the box, at the diamond. -/
syntax:max "[ " (sol_stmt "; ")* ".." term:max " ] " dl_fml:50 : dl_fml
syntax:max "⟨ " (sol_stmt "; ")* ".." term:max " ⟩ " dl_fml:50 : dl_fml
/-- `⟨[ P ]⟩ φ`: either modality over a program that is a schema variable. -/
syntax:max "⟨" "[ " sol_block " ]" "⟩ " dl_fml:50 : dl_fml
/-- A modality over a program that is a schema variable. -/
syntax:max "⟨ " sol_block " ⟩ " dl_fml:50 : dl_fml
syntax:max "[ " sol_block " ] " dl_fml:50 : dl_fml
syntax:max "(" dl_fml ")" : dl_fml
syntax:max "‹" term "›" : dl_fml
/-- A formula by its Lean name, `‹φ›`: the postcondition `φ`.  Below
`true` and `false`, which are names too. -/
syntax:max (name := dlFmlVar) (priority := low) ident : dl_fml
/-- A comparison of program values, as in Solidity: `alice.age == 10` is
`find(storage, alice.age) = 10`. -/
syntax:55 dl_term:56 " == " dl_term:56 : dl_fml
syntax:55 dl_term:56 " != " dl_term:56 : dl_fml
/-- An order between program values, as in Solidity: `count >= 1` is
`count ≥ 1 = true`. -/
syntax:55 dl_term:56 " < " dl_term:56 : dl_fml
syntax:55 dl_term:56 " <= " dl_term:56 : dl_fml
syntax:55 dl_term:56 " > " dl_term:56 : dl_fml
syntax:55 dl_term:56 " >= " dl_term:56 : dl_fml
/-- `∀ uint a; φ`: KeY's `\forall`, over the values of a primitive type. -/
syntax:25 "∀ " ident ident "; " dl_fml:25 : dl_fml
/-- `∀ fresh bytes r; φ`: `φ` for every fresh memory object of any contents
(`Fml.allocAll`, Lean only): what `catchDataBox` leaves for another
contract's data; printed, not written. -/
syntax:25 "∀ " &"fresh" ident ident "; " dl_fml:25 : dl_fml
/-- `∃ uint a; φ`: `¬(∀ uint a; ¬φ)`. -/
syntax:25 "∃ " ident ident "; " dl_fml:25 : dl_fml
syntax:50 dl_fml:55 " && " dl_fml:50 : dl_fml
/-- `φ ∨ ψ`: `¬(¬φ ∧ ¬ψ)`, the logic having no disjunction of its own. -/
syntax:30 dl_fml:31 " ∨ " dl_fml:30 : dl_fml
/-- `φ ↔ ψ`: `(φ → ψ) ∧ (ψ → φ)`. -/
syntax:20 dl_fml:21 " ↔ " dl_fml:21 : dl_fml
/-- `φ where Person memory carol`: `φ` with `carol` a memory local, a
declaration the formula's programs do not make (KeY's `\programVariables`).
Only `dl[C]{ … }` reads it; a line prints it where the kind of a local is
not otherwise written (`Delab.ppFmlE`, `Calculus/Delab.lean`). -/
syntax:10 dl_fml:11 " where " sepBy1(sol_stmt, ", ") : dl_fml

/-- What a taclet leaves: an update in front of the rest, statements, two
goals (a branch, each with its condition), a goal and a check (an `assert`:
the rest with the condition assumed, and the condition), or — for a
revert — `true` or `false` in place of the whole modality.  The modality of the premise is the
taclet's own, so it is written `⟨[ ]⟩`.  A goal of a split or a check may carry
solkey's label (`"Holds": …`); the macro drops it, and `Taclet.branchLabels`
keeps it for the printers. -/
declare_syntax_cat dl_premise (behavior := both)
/-- A symbolic-arity lexicographic invariant VC. It denotes the exact typed
`LoopLex.diamondPremise`: capture every old metric and the guard, then require
invariant preservation and capture every new metric for strict lexicographic
comparison. The frame is the schema's `xs`/`hv` from the body's frame witness.
Optional labels name the initial invariant and preservation/use branches,
respectively; like the expanded invariant notation, they do not change the VC. -/
syntax &"lexInvariant" "(" (str ": ")? sol_expr ", " "‹" term "›" ", " sol_expr ", "
  (str ": ")? sol_block ")" : dl_premise
syntax dl_upd " ⟨" "[ " "]" "⟩" : dl_premise
syntax dl_upd ppSpace dl_upd " ⟨" "[ " "]" "⟩" : dl_premise
/-- SolKey's outer conditional for division/remainder push suffixes. -/
syntax "if " dl_fml " then " "(" dl_upd ppSpace dl_upd " ⟨" "[ " "]" "⟩" ")"
  " else " "(" "⟨" "[ " &"revert" "(" ")" "; " "]" "⟩" ")" : dl_premise
syntax "⟨" "[ " (sol_stmt "; ")* "]" "⟩" : dl_premise
syntax (str ": ")? dl_fml " ⟹ " "⟨" "[ " sol_block " ]" "⟩" " ; "
  (str ": ")? dl_fml " ⟹ " "⟨" "[ " sol_block " ]" "⟩" : dl_premise
syntax (str ": ")? dl_fml " ⟹ " "⟨" "[ " (sol_stmt "; ")* "]" "⟩" " ; "
  (str ": ")? dl_fml " ⟹ " "⟨" "[ " (sol_stmt "; ")* "]" "⟩" : dl_premise
syntax (str ": ")? dl_fml " ⟹ " "⟨" "[ " (sol_stmt "; ")* "]" "⟩" " ; " (str ": ")? dl_fml :
  dl_premise
syntax &"true" : dl_premise
syntax &"false" : dl_premise
/-- A loop's invariant rule (`whileInvariantBox`): the invariant now, and
under `{anon(body)}` (solkey's `#loopAnon`), the invariant assumed, the body
from where the condition holds to its postcondition, the rest (`⟨[ ]⟩`)
from where it does not. -/
syntax (str ": ")? dl_fml " ; " (str ": ")? "{ " &"anon" "(" sol_block ")" " } " "(" dl_fml:26 " → "
  dl_fml:26 " ⟹ " "⟨" "[ " sol_block " ]" "⟩ " dl_fml:50 " ; " dl_fml:26 " ⟹ " "⟨" "[ " "]" "⟩" ")" :
  dl_premise
/-- The same with an update in front of the two goals (`whileInvariantDiamond`'s
`{ variant := dec }`). -/
syntax (str ": ")? dl_fml " ; " (str ": ")? "{ " &"anon" "(" sol_block ")" " } " "(" dl_fml:26 " → "
  dl_upd " (" dl_fml:26 " ⟹ " "⟨" "[ " sol_block " ]" "⟩ " dl_fml:50 " ; " dl_fml:26 " ⟹ "
  "⟨" "[ " "]" "⟩" ")" ")" : dl_premise
/-- `whileInvariantBox` with its break test `broke` (solkey's
`\getLoopBreak`): the iteration assumes `¬broke`, and a body that breaks
goes on to the rest (`⟨[ ]⟩`) in place of keeping the invariant. -/
syntax (str ": ")? dl_fml " ; " (str ": ")? "{ " &"anon" "(" sol_block ")" " } " "(" dl_fml:36
  " ∧ " "¬" dl_fml:max " → " dl_upd " (" dl_fml:26 " ⟹ " "⟨" "[ " sol_block " ]" "⟩ "
  "(" "¬" dl_fml:max " → " dl_fml:26 ")" " ∧ " "(" dl_fml:max " → " "⟨" "[ " "]" "⟩" ")"
  " ; " dl_fml:26 " ⟹ " "⟨" "[ " "]" "⟩" ")" ")" : dl_premise
/-- One goal of a taclet with a goal per way a statement may end (KeY's
`"label": \replacewith(…)`): the block in the statement's place, for every
value of the locals `xs` it binds (`∀ xs.`).  The label is solkey's; the
macro drops it (the proof tree's label table prints it). -/
declare_syntax_cat dl_branch (behavior := both)
syntax (str ": ")? ("∀ " ident ". ")? "⟨" "[ " sol_block " ]" "⟩" : dl_branch
syntax (str ": ")? ("∀ " ident ". ")? "[ " sol_block " ]" : dl_branch
/-- A self-call's `catch` goal (`trySelfStep`, Lean): `fails(call) →`, where
the call does not end normally as a call to the contract itself
(`ExtCall.selfFails`).  Printed only: no taclet is declared with it. -/
syntax (str ": ")? &"fails" "(" ident ")" " → " ("∀ " ident ". ")? "[ " sol_block " ]" : dl_branch
/-- A self-call's `Panic` goal (`trySelfStep`, `CodeBinder.guard`, Lean):
`panics(selfBody) →`, where the receiver is another contract or the code is
one the callee may panic with (`Prog.panicCodes`).  Printed only. -/
syntax (str ": ")? &"fails" "(" ident ")" " → " ("∀ " ident ". ")? &"panics" "(" ident ")" " → "
  "[ " sol_block " ]" : dl_branch
/-- Goals, one per branch (`Premise.branches`), separated by `;`. -/
syntax dl_branch " ; " sepBy1(dl_branch, " ; ") : dl_premise
/-- One goal of `Premise.cases`, with solkey's label: a formula to prove, or
the rest after an update, `{U} ⟨[ ]⟩`. -/
declare_syntax_cat dl_case (behavior := both)
syntax (str ": ")? dl_upd " ⟨" "[ " "]" "⟩" : dl_case
syntax (str ": ")? dl_fml : dl_case
/-- Labelled goals (`Premise.cases`), the formulas first, separated by `;`. -/
syntax dl_case " ; " sepBy1(dl_case, " ; ") : dl_premise

/-- An entry of a sequent's context: an update or a precondition. -/
declare_syntax_cat dl_hyp (behavior := both)
syntax dl_upd : dl_hyp
/-- `{U} [ ]`, `{U} ⟨ ⟩`: an update produced under the box, under the
diamond (`Hyp.upd .box U`); `{U}` alone is produced under the schema's `m`. -/
syntax dl_upd " [ " "]" : dl_hyp
syntax dl_upd " ⟨ " "⟩" : dl_hyp
syntax (priority := high) "{ " &"havoc" " }" : dl_hyp
/-- `{ anon(i, s) }`: a loop's anonymising update of the locals `i`, `s`. -/
syntax (priority := high) "{ " &"anon" "(" sepBy(ident, ", ") ")" " }" : dl_hyp
syntax dl_fml : dl_hyp
/-- `∀ T x`: the local `x` holds any value of `T` (`Hyps.all`), KeY's skolem
constant. -/
syntax "∀ " ident ident : dl_hyp
/-- `..Γ`: the rest of the context, a Lean term, written first: `..Γ, c` is
`Γ ++ [c]`. -/
syntax ".." term:max : dl_hyp

/-- A statement that is a schema variable: `s`; `fbs`, `ic`, a call with its
body (KeY's `FunctionBody`, `InternalCall`); `P`, `Q`, a program spliced in
place. -/
syntax (priority := low) ident : sol_stmt
/-- `catch Error errorBody`: the `Error` clause as KeY's schema writes it. -/
syntax "catch " &"Error" sol_block : sol_catch

/-- A formula, as the printers show one. -/
syntax (priority := high) "dl{ " dl_fml " }" : term
/-- A sequent `Γ ⟹ φ`. -/
syntax "dl{ " sepBy(dl_hyp, ", ") " ⟹ " dl_fml " }" : term
/-- A sequent `Γ ⟹ₖ φ`, to be proved with solkey's rules alone (`⊢ₖ`). -/
syntax "dl{ " sepBy(dl_hyp, ", ") " ⟹ₖ " dl_fml " }" : term
/-- A sequent `Γ ⟹[R] φ` over the rule set `R` (`Proves R Γ φ`). -/
syntax "dl{ " sepBy(dl_hyp, ", ") " ⟹[" term "] " dl_fml " }" : term
/-- A sequent `Γ ⟹ᶜ[I] φ` of the calculus with callbacks, every `transfer`,
`send` and `try` calling back into a contract with the invariant `I`
(`ProvesC I true Γ φ`; today's judgement was deleted at W4 `sem-del`, the
scoped one is `Calculus/Callback.lean`'s). -/
syntax "dl{ " sepBy(dl_hyp, ", ") " ⟹ᶜ[" term "] " dl_fml " }" : term
/-- The same under `transferSemantics:noCallback`: only a `try` and a value
call call back (`ProvesC I false Γ φ`). -/
syntax "dl{ " sepBy(dl_hyp, ", ") " ⟹ᶜ[" term "; " &"noCallback" "] " dl_fml " }" : term
/-- A term of the logic (`Tm`), its sort read off its head (`find(…)` a
value, `save(…)` a storage, `write(…)` a memory, `consr(…)` a path).  Every
name is a Lean variable of a term sort: `tm{ find(save(st, p, v), q) }`. -/
syntax "tm{ " dl_term " }" : term
/-- A taclet for either modality (`⟨[ s; ]⟩`). -/
syntax "dl{ " "⟨" "[ " sol_stmt "; " "]" "⟩" " ⇝ " dl_premise " }" : term
/-- A taclet for the box only. -/
syntax "dl{ " "[ " sol_stmt "; " "]" " ⇝ " dl_premise " }" : term
/-- A taclet for the diamond only. -/
syntax "dl{ " "⟨ " sol_stmt "; " "⟩" " ⇝ " dl_premise " }" : term
/-- A rule of another judgement `J`, read as a taclet is (`J m s p`):
`dl[LeanTaclet C k]{ ⟨ s; ⟩ ⇝ p }`, `dl[CallbackTaclet C]{ [ s; ] ⇝ p }`. -/
syntax (name := dlJudgement) "dl[" term "]{ " "⟨" "[ " sol_stmt "; " "]" "⟩" " ⇝ " dl_premise " }" : term
@[inherit_doc dlJudgement] syntax "dl[" term "]{ " "[ " sol_stmt "; " "]" " ⇝ " dl_premise " }" : term
@[inherit_doc dlJudgement] syntax "dl[" term "]{ " "⟨ " sol_stmt "; " "⟩" " ⇝ " dl_premise " }" : term
syntax "dl{ " dl_premise " }" : term
/-- `⊨ᶠ φ` for a formula given as a Lean term. -/
syntax:25 (name := validSyntax) "⊨ᶠ " term:26 : term
/-- `σ ⊧ φ`: the formula `φ` holds in the state `σ`. -/
syntax:50 (name := holdsSyntax) term:51 " ⊧ " term:51 : term

open Lean Elab Term Meta in
/-- `⊨ᶠ φ` is `Fml.Valid φ` and `σ ⊧ φ` is `holds σ φ` for a scoped formula
(`Fml`, `Calculus/Logic.lean`). -/
def elabValidHolds (σ? : Option Lean.Term) (φ : Lean.Term) : TermElabM Lean.Expr := do
  let φ ← elabTerm φ none
  synthesizeSyntheticMVarsNoPostponing
  let φ ← instantiateMVars φ
  let ty ← whnf (← inferType φ)
  match σ?, ty.getAppFn.constName?, ty.getAppArgs with
  | none, some `Solidity.Fml, #[_, _] => mkAppM `Solidity.Fml.Valid #[φ]
  | none, _, _ => throwError "⊨ᶠ reads a scoped formula (`Fml C []`), not{indentExpr φ}"
  | some σ, some `Solidity.Fml, #[C, Γ] =>
    let σ ← elabTermEnsuringType σ (mkApp2 (mkConst `Solidity.State) C Γ)
    return mkApp4 (mkConst `Solidity.holds) C Γ σ φ
  | some _, _, _ => throwError "⊧ reads a scoped formula (`Fml C Γ`), not{indentExpr φ}"

open Lean Elab Term in
elab_rules : term
  | `(⊨ᶠ $φ:term) => elabValidHolds none φ
  | `($σ:term ⊧ $φ:term) => elabValidHolds (some σ) φ

/-! ## Side conditions

A taclet's schema variables carry the conditions their names and positions
state (`sideConds` below): `nsp` is not simple, `sp` is, a value written to
storage is not a conditional.  Each is a hypothesis of the constructor,
`autoParam`ed with `side_cond`, so a rule applied to a statement proves its
own conditions (by computation, or from a branch fact in scope), and the
printers leave them out: the taclet still reads as its one line. -/

/-- Prove a taclet's side condition: by computation on a statement written
out, or from the facts a dispatcher branch has in scope (its rules are in
`Calculus/Rules.lean`, after the conditions). -/
syntax "side_cond" : tactic

-- `Solidity.sideCond`: `side_cond`, as an `autoParam` stores a tactic.
run_elab do
  discard <| Lean.Elab.Term.declareTacticSyntax (← `(tactic| side_cond)) (some `Solidity.sideCond)

/-- `taclet_side% T (h₁ : c₁) … (hₙ : cₙ)`: `T` under the hypotheses `cᵢ`,
each filled by `side_cond`.  `T` is elaborated first, so it binds the schema
variables in the order it reads them. -/
syntax "taclet_side% " term:max (ppSpace "(" ident " : " term ")")* : term

/-! ## Reading schemas (macros) -/

section Expand
open Lean (Ident Macro MacroM mkIdent mkIdentFrom Name TSyntax Syntax)

/-- The kind a name's spelling gives it: `sp2` and `sp₂` are `sp`. -/
def stemOf (s : String) : String :=
  let t := s.dropRightWhile fun c => c.isDigit || ('₀' ≤ c && c ≤ '₉') || c == '\''
  if t.isEmpty then s else t

/-- A name a declaration to the left bound. -/
inductive Decl where
  | val (x : Lean.Term)
  | alias (x : Lean.Term)
  /-- A memory local, and the proof its type holds no mapping. -/
  | mem (x h : Lean.Term)
  /-- The mark of `tm{ … }`: every name is a Lean variable of a term sort. -/
  | raw

abbrev Scope := List (String × Decl)

/-- The scope of `tm{ … }`, whose names carry no kind. -/
def rawScope : Scope := [("‹raw›", .raw)]

/-- Whether names are read without their kinds (`tm{ … }`). -/
def Scope.isRaw (Γ : Scope) : Bool := Γ.any (·.1 == "‹raw›")

/-- The scope of a scoped taclet (`open scoped Solidity.Schema`,
`docs/intrinsic.md`, "how `dl{ … }` will write a scoped taclet"): every
name declared above the mark is a position of `Solidity`'s syntax,
`Idx.there^j .here` with `j` its distance from the newest, and a schema
variable of the `\find` is read under all of them (`.there`, `up`). -/
def coreScope : Scope := [("‹core›", .raw)]

/-- Whether names are read as scoped positions. -/
def Scope.isCore (Γ : Scope) : Bool := Γ.any (·.1 == "‹core›")

/-- The locals declared above the mark, a `\find`'s schema variables read
under them. -/
def Scope.depth (Γ : Scope) : Nat := (Γ.takeWhile (·.1 != "‹core›")).length

/-- `f` applied `n` times to `x`. -/
def iterApp (f : Lean.Name) : Nat → Lean.Term → Lean.Term
  | 0, x => x
  | n + 1, x => iterApp f n (Lean.Syntax.mkApp (Lean.mkCIdent f) #[x])

/-- The position `j` locals below the newest: `Idx.there^j .here`. -/
def corePos (j : Nat) : Lean.Term :=
  iterApp `Solidity.Idx.there j (Lean.mkCIdent `Solidity.Idx.here)

/-- A variable named `s`, resolved where the notation is used. -/
def schemaIdent (s : String) : Ident := mkIdent (Name.mkSimple s)

/-- The part `s` of the dotted name `x`, on its own characters. -/
def partIdent (x : Ident) (s : String) : Ident := Id.run do
  let .original _ pos _ _ := x.raw.getHeadInfo | return mkIdentFrom x (Name.mkSimple s)
  let parts := nameParts x.getId
  let some i := parts.idxOf? s | return mkIdentFrom x (Name.mkSimple s)
  let off := (parts.take i).foldl (fun n p => n + p.utf8ByteSize + 1) 0
  let start : String.Pos := ⟨pos.byteIdx + off⟩
  let stop : String.Pos := ⟨start.byteIdx + s.utf8ByteSize⟩
  let info := Lean.SourceInfo.original "".toSubstring start "".toSubstring stop
  return ⟨Syntax.ident info s.toSubstring (Name.mkSimple s) []⟩

/-- The proof that comes with a name: `hgsp` for `gsp`, `hfld` for `fld`. -/
def proofIdent (x : Ident) (s : String) : Ident := mkIdentFrom x (Name.mkSimple ("h" ++ s))

/-- The sort a program position asks for. -/
inductive Pos where
  | val | simple | spath | loc | mpath | mloc | oploc
  deriving DecidableEq

def Pos.name : Pos → String
  | .val => "a value" | .simple => "a simple value" | .spath => "a storage path"
  | .loc => "a storage location" | .mpath => "a memory path" | .mloc => "a memory location"
  | .oploc => "a compound-assignment target"

def posError (x : Lean.Syntax) (what : String) (pos : Pos) : MacroM α :=
  Macro.throwErrorAt x s!"{what} cannot stand where {pos.name} is expected"

/-- What a name is, by its stem (or its declaration in scope). -/
inductive Head where
  | local (x : Lean.Term) | alias (x : Lean.Term) | mem (x h : Lean.Term)
  | root (x h : Lean.Term) | simple (x : Lean.Term) | val (x : Lean.Term)
  | spath (x : Lean.Term) | mpath (x : Lean.Term) | loc (x : Lean.Term) | mloc (x : Lean.Term)
  | other (x : Lean.Term)
  /-- A scoped schema variable of no fixed sort read under `d` locals: its
  position's `up` (`Pos.coreUp`) `d` times. -/
  | weak (x : Lean.Term) (d : Nat)

/-- The `up` of a position's family (`Calculus/Shift.lean`). -/
def Pos.coreUp : Pos → Lean.Name
  | .val => `Solidity.Val.up | .simple => `Solidity.Simple.up
  | .spath => `Solidity.SPath.up | .loc => `Solidity.Loc.up
  | .mpath => `Solidity.MPath.up | .mloc => `Solidity.MLoc.up
  | .oploc => `Solidity.OpLoc.up

/-- A schema variable's head by its stem (`s`, the name of `x`), weakened
past `d` locals: a position by `.there`, a part by its `up`; `none` for a
stem of no fixed sort. -/
def headOfStem (x : Ident) (s : String) (d : Nat) : Option Head :=
  let there := iterApp `Solidity.Idx.there d
  match stemOf s with
  | "v" | "lv" | "vp" | "pv" => some (.local (there x))
  | "lsv" => some (.alias (there x))
  | "mv" | "pmv" | "rmv" => some (.mem (there x) (proofIdent x s))
  | "gsp" => some (.root x (proofIdent x s))
  | "se" | "ie" | "sadr" => some (.simple (iterApp `Solidity.Simple.up d x))
  | "e" | "nse" | "nadr" | "cond" | "inv" | "dec" => some (.val (iterApp `Solidity.Val.up d x))
  | "sp" | "nsp" | "path" | "map" | "arr" | "parr" | "rarr" | "marr" | "darr" =>
    some (.spath (iterApp `Solidity.SPath.up d x))
  | "nmp" | "mpath" => some (.mpath (iterApp `Solidity.MPath.up d x))
  | "nlhs" | "loc" => some (.loc (iterApp `Solidity.Loc.up d x))
  | "mloc" => some (.mloc (iterApp `Solidity.MLoc.up d x))
  | _ => none

/-- `headOf` in a scoped taclet: a name declared above the mark is its
position; a schema variable of the `\find` is weakened past every local
declared above the mark (`headOfStem`). -/
def headOfCore (Γ : Scope) (x : Ident) (s : String) : Head :=
  match Γ.findIdx? (·.1 == s), Γ.lookup s with
  | some j, some (.val _) => .local (corePos j)
  | some j, some (.alias _) => .alias (corePos j)
  | some j, some (.mem _ h) => .mem (corePos j) h
  | _, _ =>
    let d := Γ.depth
    (headOfStem x s d).getD (if d == 0 then .other x else .weak x d)

def headOf (Γ : Scope) (x : Ident) : Head :=
  let s := x.getId.toString
  if Γ.isCore then headOfCore Γ x s else
  match Γ.lookup s with
  | some (.val v) => .local v
  | some (.alias v) => .alias v
  | some (.mem v h) => .mem v h
  | some .raw => .other x
  | none => if Γ.isRaw then .other x else match stemOf s with
    -- the invariant rules' fresh locals: KeY's `s#b` (`bType b = cond;`), the
    -- condition's value, and `\skolemTerm int variant`, the variant's before
    -- the iteration (`whileInvariantBox`, `whileInvariantDiamond`)
    | "b" => .local (Lean.Syntax.mkApp (mkIdent ``Var.fresh)
        #[Lean.Syntax.mkStrLit "se", schemaIdent "k"])
    | "variant" => .local (Lean.Syntax.mkApp (mkIdent ``Var.fresh)
        #[Lean.Syntax.mkStrLit "ie", schemaIdent "k"])
    | _ => (headOfStem x s 0).getD (.other x)

/-- A head at a position. -/
def headAt (pos : Pos) (stx : Lean.Syntax) : Head → MacroM Lean.Term
  | .local v => match pos with
    | .val => `(Val.simple (Simple.local $v))
    | .simple => `(Simple.local $v)
    | .oploc => `(OpLoc.local $v)
    | _ => posError stx "a stack local" pos
  | .alias v => match pos with
    | .spath => `(SPath.alias $v)
    | _ => posError stx "a storage alias" pos
  | .mem v h => match pos with
    | .mpath => `(MPath.var $v $h)
    | _ => posError stx "a memory local" pos
  | .root r h => match pos with
    | .loc => `(Loc.root $r $h)
    | .spath => `(SPath.loc (Loc.root $r $h))
    | .val => `(Val.read (Loc.root $r $h))
    | .oploc => `(OpLoc.root $r $h)
    | _ => posError stx "a state variable" pos
  | .simple x => match pos with
    | .val => `(Val.simple $x)
    | .simple => pure x
    | _ => posError stx "a simple value" pos
  | .val x => match pos with
    | .val => pure x
    | _ => posError stx "a value" pos
  | .spath x => match pos with
    | .spath => pure x
    | .val => `(SPath.primitiveRead $x)
    | _ => posError stx "a storage path" pos
  | .mpath x => match pos with
    | .mpath => pure x
    | _ => posError stx "a memory path" pos
  | .loc x => match pos with
    | .loc => pure x
    | .spath => `(SPath.loc $x)
    | .val => `(Val.read $x)
    | _ => posError stx "a storage location" pos
  | .mloc x => match pos with
    | .mloc => pure x
    | .mpath => `(MPath.loc $x)
    | .val => `(Val.readMem $x)
    | _ => posError stx "a memory location" pos
  | .other x => pure x
  | .weak x d => pure (iterApp pos.coreUp d x)

/-- Whether an expression is a memory path: its head is a memory local or a
memory path variable. -/
partial def isMem (Γ : Scope) : TSyntax `sol_expr → Bool
  | `(sol_expr| $x:ident) =>
    match nameParts x.getId with
    | h :: _ => match headOf Γ (mkIdent (Name.mkSimple h)) with
      | .mem .. | .mpath _ | .mloc _ => true
      | _ => false
    | [] => false
  | `(sol_expr| $e:sol_expr . $_:ident) => isMem Γ e
  | `(sol_expr| $e:sol_expr [ $_:sol_expr ]) => isMem Γ e
  | `(sol_expr| ( $e:sol_expr )) => isMem Γ e
  | _ => false

/-- Whether a write's right-hand side is a path to copy: its head is a path
variable (`sp`, `nsp`, `path`, `map`, `arr`, an alias).  A value's head is a
value variable (`se`, `nse`, `e`), a local, or a literal. -/
partial def isPath (Γ : Scope) : TSyntax `sol_expr → Bool
  | `(sol_expr| $x:ident) =>
    match nameParts x.getId with
    | h :: _ => match headOf Γ (mkIdent (Name.mkSimple h)) with
      | .spath _ | .alias _ => true
      | _ => false
    | [] => false
  | `(sol_expr| $e:sol_expr . $_:ident) => isPath Γ e
  | `(sol_expr| $e:sol_expr [ $_:sol_expr ]) => isPath Γ e
  | `(sol_expr| ( $e:sol_expr )) => isPath Γ e
  | _ => false

/-- A whole right-hand side that is a schema variable: `src`, `rhs`, `mrhs`,
`msrc`. -/
def rhsVar? (stem : String) : TSyntax `sol_expr → Option Ident
  | `(sol_expr| $x:ident) => if stemOf x.getId.toString == stem then some x else none
  | _ => none

/-- A whole right-hand side that is a schema variable, as a term: in a
scoped taclet weakened past the locals declared above the mark. -/
def rhsTerm (Γ : Scope) (stem : String) (r : TSyntax `sol_expr) : Option Lean.Term :=
  (rhsVar? stem r).map fun x =>
    if !Γ.isCore then x else
    let up := match stem with
      | "rhs" => `Solidity.ARhs.up | "mrhs" => `Solidity.MRhs.up
      | "src" => `Solidity.Src.up | _ => `Solidity.MSrc.up
    iterApp up Γ.depth x

/-- How a storage receiver of the name `n` is indexed, by its stem. -/
def indexTyOfStem (n : String) : MacroM Lean.Term :=
  match stemOf n with
  | "map" => `(IndexTy.map)
  | "arr" | "parr" | "rarr" | "marr" | "darr" => `(IndexTy.arr $(schemaIdent "ak"))
  | _ => pure (schemaIdent "it")

/-- How a storage receiver is indexed: `map[ie]` by key, `arr[ie]` by
position — into a dynamic or a fixed-size array, the schema variable `ak`
(`ArrTy`), as solkey's `Path[…,array]` takes either — anything else by the
schema variable `it`. -/
def indexTyOf : TSyntax `sol_expr → MacroM Lean.Term
  | `(sol_expr| $x:ident) => indexTyOfStem x.getId.toString
  | _ => pure (schemaIdent "it")

mutual

/-- `b.f` at `pos`: a storage or a memory member. -/
partial def fieldAt (Γ : Scope) (pos : Pos) (stx : Lean.Syntax) (mem : Bool) (b : Lean.Term)
    (f : Ident) : MacroM Lean.Term := do
  let h := proofIdent f f.getId.toString
  if f.getId.toString == "length" && pos == .val then
    -- the element type named `E`, so that the scratch path a rule reads the
    -- length through has it too
    return ← if mem then `(Val.mlen (E := $(schemaIdent "E")) $b $(schemaIdent "hlen"))
      else `(Val.len (E := $(schemaIdent "E")) $b $(schemaIdent "hlen"))
  if mem then
    match pos with
    | .mloc => `(MLoc.field $b $f $h)
    | .mpath => `(MPath.loc (MLoc.field $b $f $h))
    | .val => `(Val.readMem (MLoc.field $b $f $h))
    | .oploc => `(OpLoc.mfield $b $f $h)
    | _ => posError stx "a memory member" pos
  else
    match pos with
    | .loc => `(Loc.field $b $f $h)
    | .spath => `(SPath.loc (Loc.field $b $f $h))
    | .val => `(Val.read (Loc.field $b $f $h))
    | .oploc => `(OpLoc.field $b $f $h)
    | _ => posError stx "a storage member" pos

/-- `b.f₁.….fₙ`: the inner members are receivers. -/
partial def fieldsAt (Γ : Scope) (pos : Pos) (stx : Lean.Syntax) (mem : Bool) (b : Lean.Term) :
    List Ident → MacroM Lean.Term
  | [] => pure b
  | [f] => fieldAt Γ pos stx mem b f
  | f :: fs => do fieldsAt Γ pos stx mem (← fieldAt Γ (if mem then .mpath else .spath) stx mem b f) fs

/-- A program expression at the sort `pos`. -/
partial def schemaAt (Γ : Scope) (pos : Pos) : TSyntax `sol_expr → MacroM Lean.Term
  | stx@`(sol_expr| $n:num) => match pos with
    | .val => `(Val.simple (Simple.lit $n rfl))
    | .simple => `(Simple.lit $n rfl)
    | _ => posError stx "a number" pos
  | stx@`(sol_expr| $x:ident) => do
    match nameParts x.getId with
    | [] => Macro.throwError "empty identifier"
    | ["true"] | ["false"] =>
      let b ← if x.getId.toString == "true" then `(true) else `(false)
      match pos with
      | .val => `(Val.simple (Simple.bool $b))
      | .simple => `(Simple.bool $b)
      | _ => posError stx "a Boolean" pos
    | [_] => headAt pos x (headOf Γ x)
    | h :: fs =>
      let hx := partIdent x h
      let mem := match headOf Γ hx with
        | .mem .. | .mpath _ | .mloc _ => true
        | _ => false
      let b ← headAt (if mem then .mpath else .spath) x (headOf Γ hx)
      fieldsAt Γ pos stx mem b (fs.map (partIdent x))
  | stx@`(sol_expr| $e:sol_expr . $f:ident) => do
    let mem := isMem Γ e
    fieldsAt Γ pos stx mem (← schemaAt Γ (if mem then .mpath else .spath) e)
      ((nameParts f.getId).map (partIdent f))
  | stx@`(sol_expr| $e:sol_expr [ $k:sol_expr ]) => do
    if isMem Γ e then
      let b ← schemaAt Γ .mpath e
      -- a memory array of either kind: the schema variable `mk` (`ArrTy`)
      let a := schemaIdent "mk"
      match pos with
      | .mloc => `(MLoc.index $a $b $(← schemaAt Γ .val k))
      | .mpath => `(MPath.loc (MLoc.index $a $b $(← schemaAt Γ .val k)))
      | .val => `(Val.readMem (MLoc.index $a $b $(← schemaAt Γ .val k)))
      | .oploc => `(OpLoc.mindex $a $b $(← schemaAt Γ .simple k))
      | _ => posError stx "a memory element" pos
    else
      let b ← schemaAt Γ .spath e
      let it ← indexTyOf e
      match pos with
      | .loc => `(Loc.index $it $b $(← schemaAt Γ .val k))
      | .spath => `(SPath.loc (Loc.index $it $b $(← schemaAt Γ .val k)))
      | .val => `(Val.read (Loc.index $it $b $(← schemaAt Γ .val k)))
      | .oploc => `(OpLoc.index $it $b $(← schemaAt Γ .simple k))
      | _ => posError stx "a storage entry" pos
  | `(sol_expr| ( $e:sol_expr )) => schemaAt Γ pos e
  | `(sol_expr| ‹ $t:term ›) => pure t
  | stx@`(sol_expr| $f:ident($a:sol_expr, $b:sol_expr, $k:sol_expr)) => do
    unless pos == .val do posError stx "a modular builtin" pos
    let op : Lean.Term ← match f.getId.eraseMacroScopes.toString with
      | "addmod" => `(ModOp.addmod)
      | "mulmod" => `(ModOp.mulmod)
      | _ => Macro.throwUnsupported
    `(Val.modular $op $(← schemaAt Γ .val a) $(← schemaAt Γ .val b) $(← schemaAt Γ .val k))
  | stx@`(sol_expr| $f:ident($a:sol_expr)) => do
    -- `hash(b)`: a hashing builtin, its kind the schema variable `hh`;
    -- `keccak256(b)`, `sha256(b)`, … one of them
    let fn := f.getId.eraseMacroScopes.toString
    let k : Lean.Term ← if fn == "hash" then pure (schemaIdent "hh") else
      match HashKind.ofName? fn with
      | some .keccak => pure (Lean.mkCIdent ``HashKind.keccak)
      | some .sha256 => pure (Lean.mkCIdent ``HashKind.sha256)
      | some .ripemd160 => pure (Lean.mkCIdent ``HashKind.ripemd160)
      | some .ecrecover => pure (Lean.mkCIdent ``HashKind.ecrecover)
      | none => Macro.throwUnsupported
    unless pos == .val do posError stx "a hash" pos
    `(Val.hash $k $(← schemaAt Γ .mpath a) $(schemaIdent "hk"))
  | stx@`(sol_expr| $a:sol_expr ⊕ $b:sol_expr) => do
    unless pos == .val do posError stx "an operator application" pos
    `(Val.binop (p := $(schemaIdent "p")) $(schemaIdent "op") $(schemaIdent "hop") $(schemaIdent "hq")
        $(← schemaAt Γ .val a) $(← schemaAt Γ .val b))
  | stx@`(sol_expr| ⊖ $a:sol_expr) => do
    unless pos == .val do posError stx "an operator application" pos
    `(Val.unop (p := $(schemaIdent "p")) $(schemaIdent "op") $(schemaIdent "hop") $(schemaIdent "hq")
      $(← schemaAt Γ .val a))
  | stx@`(sol_expr| $a:sol_expr && $b:sol_expr) => do
    unless pos == .val do posError stx "`&&`" pos
    `(Val.binop BinOp.and rfl rfl $(← schemaAt Γ .val a) $(← schemaAt Γ .val b))
  | stx@`(sol_expr| $a:sol_expr || $b:sol_expr) => do
    unless pos == .val do posError stx "`||`" pos
    `(Val.binop BinOp.or rfl rfl $(← schemaAt Γ .val a) $(← schemaAt Γ .val b))
  | stx@`(sol_expr| $c:sol_expr ? $a:sol_expr : $b:sol_expr) => do
    unless pos == .val do posError stx "a conditional" pos
    `(Val.ternary $(← schemaAt Γ .val c) $(← schemaAt Γ .val a) $(← schemaAt Γ .val b))
  | _ => Macro.throwUnsupported

end

/-- The variable a declaration introduces: the name itself, or — in a
taclet's `\replacewith` — the fresh variable its spelling asks for. -/
def declVar (fresh : Bool) (x : Ident) : MacroM Lean.Term := do
  unless fresh do return x
  let k := schemaIdent "k"
  match stemOf x.getId.toString with
  | "se" => `(Var.fresh "se" $k)
  | "sp" => `(Var.fresh "sp" $k)
  | "ie" => `(Var.fresh "ie" $k)
  | "mv" => `(Var.fresh "mv" $k)
  | "source" => `(Var.fresh "source" $k)
  | _ => Macro.throwErrorAt x "a taclet declares only fresh `se`, `sp`, `ie`, `mv` or `source`"

/-- `sp.push` called: the receiver `sp` and the method `push`. -/
def callRecv? (f : TSyntax `sol_expr) : MacroM (Option (TSyntax `sol_expr × String)) := do
  match f with
  | `(sol_expr| $x:ident) =>
    match (nameParts x.getId).reverse with
    | m :: r :: rs =>
      let n := (r :: rs).reverse.foldl (fun n s => Name.str n s) Name.anonymous
      return some (← `(sol_expr| $(mkIdentFrom x n):ident), m)
    | _ => return none
  | `(sol_expr| $e:sol_expr . $g:ident) => return some (e, g.getId.toString)
  | _ => return none

/-- The array receiver of a primitive push used as an lvalue. -/
partial def pushExprBase? : TSyntax `sol_expr → MacroM (Option (TSyntax `sol_expr))
  | `(sol_expr| $f:sol_expr ( )) => do
    let some (b, "push") ← callRecv? f | return none
    return some b
  | `(sol_expr| ($e:sol_expr)) => pushExprBase? e
  | _ => return none

/-- A fixed native push operator, for specializing its replacement terms. -/
partial def fixedPushOperator? (s : TSyntax `sol_stmt) : MacroM (Option (Lean.Term × Bool)) := do
  if s.raw.getKind == Lean.choiceKind then
    for alt in s.raw.getArgs do
      if let some fixed ← fixedPushOperator? ⟨alt⟩ then return some fixed
    return none
  if let some (op, _, _) ← pushCompoundParts? s.raw then
    return some (⟨(ctorIdent ``BinOp op).raw⟩, true)
  if let some (op, _) ← pushIncrementParts? s.raw then
    return some (⟨(ctorIdent ``IncDec op).raw⟩, false)
  let (l, op, compound) ← match s with
    | `(sol_stmt| $l:sol_expr += $_:sol_expr) => pure (l, ← `(BinOp.add), true)
    | `(sol_stmt| $l:sol_expr -= $_:sol_expr) => pure (l, ← `(BinOp.sub), true)
    | `(sol_stmt| $l:sol_expr *= $_:sol_expr) => pure (l, ← `(BinOp.mul), true)
    | `(sol_stmt| $l:sol_expr /= $_:sol_expr) => pure (l, ← `(BinOp.div), true)
    | `(sol_stmt| $l:sol_expr %= $_:sol_expr) => pure (l, ← `(BinOp.mod), true)
    | `(sol_stmt| $l:sol_expr ++) => pure (l, ← `(IncDec.postInc), false)
    | `(sol_stmt| ++ $l:sol_expr) => pure (l, ← `(IncDec.preInc), false)
    | `(sol_stmt| $l:sol_expr −−) => pure (l, ← `(IncDec.postDec), false)
    | `(sol_stmt| −− $l:sol_expr) => pure (l, ← `(IncDec.preDec), false)
    | _ => return none
  if (← pushExprBase? l).isSome then return some (op, compound) else return none

/-- The native statement shape of `sp.push() += se`. -/
def schemaPushCompound (Γ : Scope) (op : Lean.Term) (l r : TSyntax `sol_expr) :
    MacroM (Lean.Term × Scope) := do
  let some b ← pushExprBase? l | Macro.throwUnsupported
  return (← `(Stmt.pushOpAssign (p := $(schemaIdent "p")) $op rfl $(schemaIdent "hp")
    $(← schemaAt Γ .spath b) $(← schemaAt Γ .val r)), Γ)

/-- The native statement shape of `++sp.push();` or `sp.push()++;`. -/
def schemaPushIncrement (Γ : Scope) (op : Lean.Term) (l : TSyntax `sol_expr) :
    MacroM (Lean.Term × Scope) := do
  let some b ← pushExprBase? l | Macro.throwUnsupported
  return (← `(Stmt.pushIncDec (p := $(schemaIdent "p")) $op $(schemaIdent "hp")
    $(← schemaAt Γ .spath b)), Γ)

/-- `new T(n)`: its size. -/
def newRhs? : TSyntax `sol_expr → Option (TSyntax `sol_expr)
  | `(sol_expr| new $_:sol_ty ( $n:sol_expr )) => some n
  | _ => none

/-- The stem of a one-name expression. -/
def stemOfExpr? : TSyntax `sol_expr → Option String
  | `(sol_expr| $x:ident) =>
    match nameParts x.getId with
    | [s] => some (stemOf s)
    | _ => none
  | _ => none

/-- The type a memory `delete` fixes by its spelling: `delete mv;` a
reference, `delete mv.pfld;` and `delete pmv[ie];` a primitive,
`delete mv.rfld;` and `delete rmv[ie];` a reference; any other leaves it
free. -/
def deleteTy? : TSyntax `sol_expr → MacroM (Option Lean.Term)
  | `(sol_expr| $x:ident) => do
    match (nameParts x.getId).reverse with
    | [_] => some <$> `(Ty.ref $(schemaIdent "R"))
    | f :: _ =>
      match stemOf f with
      | "pfld" => some <$> `(Ty.prim $(schemaIdent "p"))
      | "rfld" => some <$> `(Ty.ref $(schemaIdent "R"))
      | _ => pure none
    | [] => pure none
  | `(sol_expr| $b:sol_expr [ $_:sol_expr ]) => do
    match stemOfExpr? b with
    | some "pmv" => some <$> `(Ty.prim $(schemaIdent "p"))
    | some "rmv" => some <$> `(Ty.ref $(schemaIdent "R"))
    | _ => pure none
  | _ => pure none

/-- Whether an expression is a stack local, a storage alias, a memory local,
a hole — the statement it is the left of. -/
def lhsHead (Γ : Scope) : TSyntax `sol_expr → Option Head
  | `(sol_expr| $x:ident) =>
    match nameParts x.getId with
    | [_] => some (headOf Γ x)
    | _ => none
  | _ => none

/-- What a statement of a schema stands for: one statement, or a program
spliced in its place (`P`, `expand_function_body(fbs)`). -/
inductive Item where
  | one (t : Lean.Term)
  | many (t : Lean.Term)
  deriving Inhabited

/-- A program schema variable, by its stem. -/
def isProgStem (s : String) : Bool := ["P", "Q", "ω", "body"].contains (stemOf s)

/-- Whether `s` names a call with its body: `fbs` (KeY's `FunctionBody`) or
`ic` (`InternalCall`). -/
def isCallStem (s : String) : Bool := ["fbs", "ic"].contains (stemOf s)

/-- `fbs`, `ic`, a call with its body: `Stmt.call f args ret body`, its
parts the taclet's schema variables (a call is closed over its frame). -/
def fbsCall : MacroM Lean.Term :=
  `(Stmt.call $(schemaIdent "f") $(schemaIdent "args") $(schemaIdent "ret") $(schemaIdent "body"))

/-- A scoped program: the items consed onto `Prog.nil`, a program spliced in
as one block (`Stmt.block`, the scoped syntax has no append). -/
def progTermCore (items : Array Item) : MacroM Lean.Term :=
  items.foldrM (init := Lean.mkCIdent `Solidity.Prog.nil) fun it acc => match it with
    | .one s => `($(Lean.mkCIdent `Solidity.Prog.cons) $s $acc)
    | .many P => `($(Lean.mkCIdent `Solidity.Prog.cons) ($(Lean.mkCIdent `Solidity.Stmt.block) $P) $acc)

/-- A clause parameter that is one name, a schema variable: `rets`, `code`. -/
def tparamVar? (p : TSyntax `sol_tparam) : Option Ident :=
  match p with
  | `(sol_tparam| $T:sol_ty) => match T with
    | `(sol_ty| $x:ident) => some x
    | _ => none
  | _ => none

/-- The `try` of a taclet's `\find`, in KeY's schema: `try call returns (rets)
body catch Error errorBody catch Panic (code) panicBody catch otherBody`.  The
names are the schema variables they spell (`call`, `rets`, `code`, the blocks). -/
def schemaTry (stx : TSyntax `sol_stmt) : MacroM Lean.Term := do
  let (c, rets, ok, cs) ← match stx with
    | `(sol_stmt| try $c:sol_expr returns ($ps,*) $ok:sol_block $cs:sol_catch*) => do
      let #[p] := ps.getElems | Macro.throwErrorAt stx "a taclet's `try` returns `(rets)`"
      let some x := tparamVar? p | Macro.throwErrorAt p "a taclet's `try` returns `(rets)`"
      pure (c, (x : Lean.Term), ok, cs)
    | `(sol_stmt| try $c:sol_expr $ok:sol_block $cs:sol_catch*) => do
      pure (c, ← `([]), ok, cs)
    | _ => Macro.throwUnsupported
  let `(sol_expr| $call:ident) := c | Macro.throwErrorAt c "a taclet's `try` calls `call`"
  let block (b : TSyntax `sol_block) : MacroM Lean.Term := match b with
    | `(sol_block| $x:ident) => pure x
    | `(sol_block| ‹ $t:term ›) => pure t
    | _ => Macro.throwErrorAt b "a taclet's `try` has a schema variable for each block"
  let #[e, p, o] := cs |
    Macro.throwErrorAt stx "a taclet's `try` has the clauses `catch Error`, `catch Panic (code)`, `catch`"
  let err ← match e with
    | `(sol_catch| catch Error $b:sol_block) => block b
    | _ => Macro.throwErrorAt e "`catch Error errorBody`"
  let (code, pnc) ← match p with
    | `(sol_catch| catch Panic ($t:sol_tparam) $b:sol_block) =>
      match tparamVar? t with
      | some x => do pure ((x : Lean.Term), ← block b)
      | none => Macro.throwErrorAt t "`catch Panic (code) panicBody`"
    | _ => Macro.throwErrorAt p "`catch Panic (code) panicBody`"
  let other ← match o with
    | `(sol_catch| catch $b:sol_block) => block b
    | _ => Macro.throwErrorAt o "`catch otherBody`"
  -- another contract's callee: the self-call's parts unused (`Stmt.tryCall`'s `self`)
  `(Stmt.tryCall $call $rets $(← block ok) $err $code $pnc $other $(mkIdent `selfArgs)
      $(mkIdent `selfBody) false)

/-- A taclet's `/// @custom:key` clauses above `while`: the annotation written
(`unwind 0`, `unwind n`, `unwind n + 1`, `invariant inv` with any `dec`, or
`invariant inv` and `decreases dec`), and the `while`. An escaped decrease
term is the packed, length-indexed tuple rather than a scalar component. -/
def schemaLoopSpec (stx : Lean.Syntax) : MacroM (Lean.Term × Lean.Syntax) := do
  let cl := stx[0]
  let w := stx[1]
  -- `/// @custom:key invariant inv /// @custom:key decreases dec while …`
  if w.getKind == ``solLoopSpec && cl[5].getId.toString == "invariant"
      && w[0][5].getId.toString == "decreases" then
    let w' := w[1]
    unless w'.getKind == ``solWhile do
      Macro.throwErrorAt w' "a taclet's `/// @custom:key` clauses stand above `while`"
    let msg := "a taclet's clauses are `invariant inv` and `decreases dec`"
    let x : Ident ← match (⟨cl[6]⟩ : TSyntax `sol_expr) with
      | `(sol_expr| $x:ident) => pure x
      | _ => Macro.throwErrorAt cl msg
    let annotation ← match (⟨w[0][6]⟩ : TSyntax `sol_expr) with
      | `(sol_expr| $d:ident) =>
        `(LoopAnn.inv $x (some $d) $(schemaIdent "brk") $(schemaIdent "qs"))
      | `(sol_expr| ‹ $metrics:term ›) =>
        `(LoopAnn.invLex $x $metrics $(schemaIdent "brk") $(schemaIdent "qs"))
      | _ => Macro.throwErrorAt cl msg
    return (annotation, w')
  unless w.getKind == ``solWhile do
    Macro.throwErrorAt w "a taclet's `/// @custom:key` clause stands above `while`"
  let e : TSyntax `sol_expr := ⟨cl[6]⟩
  let bad : MacroM Lean.Term := Macro.throwErrorAt cl
    "a taclet's clause is `unwind 0`, `unwind n`, `unwind n + 1` or `invariant inv`"
  let kw := cl[5].getId.toString
  let ann ← if kw == "unwind" then
      match e with
      | `(sol_expr| $n:num) => `(LoopAnn.unwind $n)
      | `(sol_expr| $x:ident) => `(LoopAnn.unwind $x)
      | `(sol_expr| $x:ident + 1) => `(LoopAnn.unwind ($x + 1))
      | _ => bad
    else if kw == "invariant" then
      match e with
      | `(sol_expr| $x:ident) =>
        `(LoopAnn.inv $x $(schemaIdent "dec") $(schemaIdent "brk") $(schemaIdent "qs"))
      | _ => bad
    else bad
  return (ann, w)

mutual

partial def schemaStmt (fresh : Bool) (Γ : Scope) :
    TSyntax `sol_stmt → MacroM (Lean.Term × Scope)
  | `(sol_stmt| ‹ $t:term ›) => return (t, Γ)
  | stx@`(sol_stmt| $x:ident) => do
    let s := x.getId.toString
    if isProgStem s then Macro.throwErrorAt stx s!"`{s}` is a program, not one statement"
    if isCallStem s then return (← fbsCall, Γ)
    return (x, Γ)
  | `(sol_stmt| $l:sol_expr = $b:sol_expr .push()) => do
    match lhsHead Γ l with
    | some (.alias x) =>
      return (← `(Stmt.rebind (R := $(schemaIdent "R")) $x (ARhs.push $(← schemaAt Γ .spath b) $(schemaIdent "hd"))), Γ)
    | some (.local v) =>
      return (← `(Stmt.assignLocalPush (p := $(schemaIdent "p")) $v $(← schemaAt Γ .spath b)), Γ)
    | _ => Macro.throwErrorAt l "`= b.push()` binds a storage alias or a value local"
  | `(sol_stmt| $l:sol_expr = $f:sol_expr ( )) => do
    let some (b, "push") ← callRecv? f | Macro.throwErrorAt f "only `b.push()` is a call on the right"
    schemaStmt fresh Γ (← `(sol_stmt| $l:sol_expr = $b:sol_expr .push()))
  | `(sol_stmt| $T:sol_ty storage $x:ident = $f:sol_expr ( )) => do
    let some (b, "push") ← callRecv? f | Macro.throwErrorAt f "only `b.push()` is a call on the right"
    schemaStmt fresh Γ (← `(sol_stmt| $T:sol_ty storage $x:ident = $b:sol_expr .push()))
  | `(sol_stmt| $x:sol_expr = $l:sol_expr ⊕⊕) => do
    let some (.local v) := lhsHead Γ x | Macro.throwErrorAt x "the value of `++` goes to a stack local"
    return (← `(Stmt.assignIncDec (p := $(schemaIdent "p")) $v $(schemaIdent "op") $(schemaIdent "hp")
      $(← schemaAt Γ .oploc l) $(schemaIdent "hs")), Γ)
  | `(sol_stmt| $l:sol_expr += $r:sol_expr) => do
    schemaPushCompound Γ (← `(BinOp.add)) l r
  | `(sol_stmt| $l:sol_expr -= $r:sol_expr) => do
    schemaPushCompound Γ (← `(BinOp.sub)) l r
  | `(sol_stmt| $l:sol_expr *= $r:sol_expr) => do
    schemaPushCompound Γ (← `(BinOp.mul)) l r
  | `(sol_stmt| $l:sol_expr /= $r:sol_expr) => do
    schemaPushCompound Γ (← `(BinOp.div)) l r
  | `(sol_stmt| $l:sol_expr %= $r:sol_expr) => do
    schemaPushCompound Γ (← `(BinOp.mod)) l r
  | `(sol_stmt| $l:sol_expr ++) => do
    schemaPushIncrement Γ (← `(IncDec.postInc)) l
  | `(sol_stmt| ++ $l:sol_expr) => do
    schemaPushIncrement Γ (← `(IncDec.preInc)) l
  | `(sol_stmt| $l:sol_expr −−) => do
    schemaPushIncrement Γ (← `(IncDec.postDec)) l
  | `(sol_stmt| −− $l:sol_expr) => do
    schemaPushIncrement Γ (← `(IncDec.preDec)) l
  | `(sol_stmt| $l:sol_expr ⊕⊕) => do
    if let some b ← pushExprBase? l then
      return (← `(Stmt.pushIncDec (p := $(schemaIdent "p")) $(schemaIdent "op") $(schemaIdent "hp")
        $(← schemaAt Γ .spath b)), Γ)
    return (← `(Stmt.incDec (p := $(schemaIdent "p")) $(schemaIdent "op") $(schemaIdent "hp")
      $(← schemaAt Γ .oploc l)), Γ)
  | `(sol_stmt| $l:sol_expr ⊕= $r:sol_expr) => do
    if let some b ← pushExprBase? l then
      return (← `(Stmt.pushOpAssign (p := $(schemaIdent "p")) $(schemaIdent "op")
        $(schemaIdent "hop") $(schemaIdent "hp") $(← schemaAt Γ .spath b)
        $(← schemaAt Γ .val r)), Γ)
    return (← `(Stmt.opAssign (p := $(schemaIdent "p")) $(schemaIdent "op") $(schemaIdent "hop") $(schemaIdent "hp")
      $(← schemaAt Γ .oploc l) $(← schemaAt Γ .val r)), Γ)
  | `(sol_stmt| $l:sol_expr = $f:sol_expr($a:sol_expr, $b:sol_expr, $k:sol_expr)) => do
    let r ← `(sol_expr| $f:sol_expr($a:sol_expr, $b:sol_expr, $k:sol_expr))
    let some (.local v) := lhsHead Γ l | Macro.throwUnsupported
    return (← `(Stmt.assignLocal $v $(← schemaAt Γ .val r)), Γ)
  | `(sol_stmt| $l:sol_expr = $r:sol_expr) => do
    let R := schemaIdent "R"
    if let some n := newRhs? r then
      let n ← schemaAt Γ .simple n
      match lhsHead Γ l, stemOfExpr? l with
      | some (.mem x _), _ =>
        return (← `(Stmt.rebindMem (R := $R) $x (MRhs.newArr (R := $R) $n $(schemaIdent "hn"))), Γ)
      | _, some "tgt" =>
        let `(sol_expr| $x:ident) := l | Macro.throwErrorAt l "a `tgt`"
        return (← `(Stmt.assignNew (R := $R) $x $n $(schemaIdent "hn")), Γ)
      | _, _ => Macro.throwErrorAt l "`new` lands in a memory local or a `tgt`"
    if stemOfExpr? l == some "tgt" then
      let `(sol_expr| $x:ident) := l | Macro.throwErrorAt l "a `tgt`"
      return (← `($(Lean.mkCIdent `Solidity.NewLhs.fill)
        $(iterApp `Solidity.NewLhs.up Γ.depth x) $(← schemaAt Γ .mpath r)), Γ)
    let t ← match lhsHead Γ l with
      | some (.local v) => `(Stmt.assignLocal $v $(← schemaAt Γ .val r))
      | some (.alias x) =>
        match rhsTerm Γ "rhs" r with
        | some v => `(Stmt.rebind $x $v)
        | none => `(Stmt.rebind $x (ARhs.path $(← schemaAt Γ .spath r)))
      | some (.mem x _) =>
        if let some v := rhsTerm Γ "mrhs" r then `(Stmt.rebindMem $x $v) else
        if isMem Γ r then `(Stmt.rebindMem $x (MRhs.alias $(← schemaAt Γ .mpath r)))
        else `(Stmt.rebindMem $x (MRhs.copy $(← schemaAt Γ .spath r) $(schemaIdent "hm")))
      | some (.other h) | some (.weak h _) =>
        match h with
        | `($x:ident) =>
          -- a scoped hole is weakened past the locals declared above the mark
          let hole (core : Lean.Name) : Lean.Term × Lean.Term :=
            (Lean.mkCIdent (`Solidity ++ core ++ `fill),
              iterApp (`Solidity ++ core ++ `up) Γ.depth x)
          match stemOf x.getId.toString with
          | "lhs" =>
            if isMem Γ r then
              let (f, h) := hole `MHole
              `($f $h $(← schemaAt Γ .mloc r))
            else if isPath Γ r then
              let (f, h) := hole `SHole
              `($f $h $(← schemaAt Γ .spath r))
            else
              let (f, h) := hole `VHole
              `($f $h $(← schemaAt Γ .val r))
          | _ => Macro.throwErrorAt l "not a left-hand side"
        | _ => Macro.throwErrorAt l "not a left-hand side"
      | _ =>
        if isMem Γ l then
          if let some v := rhsTerm Γ "msrc" r then `(Stmt.assignMem $(← schemaAt Γ .mloc l) $v) else
          if isMem Γ r then `(Stmt.assignMem $(← schemaAt Γ .mloc l) (MSrc.ref $(← schemaAt Γ .mpath r)))
          else
            -- a memory element's type is its value's, named `p` so that a
            -- scratch value written back (`mv[ie] = se`) has it too
            let elem := match l with
              | `(sol_expr| $_:sol_expr [ $_:sol_expr ]) => true
              | _ => false
            if elem then
              `(Stmt.assignMem (T := Ty.prim $(schemaIdent "p")) $(← schemaAt Γ .mloc l)
                (MSrc.val $(← schemaAt Γ .val r)))
            else `(Stmt.assignMem $(← schemaAt Γ .mloc l) (MSrc.val $(← schemaAt Γ .val r)))
        else if isMem Γ r then
          `(Stmt.assignFromMem $(← schemaAt Γ .loc l) $(← schemaAt Γ .mpath r))
        else if let some v := rhsTerm Γ "src" r then `(Stmt.assign $(← schemaAt Γ .loc l) $v)
        else if isPath Γ r then
          `(Stmt.assign $(← schemaAt Γ .loc l) (Src.copy $(← schemaAt Γ .spath r) $(schemaIdent "hm")))
        else `(Stmt.assign $(← schemaAt Γ .loc l) (Src.val $(← schemaAt Γ .val r)))
    return (t, Γ)
  | `(sol_stmt| $T:sol_ty storage $x:ident = $b:sol_expr .push()) => do
    let v ← declVar fresh x
    let _ := T
    let t ← `(Stmt.declStorage _ $v (some (ARhs.push $(← schemaAt Γ .spath b) $(schemaIdent "hd"))))
    return (t, (x.getId.toString, .alias v) :: Γ)
  | `(sol_stmt| $T:sol_ty storage $x:ident = $e:sol_expr) => do
    let v ← declVar fresh x
    let _ := T
    let r : Lean.Term ← match rhsTerm Γ "rhs" e with
      | some r => pure r
      | none => `(ARhs.path $(← schemaAt Γ .spath e))
    let t ← `(Stmt.declStorage _ $v (some $r))
    return (t, (x.getId.toString, .alias v) :: Γ)
  | `(sol_stmt| $T:sol_ty storage $x:ident) => do
    let v ← declVar fresh x
    let _ := T
    let t ← `(Stmt.declStorage $(schemaIdent "R") $v none)
    return (t, (x.getId.toString, .alias v) :: Γ)
  | `(sol_stmt| $T:sol_ty memory $x:ident = $e:sol_expr) => do
    let v ← declVar fresh x
    let _ := T
    let r : Lean.Term ← if let some r := rhsTerm Γ "mrhs" e then pure r
      else if let some n := newRhs? e then
        `(MRhs.newArr (R := $(schemaIdent "R")) $(← schemaAt Γ .simple n) $(schemaIdent "hn"))
      else if isMem Γ e then `(MRhs.alias $(← schemaAt Γ .mpath e))
      else `(MRhs.copy $(← schemaAt Γ .spath e) $(schemaIdent "hm"))
    let h ← `(MRhs.mapFree $r)
    let t ← `(Stmt.declMem _ $v (some $r) rfl $h)
    return (t, (x.getId.toString, .mem v h) :: Γ)
  | `(sol_stmt| $T:sol_ty memory $x:ident) => do
    let v ← declVar fresh x
    let _ := T
    let h := proofIdent x x.getId.toString
    let t ← `(Stmt.declMem $(schemaIdent "R") $v none $(schemaIdent "hd") $h)
    return (t, (x.getId.toString, .mem v h) :: Γ)
  | `(sol_stmt| $T:sol_ty $x:ident = $e:sol_expr) => do
    let v ← declVar fresh x
    let _ := T
    let t ← `(Stmt.declLocal _ $v (some $(← schemaAt Γ .val e)))
    return (t, (x.getId.toString, .val v) :: Γ)
  | `(sol_stmt| $T:sol_ty $x:ident) => do
    let v ← declVar fresh x
    let _ := T
    let t ← `(Stmt.declLocal $(schemaIdent "p") $v none)
    return (t, (x.getId.toString, .val v) :: Γ)
  | `(sol_stmt| $b:sol_expr .push( $a:sol_expr )) => do
    let v : Lean.Term ← if let some r := rhsTerm Γ "src" a then pure r else if isMem Γ a then `(Src.copyMem $(← schemaAt Γ .mpath a))
      else if isPath Γ a then `(Src.copy $(← schemaAt Γ .spath a) $(schemaIdent "hm"))
      else `(Src.val $(← schemaAt Γ .val a))
    return (← `(Stmt.push $(← schemaAt Γ .spath b) (some $v) rfl), Γ)
  | `(sol_stmt| $b:sol_expr .push()) => do
    return (← `(Stmt.push (E := $(schemaIdent "E")) $(← schemaAt Γ .spath b) none $(schemaIdent "hd")), Γ)
  | `(sol_stmt| $b:sol_expr .pop()) => do
    -- the element type named `E`, so that a scratch alias popped has it too
    return (← `(Stmt.pop (E := $(schemaIdent "E")) $(← schemaAt Γ .spath b)), Γ)
  | `(sol_stmt| $r:sol_expr .transfer( $a:sol_expr )) => do
    return (← `(Stmt.transfer $(← schemaAt Γ .val r) $(← schemaAt Γ .val a)), Γ)
  | `(sol_stmt| $l:sol_expr = $r:sol_expr .send( $a:sol_expr )) => do
    let some (.local v) := lhsHead Γ l | Macro.throwErrorAt l "a send's result lands in a stack local"
    return (← `(Stmt.send $v $(← schemaAt Γ .val r) $(← schemaAt Γ .val a) $(schemaIdent "full")),
      Γ)
  | `(sol_stmt| $l:sol_expr = $f:sol_expr ( $a:sol_expr )) => do
    -- `v = keccak256(mpath)`: a value, not a call
    if let `(sol_expr| $g:ident) := f then
      let fn := g.getId.eraseMacroScopes.toString
      if fn == "hash" || (HashKind.ofName? fn).isSome then
        let e ← `(sol_expr| $f:sol_expr ( $a:sol_expr ))
        return ← schemaStmt fresh Γ (← `(sol_stmt| $l:sol_expr = $e:sol_expr))
    let some (b, "send") ← callRecv? f | Macro.throwErrorAt f "only `r.send(a)` is a call assigned"
    schemaStmt fresh Γ (← `(sol_stmt| $l:sol_expr = $b:sol_expr .send( $a )))
  | `(sol_stmt| $f:sol_expr ( $a:sol_expr )) => do
    let some (b, m) ← callRecv? f | Macro.throwErrorAt f "only `b.push(a)` and `r.transfer(a)` are calls"
    match m with
    | "push" => schemaStmt fresh Γ (← `(sol_stmt| $b:sol_expr .push( $a )))
    | "transfer" => schemaStmt fresh Γ (← `(sol_stmt| $b:sol_expr .transfer( $a )))
    | _ => Macro.throwErrorAt f "only `b.push(a)` and `r.transfer(a)` are calls"
  | `(sol_stmt| $f:sol_expr ( )) => do
    let some (b, m) ← callRecv? f | Macro.throwErrorAt f "only `b.push()` and `b.pop()` are calls"
    match m with
    | "push" => schemaStmt fresh Γ (← `(sol_stmt| $b:sol_expr .push()))
    | "pop" => schemaStmt fresh Γ (← `(sol_stmt| $b:sol_expr .pop()))
    | _ => Macro.throwErrorAt f "only `b.push()` and `b.pop()` are calls"
  | `(sol_stmt| if ($c:sol_expr) $t:sol_block else $f:sol_block) => do
    return (← `(Stmt.ite $(← schemaAt Γ .val c) $(← schemaBlock fresh Γ t) $(← schemaBlock fresh Γ f)), Γ)
  | `(sol_stmt| if ($c:sol_expr) $t:sol_block) => do
    let nil : Lean.Term := ⟨(Lean.mkCIdent `Solidity.Prog.nil).raw⟩
    return (← `(Stmt.ite $(← schemaAt Γ .val c) $(← schemaBlock fresh Γ t) $nil), Γ)
  | stx => do
    let k := stx.raw.getKind
    if let some (op, b, r) ← pushCompoundParts? stx.raw then
      return (← `(Stmt.pushOpAssign (p := $(schemaIdent "p")) $(ctorIdent ``BinOp op)
        rfl $(schemaIdent "hp") $(← schemaAt Γ .spath b) $(← schemaAt Γ .val r)), Γ)
    if let some (op, b) ← pushIncrementParts? stx.raw then
      return (← `(Stmt.pushIncDec (p := $(schemaIdent "p")) $(ctorIdent ``IncDec op)
        $(schemaIdent "hp") $(← schemaAt Γ .spath b)), Γ)
    if k == ``solDelete then
      let e : TSyntax `sol_expr := ⟨stx.raw[1]⟩
      if isMem Γ e then
        let p ← schemaAt Γ .mpath e
        let hd := schemaIdent "hd"
        match ← deleteTy? e with
        | some T => return (← `(Stmt.deleteMem (T := $T) $p $hd), Γ)
        | none => return (← `(Stmt.deleteMem $p $hd), Γ)
      return (← `(Stmt.delete $(← schemaAt Γ .loc e)), Γ)
    if k == ``solRequire then return (← `(Stmt.require $(← schemaAt Γ .val ⟨stx.raw[2]⟩)), Γ)
    if k == ``solAssert then return (← `(Stmt.assert $(← schemaAt Γ .val ⟨stx.raw[2]⟩)), Γ)
    if k == ``solRevert then return (← `(Stmt.revert), Γ)
    if k == ``solAssumeFalse then return (← `(Stmt.assumeFalse), Γ)
    if k == ``solTry then return (← schemaTry stx, Γ)
    if k == ``solWhile then
      -- `while (cond) body`: the annotation is the schema variable `ann`
      return (← `(Stmt.loop $(schemaIdent "ann") $(← schemaAt Γ .val ⟨stx.raw[2]⟩)
        $(← schemaBlock fresh Γ ⟨stx.raw[4]⟩)), Γ)
    if k == ``solLoopSpec then
      let (ann, w) ← schemaLoopSpec stx.raw
      return (← `(Stmt.loop $ann $(← schemaAt Γ .val ⟨w[2]⟩) $(← schemaBlock fresh Γ ⟨w[4]⟩)), Γ)
    if k == Lean.choiceKind then
      let alts := stx.raw.getArgs
      for alt in alts.filter (·[0].isAtom) ++ alts do
        try return ← schemaStmt fresh Γ ⟨alt⟩ catch _ => pure ()
    Macro.throwUnsupported

/-- A statement of a program: one statement, or a program in its place, a
program schema variable (`P`).  `expand_function_body(fbs)` (KeY's, the
statements a call runs) is a whole premise (`schemaPremiseCore`). -/
partial def schemaItem (fresh : Bool) (Γ : Scope) (s : TSyntax `sol_stmt) :
    MacroM (Item × Scope) := do
  match s with
  | `(sol_stmt| $x:ident) =>
    if isProgStem x.getId.toString then return (.many x, Γ)
  | `(sol_stmt| $f:sol_expr ( $a:sol_expr )) =>
    if let `(sol_expr| $g:ident) := f then
      if g.getId.toString == "expand_function_body" then
        Macro.throwErrorAt a "`expand_function_body(fbs)` is a whole premise"
  | _ => pure ()
  let (t, Γ) ← schemaStmt fresh Γ s
  return (.one t, Γ)

partial def schemaProg (fresh : Bool) (Γ : Scope) (ss : Array (TSyntax `sol_stmt)) :
    MacroM (Array Item × Scope) :=
  ss.foldlM (init := (#[], Γ)) fun (ts, Γ) s => do
    let (t, Γ) ← schemaItem fresh Γ s
    return (ts.push t, Γ)

/-- A branch: its statements (their declarations stay inside), or a schema
variable standing for all of them. -/
partial def schemaBlock (fresh : Bool) (Γ : Scope) : TSyntax `sol_block → MacroM Lean.Term
  | `(sol_block| { $[$ss:sol_stmt;]* }) => do
    let (ts, _) ← schemaProg fresh Γ ss
    progTermCore ts
  | `(sol_block| $x:ident) => do
    -- a block variable read under fresh locals: weakened by `Prog.wk`
    -- (`Prog.up`, as `ifElseUnfold`'s branches are, `Calculus/Arms.lean`)
    return iterApp `Solidity.Prog.up Γ.depth x
  | `(sol_block| ‹ $t:term ›) => pure t
  | _ => Macro.throwUnsupported

end

end Expand

end Solidity
