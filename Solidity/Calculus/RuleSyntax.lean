import Solidity.Update
import Solidity.Syntax.PushSource

/-!
# The calculus's notation: `dl{ … }`

The calculus is written and read in its own notation (mini-solkey's
`Notation.lean`).  A taclet is one line,

```
storageFieldWriteSave :
  dl{ ⟨[ sp.fld = se; ]⟩ ⇝ { storage := save(storage, sp.fld, se) } ⟨[ ]⟩ }
```

and a goal prints as the line of the derivation it is.  `set_option
pp.sol.dl false` shows the constructors again.

| notation | term |
|---|---|
| `dl{ ⟨[ s; ]⟩ ⇝ p }` | the taclet `Taclet C k m s p`, for either modality (solkey's `#mod`) |
| `dl{ [ s; ] ⇝ p }`, `dl{ ⟨ s; ⟩ ⇝ p }` | a taclet for the box only, the diamond only |
| `dl[LeanTaclet C k]{ ⟨ s; ⟩ ⇝ p }` | a rule of another judgement, `LeanTaclet C k .diamond s p` |
| `dl{ p }` | a premise |
| `dl{ ..H, c, {U} ⟹[R] φ }` | the scoped sequent `Proves C R Γ₀ ((H.pre c).upd m U) φ` (`Calculus/SequentNotation.lean`) |
| `dl{ ..Γ ⟹ᶜ[I] φ }` | printing only: a scoped sequent with callbacks (`ProvesC`, `Calculus/Callback.lean`) |
| `tm{ find(save(s, p, v), q) }` | a scoped term `Tm`, every name a Lean variable (where `Calculus/TermLib.lean` is imported) |
| `⊨ φ` | `Valid φ` of a scoped `φ` (`Calculus/Logic.lean`) |
| `σ ⊧ φ` | `holds σ φ`, likewise |

At a state variable a write is `save(storage, gsp, se)` and a read
`find(storage, gsp)`, as solkey writes them; `store`/`select` still read.
`set_option pp.sol.key true` (on in `#taclet`) prints KeY's long forms,
`consr(sp, fld)`, `find(storage, consr(sp, size))`, which read as well.

## Names are schema variables, and a name carries its kind

In a taclet every identifier is a Lean variable, bound by the constructor
(an auto-bound implicit), and what it stands for is read off its name with
trailing digits and subscripts dropped, so no rule
writes an `\is…` side condition to say what its variables are.  The name
also gives the side condition the rule carries (`sideConds`, a hidden
hypothesis):

| name | is | Lean sort | side condition |
|---|---|---|---|
| `v`, `lv`, `vp`, `pv` | a stack local (`pv`: where a send's outcome lands) | `Idx Γ (LTy.val p)` (a `Var` where declared) | |
| `lsv` | a storage alias | `Idx Γ (LTy.alias R)` (a `Var` where declared) | |
| `mv` | a memory local | `Idx Γ (LTy.mem R)` (a `Var` where declared) | |
| `pmv`, `rmv` | a memory local, an array of primitives, of references (`delete pmv[ie]` fixes the element type) | `Idx Γ (LTy.mem R)` | |
| `gsp` | a state variable, with its proof `hgsp` | `Name` | |
| `se`, `ie`, `sadr` | a simple value | `Simple C Γ p` | |
| `e` | a value | `Val C Γ p` | not a conditional, when written to storage or to a memory target |
| `nse`, `nadr` | a value that is not simple | `Val C Γ p` | not simple (and as `e`) |
| `sp`, `map`, `arr` | a simple storage path (`map`/`arr` fix how it is indexed) | `SPath C Γ T` | simple |
| `parr`, `rarr` | a simple path to an array of primitives, of nonmapping references | `SPath C Γ T` | simple; the element primitive (`SPath.elemPrim`), or neither primitive nor mapping |
| `marr`, `darr` | a simple path to an array of mappings, of anything else | `SPath C Γ T` | simple; the element a mapping (`SPath.elemMapping`), or not |
| `nsp` | a storage path that is not simple | `SPath C Γ T` | not simple |
| `path` | any storage path | `SPath C Γ T` | |
| `nmp` | a memory path that is not a memory local | `MPath C Γ T` | not simple |
| `mpath` | a memory path | `MPath C Γ T` | bindable, when written as a reference into a target |
| `fld`, `fr`, with its proof `hfld`, `hfr` | a member name | `Name` | |
| `pfld`, `rfld` | a member of primitive, of reference type (`delete mv.pfld` fixes it) | `Name` | |
| `tgt` | where a fresh array lands | `NewLhs C Γ R` | |
| `lhs` | where a storage or memory read lands | `SHole C Γ T`, `MHole C Γ T` | a target |
| `x` | where a value lands | `VHole C Γ p` | |
| `loc`, `nlhs` | a member or entry a copy lands in | `Loc C Γ T` | `loc`: a target, not a state variable |
| `l` | the target of `⊕=` and `++` | `OpLoc C Γ p` | |
| `s`; `P`, `Q`, `ω` | a statement; a program, spliced in place (`P; ..ω` is `P ++ ω`) | `Stmt C Γ Γ'`; `Prog C Γ Γ'` | |
| `fbs` | a call with its body and its targets (KeY's `FunctionBody`), `expand_function_body(fbs)` its statements | `Stmt.call f args ret body` | its arguments simple; it returns to targets (`CallRet.isRets`) |
| `ic` | any other call with its body (KeY's `InternalCall`), `expand_function_body(ic)` its statements | `Stmt.call f args ret body` | its arguments simple; not `CallRet.isRets` (a result, if any, assigned inside the expansion: `y = f(a);`) |
| `call`, `rets`, `code`; `body`, `errorBody`, `panicBody`, `otherBody` | a `try`'s call, its return locals, its `Panic` code; its blocks | `ExtCall C Γ`, …; `Prog C Γ Γ'` | |
| `cond`; `body`; `n` | a loop's condition (KeY's `s#cond`); its body, a block, or spliced in place inside one (`{ body; … }`); the bound of `/// @custom:key unwind n` | `Val C Γ .bool`; `Prog C Γ Γ'`; `Nat` | |

The position says which sort an operand is read at: `sp.fld` is a location
left of `=`, a value right of it, a path under `delete`.  A copy is a write
whose right-hand side is a path (`gsp = sp`, `sp1.fld = sp2`); a write whose
right-hand side is a value (`se`, `nse`, `e`) stores it.  `⊕` is an
operator schema variable `op` (`⊖` a unary one, `⊕⊕` an increment or
decrement), with its proofs.  A declaration binds its name for the
statements after it; in a taclet's `\replacewith` a declared `se`, `sp`,
`ie`, `mv` is **fresh**, `seV k` and the like (KeY's `\newLocalVars`).

`‹t›` puts any Lean term in any position; where a formula stands, so does a
bare name (`φ`, the postcondition), and where an update stands an update
schema variable (`{u}`, `{u ‖ {u}u2}`).  A fresh name beside a schema
variable of its spelling prints primed: `T storage sp' = sp.fld;`.
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
/-- `if(r = this) then net else …`: KeY's `\if … \then … \else`, the form of a
payment's booking (`UpdElem.pay`), and read only there. -/
syntax:max "if" noWs "(" dl_term " = " dl_term ")" " then " dl_term " else " dl_term : dl_term
syntax:max "(" dl_term ")" : dl_term
/-- `(a == b)`: a comparison as a `bool` term. Parenthesised, since a bare `==`
after `:=` is the update `x := a == b`. -/
syntax:max "(" dl_term " == " dl_term ")" : dl_term
syntax:max "‹" term "›" : dl_term

/-- One elementary update `x := t`.  The funds and the ledger are written
`selfBalance := selfBalance - a` and `net := store(net, at(r), net(r) - a)`
(`+` as well), their arithmetic KeY's `int`; a payment
`net := if(r = this) then net else store(net, at(r), net(r) - a)`. -/
declare_syntax_cat dl_upd_elem (behavior := both)
syntax dl_term " := " dl_term : dl_upd_elem
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
/-- `a = b`.  In a taclet (`dl{ … }`) the total equation `Fml.eq`, KeY's
`=`; against a contract (`dl[C]{ … }`) the defined one, `Fml.eqD`, which is
what `==` means.  `Fml.eqD` prints as it. -/
syntax:50 dl_term:51 " = " dl_term:51 : dl_fml
/-- `a ≐ b`: the total equation `Fml.eq` in either reading, which may hold of
terms that halt.  `Fml.eq` prints as it. -/
syntax:50 dl_term:51 " ≐ " dl_term:51 : dl_fml
/-- `defined(t)`: `t` returns (`Fml.defined`). -/
syntax:max &"defined" "(" dl_term ")" : dl_fml
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
/-- A sequent `Γ ⟹ᶜ[I] φ` of the calculus with callbacks, every `transfer`
calling back into a contract with the invariant `I` (`ProvesC I Γ φ`;
today's judgement was deleted at W4 `sem-del`, the scoped one is
`Calculus/Callback.lean`'s). -/
syntax "dl{ " sepBy(dl_hyp, ", ") " ⟹ᶜ[" term "] " dl_fml " }" : term
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
/-- `⊨ φ` for a formula given as a Lean term. -/
syntax:25 (name := validSyntax) "⊨ " term:26 : term
/-- `σ ⊧ φ`: the formula `φ` holds in the state `σ`. -/
syntax:50 (name := holdsSyntax) term:51 " ⊧ " term:51 : term

open Lean Elab Term Meta in
/-- `⊨ φ` is `Valid φ` and `σ ⊧ φ` is `holds σ φ` for a scoped formula
(`Fml`, `Calculus/Logic.lean`). -/
def elabValidHolds (σ? : Option Lean.Term) (φ : Lean.Term) : TermElabM Lean.Expr := do
  let φ ← elabTerm φ none
  synthesizeSyntheticMVarsNoPostponing
  let φ ← instantiateMVars φ
  let ty ← whnf (← inferType φ)
  match σ?, ty.getAppFn.constName?, ty.getAppArgs with
  | none, some `Solidity.Fml, #[_, _] => mkAppM `Solidity.Valid #[φ]
  | none, _, _ => throwError "⊨ reads a scoped formula (`Fml C []`), not{indentExpr φ}"
  | some σ, some `Solidity.Fml, #[C, Γ] =>
    let σ ← elabTermEnsuringType σ (mkApp2 (mkConst `Solidity.State) C Γ)
    return mkApp4 (mkConst `Solidity.holds) C Γ σ φ
  | some _, _, _ => throwError "⊧ reads a scoped formula (`Fml C Γ`), not{indentExpr φ}"

open Lean Elab Term in
elab_rules : term
  | `(⊨ $φ:term) => elabValidHolds none φ
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
`Rules.lean`, after the conditions). -/
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

/-- `headOf` in a scoped taclet: a name declared above the mark is its
position; a schema variable of the `\find` is weakened past every local
declared above the mark, a position by `.there`, a part by its `up`. -/
def headOfCore (Γ : Scope) (x : Ident) (s : String) : Head :=
  match Γ.findIdx? (·.1 == s), Γ.lookup s with
  | some j, some (.val _) => .local (corePos j)
  | some j, some (.alias _) => .alias (corePos j)
  | some j, some (.mem _ h) => .mem (corePos j) h
  | _, _ =>
    let d := Γ.depth
    let there := iterApp `Solidity.Idx.there d
    match stemOf s with
    | "v" | "lv" | "vp" | "pv" => .local (there x)
    | "lsv" => .alias (there x)
    | "mv" | "pmv" | "rmv" => .mem (there x) (proofIdent x s)
    | "gsp" => .root x (proofIdent x s)
    | "se" | "ie" | "sadr" => .simple (iterApp `Solidity.Simple.up d x)
    | "e" | "nse" | "nadr" | "cond" | "inv" | "dec" => .val (iterApp `Solidity.Val.up d x)
    | "sp" | "nsp" | "path" | "map" | "arr" | "parr" | "rarr" | "marr" | "darr" =>
      .spath (iterApp `Solidity.SPath.up d x)
    | "nmp" | "mpath" => .mpath (iterApp `Solidity.MPath.up d x)
    | "nlhs" | "loc" => .loc (iterApp `Solidity.Loc.up d x)
    | "mloc" => .mloc (iterApp `Solidity.MLoc.up d x)
    | _ => if d == 0 then .other x else .weak x d

def headOf (Γ : Scope) (x : Ident) : Head :=
  let s := x.getId.toString
  if Γ.isCore then headOfCore Γ x s else
  match Γ.lookup s with
  | some (.val v) => .local v
  | some (.alias v) => .alias v
  | some (.mem v h) => .mem v h
  | some .raw => .other x
  | none => if Γ.isRaw then .other x else match stemOf s with
    | "v" | "lv" | "vp" | "pv" => .local x
    | "lsv" => .alias x
    | "mv" | "pmv" | "rmv" => .mem x (proofIdent x s)
    | "gsp" => .root x (proofIdent x s)
    | "se" | "ie" | "sadr" => .simple x
    | "e" | "nse" | "nadr" | "cond" | "inv" | "dec" => .val x
    -- the invariant rules' fresh locals: KeY's `s#b` (`bType b = cond;`), the
    -- condition's value, and `\skolemTerm int variant`, the variant's before
    -- the iteration (`whileInvariantBox`, `whileInvariantDiamond`)
    | "b" => .local (Lean.Syntax.mkApp (mkIdent ``Var.fresh)
        #[Lean.Syntax.mkStrLit "se", schemaIdent "k"])
    | "variant" => .local (Lean.Syntax.mkApp (mkIdent ``Var.fresh)
        #[Lean.Syntax.mkStrLit "ie", schemaIdent "k"])
    | "sp" | "nsp" | "path" | "map" | "arr" | "parr" | "rarr" | "marr" | "darr" => .spath x
    | "nmp" | "mpath" => .mpath x
    | "nlhs" | "loc" => .loc x
    | "mloc" => .mloc x
    | _ => .other x

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

/-- How a storage receiver is indexed: `map[ie]` by key, `arr[ie]` by
position — into a dynamic or a fixed-size array, the schema variable `ak`
(`ArrTy`), as solkey's `Path[…,array]` takes either — anything else by the
schema variable `it`. -/
def indexTyOf : TSyntax `sol_expr → MacroM Lean.Term
  | `(sol_expr| $x:ident) =>
    match stemOf x.getId.toString with
    | "map" => `(IndexTy.map)
    | "arr" | "parr" | "rarr" | "marr" | "darr" => `(IndexTy.arr $(schemaIdent "ak"))
    | _ => pure (schemaIdent "it")
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
  `(Stmt.tryCall $call $rets $(← block ok) $err $code $pnc $other)

/-- A taclet's `/// @custom:key` clauses above `while`: the annotation written
(`unwind 0`, `unwind n`, `unwind n + 1`, `invariant inv` with any `dec`, or
`invariant inv` and `decreases dec`), and the `while`. -/
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
    let d : Ident ← match (⟨w[0][6]⟩ : TSyntax `sol_expr) with
      | `(sol_expr| $d:ident) => pure d
      | _ => Macro.throwErrorAt cl msg
    return (← `(LoopAnn.inv $x (some $d) $(schemaIdent "brk")), w')
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
      | `(sol_expr| $x:ident) => `(LoopAnn.inv $x $(schemaIdent "dec") $(schemaIdent "brk"))
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
    return (← `(Stmt.send $v $(← schemaAt Γ .val r) $(← schemaAt Γ .val a)), Γ)
  | `(sol_stmt| $l:sol_expr = $f:sol_expr ( $a:sol_expr )) => do
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

/-! ### Terms -/

/-- The three sorts a term position asks for, and the memory ones. -/
inductive TPos where
  | val | path | storage | ident | addr | memory | svalue | mvalue
  deriving DecidableEq

def TPos.name : TPos → String
  | .val => "a value" | .path => "a storage path" | .storage => "a storage"
  | .ident => "a memory identity" | .addr => "a memory location" | .memory => "a memory"
  | .svalue => "a storage value" | .mvalue => "a memory value"

def tposError (x : Lean.Syntax) (what : String) (pos : TPos) : MacroM α :=
  Macro.throwErrorAt x s!"{what} is not {pos.name}"

/-- A name at a term sort: a schema variable of a program sort is lowered
(`se` is the term `se.lower`), a stack local is `pv`. -/
def headTerm (Γ : Scope) (pos : TPos) (x : Ident) : MacroM Lean.Term := do
  let n := x.getId.toString
  if stemOf n == "src" && pos == .svalue then
    return ← `($(Lean.mkCIdent `Solidity.Src.lower) $(rhsTerm Γ "src" ⟨x⟩ |>.getD x))
  if (n == "true" || n == "false") && pos == .val then
    return ← `(Term.litB $(mkIdent (Name.mkSimple n)))
  if n == "storage" && pos == .storage then return ← `(STerm.storage)
  if n == "memory" && pos == .memory then return ← `(MTerm.memory)
  if n == "selfBalance" && pos == .val then return ← `(Term.env EnvKey.selfBalance)
  if (n == "this" || n == "self") && pos == .val then return ← `(Term.env EnvKey.selfAddress)
  match headOf Γ x, pos with
  | .local v, .val => `(Term.pv $v)
  | .local v, .svalue => `(SValT.val (Term.pv $v))
  | .local v, .mvalue => `(MValT.val (Term.pv $v))
  | .alias v, .path => `(PTerm.pv $v)
  | .mem v _, .ident => `(ITerm.pv $v)
  | .mem v _, .mvalue => `(MValT.ref (ITerm.pv $v))
  | .root r h, .val => `(Term.find STerm.storage (PTerm.root $r $h))
  | .root r h, .path => `(PTerm.root $r $h)
  | .simple s, .val => `($(Lean.mkCIdent `Solidity.Simple.lower) $s)
  | .simple s, .svalue => `(SValT.val ($(Lean.mkCIdent `Solidity.Simple.lower) $s))
  | .simple s, .mvalue => `(MValT.val ($(Lean.mkCIdent `Solidity.Simple.lower) $s))
  | .val e, .val => `($(Lean.mkCIdent `Solidity.Val.lower) $e)
  | .spath p, .path => `($(Lean.mkCIdent `Solidity.SPath.lower) $p)
  | .mpath p, .ident => `($(Lean.mkCIdent `Solidity.MPath.lower) $p)
  | .mpath p, .mvalue => `(MValT.ref ($(Lean.mkCIdent `Solidity.MPath.lower) $p))
  | .loc l, .path => `($(Lean.mkCIdent `Solidity.Loc.lower) $l)
  | .other o, _ => pure o
  | _, _ => tposError x s!"`{n}`" pos

/-- `mv.f₁.….fₙ` at a term sort: the inner members are identities read. -/
def memMember (core : Bool) (pos : TPos) (stx : Lean.Syntax) :
    Lean.Term → List Ident → MacroM Lean.Term
  | b, [] => pure b
  | b, [f] =>
    -- in a rule, `mv.length` at the local's type (`Val.mlen`'s `hlen`)
    if f.getId.toString == "length" && pos == .val && core then
      `(Term.mlenH $(schemaIdent "hlen") MTerm.memory $b) else
    if f.getId.toString == "length" && pos == .val then `(Term.mlen MTerm.memory $b) else
    let h := proofIdent f f.getId.toString
    match pos with
    | .addr => `(MAddr.field $b $f $h)
    | .val => `(Term.read MTerm.memory (MAddr.field $b $f $h))
    | .ident => `(ITerm.read MTerm.memory (MAddr.field $b $f $h))
    | .mvalue => `(MValT.ref (ITerm.read MTerm.memory (MAddr.field $b $f $h)))
    | _ => tposError stx "a memory member" pos
  | b, f :: fs => do
    let h := proofIdent f f.getId.toString
    memMember core pos stx (← `(ITerm.read MTerm.memory (MAddr.field $b $f $h))) fs

/-- `p.length`, however it was parsed, or KeY's `consr(p, size)`: the path `p`. -/
def lengthBase? : TSyntax `dl_term → MacroM (Option (TSyntax `dl_term))
  | `(dl_term| consr($b, $sz:ident)) => pure (if sz.getId.toString == "size" then some b else none)
  | `(dl_term| $x:ident) =>
    match (nameParts x.getId).reverse with
    | "length" :: r :: rs => do
      let n := (r :: rs).reverse.foldl (fun n s => Name.str n s) Name.anonymous
      some <$> `(dl_term| $(mkIdentFrom x n):ident)
    | _ => pure none
  | `(dl_term| $t:dl_term . $f:ident) => pure (if f.getId.toString == "length" then some t else none)
  | _ => pure none

/-- How a storage receiver term is indexed, as `indexTyOf` reads a program
expression: `map[ie]` by key, `arr[ie]` (and its kin) by position, anything
else by the schema variable `it`. -/
def indexTyOfTerm : TSyntax `dl_term → MacroM Lean.Term
  | `(dl_term| $x:ident) =>
    match nameParts x.getId with
    | [n] => match stemOf n with
      | "map" => `(IndexTy.map)
      | "arr" | "parr" | "rarr" | "marr" | "darr" => `(IndexTy.arr $(schemaIdent "ak"))
      | _ => pure (schemaIdent "it")
    | _ => pure (schemaIdent "it")
  | _ => pure (schemaIdent "it")

mutual

/-- A term at a sort.  At a storage or a memory value's sort, a value term is
wrapped as one; a path, `find(…)` and `copyMem(…)` are storage values of
their own, a memory path a memory value of its own. -/
partial def schemaTerm (Γ : Scope) (pos : TPos) (t : TSyntax `dl_term) : MacroM Lean.Term := do
  -- in `tm{ … }` a name is a variable of the sort it stands at
  if Γ.isRaw && (pos == .svalue || pos == .mvalue) then
    if let `(dl_term| $x:ident) := t then
      if (nameParts x.getId).length == 1 then return x
  match pos with
  | .svalue =>
    match t with
    | `(dl_term| $x:ident) =>
      if stemOf x.getId.toString == "src" then headTerm Γ .svalue x
      else `(SValT.val $(← schemaTerm0 Γ .val t))
    | `(dl_term| $f:ident($_,*)) =>
      if ["find", "copyMem", "newArr"].contains f.getId.toString then schemaTerm0 Γ .svalue t
      else `(SValT.val $(← schemaTerm0 Γ .val t))
    | _ => `(SValT.val $(← schemaTerm0 Γ .val t))
  | .mvalue =>
    let memHead := match t with
      | `(dl_term| $x:ident) => match nameParts x.getId with
        | [h] => match headOf Γ (mkIdent (Name.mkSimple h)) with
          | .mem .. | .mpath _ => true
          | _ => false
        | _ => false
      | `(dl_term| $f:ident($_,*)) => f.getId.toString == "freshId"
      | _ => false
    if memHead then `(MValT.ref $(← schemaTerm0 Γ .ident t))
    else `(MValT.val $(← schemaTerm0 Γ .val t))
  | _ => schemaTerm0 Γ pos t

/-- A storage index: a program expression's term is its lowering
(`Simple.lower`, `Loc.lower`'s), any other term itself. -/
partial def schemaKey (Γ : Scope) (i : TSyntax `dl_term) : MacroM Lean.Term := do
  if let `(dl_term| $x:ident) := i then
    if (nameParts x.getId).length == 1 then
      match headOf Γ x with
      | .simple s => return ← `($(Lean.mkCIdent `Solidity.Simple.lower) $s)
      | .val e => return ← `($(Lean.mkCIdent `Solidity.Val.lower) $e)
      | _ => pure ()
  schemaTerm Γ .val i

partial def schemaTerm0 (Γ : Scope) (pos : TPos) : TSyntax `dl_term → MacroM Lean.Term
  | stx@`(dl_term| $n:num) =>
    match pos with
    | .val => `(Term.nat $n)
    | .svalue => `(SValT.val (Term.nat $n))
    | .mvalue => `(MValT.val (Term.nat $n))
    | _ => tposError stx "a number" pos
  | stx@`(dl_term| $x:ident) => do
    match nameParts x.getId with
    | [] => Macro.throwError "empty identifier"
    | [_] => headTerm Γ pos x
    | h :: fs =>
      -- `sp.fld`: a path, or (at a memory sort) a member of a memory object
      let hx := partIdent x h
      match headOf Γ hx with
      | .mem .. | .mpath _ =>
        memMember Γ.isCore pos stx (← headTerm Γ .ident hx) (fs.map (partIdent x))
      | _ =>
        if fs.getLast? == some "length" then
          let p' ← (fs.dropLast).foldlM (init := ← headTerm Γ .path hx) fun acc f =>
            `(PTerm.field $acc $(partIdent x f) $(proofIdent x f))
          match pos with
          | .val =>
            if Γ.isCore then `(Term.lenH $(schemaIdent "hlen") STerm.storage $p')
            else `(Term.len STerm.storage $p')
          | _ => tposError stx "a length" pos
        else
        let p ← fs.foldlM (init := ← headTerm Γ .path hx) fun acc f =>
          `(PTerm.field $acc $(partIdent x f) $(proofIdent x f))
        match pos with
        | .path => pure p
        | .val => `(Term.find STerm.storage $p)
        | .svalue => `(SValT.find STerm.storage $p)
        | _ => tposError stx "a storage path" pos
  | stx@`(dl_term| $t:dl_term . $f:ident) => do
    let p ← (nameParts f.getId).foldlM (init := ← schemaTerm Γ .path t) fun acc c =>
      `(PTerm.field $acc $(partIdent f c) $(proofIdent f c))
    match pos with
    | .path => pure p
    | _ => tposError stx "a member" pos
  | stx@`(dl_term| $t:dl_term [ $i:dl_term ]) => do
    let mem := match t with
      | `(dl_term| $x:ident) => match nameParts x.getId with
        | h :: _ => match headOf Γ (mkIdent (Name.mkSimple h)) with
          | .mem .. | .mpath _ => true
          | _ => false
        | [] => false
      | _ => false
    if mem then
      let a ← `(MAddr.at $(schemaIdent "mk") $(← schemaTerm Γ .ident t) $(← schemaTerm Γ .val i))
      match pos with
      | .addr => pure a
      | .val => `(Term.read MTerm.memory $a)
      | .ident => `(ITerm.read MTerm.memory $a)
      | .mvalue => `(MValT.ref (ITerm.read MTerm.memory $a))
      | _ => tposError stx "a memory element" pos
    else
      -- `p[p.length]`, the slot one past the end: no bounds check
      let pastEnd ← do
        let some b ← lengthBase? i | pure false
        match b, t with
        | `(dl_term| $b:ident), `(dl_term| $x:ident) => pure (b.getId == x.getId)
        | _, _ => pure false
      let p ← if pastEnd then `(PTerm.next $(← schemaTerm Γ .path t))
        else `(PTerm.at $(← indexTyOfTerm t) $(← schemaTerm Γ .path t) $(← schemaKey Γ i))
      match pos with
      | .path => pure p
      | .val => `(Term.find STerm.storage $p)
      | .svalue => `(SValT.find STerm.storage $p)
      | _ => tposError stx "an entry" pos
  | `(dl_term| $a:dl_term ⊕ $b:dl_term) => do
    -- the operator schema variable's proofs are `Val.binop`'s (`hop`, `hq`);
    -- in a compound assignment `schemaTacletCore` turns them into `⊕=`'s
    `(Term.binopS $(schemaIdent "op") $(schemaIdent "hop") $(schemaIdent "hq")
        $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| ⊖ $a:dl_term) => do
    `(Term.unopS $(schemaIdent "op") $(schemaIdent "hop") $(schemaIdent "hq")
        $(← schemaTerm Γ .val a))
  | `(dl_term| $a:dl_term ± $b:dl_term) => do
    -- the step of `++`/`--`, `1` at the target's type
    let b ← match b with
      | `(dl_term| 1) => `(Term.one $(schemaIdent "p") $(schemaIdent "hp"))
      | _ => schemaTerm Γ .val b
    `(Term.binopI $(schemaIdent "op") $(schemaIdent "hp") $(← schemaTerm Γ .val a) $b)
  | `(dl_term| $a:dl_term ⊕⊕) => do
    `(Term.bumped $(schemaIdent "op") $(schemaIdent "hp") $(← schemaTerm Γ .val a))
  | `(dl_term| $a:dl_term + $b:dl_term) => do
    `(Term.binop BinOp.add PrimTy.uint $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| $a:dl_term - $b:dl_term) => do
    `(Term.binop BinOp.sub PrimTy.uint $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| $a:dl_term / $b:dl_term) => do
    `(Term.binop BinOp.div PrimTy.uint $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| $a:dl_term * $b:dl_term) => do
    `(Term.binop BinOp.mul PrimTy.uint $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| $a:dl_term % $b:dl_term) => do
    `(Term.binop BinOp.mod PrimTy.uint $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| $a:dl_term && $b:dl_term) => do
    `(Term.binop BinOp.and PrimTy.bool $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| $a:dl_term || $b:dl_term) => do
    `(Term.binop BinOp.or PrimTy.bool $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| ( $a:dl_term == $b:dl_term )) => do
    `(Term.binop BinOp.eqB _ $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| ( $t:dl_term )) => schemaTerm Γ pos t
  | `(dl_term| ‹ $t:term ›) => pure t
  | stx@`(dl_term| $f:ident($args,*)) => do
    let args := args.getElems
    let st := schemaTerm Γ .storage
    let pa := schemaTerm Γ .path
    let me := schemaTerm Γ .memory
    -- KeY's three-argument `read(m, i, f)`, four-argument `write(m, i, f, v)`:
    -- the member `f`, the element `at(k)`
    let maddr (i a : TSyntax `dl_term) : MacroM Lean.Term := do
      match a with
      | `(dl_term| at($k)) =>
        `(MAddr.at $(schemaIdent "mk") $(← schemaTerm Γ .ident i) $(← schemaTerm Γ .val k))
      | `(dl_term| $g:ident) =>
        `(MAddr.field $(← schemaTerm Γ .ident i) $g $(proofIdent g g.getId.toString))
      | _ => tposError a "a member `f` or an element `at(k)`" .addr
    match f.getId.eraseMacroScopes.toString, args, pos with
    | "addmod", #[a, b, k], .val =>
      `(Term.modular ModOp.addmod $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b)
        $(← schemaTerm Γ .val k))
    | "mulmod", #[a, b, k], .val =>
      `(Term.modular ModOp.mulmod $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b)
        $(← schemaTerm Γ .val k))
    | "select", #[s, r], .val => `(Term.find $(← st s) $(← pa r))
    | "select", #[s, r], .storage | "selectSt", #[s, r], .storage =>
      let `(dl_term| $r:ident) := r | tposError r "a member name" .storage
      `(STerm.select $(← st s) $r $(proofIdent r r.getId.toString))
    | "net", #[a], .val => `(Term.net $(← schemaTerm Γ .val a))
    | "selectSt", #[n, a], .val =>
      let `(dl_term| net) := n | tposError n "`net`" .val
      let `(dl_term| at($a)) := a | tposError a "`at(a)`" .val
      `(Term.net $(← schemaTerm Γ .val a))
    | "find", #[s, p], .val =>
      match ← lengthBase? p with
      | some b =>
        if Γ.isCore then `(Term.lenH $(schemaIdent "hlen") $(← st s) $(← pa b))
        else `(Term.len $(← st s) $(← pa b))
      | none => `(Term.find $(← st s) $(← pa p))
    | "find", #[s, p], .svalue =>
      match ← lengthBase? p with
      | some b => `(SValT.val (Term.len $(← st s) $(← pa b)))
      | none => `(SValT.find $(← st s) $(← pa p))
    | "consr", #[p, f], .path =>
      match f with
      | `(dl_term| at($i)) =>
        -- `consr(p, at(find(storage, consr(p, size))))`: the slot past the end
        let past ← match i with
          | `(dl_term| find(storage, $q)) => do
            match ← lengthBase? q with
            | some b => pure (b.raw.structEq p.raw)
            | none => pure false
          | _ => pure false
        if past then `(PTerm.next $(← pa p))
        else `(PTerm.at $(← indexTyOfTerm p) $(← pa p) $(← schemaKey Γ i))
      | `(dl_term| atMap($i)) => `(PTerm.at IndexTy.map $(← pa p) $(← schemaKey Γ i))
      | `(dl_term| $g:ident) =>
        if g.getId.toString == "size" then tposError f "`consr(p, size)` outside `find`" .path
        else `(PTerm.field $(← pa p) $g $(proofIdent g g.getId.toString))
      | _ => tposError f "a member, `at(i)` or `atMap(i)`" .path
    | "read", #[m, a], .val => `(Term.read $(← me m) $(← schemaTerm Γ .addr a))
    | "read", #[m, a], .ident => `(ITerm.read $(← me m) $(← schemaTerm Γ .addr a))
    | "read", #[m, i, a], .val =>
      if let `(dl_term| $g:ident) := a then
        if g.getId.toString == "size" then
          if Γ.isCore then
            return ← `(Term.mlenH $(schemaIdent "hlen") $(← me m) $(← schemaTerm Γ .ident i))
          return ← `(Term.mlen $(← me m) $(← schemaTerm Γ .ident i))
      `(Term.read $(← me m) $(← maddr i a))
    | "read", #[m, i, a], .ident => `(ITerm.read $(← me m) $(← maddr i a))
    | "write", #[m, i, a, v], .memory =>
      `(MTerm.write $(← me m) $(← maddr i a) $(← schemaTerm Γ .mvalue v))
    | "delValue", #[t], .val => `(Term.delValue $(← schemaTerm Γ .val t))
    | "lit", #[v], .val =>
      match v with
      | `(dl_term| $x:ident) => `(Term.lit $x)
      | `(dl_term| ‹ $x:term ›) => `(Term.lit $x)
      | _ => tposError v "a value variable" .val
    | "copyMem", #[_, m, i], .svalue => `(SValT.copyMem $(← me m) $(← schemaTerm Γ .ident i))
    | "newArr", #[n], .svalue => `(SValT.newArr $(schemaIdent "R") $(← schemaTerm Γ .val n))
    | "freshId", #[t], .ident =>
      match t with
      | `(dl_term| addM($m)) => `(ITerm.alloc $(← me m) $(schemaIdent "R"))
      | `(dl_term| copySt($m, $v)) => `(ITerm.copy $(← me m) $(← schemaTerm Γ .svalue v))
      | _ => Macro.throwErrorAt t "`freshId(addM(m))` or `freshId(copySt(m, v))`"
    | "store", #[s, r, v], .storage => `(STerm.save $(← st s) $(← pa r) $(← schemaTerm Γ .svalue v))
    | "save", #[s, p, v], .storage =>
      -- push and pop, nested writes over the extent
      match ← lengthBase? p with
      | some b =>
        -- the element written or deleted: `p[i]`, KeY's `consr(p, at(i))`
        let elem (q : TSyntax `dl_term) : Bool := match q with
          | `(dl_term| $_[$_]) => true
          | `(dl_term| consr($_, at($_))) => true
          | _ => false
        match s, v with
        | `(dl_term| save($s', $q, $w)), `(dl_term| $_ + 1) =>
          if elem q then return ← `(STerm.push $(← st s') $(← pa b) $(← schemaTerm Γ .svalue w))
        | `(dl_term| delAt($s', $q)), `(dl_term| $_ - 1) =>
          if elem q then return ← `(STerm.pop $(← st s') $(← pa b))
        | _, _ => pure ()
        match v with
        | `(dl_term| $_ + 1) =>
          -- an empty push saves only the length (solkey's `storagePushLengthSave`)
          `(STerm.pushSlot $(← st s) $(← pa b) _)
        | `(dl_term| $_ - 1) => `(STerm.shrink $(← st s) $(← pa b))
        | _ => `(STerm.save $(← st s) $(← pa p) $(← schemaTerm Γ .svalue v))
      | none => `(STerm.save $(← st s) $(← pa p) $(← schemaTerm Γ .svalue v))
    | "delAt", #[s, p], .storage => `(STerm.delAt $(← st s) $(← pa p))
    | "defVal", #[_], .val => `(Term.dflt $(schemaIdent "p"))
    | "write", #[m, a, v], .memory =>
      `(MTerm.write $(← me m) $(← schemaTerm Γ .addr a) $(← schemaTerm Γ .mvalue v))
    | "addM", #[m], .memory => `(MTerm.addM $(← me m) $(schemaIdent "R"))
    | "copySt", #[m, v], .memory => `(MTerm.copySt $(← me m) $(← schemaTerm Γ .svalue v))
    | _, _, _ => tposError stx s!"`{f.getId}(…)` here" pos
  | _ => Macro.throwUnsupported

end

/-- The sort of a term of `tm{ … }`, read off its head. -/
def tmSort : TSyntax `dl_term → TPos
  | `(dl_term| $f:ident($_,*)) =>
    match f.getId.toString with
    | "save" | "delAt" | "store" | "select" | "selectSt" => .storage
    | "write" | "addM" | "copySt" => .memory
    | "consr" => .path
    | "freshId" => .ident
    | "copyMem" | "newArr" => .svalue
    | _ => .val
  | `(dl_term| $x:ident) =>
    match x.getId.toString with
    | "storage" => .storage
    | "memory" => .memory
    | _ => if (nameParts x.getId).length > 1 then .path else .val
  | `(dl_term| $_:dl_term . $_:ident) | `(dl_term| $_:dl_term [ $_:dl_term ]) => .path
  | _ => .val

/-- One elementary update of a global: `selfBalance`, `net`, `storage` or
`memory` (`schemaUpdCore` reads a local's itself, as `UpdElem.local`). -/
def schemaUpdElem (Γ : Scope) : TSyntax `dl_upd_elem → MacroM Lean.Term
  | `(dl_upd_elem| $l:dl_term := $r:dl_term) => do
    let `(dl_term| $x:ident) := l | Macro.throwErrorAt l "an update assigns a variable"
    let n := x.getId.toString
    if n == "selfBalance" then
      return ← match r with
        | `(dl_term| selfBalance - $a) => do
          `(UpdElem.selfBalance IntOp.sub $(← schemaTerm Γ .val a))
        | `(dl_term| selfBalance + $a) => do
          `(UpdElem.selfBalance IntOp.add $(← schemaTerm Γ .val a))
        | _ => Macro.throwErrorAt r "`selfBalance - a` or `selfBalance + a`"
    if n == "net" then
      return ← match r with
        | `(dl_term| store(net, at($a), net($a') - $v)) =>
          if a.raw.structEq a'.raw then do
            `(UpdElem.net $(← schemaTerm Γ .val a) IntOp.sub $(← schemaTerm Γ .val v))
          else Macro.throwErrorAt a' "the entry read is the one written"
        | `(dl_term| store(net, at($a), net($a') + $v)) =>
          if a.raw.structEq a'.raw then do
            `(UpdElem.net $(← schemaTerm Γ .val a) IntOp.add $(← schemaTerm Γ .val v))
          else Macro.throwErrorAt a' "the entry read is the one written"
        | `(dl_term| storeSt(net, at($a), selectSt(net, at($a')) - $v)) =>
          if a.raw.structEq a'.raw then do
            `(UpdElem.net $(← schemaTerm Γ .val a) IntOp.sub $(← schemaTerm Γ .val v))
          else Macro.throwErrorAt a' "the entry read is the one written"
        | `(dl_term| storeSt(net, at($a), selectSt(net, at($a')) + $v)) =>
          if a.raw.structEq a'.raw then do
            `(UpdElem.net $(← schemaTerm Γ .val a) IntOp.add $(← schemaTerm Γ .val v))
          else Macro.throwErrorAt a' "the entry read is the one written"
        | `(dl_term| if($a = $t:ident) then $n':ident else storeSt(net, at($a'), selectSt(net, at($a'')) - $v))
        | `(dl_term| if($a = $t:ident) then $n':ident else store(net, at($a'), net($a'') - $v)) => do
          unless ["this", "self"].contains t.getId.toString do
            Macro.throwErrorAt t "a payment compares with `this`"
          unless n'.getId.toString == "net" do Macro.throwErrorAt n' "a payment to `this` leaves `net`"
          unless a.raw.structEq a'.raw && a.raw.structEq a''.raw do
            Macro.throwErrorAt a' "the entry read is the one written, and the one compared"
          `(UpdElem.pay $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val v))
        | _ => Macro.throwErrorAt r "`store(net, at(r), net(r) - a)`, `… + a`, or \
            `if(r = this) then net else store(net, at(r), net(r) - a)`"
    if n == "storage" then return ← `(UpdElem.storage $(← schemaTerm Γ .storage r))
    if n == "memory" then return ← `(UpdElem.memory $(← schemaTerm Γ .memory r))
    Macro.throwErrorAt x "an elementary update of a global assigns `selfBalance`, `net`, \
      `storage` or `memory`"
  | _ => Macro.throwUnsupported

/-- The modality of the formula under an update: an update is judged as the
goal it came from.  `⟨[ ]⟩` is `either`: the taclet's `m` in `dl{ … }`, the
formula's modality in `dl![m]{ … }` (`Notation.lean`). -/
partial def fmlModality? (either : Lean.Term) : TSyntax `dl_fml → MacroM (Option Lean.Term)
  | `(dl_fml| ⟨ $[$_:sol_stmt;]* ⟩ $_:dl_fml) | `(dl_fml| ⟨ $_:sol_block ⟩ $_:dl_fml) =>
    some <$> `(Modality.diamond)
  | `(dl_fml| [ $[$_:sol_stmt;]* ] $_:dl_fml) | `(dl_fml| [ $_:sol_block ] $_:dl_fml) =>
    some <$> `(Modality.box)
  | `(dl_fml| ⟨ $[$_:sol_stmt;]* .. $_:term ⟩ $_:dl_fml) => some <$> `(Modality.diamond)
  | `(dl_fml| [ $[$_:sol_stmt;]* .. $_:term ] $_:dl_fml) => some <$> `(Modality.box)
  | `(dl_fml| ⟨[ $[$_:sol_stmt;]* ]⟩ $_:dl_fml) | `(dl_fml| ⟨[ $[$_:sol_stmt;]* .. $_:term ]⟩ $_:dl_fml)
  | `(dl_fml| ⟨[ $_:sol_block ]⟩ $_:dl_fml) => pure (some either)
  | `(dl_fml| $_:dl_upd $φ:dl_fml) | `(dl_fml| { havoc } $φ:dl_fml) => fmlModality? either φ
  | `(dl_fml| ( $φ:dl_fml )) => fmlModality? either φ
  | _ => pure none

/-- One goal of `Premise.branches`: the locals it binds (`∀ rets.`; `∀ code.`
the `Panic` code's, `CodeBinder.binders`), and its block.  The label is dropped. -/
def schemaBranch (fresh : Bool) (Γ : Scope) (b : TSyntax `dl_branch) : MacroM Lean.Term := do
  let (x?, blk) ← match b with
    | `(dl_branch| $[$_:str :]? $[∀ $x?:ident .]? ⟨[ $blk:sol_block ]⟩) => pure (x?, blk)
    | `(dl_branch| $[$_:str :]? $[∀ $x?:ident .]? [ $blk:sol_block ]) => pure (x?, blk)
    | _ => Macro.throwUnsupported
  -- its binders (`Binders`, the `Panic` code's `CodeBinder.binders`) and
  -- its block read on top of them
  let xs ← match x? with
    | none => pure (Lean.mkCIdent `Solidity.Binders.nil : Lean.Term)
    | some x =>
      if stemOf x.getId.toString == "code" then
        `($(Lean.mkCIdent `Solidity.CodeBinder.binders) $x)
      else pure x
  `($(Lean.mkCIdent `Solidity.Branch.mk) $xs $(← schemaBlock fresh Γ blk))

/-- The identifiers of a `\find`, outside `‹…›`. -/
partial def findIdents : Lean.Syntax → Array Ident
  | stx@(.ident ..) => #[⟨stx⟩]
  | .node _ _ args =>
    if args[0]?.any (·.isOfKind `atom) && args[0]!.getAtomVal == "‹" then #[]
    else args.flatMap findIdents
  | _ => #[]

/-- A right-hand side that is one schema variable, and its spelling. -/
def singleVar? : TSyntax `sol_expr → Option String
  | `(sol_expr| $x:ident) =>
    match nameParts x.getId with
    | [s] => some s
    | _ => none
  | _ => none

/-- A memory location every part of which is simple: a member or an element
of a memory local at a simple index (`mv.fld`, `mv[ie]`). -/
def memTarget : TSyntax `sol_expr → Bool
  | `(sol_expr| $x:ident) =>
    match nameParts x.getId with
    | [h, _] => stemOf h == "mv"
    | _ => false
  | `(sol_expr| $b:ident [ $i:ident ]) =>
    stemOf b.getId.toString == "mv" && ["se", "ie"].contains (stemOf i.getId.toString)
  | _ => false

/-- **The side conditions of a `\find`**, as hypothesis names and types: what
`Stmt.step` knows of the parts when it fires the rule.

* by name: `nsp` is not simple and `sp`, `map`, `arr` are (`SPath.isSimple`),
  `nse`, `nadr` are not simple values, `nmp` is not a memory local, and `loc`
  is a member or an entry at a target, never a state variable;
* by position: a hole `lhs` lands in a target (`Hole.isTarget`,
  `MHole.isTarget`, `VHole.isTarget`); a value `e`, `nse` written to storage
  or memory is not a conditional (`Val.notTernary`: a conditional is lowered
  first); a memory path `mpath` written as a reference is bindable
  (`MPath.isBindable`). -/
def sideConds (s : TSyntax `sol_stmt) : MacroM (Array (Ident × Lean.Term)) := do
  let mut out : Array (Ident × Lean.Term) := #[]
  let mut seen : List String := []
  let hyp (n : String) : Ident := mkIdent (Name.mkSimple ("h" ++ n))
  for x in findIdents s.raw do
    let some n := (nameParts x.getId).head? | continue
    if seen.contains n then continue
    seen := n :: seen
    let v := schemaIdent n
    match stemOf n with
    | "nsp" => out := out.push (hyp n, ← `(SPath.isSimple $v = false))
    | "sp" | "map" | "arr" => out := out.push (hyp n, ← `(SPath.isSimple $v = true))
    | "parr" | "rarr" | "marr" | "darr" =>
      out := out.push (hyp n, ← `(SPath.isSimple $v = true))
      let (pred, b) := match stemOf n with
        | "parr" => (`Solidity.SPath.elemPrim, true)
        | "rarr" => (`Solidity.SPath.elemPrim, false)
        | "marr" => (`Solidity.SPath.elemMapping, true)
        | _ => (`Solidity.SPath.elemMapping, false)
      let bv ← if b then `(true) else `(false)
      out := out.push (hyp (n ++ "_e"), ← `($(mkIdent pred) $v = $bv))
      if stemOf n == "rarr" then
        out := out.push (hyp (n ++ "_nm"), ← `($(mkIdent `Solidity.SPath.elemMapping) $v = false))
    | "nse" | "nadr" => out := out.push (hyp n, ← `(Val.isSimple $v = false))
    | "nmp" => out := out.push (hyp n, ← `(MPath.isSimple $v = false))
    | "loc" =>
      out := out.push (hyp n, ← `($(mkIdent `Solidity.Loc.isTarget) $v = true))
      out := out.push (hyp (n ++ "_nr"), ← `($(mkIdent `Solidity.Loc.isRoot) $v = false))
    | _ => pure ()
  let notTernary (r : TSyntax `sol_expr) : MacroM (Array (Ident × Lean.Term)) := do
    let some n := singleVar? r | return #[]
    unless ["e", "nse"].contains (stemOf n) do return #[]
    return #[(hyp (n ++ "_nt"), ← `($(mkIdent `Solidity.Val.notTernary) $(schemaIdent n) = true))]
  let pushArg ← match s with
    | `(sol_stmt| $_:sol_expr .push( $e:sol_expr )) => pure (some e)
    | `(sol_stmt| $f:sol_expr ( $e:sol_expr )) => do
      let some (_, "push") ← callRecv? f | pure none
      pure (some e)
    | _ => pure none
  if let some e := pushArg then
    if let some n := singleVar? e then
      if stemOf n == "nse" then
        out := out.push (hyp (n ++ "_path"),
          ← `(Val.complexStorageRead $(schemaIdent n) = false))
  match s with
  | `(sol_stmt| $x:ident) =>
    -- `fbs`, `ic`, a call: its arguments simple (`functionCallArgCapture`
    -- first), and with targets (`fbs`) or without (`ic`)
    let n := x.getId.toString
    unless isCallStem n do return out
    let b ← if stemOf n == "fbs" then `(true) else `(false)
    return out.push (mkIdent `hexp, ← `($(mkIdent `Solidity.Args.firstNonSimple) $(schemaIdent "args") = none))
      |>.push (mkIdent `hrets, ← `($(mkIdent `Solidity.CallRet.isRets) $(schemaIdent "ret") = $b))
  | `(sol_stmt| $l:sol_expr = $r:sol_expr) =>
    match lhsHead [] l with
    | some (.other h) =>
      let some n := singleVar? l | return out
      unless stemOf n == "lhs" do return out
      if isMem [] r then return out.push (hyp n, ← `($(mkIdent `Solidity.MHole.isTarget) $h = true))
      if isPath [] r then return out.push (hyp n, ← `($(mkIdent `Solidity.SHole.isTarget) $h = true))
      return out.push (hyp n, ← `($(mkIdent `Solidity.VHole.isTarget) $h = true))
    | some (.local _) | some (.alias _) | some (.mem ..) => return out
    | _ =>
      if isMem [] l then
        if (rhsVar? "msrc" r).isSome then return out
        -- only into a target (`mv.fld`, `mv[ie]`) is a source lowered or
        -- written as it is; into any other the capture takes it whole
        unless memTarget l do return out
        if isMem [] r then
          let some n := singleVar? r | return out
          return out.push (hyp (n ++ "_b"), ← `($(mkIdent `Solidity.MPath.isBindable) $(schemaIdent n) = true))
        return out ++ (← notTernary r)
      if isMem [] r || (rhsVar? "src" r).isSome || isPath [] r then return out
      return out ++ (← notTernary r)
  | _ => return out

/-! ### Scoped taclets

The lines read into `Solidity`'s scoped syntax under `open scoped
Solidity.Schema`.  The statements and expressions are read as above, from
`coreScope`: a fresh local is a position, a `\find`'s schema variable is
weakened past the fresh locals before it (`headOfCore`); a program is
`Prog.cons`.  The terms are written by their symbols' KeY names
(`Term.find`, `STerm.save`), which no declaration here resolves, and then
turned into the scoped symbols (`coreNames`); a formula is written scoped
(`fmlC`).  The premise: an
unfolding premise pops its fresh locals (`Premise.unfold P (Ext.push^d
.refl)`), a `\find` that declares binds its local in front of the premise
(`Premise.bind`) or declares it in the update (`Upd.decl`), a split says how
its goals end (`BlockKind`), a check has no program. -/

/-- The scoped family a symbol's family name stands for: the
term symbols (`Term.find`, `STerm.save`, …) are `Calculus/Rules.lean`'s,
under `Tms` (`Solidity.MAddr` is the typed heap's); a term, an update and
its elements their families of the same name.  A formula is written scoped
(`fmlC`). -/
def coreFamily? : Lean.Name → Option Lean.Name
  | n =>
    if [`Term, `PTerm, `STerm, `SValT, `ITerm, `MAddr, `MTerm, `MValT].contains n then
      some (`Tms ++ n)
    else if [`Tm, `UpdElem, `Upd].contains n then some n
    else none

/-- `Solidity.F.x` as `Solidity.F'.x`, `F'` the scoped twin of `F`. -/
def coreName? (n : Lean.Name) : Option Lean.Name :=
  match n.components with
  | s :: s' :: f :: rest =>
    if s != `Solidity then none
    else (coreFamily? s').map fun f' => (f :: rest).foldl (· ++ ·) (`Solidity ++ f')
  | [s, f] => if s != `Solidity then none else (coreFamily? f).map fun f' => `Solidity ++ f'
  | _ => none

/-- Every name of a term symbol the reader wrote, by its quotation's
resolution, spelled in full, or (a symbol `F.x` of a family `coreFamily?`
names, which no declaration below the rule table resolves) by its family,
turned into its scoped twin, which must exist. -/
partial def coreNames (stx : Syntax) : MacroM Syntax := do
  match stx with
  | .ident _ _ val pre =>
    let byPre := pre.findSome? fun
      | .decl n [] => if (`Solidity).isPrefixOf n then some n else none
      | _ => none
    let v := val.eraseMacroScopes
    let byFamily := match v.components with
      | f :: _ :: _ => if (coreFamily? f).isSome then some (`Solidity ++ v) else none
      | _ => none
    let some n := byPre <|> (if (`Solidity).isPrefixOf v then some v else none) <|> byFamily
      | return stx
    let some n' := coreName? n | return stx
    unless ← Macro.hasDecl n' do Macro.throwErrorAt stx s!"no scoped twin `{n'}` of `{n}`"
    return Lean.mkCIdentFrom stx n'
  | .node info k args => return .node info k (← args.mapM coreNames)
  | _ => return stx

/-- A scoped update's right-hand side for the local `x`, by its kind:
`Rhs.val`, `Rhs.path` (`unset` too), `Rhs.mref`. -/
def schemaRhsCore (Γ : Scope) (x : Ident) (r : TSyntax `dl_term) : MacroM Lean.Term := do
  match headOf Γ x with
  | .local _ => `($(Lean.mkCIdent `Solidity.Rhs.val) $(← schemaTerm Γ .val r))
  | .alias _ =>
    if let `(dl_term| $u:ident) := r then
      if u.getId == `unset then return Lean.mkCIdent `Solidity.Rhs.unset
    `($(Lean.mkCIdent `Solidity.Rhs.path) $(← schemaTerm Γ .path r))
  | .mem .. => `($(Lean.mkCIdent `Solidity.Rhs.mref) $(← schemaTerm Γ .ident r))
  | _ => Macro.throwErrorAt x "an update assigns a local, an alias, a memory local, \
      `storage` or `memory`"

/-- `Ext.push^d .refl`: the `d` fresh locals a premise declared, popped. -/
def extPush (d : Nat) : MacroM Lean.Term := do
  let mut h : Lean.Term := Lean.mkCIdent `Solidity.Ext.refl
  for _ in [0:d] do h ← `($(Lean.mkCIdent `Solidity.Ext.push) $h)
  return h

/-- The fresh local an update element declares by its spelling: KeY's `b`
(`bType b = cond;`, a `bool`) and `variant` (`\\skolemTerm int variant`, a
`uint`), the invariant rules' (`headOf` names them `se`, `ie`). -/
def updFresh? (n : String) : Option (Lean.Term × Lean.Term) :=
  let k := schemaIdent "k"
  match stemOf n with
  | "b" => some (Lean.Syntax.mkApp (mkIdent ``Var.fresh) #[Lean.Syntax.mkStrLit "se", k],
      Lean.mkCIdent ``PrimTy.bool)
  | "variant" => some (Lean.Syntax.mkApp (mkIdent ``Var.fresh) #[Lean.Syntax.mkStrLit "ie", k],
      Lean.mkCIdent ``PrimTy.uint)
  | _ => none

/-- A scoped update: its elements `snoc`ed onto `Upd.nil` in order, every
right-hand side read in `Γ`; the local the `\find` declares (`found`), and
an invariant rule's `b` and `variant` (`updFresh?`), declared (`Upd.decl`),
the scope after it returned. -/
def schemaUpdCore (Γ : Scope) (found : Option String) (U : TSyntax `dl_upd) :
    MacroM (Lean.Term × Scope) := do
  if let `(dl_upd| ‹ $t:term ›) := U then return (t, Γ)
  let mut acc : Lean.Term := Lean.mkCIdent `Solidity.Upd.nil
  let mut Γ' := Γ
  for e in U.raw[1].getSepArgs do
    match (⟨e⟩ : TSyntax `dl_upd_elem) with
    | `(dl_upd_elem| $l:dl_term := $r:dl_term) =>
      let `(dl_term| $x:ident) := l | Macro.throwErrorAt l "an update assigns a variable"
      let n := x.getId.toString
      if found == some n then
        acc ← `($(Lean.mkCIdent `Solidity.Upd.decl) $acc $x $(← schemaRhsCore Γ x r))
        Γ' := (n, .val x) :: Γ'
      else if let some (v, p) := updFresh? n then
        acc ← `($(Lean.mkCIdent `Solidity.Upd.decl) $acc $v
          ($(Lean.mkCIdent `Solidity.Rhs.val) (p := $p) $(← schemaTerm Γ .val r)))
        Γ' := (n, .val v) :: Γ'
      else if ["storage", "memory", "net", "selfBalance"].contains n then
        acc ← `($(Lean.mkCIdent `Solidity.Upd.snoc) $acc $(← schemaUpdElem Γ ⟨e⟩))
      else
        -- the target a local of the scope after the declarations so far
        let tgt ← match headOf Γ' x with
          | .local v | .alias v | .mem v _ => pure v
          | _ => Macro.throwErrorAt x "an update assigns a local, an alias, a memory local, \
              `storage` or `memory`"
        acc ← `($(Lean.mkCIdent `Solidity.Upd.snoc) $acc
          ($(Lean.mkCIdent `Solidity.UpdElem.local) $tgt $(← schemaRhsCore Γ x r)))
    | _ => Macro.throwErrorAt e "a scoped taclet's update has no update variable"
  return (acc, Γ')

/-- `Solidity.Fml.c`, a constructor of the scoped formulas, by its full
name, so that `coreNames` leaves it as it is. -/
def fmlC (c : String) : Lean.Term := Lean.mkCIdent (`Solidity.Fml ++ Name.mkSimple c)

/-- A scoped formula, its names read in `Γ`: a fresh local an update in it
declares (`{ b := cond } (b = TRUE → …)`) is a position in the formula after
it.  The forms the rule lines write. -/
partial def schemaFmlCore (Γ : Scope) : TSyntax `dl_fml → MacroM Lean.Term
  | `(dl_fml| true) => pure (fmlC "tt")
  | `(dl_fml| false) => `($(fmlC "not") $(fmlC "tt"))
  | `(dl_fml| $a:dl_term != $b:dl_term) => do
    `($(fmlC "not") ($(fmlC "eq") $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b)))
  | `(dl_fml| $a:dl_term = $b:dl_term) => do
    if let `(dl_term| $c:ident) := b then
      let n := c.getId.toString
      if n == "TRUE" || n == "FALSE" then
        let v := mkIdent (Name.mkSimple (if n == "TRUE" then "true" else "false"))
        return ← `($(fmlC "eqD") $(← schemaTerm Γ .val a) (Term.litB $v))
    `($(fmlC "eq") $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_fml| $a:dl_term ≐ $b:dl_term) => do
    `($(fmlC "eq") $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_fml| defined( $t:dl_term )) => do `($(fmlC "defined") $(← schemaTerm Γ .val t))
  | `(dl_fml| ¬ $φ:dl_fml) => do `($(fmlC "not") $(← schemaFmlCore Γ φ))
  | `(dl_fml| $φ:dl_fml ∧ $ψ:dl_fml) => do
    `($(fmlC "and") $(← schemaFmlCore Γ φ) $(← schemaFmlCore Γ ψ))
  | `(dl_fml| $φ:dl_fml → $ψ:dl_fml) => do
    `($(fmlC "imp") $(← schemaFmlCore Γ φ) $(← schemaFmlCore Γ ψ))
  | `(dl_fml| $U:dl_upd $φ:dl_fml) => do
    let m ← match ← fmlModality? (schemaIdent "m") φ with
      | some m => pure m
      | none => `(Modality.diamond)
    let (U, Γ') ← schemaUpdCore Γ none U
    `($(fmlC "upd") $m $U $(← schemaFmlCore Γ' φ))
  | `(dl_fml| ( $φ:dl_fml )) => schemaFmlCore Γ φ
  | `(dl_fml| ‹ $t:term ›) => pure t
  | `(dl_fml| $x:ident) => pure x
  | `(dl_fml| $a:dl_term <= $b:dl_term) => do
    `($(fmlC "eqD") (Term.binop BinOp.le PrimTy.uint $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
        (Term.litB true))
  | `(dl_fml| $a:dl_term < $b:dl_term) => do
    `($(fmlC "eqD") (Term.binop BinOp.lt PrimTy.uint $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
        (Term.litB true))
  | φ => Macro.throwErrorAt φ "no scoped reading of this formula yet"

/-- The invariant rule's premise: the invariant now;
the body's frame (`xs`, `hv`, bound by the side condition
`Prog.frame body = some (xs, hv)`); the update of the condition's value `b`
(and under the diamond the variant's `variant`), the conditions read after
it; the body and its postcondition read where `b` is popped (`hb`), the
variant kept above the loop's context (`hu`). -/
def schemaInvCore (i : TSyntax `dl_fml) (b : TSyntax `sol_block) (h : TSyntax `dl_fml)
    (U : TSyntax `dl_upd) (c : TSyntax `dl_fml) (t : TSyntax `sol_block)
    (post c' : TSyntax `dl_fml) (B : Option Lean.Term := none) : MacroM Lean.Term := do
  unless i.raw.structEq h.raw do
    Macro.throwErrorAt h "the invariant assumed is the one shown initially valid"
  unless b.raw.structEq t.raw do
    Macro.throwErrorAt t "the frame is the body's, which the goal runs"
  let (Ut, Γu) ← schemaUpdCore coreScope none U
  -- the body's scope: the update's locals but `b`
  let Γ₀ : Scope := Γu.filter (·.1 != "b")
  let hu ← extPush (Scope.depth Γ₀)
  let hb ← extPush (Scope.depth Γu - Scope.depth Γ₀)
  let B ← match B with
    | some B => pure B
    | none => `(Option.none)
  `($(Lean.mkCIdent `Solidity.Premise.inv) $(← schemaFmlCore coreScope i) $B
      $(schemaIdent "xs") $(schemaIdent "hv") $Ut $(← schemaFmlCore Γu c) $(← schemaFmlCore Γu c')
      $hu $hb $(← schemaBlock true Γ₀ t) $(← schemaFmlCore Γ₀ post))

/-- `expand_function_body(fbs)`, a whole premise. -/
def expandBody? : TSyntax `sol_stmt → Bool
  | `(sol_stmt| $f:sol_expr ( $a:sol_expr )) =>
    match f with
    | `(sol_expr| $g:ident) =>
      g.getId.toString == "expand_function_body" && (stemOfExpr? a).any isCallStem
    | _ => false
  | _ => false

/-- A scoped premise.  `Γ` is the scope after the `\find`, `found` the local
it declares (its name and its variable), `split` how a split's goals end. -/
def schemaPremiseCore (Γ : Scope) (found : Option (String × Lean.Term)) (split : Lean.Term) :
    TSyntax `dl_premise → MacroM Lean.Term
  | `(dl_premise| if $c:dl_fml then ($U:dl_upd $V:dl_upd ⟨[ ]⟩) else (⟨[ revert(); ]⟩)) => do
    let (Ut, Δ) ← schemaUpdCore coreScope none U
    let (Vt, _) ← schemaUpdCore Δ none V
    let ct ← match c with
      | `(dl_fml| $a:dl_term != 0) => do
        let lhsTerm ← schemaTerm coreScope .val a
        `($(fmlC "not") ($(fmlC "eq") $lhsTerm
          ($(Lean.mkCIdent `Solidity.Tm.zeroLike) $lhsTerm)))
      | _ => schemaFmlCore coreScope c
    `($(Lean.mkCIdent `Solidity.Premise.guardedUpdates) $ct $Ut $Vt)
  | `(dl_premise| $U:dl_upd $V:dl_upd ⟨[ ]⟩) => do
    let declared := found.map (·.1)
    let inFirst := declared.filter fun n => U.raw[1].getSepArgs.any fun e =>
      match (⟨e⟩ : TSyntax `dl_upd_elem) with
      | `(dl_upd_elem| $x:ident := $_:dl_term) => x.getId.toString == n
      | _ => false
    let (Ut, Δ) ← schemaUpdCore coreScope inFirst U
    let (Vt, _) ← schemaUpdCore Δ (if inFirst.isSome then none else declared) V
    `($(Lean.mkCIdent `Solidity.Premise.updates) $Ut $Vt)
  | `(dl_premise| $U:dl_upd ⟨[ ]⟩) => do
    `($(Lean.mkCIdent `Solidity.Premise.update)
      $((← schemaUpdCore coreScope (found.map (·.1)) U).1))
  | `(dl_premise| ⟨[ $[$ss:sol_stmt;]* ]⟩) => do
    if ss.size == 1 && expandBody? ss[0]! then
      -- a call inlined: the premise `Stmt.step` builds (`Premise.expandCall`)
      return ← `($(Lean.mkCIdent `Solidity.Premise.expandCall) $(schemaIdent "k")
        $(schemaIdent "args") $(schemaIdent "ret") $(schemaIdent "body"))
    let (ts, Γ') ← schemaProg true Γ ss
    let P ← progTermCore ts
    match found with
    | some (_, x) => `($(Lean.mkCIdent `Solidity.Premise.bind) $x _ $P)
    | none => `($(Lean.mkCIdent `Solidity.Premise.unfold) $P $(← extPush (Γ'.depth - Γ.depth)))
  | `(dl_premise| $[$_:str :]? $c:dl_fml ⟹ ⟨[ $t:sol_block ]⟩ ; $[$_:str :]? $nc:dl_fml ⟹ ⟨[ $f:sol_block ]⟩) => do
    `($(Lean.mkCIdent `Solidity.Premise.split) $split $(← schemaFmlCore coreScope c) $(← schemaFmlCore coreScope nc)
        $(← schemaBlock true Γ t) $(← schemaBlock true Γ f))
  | `(dl_premise| $[$_:str :]? $c:dl_fml ⟹ ⟨[ $[$ts:sol_stmt;]* ]⟩ ;
      $[$_:str :]? $nc:dl_fml ⟹ ⟨[ $[$fs:sol_stmt;]* ]⟩) => do
    let (ts, _) ← schemaProg true Γ ts
    let (fs, _) ← schemaProg true Γ fs
    `($(Lean.mkCIdent `Solidity.Premise.split) $split $(← schemaFmlCore coreScope c) $(← schemaFmlCore coreScope nc)
        $(← progTermCore ts) $(← progTermCore fs))
  | `(dl_premise| $[$_:str :]? $c:dl_fml ⟹ ⟨[ $[$ts:sol_stmt;]* ]⟩ ; $[$_:str :]? $c':dl_fml) => do
    unless c.raw.structEq c'.raw do
      Macro.throwErrorAt c' "a check assumes the condition it checks: write it on both sides"
    unless ts.isEmpty do Macro.throwErrorAt c "a scoped check goes on with the rest of the program"
    `($(Lean.mkCIdent `Solidity.Premise.check) $(← schemaFmlCore coreScope c))
  | `(dl_premise| true) => `($(Lean.mkCIdent `Solidity.Premise.done) true)
  | `(dl_premise| false) => `($(Lean.mkCIdent `Solidity.Premise.done) false)
  | `(dl_premise| $b:dl_branch ; $bs:dl_branch;*) => do
    let bs ← (#[b] ++ bs.getElems).mapM (schemaBranch true coreScope)
    `($(Lean.mkCIdent `Solidity.Premise.branches) [$bs,*])
  | `(dl_premise| $c:dl_case ; $cs:dl_case;*) => do
    let mut fs : Array Lean.Term := #[]
    let mut us : Array Lean.Term := #[]
    for c in #[c] ++ cs.getElems do
      match c with
      | `(dl_case| $[$_:str :]? $U:dl_upd ⟨[ ]⟩) => us := us.push (← schemaUpdCore coreScope none U).1
      | `(dl_case| $[$_:str :]? $φ:dl_fml) =>
        unless us.isEmpty do Macro.throwErrorAt c "the formula goals come first"
        fs := fs.push (← schemaFmlCore coreScope φ)
      | _ => Macro.throwUnsupported
    `($(Lean.mkCIdent `Solidity.Premise.cases) [$fs,*] [$us,*])
  | `(dl_premise| $[$_:str :]? $i:dl_fml ; $[$_:str :]? { anon($b:sol_block) } ($h:dl_fml →
      $U:dl_upd ($c:dl_fml ⟹ ⟨[ $t:sol_block ]⟩ $post:dl_fml ; $c':dl_fml ⟹ ⟨[ ]⟩))) => do
    schemaInvCore i b h U c t post c'
  | `(dl_premise| $[$_:str :]? $i:dl_fml ; $[$_:str :]? { anon($b:sol_block) } ($h:dl_fml ∧ ¬$k₁:dl_fml →
      $U:dl_upd ($c:dl_fml ⟹ ⟨[ $t:sol_block ]⟩ (¬$k₂:dl_fml → $post:dl_fml) ∧ ($k₃:dl_fml → ⟨[ ]⟩) ;
        $c':dl_fml ⟹ ⟨[ ]⟩))) => do
    -- the break test is the one `Stmt.step` computes (`loopBreak`), named
    -- `broke` as solkey names it
    for k in [k₁, k₂, k₃] do
      let named := match k with
        | `(dl_fml| $x:ident) => x.getId.toString == "broke"
        | _ => false
      unless named do Macro.throwErrorAt k "a loop's break test is written `broke`"
    unless post.raw.structEq h.raw do
      Macro.throwErrorAt post "a body that does not break keeps the invariant"
    -- the invariant initially valid, the flag not set
    let i ← match i with
      | `(dl_fml| $i:dl_fml ∧ ¬$k₀:dl_fml) =>
        unless k₀.raw.structEq k₁.raw do
          Macro.throwErrorAt k₀ "a loop's break test is written `broke`"
        pure i
      | _ => Macro.throwErrorAt i "the loop starts with the invariant and its flag not set"
    schemaInvCore i b h U c t post c'
      (some (← `($(Lean.mkCIdent `Solidity.loopBreak) $(schemaIdent "brk") $(schemaIdent "cond"))))
  | p => Macro.throwErrorAt p "no scoped reading of this premise yet"

/-- A compound assignment's operator terms: `l ⊕ se` in `l ⊕= se`'s premise
takes `⊕=`'s proofs (`hop` that it has a compound form, `hp` that the type is
numeric), not `Val.binop`'s (`hop`, `hq`): `Term.binopS … hq` becomes
`Term.binopC … hp`. -/
partial def compoundOps : Syntax → Syntax
  | stx@(.ident _ _ val _) =>
    let v := val.eraseMacroScopes
    if v == `Term.binopS then (mkIdentFrom stx `Term.binopC).raw
    else if v == `hq then (mkIdentFrom stx `hp).raw
    else stx
  | .node i k args => .node i k (args.map compoundOps)
  | stx => stx

/-- Instantiate a fixed push operator in its otherwise shared replacement
shape; its appended index is always a dynamic-array index. -/
partial def specializePush (op proof index : Syntax) : Syntax → Syntax
  | stx@(.ident _ _ val _) =>
    match val.eraseMacroScopes with
    | `op => op
    | `hop => proof
    | `it => index
    | _ => stx
  | .node i k args => .node i k (args.map (specializePush op proof index))
  | stx => stx

/-- The indexed primitive read in a push suffix replacement, excluding its
`size` reads. `sp.push() += se` determines the arithmetic's numeric type;
the index arithmetic remains `uint`. -/
def pushValueRead : TSyntax `dl_term → Bool
  | `(dl_term| find($_, $_:dl_term[$_:dl_term])) => true
  | `(dl_term| find($_, consr($_, at($_)))) => true
  | _ => false

/-- Read the literal arithmetic of a native push rule at its target type.
Only the matching operator on the appended primitive is specialized: a
`size + 1` or `size - 1` still uses the ordinary `uint` term reader. -/
partial def pushArithmetic (compound : Bool) (sym : String) (s : Syntax) : MacroM Syntax := do
  let .node info kind args := s | return s
  let s := Syntax.node info kind (← args.mapM (pushArithmetic compound sym))
  let bin : Option (String × TSyntax `dl_term × TSyntax `dl_term) := match (⟨s⟩ : TSyntax `dl_term) with
    | `(dl_term| $a + $b) => some ("+", a, b)
    | `(dl_term| $a - $b) => some ("-", a, b)
    | `(dl_term| $a * $b) => some ("*", a, b)
    | `(dl_term| $a / $b) => some ("/", a, b)
    | `(dl_term| $a % $b) => some ("%", a, b)
    | _ => none
  let some (actual, a, b) := bin | return s
  unless actual == sym && pushValueRead a do return s
  if compound then return (← `(dl_term| $a ⊕ $b)).raw
  if let `(dl_term| 1) := b then return (← `(dl_term| $a ± $b)).raw
  return s

/-- The literal arithmetic symbol supplied by a native push statement. -/
def pushOperatorSymbol (op : Lean.Term) : String :=
  match op with
  | `($name:ident) =>
    match name.getId.eraseMacroScopes.getString! with
    | "add" | "preInc" | "postInc" => "+"
    | "sub" | "preDec" | "postDec" => "-"
    | "mul" => "*" | "div" => "/" | "mod" => "%"
    | _ => ""
  | _ => ""

/-- Whether a statement is a compound assignment `l ⊕= r`. -/
def isCompound : TSyntax `sol_stmt → Bool
  | `(sol_stmt| $_:sol_expr ⊕= $_:sol_expr) => true
  | _ => false

/-- The receiver and argument of either spelling of `sp.push(arg)`. -/
def valuePushParts? : TSyntax `sol_stmt → MacroM (Option (TSyntax `sol_expr × TSyntax `sol_expr))
  | `(sol_stmt| $b:sol_expr .push( $a:sol_expr )) => pure (some (b, a))
  | `(sol_stmt| $f:sol_expr ( $a:sol_expr )) => do
    let some (b, "push") ← callRecv? f | pure none
    pure (some (b, a))
  | _ => pure none

/-- The operation in either spelling of `fc.push(e)`, `fc.push()` or `fc.pop()`. -/
def receiverParts? (s : TSyntax `sol_stmt) :
    MacroM (Option (TSyntax `sol_expr × Option (TSyntax `sol_expr) × Bool)) := do
  if let some (b, a) ← valuePushParts? s then return some (b, some a, false)
  match s with
  | `(sol_stmt| $b:sol_expr .push()) => return some (b, none, false)
  | `(sol_stmt| $b:sol_expr .pop()) => return some (b, none, true)
  | `(sol_stmt| $f:sol_expr ( )) =>
    let some (b, method) ← callRecv? f | return none
    if method == "push" then return some (b, none, false)
    if method == "pop" then return some (b, none, true)
    return none
  | _ => return none

/-- A native call-receiver capture. The two written statements must retain
the same getter, operation and operand, and bind the fresh `sp` they use. -/
def callReceiverTaclet? (s : TSyntax `sol_stmt) (p : TSyntax `dl_premise) :
    MacroM (Option (Lean.Term × Lean.Term)) := do
  let some (fc, arg, pop) ← receiverParts? s | return none
  unless (singleVar? fc).any (fun n => stemOf n == "fc") do return none
  let `(dl_premise| ⟨[ $[$ss:sol_stmt;]* ]⟩) := p |
    Macro.throwErrorAt p "a call receiver is captured in `sp` before its array operation"
  unless ss.size == 2 do
    Macro.throwErrorAt p "a call-receiver capture has a declaration and its array operation"
  let `(sol_stmt| $aliasType:sol_ty storage $sp:ident = $getter:sol_expr) := ss[0]! |
    Macro.throwErrorAt ss[0]! "a call receiver is bound as a storage alias"
  let _ := aliasType
  unless stemOf sp.getId.toString == "sp" && fc.raw.structEq getter.raw do
    Macro.throwErrorAt ss[0]! "the fresh `sp` captures the getter of the find"
  let some (recv, arg', pop') ← receiverParts? ss[1]! |
    Macro.throwErrorAt ss[1]! "the captured receiver is pushed or popped"
  let sameArg := match arg, arg' with
    | none, none => true
    | some a, some b => a.raw.structEq b.raw
    | _, _ => false
  unless singleVar? recv == some sp.getId.toString && pop == pop' && sameArg do
    Macro.throwErrorAt ss[1]! "the replacement keeps the operation and operand on fresh `sp`"
  if let some a := arg then
    let some n := singleVar? a |
      Macro.throwErrorAt a "the call-receiver operand is a typed source schema variable"
    let st ← `($(Lean.mkCIdent `Solidity.ReceiverValue.statement) $(schemaIdent "f")
      $(schemaIdent "args") $(schemaIdent "r") $(schemaIdent "body") $(schemaIdent n))
    let pt ← `($(Lean.mkCIdent `Solidity.ReceiverValue.step) $(schemaIdent "k")
      $(schemaIdent "f") $(schemaIdent "args") $(schemaIdent "r") $(schemaIdent "body")
      $(schemaIdent n))
    return some (st, pt)
  let op ← if pop then `($(Lean.mkCIdent `Solidity.ReceiverOp.pop)) else
    match arg with
    | none => `($(Lean.mkCIdent `Solidity.ReceiverOp.push) none $(schemaIdent "hd"))
    | some a =>
      let some n := singleVar? a |
        Macro.throwErrorAt a "the call-receiver operand is a typed source schema variable"
      `($(Lean.mkCIdent `Solidity.ReceiverOp.push) (some $(schemaIdent n)) rfl)
  let st ← `($(Lean.mkCIdent `Solidity.Stmt.callReceiver) $(schemaIdent "f")
    $(schemaIdent "args") $(schemaIdent "r") $(schemaIdent "body") $op)
  let pt ← `($(Lean.mkCIdent `Solidity.callReceiverStep) $(schemaIdent "k")
    $(schemaIdent "f") $(schemaIdent "args") $(schemaIdent "r") $(schemaIdent "body") $op)
  return some (st, pt)

/-- Recognise the exact upstream `whileUnwind` shape, retaining a typed proof-search mode. -/
def whileUnwindTaclet? (s : TSyntax `sol_stmt) (p : TSyntax `dl_premise) :
    MacroM (Option (Lean.Term × Lean.Term)) := do
  let rec plain : Syntax → Syntax
    | .ident info raw name _ => .ident info raw name.eraseMacroScopes []
    | .node info kind args => .node info kind (args.map plain)
    | stx => stx
  let find ← `(sol_stmt| while (cond) body)
  unless (plain s.raw).structEq (plain find.raw) do return none
  let expected ← `(dl_premise| ⟨[ if (cond) { body; while (cond) body; }; ]⟩)
  unless (plain p.raw).structEq (plain expected.raw) do return none
  let c ← schemaAt coreScope .val ⟨s.raw[2]⟩
  let body ← schemaBlock false coreScope ⟨s.raw[4]⟩
  let st ← `($(Lean.mkCIdent `Solidity.Stmt.loop)
    ($(Lean.mkCIdent `Solidity.LoopUnwind.before) $(schemaIdent "u")) $c $body)
  let pt ← `($(Lean.mkCIdent `Solidity.loopUnwindStep) $(schemaIdent "u") $c $body)
  return some (st, pt)

/-- The taclet `s ⇝ p` under modality `m`: the find binds schema variables;
the replacement reads them and introduces its own fresh declarations. -/
def schemaTacletCore (m : Lean.Term) (s : TSyntax `sol_stmt) (p : TSyntax `dl_premise)
    (J : Option Lean.Term := none) : MacroM Lean.Term := do
  let receiver ← callReceiverTaclet? s p
  let native ← if receiver.isSome then pure receiver else whileUnwindTaclet? s p
  let conds ← sideConds s
  -- A value declaration in this capture replacement identifies a primitive
  -- source. A storage declaration instead keeps the reference-copy reading.
  let primitive : Option (TSyntax `sol_expr × TSyntax `sol_expr) ← do
    let some (b, a) ← valuePushParts? s | pure none
    let `(dl_premise| ⟨[ $[$ss:sol_stmt;]* ]⟩) := p | pure none
    if ss.size != 2 then pure none else do
      let `(sol_stmt| $sourceTy:sol_ty $source:ident = $r:sol_expr) := ss[0]! | pure none
      let _ := sourceTy
      let some (b', v) ← valuePushParts? ss[1]! | pure none
      if isPath coreScope a && a.raw.structEq r.raw && b.raw.structEq b'.raw &&
          (singleVar? v) == some source.getId.toString then pure (some (b, a)) else pure none
  let (st, Γ) ← match native, primitive with
    | some (st, _), _ => pure (st, coreScope)
    | none, some (b, a) => do
      let src ← schemaAt coreScope .spath a
      let recv ← schemaAt coreScope .spath b
      pure (← `(Stmt.push $recv (some (Src.val (SPath.primitiveRead $src))) rfl), coreScope)
    | none, none => schemaStmt false coreScope s
  let found : Option (String × Lean.Term) := match Γ with
    | (n, .val v) :: _ | (n, .alias v) :: _ | (n, .mem v _) :: _ => some (n, v)
    | _ => none
  let split := match s with
    | `(sol_stmt| if ($_:sol_expr) $_:sol_block else $_:sol_block) =>
      Lean.mkCIdent `Solidity.BlockKind.block
    | _ => Lean.mkCIdent `Solidity.BlockKind.capture
  let fixed ← fixedPushOperator? s
  let p : TSyntax `dl_premise ← match fixed with
    | none => pure p
    | some (op, compound) => do pure ⟨← pushArithmetic compound (pushOperatorSymbol op) p⟩
  let pt ← match native with
    | some (_, pt) => pure pt
    | none => schemaPremiseCore Γ found split p
  let pt : Lean.Term := if isCompound s || fixed.any (·.2) then ⟨compoundOps pt⟩ else pt
  let pt : Lean.Term ← match fixed with
    | none => pure pt
    | some (op, _) => do
      pure ⟨specializePush op (← `(by rfl)) (← `(IndexTy.arr ArrTy.dyn)) pt⟩
  let st ← `(($st : $(Lean.mkCIdent `Solidity.Stmt) $(schemaIdent "C") $(schemaIdent "Γ") _))
  let jArgs : Array Lean.Term := #[schemaIdent "C", schemaIdent "k"]
  let ((f, args) : Ident × Array Lean.Term) ← match J with
    | none => pure (mkIdent `Taclet, jArgs)
    | some J => match J with
      | `($f:ident $args*) => pure (f, args)
      | `($f:ident) => pure (f, #[])
      | _ => Macro.throwErrorAt J "`dl[J]{ … }` names a judgement: `LeanTaclet C k`"
  let t ← `($f:ident $args* $m $st $pt)
  let t ← if conds.isEmpty then pure t else
    let hs := conds.map (·.1)
    let cs := conds.map (·.2)
    `(taclet_side% $t $[($hs : $cs)]*)
  return ⟨← coreNames t⟩

/-- A quantifier's type written by name: `uint`, `int`, `bool`, or a Lean term. -/
def schemaPrim (T : Ident) : MacroM Lean.Term :=
  match T.getId.toString with
  | "uint" => `(PrimTy.uint)
  | "int" => `(PrimTy.int)
  | "bool" => `(PrimTy.bool)
  | _ => pure T

end Expand

namespace Schema

/-- Under `open scoped Solidity.Schema`, a taclet line writes a scoped
taclet (`schemaTacletCore`): the same text, the `Taclet` (or the judgement
named) in scope where it is used. -/
scoped macro_rules
  | `(dl{ if $c:dl_fml then ($U:dl_upd $V:dl_upd ⟨[ ]⟩) else (⟨[ revert(); ]⟩) }) => do
    let t ← schemaPremiseCore coreScope none (← `(BlockKind.capture))
      (← `(dl_premise| if $c:dl_fml then ($U:dl_upd $V:dl_upd ⟨[ ]⟩) else (⟨[ revert(); ]⟩)))
    coreNames t
  | `(dl{ $U:dl_upd $V:dl_upd ⟨[ ]⟩ }) => do
    schemaPremiseCore coreScope none (← `(BlockKind.capture))
      (← `(dl_premise| $U:dl_upd $V:dl_upd ⟨[ ]⟩))
  | `(dl{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p:dl_premise }) => schemaTacletCore (schemaIdent "m") s p
  | `(dl{ [ $s:sol_stmt; ] ⇝ $p:dl_premise }) => do schemaTacletCore (← `(Modality.box)) s p
  | `(dl{ ⟨ $s:sol_stmt; ⟩ ⇝ $p:dl_premise }) => do schemaTacletCore (← `(Modality.diamond)) s p
  | `(dl[ $J:term ]{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p:dl_premise }) => schemaTacletCore (schemaIdent "m") s p J
  | `(dl[ $J:term ]{ [ $s:sol_stmt; ] ⇝ $p:dl_premise }) => do
    schemaTacletCore (← `(Modality.box)) s p J
  | `(dl[ $J:term ]{ ⟨ $s:sol_stmt; ⟩ ⇝ $p:dl_premise }) => do
    schemaTacletCore (← `(Modality.diamond)) s p J

end Schema

section Side
open Lean Elab Term

elab_rules : term
  | `(taclet_side% $t $[($hs : $cs)]*) => do
    let T ← elabType t
    let mut hyps : Array (Lean.Name × Expr) := #[]
    for h in hs, c in cs do
      hyps := hyps.push (h.getId, ← elabType c)
    return hyps.foldr (init := T) fun (n, ty) b =>
      .forallE n (mkApp2 (mkConst ``autoParam [levelZero]) ty (mkConst ``Solidity.sideCond)) b
        .default

end Side

/-! ## Printing the notation (delaborators)

Each `pp…` function walks a Lean `Expr` and builds syntax of the grammar
above; Lean's formatter prints it.  The walk first computes (`whnf`), so a
lowered schema variable, `P ++ ω` and the like print as what they compute
to.  A subterm the walk does not recognise prints as `‹…›`. -/

section Print
open Lean Meta PrettyPrinter Delaborator SubExpr
set_option hygiene false

@[category_parenthesizer dl_fml] def dl_fml.parenthesizer : CategoryParenthesizer
  | prec => Parenthesizer.maybeParenthesize `dl_fml false
      (fun stx => Unhygienic.run `(dl_fml| ($(⟨stx⟩)))) prec
      (Parenthesizer.parenthesizeCategoryCore `dl_fml prec)

@[category_parenthesizer dl_term] def dl_term.parenthesizer : CategoryParenthesizer
  | prec => Parenthesizer.maybeParenthesize `dl_term false
      (fun stx => Unhygienic.run `(dl_term| ($(⟨stx⟩)))) prec
      (Parenthesizer.parenthesizeCategoryCore `dl_term prec)

@[category_parenthesizer sol_expr] def sol_expr.parenthesizer : CategoryParenthesizer
  | prec => Parenthesizer.maybeParenthesize `sol_expr false
      (fun stx => Unhygienic.run `(sol_expr| ($(⟨stx⟩)))) prec
      (Parenthesizer.parenthesizeCategoryCore `sol_expr prec)

register_option pp.sol.dl : Bool := {
  defValue := true
  descr := "print statements, formulas, taclets and sequents in the calculus's \
            notation, rather than as constructor applications"
}

def ppOn : MetaM Bool := return pp.sol.dl.get (← getOptions)

register_option pp.sol.key : Bool := {
  defValue := false
  descr := "print terms in KeY's long forms: `consr(p, f)` for `p.f`, `consr(p, at(i))` for \
            `p[i]`, `find(storage, consr(p, size))` for `p.length`, `read(m, i, f)`, \
            `write(m, i, f, v)`, `storeSt`/`selectSt`/`self` in the ledger (`#taclet` sets it)"
}

/-- Whether terms print in KeY's long forms (`pp.sol.key`). -/
def keyOn : MetaM Bool := return pp.sol.key.get (← getOptions)

register_option pp.sol.reduce : Bool := {
  defValue := true
  descr := "the notation's printers compute (`whnf`) each term before they print it; \
            `tm{ … }` prints a term as it is written, with this off"
}

def nameIdent (s : String) : Ident := mkIdent (Name.mkSimple s)

/-- Lean's own printing of `e`, with this notation off. -/
def escapeTerm (e : Lean.Expr) : MetaM Lean.Term :=
  withOptions (fun o => pp.sol.dl.set o false) (PrettyPrinter.delab e)

partial def listElems? (es : Lean.Expr) : MetaM (Option (Array Lean.Expr)) := do
  let mut out := #[]
  let mut cur ← whnf es
  repeat
    if cur.isAppOfArity ``List.nil 1 then return some out
    unless cur.isAppOfArity ``List.cons 3 do return none
    let args := cur.getAppArgs
    out := out.push args[1]!
    cur ← whnf args[2]!
  return some out

/-- The name of a free variable. -/
def fvarName? (e : Lean.Expr) : MetaM (Option String) := do
  let .fvar fv := (← instantiateMVars e).consumeMData | return none
  return some (← fv.getUserName).eraseMacroScopes.toString

/-- A string, or the name of a string variable. -/
def nameOf? (e : Lean.Expr) : MetaM (Option String) := do
  if let some n ← fvarName? e then return some n
  match (← whnf (← instantiateMVars e)).consumeMData with
  | .lit (.strVal s) => return some s
  | _ => return none

/-- A closed natural number. -/
def natOf? (e : Lean.Expr) : MetaM (Option Nat) := do
  let e ← instantiateMVars e
  if let some n ← (evalNat e).run then return some n
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return none
  try return some (← unsafe evalExpr Nat (mkConst ``Nat) e) catch _ => return none

/-- A closed integer. -/
def intOf? (e : Lean.Expr) : MetaM (Option Int) := do
  let e ← instantiateMVars e
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return none
  try return some (← unsafe evalExpr Int (mkConst ``Int) e) catch _ => return none

/-- The spelling of `.fresh b k` by the `FreshNames` in scope. -/
def freshName (b : String) (k : Nat) : MetaM String := do
  let fn ← synthInstance (mkConst ``Solidity.FreshNames)
  unsafe evalExpr String (mkConst ``String)
    (mkApp3 (mkConst ``Solidity.FreshNames.name) fn (toExpr b) (toExpr k))

/-- A variable: `x`, `se1` (as `FreshNames` spells it), or `se` for a taclet's
fresh `.fresh "se" k`. -/
def ppVar? (e : Lean.Expr) : MetaM (Option Ident) := do
  if let some n ← fvarName? e then return some (nameIdent n)
  match_expr (← whnf (← instantiateMVars e)) with
  | Solidity.Var.user s => return (← nameOf? s).map nameIdent
  | Solidity.Var.fresh b k =>
    let some b ← nameOf? b | return none
    match ← natOf? k with
    | some n => return some (nameIdent (← freshName b n))
    | none =>
      -- a taclet's fresh `sp` beside a schema variable `sp` it reads: `sp'`
      let lctx ← getLCtx
      let mut x := b
      while (lctx.findFromUserName? (Name.mkSimple x)).isSome do x := x ++ "'"
      return some (nameIdent x)
  | _ => return none

/-! ### Programs

The builders `Calculus/PrintStmt.lean`'s printers of the scoped syntax use. -/

def binopSym? (op : Lean.Expr) : MetaM (Option String) := do
  if (← fvarName? op).isSome then return some "⊕"
  let op ← whnf op
  return (BinOp.all.find? (toExpr · == op)).map BinOp.sym

/-- `a ⊕ b` in the program grammar: the node the parser makes of `a ⊕ b` for
an operator of the table (`BinOp.ofSym?`), else the schema operator `⊕`. -/
def mkBinExpr (sym : String) (a b : TSyntax `sol_expr) : MetaM (TSyntax `sol_expr) := do
  if (BinOp.ofSym? sym).isSome then
    if let .ok t := Lean.Parser.runParserCategory (← getEnv) `sol_expr s!"a {sym} b" then
      if t.getNumArgs == 3 then
        return ⟨Syntax.node .none t.getKind #[a, mkAtom sym, b]⟩
  `(sol_expr| $a ⊕ $b)

/-- `b.f`: one dotted name when `b` is a name, as the parser reads it. -/
def dotExpr (b : TSyntax `sol_expr) (f : String) : MetaM (TSyntax `sol_expr) :=
  match b with
  | `(sol_expr| $x:ident) => `(sol_expr| $(mkIdent (x.getId.str f)):ident)
  | _ => `(sol_expr| $b . $(nameIdent f):ident)

/-- A Solidity type, as written: `uint`, `Person`, `uint[]`, `mapping(uint => Person)`. -/
partial def ppTy (e : Lean.Expr) : MetaM (TSyntax `sol_ty) := do
  if let some n ← fvarName? e then return ← `(sol_ty| $(nameIdent n):ident)
  let T := nameIdent "T"
  match_expr (← whnf e) with
  | Ty.prim p => ppPrim p
  | Ty.ref R => ppRef R
  | _ => `(sol_ty| $T:ident)
where
  ppPrim (p : Lean.Expr) : MetaM (TSyntax `sol_ty) := do
    if (← fvarName? p).isSome then return ← `(sol_ty| T)
    match_expr (← whnf p) with
    | PrimTy.uint => `(sol_ty| uint)
    | PrimTy.int => `(sol_ty| int)
    | PrimTy.bool => `(sol_ty| bool)
    | _ => `(sol_ty| T)
  ppRef (R : Lean.Expr) : MetaM (TSyntax `sol_ty) := do
    if (← instantiateMVars R).hasFVar then return ← `(sol_ty| T)
    match_expr (← whnf R) with
    | RefTy.struct s =>
      if (← fvarName? s).isSome then return ← `(sol_ty| T)
      let some s ← nameOf? s | `(sol_ty| T)
      `(sol_ty| $(nameIdent s):ident)
    | RefTy.array E => `(sol_ty| $(← ppTy E):sol_ty[])
    | RefTy.fixed E n =>
      let some n ← natOf? n | `(sol_ty| T)
      `(sol_ty| $(← ppTy E):sol_ty[$(Syntax.mkNumLit (toString n)):num])
    | RefTy.mapping K V => `(sol_ty| mapping($(← ppPrim K) => $(← ppTy V)))
    | _ => `(sol_ty| T)

/-- `l++`, `−−l` and the rest; `l⊕⊕` for a schema operator. -/
def ppIncDec (op : Lean.Expr) (l : TSyntax `sol_expr) : MetaM (Option (TSyntax `sol_stmt)) := do
  if (← fvarName? op).isSome then return some (← `(sol_stmt| $l:sol_expr ⊕⊕))
  match_expr (← whnf op) with
  | IncDec.postInc => return some (← `(sol_stmt| $l:sol_expr ++))
  | IncDec.preInc => return some (← `(sol_stmt| ++ $l:sol_expr))
  | IncDec.postDec => return some (← `(sol_stmt| $l:sol_expr −−))
  | IncDec.preDec => return some (← `(sol_stmt| −− $l:sol_expr))
  | _ => return none

/-! ### Terms -/

def escapeDl (e : Lean.Expr) : MetaM (TSyntax `dl_term) := do `(dl_term| ‹$(← escapeTerm e):term›)

/-- `p` where a member or an index follows it: `p[i]@S` in parentheses, since
its storage `S` would take the `.f` or `[j]` after it. -/
def recvTerm (b : TSyntax `dl_term) : MetaM (TSyntax `dl_term) :=
  match b with
  | `(dl_term| $_:dl_term[$_:dl_term]@$_:dl_term) => `(dl_term| ($b))
  | _ => pure b

/-- `p.f`, dotted when `p` is a name. -/
def dotTerm (b : TSyntax `dl_term) (f : String) : MetaM (TSyntax `dl_term) := do
  match b with
  | `(dl_term| $x:ident) => `(dl_term| $(mkIdent (x.getId.str f)):ident)
  | _ => `(dl_term| $(← recvTerm b) . $(nameIdent f):ident)

/-- The type a concrete allocation carries, which `dl!{ … }` needs to read
`addM(m, T)` and `newArr(T, n)` back: `Person`, `uint[]`, `Token[3]`.  A rule's
`R` gives none: the rule table writes `addM(m)`, the type being the
statement's. -/
partial def allocTy? (R : Lean.Expr) : MetaM (Option (TSyntax `dl_term)) := do
  let R ← instantiateMVars R
  if R.hasFVar then return none
  let elem (E : Lean.Expr) : MetaM (Option (TSyntax `dl_term)) := do
    match_expr (← whnf E) with
    | Ty.prim p =>
      let T? : Option String ← match_expr (← whnf p) with
        | PrimTy.uint => pure (some "uint")
        | PrimTy.int => pure (some "int")
        | PrimTy.bool => pure (some "bool")
        | _ => pure none
      let some T := T? | return none
      return some (← `(dl_term| $(nameIdent T):ident))
    | Ty.ref R' => allocTy? R'
    | _ => return none
  match_expr (← whnf R) with
  | RefTy.struct s =>
    let .lit (.strVal s) := (← whnf s).consumeMData | return none
    return some (← `(dl_term| $(nameIdent s):ident))
  | RefTy.array E =>
    let some E ← elem E | return none
    return some (← `(dl_term| $E:dl_term[]))
  | RefTy.fixed E n =>
    let some E ← elem E | return none
    let some n ← natOf? n | return none
    return some (← `(dl_term| $E:dl_term[$(Syntax.mkNumLit (toString n)):num]))
  | _ => return none

def mkBinTerm (sym : String) (a b : TSyntax `dl_term) : MetaM (TSyntax `dl_term) :=
  match sym with
  | "+" => `(dl_term| $a + $b) | "-" => `(dl_term| $a - $b) | "/" => `(dl_term| $a / $b)
  | "*" => `(dl_term| $a * $b) | "%" => `(dl_term| $a % $b)
  | "&&" => `(dl_term| $a && $b) | "||" => `(dl_term| $a || $b)
  | "==" => `(dl_term| ($a == $b))
  | "±" => `(dl_term| $a ± $b)
  | _ => `(dl_term| $a ⊕ $b)

/-- The term of `t ⊕ u` with a concrete operator: `+`, `-`, `*`, `/` have
term syntax at `uint`, `&&`, `||` at `bool` and `==` at any type (the types
they read back at: `ppTermS` escapes the others); the other operators escape
(`‹…›`). -/
def termOpSym? (op : Lean.Expr) : MetaM (Option String) := do
  if (← fvarName? op).isSome then return some "⊕"
  if op.isAppOfArity ``IncDec.binOp 1 then
    if (← fvarName? op.appArg!).isSome then return some "±"
  match_expr (← whnf op) with
  | BinOp.add => return "+"
  | BinOp.sub => return "-"
  | BinOp.div => return "/"
  | BinOp.mul => return "*"
  | BinOp.mod => return "%"
  | BinOp.and => return "&&"
  | BinOp.or => return "||"
  | BinOp.eqB => return "=="
  | _ => return none

/-- A variable of a term sort, by its name, where a term prints as it is
written (`tm{ … }`, `pp.sol.reduce false`, whose names are such variables). -/
def tmVar? (e : Lean.Expr) : MetaM (Option (TSyntax `dl_term)) := do
  if pp.sol.reduce.get (← getOptions) then return none
  let some n ← fvarName? e | return none
  return some (← `(dl_term| $(nameIdent n):ident))

/-- `p[i]`, KeY's `consr(p, at(i))`. -/
def elemTerm (p i : TSyntax `dl_term) : MetaM (TSyntax `dl_term) := do
  if ← keyOn then `(dl_term| consr($p, at($i))) else `(dl_term| $(← recvTerm p):dl_term[$i:dl_term])

/-- The push positions of the array `p`: its length as a path, as the value
read in `storage`, and the slot past the end — `p.length`, `p.length` and
`p[p.length]`, KeY's `consr(p, size)`, `find(storage, consr(p, size))` and
`consr(p, at(find(storage, consr(p, size))))`. -/
def lenTerms (p : TSyntax `dl_term) :
    MetaM (TSyntax `dl_term × TSyntax `dl_term × TSyntax `dl_term) := do
  if ← keyOn then
    let path ← `(dl_term| consr($p, size))
    let val ← `(dl_term| find(storage, $path))
    return (path, val, ← `(dl_term| consr($p, at($val))))
  let p ← recvTerm p
  let len ← match p with
    | `(dl_term| $x:ident) => `(dl_term| $(mkIdent (x.getId.str "length")):ident)
    | _ => `(dl_term| $p . $(nameIdent "length"):ident)
  return (len, len, ← `(dl_term| $p[$len]))

/-! ### Updates and formulas -/

/-- A quantifier's type, as the specification writes it. -/
def primName? (p : Lean.Expr) : MetaM (Option String) := do
  match_expr (← whnf p) with
  | PrimTy.uint => return "uint"
  | PrimTy.int => return "int"
  | PrimTy.bool => return "bool"
  | _ => return none

/-- A formula that is a Lean variable, or the coercion of one (`↑φ` for
`φ : Post C`, `Chains.lean`): its name, which reads back as `‹φ›` does.  Not
an inaccessible one (`φ✝`): its bare name would read back as another variable,
so it stays `‹φ✝›`. -/
def fmlVar? (e : Lean.Expr) : MetaM (Option Ident) := do
  let e := (← instantiateMVars e).consumeMData
  let x ← match e.getAppFn with
    | .const f _ => match ← getCoeFnInfo? f with
      | some i => pure (if e.getAppNumArgs == i.numArgs then e.getArg! i.coercee else e)
      | none => pure e
    | _ => pure e
  let .fvar fv := x.consumeMData | return none
  let n : Lean.Name ← fv.getUserName
  if n.hasMacroScopes || n.isInaccessibleUserName then return none
  return (← fvarName? x).map nameIdent

/-! ### The delaborators

Each stands aside (`failure`, and Lean prints the term its own way) when all
it would print is one `‹…›`, and `⊨`, `⊧` when it is a name: `⊨ φ`. -/

/-- Printed as `‹…›` as a whole. -/
def isEscape (s : Syntax) : Bool := s[0].isToken "‹"

/-- Only a full application: `Fml.modal m P` alone is a function. -/
def fullApp : DelabM Unit := do
  let e ← getExpr
  let some c := e.getAppFn.constName? | failure
  let info ← getConstInfoCtor c
  guard (e.getAppNumArgs == info.numParams + info.numFields)

/-- Whether `e` has at most `n` nodes (shared ones counted each time). -/
partial def sizeAtMost (n : Nat) (e : Lean.Expr) : Bool :=
  (go e n).isSome
where
  /-- The fuel left once `e` is counted, if any is. -/
  go (e : Lean.Expr) (fuel : Nat) : Option Nat := do
    if fuel == 0 then none
    match e with
    | .app f a => go a (← go f (fuel - 1))
    | .mdata _ b => go b fuel
    | .lam _ t b _ | .forallE _ t b _ => go b (← go t (fuel - 1))
    | .letE _ t v b _ => go b (← go v (← go t (fuel - 1)))
    | .proj _ _ b => go b (fuel - 1)
    | _ => some (fuel - 1)

/-- The largest term `tm{ … }` prints; a larger one prints as Lean prints it. -/
def tmCutoff : Nat := 2000

end Print

end Solidity
