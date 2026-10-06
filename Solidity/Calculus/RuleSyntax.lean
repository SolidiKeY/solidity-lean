import Solidity.Update

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
| `dl_schema{ φ }` | a formula whose names are Lean variables (schema variables) |
| `dl{ ⟨[ s; ]⟩ ⇝ p }` | the taclet `Taclet C k m s p`, for either modality (solkey's `#mod`) |
| `dl{ [ s; ] ⇝ p }`, `dl{ ⟨ s; ⟩ ⇝ p }` | a taclet for the box only, the diamond only |
| `dl[LeanTaclet C k]{ ⟨ s; ⟩ ⇝ p }` | a rule of another judgement, `LeanTaclet C k .diamond s p` |
| `dl{ p }` | a premise |
| `dl{ ..Γ, c, {U} ⟹[R] ⟨[ s; ..ω ]⟩ φ }` | the sequent `Proves R (Γ ++ [.pre c] ++ [.upd m U]) (.modal m (s :: ω) φ)` |
| `dl{ ..Γ, {U} [ ] ⟹ᶜ[I] [ s; ..ω ] φ }` | an update produced under the box; the sequent `ProvesC I Γ φ` with callbacks |
| `tm{ find(save(s, p, v), q) }` | a term (`Tm`), every name a Lean variable |
| `⊨ φ` | `Valid φ` |
| `σ ⊧ φ` | `holds σ φ` |

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
| `v`, `lv`, `vp`, `pv` | a stack local (`pv`: where a send's outcome lands) | `Var` | |
| `lsv` | a storage alias | `Var` | |
| `mv` | a memory local | `Var` | |
| `pmv`, `rmv` | a memory local, an array of primitives, of references (`delete pmv[ie]` fixes the element type) | `Var` | |
| `gsp` | a state variable, with its proof `hgsp` | `Name` | |
| `se`, `ie`, `sadr` | a simple value | `Simple C p` | |
| `e` | a value | `Val C p` | not a conditional, when written to storage or to a memory target |
| `nse`, `nadr` | a value that is not simple | `Val C p` | not simple (and as `e`) |
| `sp`, `map`, `arr` | a simple storage path (`map`/`arr` fix how it is indexed) | `SPath C T` | simple |
| `parr`, `rarr` | a simple path to an array of primitives, of references | `SPath C T` | simple; the element primitive (`SPath.elemPrim`), or not |
| `marr`, `darr` | a simple path to an array of mappings, of anything else | `SPath C T` | simple; the element a mapping (`SPath.elemMapping`), or not |
| `nsp` | a storage path that is not simple | `SPath C T` | not simple |
| `path` | any storage path | `SPath C T` | |
| `nmp` | a memory path that is not a memory local | `MPath C T` | not simple |
| `mpath` | a memory path | `MPath C T` | bindable, when written as a reference into a target |
| `fld`, `fr`, with its proof `hfld`, `hfr` | a member name | `Name` | |
| `pfld`, `rfld` | a member of primitive, of reference type (`delete mv.pfld` fixes it) | `Name` | |
| `tgt` | where a fresh array lands (`NewLhs`) | | |
| `lhs` | where a storage or memory read lands (`Hole`, `MHole`) | | a target |
| `x` | where a value lands (`VHole`) | | |
| `loc`, `nlhs` | a member or entry a copy lands in | `Loc C T` | `loc`: a target, not a state variable |
| `l` | the target of `⊕=` and `++` | `OpLoc C p` | |
| `s`; `P`, `Q`, `ω` | a statement; a program, spliced in place (`P; ..ω` is `P ++ ω`) | `Stmt C`; `Prog C` | |
| `fbs` | a call with its body and its targets (KeY's `FunctionBody`), `expand_function_body(fbs)` its statements | `Stmt.call f args hsep ret body` | its arguments simple; it returns to targets (`CallRet.isRets`) |
| `ic` | any other call with its body (KeY's `InternalCall`), `expand_function_body(ic)` its statements | `Stmt.call f args hsep ret body` | its arguments simple; no targets |
| `call`, `rets`, `code`; `body`, `errorBody`, `panicBody`, `otherBody` | a `try`'s call, its return locals, its `Panic` code; its blocks | `ExtCall C`, …; `List (Stmt C)` | |

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
/-- `at(r)`: the ledger's key for the address `r` (`net := store(net, at(r), …)`). -/
syntax:max "at" noWs "(" dl_term ")" : dl_term
/-- `if(r = this) then net else …`: KeY's `\if … \then … \else`, the form of a
payment's booking (`UpdElem.pay`), and read only there. -/
syntax:max "if" noWs "(" dl_term " = " dl_term ")" " then " dl_term " else " dl_term : dl_term
syntax:max "(" dl_term ")" : dl_term
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
/-- `u`: an update schema variable, its elements in place (KeY's `{u}`). -/
syntax ident : dl_upd_elem
/-- `{u}u2`: the update `u2` with `u` applied to its right-hand sides
(`Upd.subst`), KeY's `{u}u2` in `{u ‖ {u}u2}`. -/
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
not otherwise written (`copyDecls`). -/
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
syntax "⟨" "[ " (sol_stmt "; ")* "]" "⟩" : dl_premise
syntax (str ": ")? dl_fml " ⟹ " "⟨" "[ " sol_block " ]" "⟩" " ; "
  (str ": ")? dl_fml " ⟹ " "⟨" "[ " sol_block " ]" "⟩" : dl_premise
syntax (str ": ")? dl_fml " ⟹ " "⟨" "[ " (sol_stmt "; ")* "]" "⟩" " ; "
  (str ": ")? dl_fml " ⟹ " "⟨" "[ " (sol_stmt "; ")* "]" "⟩" : dl_premise
syntax (str ": ")? dl_fml " ⟹ " "⟨" "[ " (sol_stmt "; ")* "]" "⟩" " ; " (str ": ")? dl_fml :
  dl_premise
syntax &"true" : dl_premise
syntax &"false" : dl_premise
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
syntax dl_fml : dl_hyp
/-- `∀ T x`: the local `x` holds any value of `T` (`Hyp.all`), KeY's skolem
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

/-- A formula whose names are Lean variables. -/
syntax "dl_schema{ " dl_fml " }" : term
/-- A formula, as the printers show one. -/
syntax (priority := high) "dl{ " dl_fml " }" : term
/-- A sequent `Γ ⟹ φ`. -/
syntax "dl{ " sepBy(dl_hyp, ", ") " ⟹ " dl_fml " }" : term
/-- A sequent `Γ ⟹ₖ φ`, to be proved with solkey's rules alone (`⊢ₖ`). -/
syntax "dl{ " sepBy(dl_hyp, ", ") " ⟹ₖ " dl_fml " }" : term
/-- A sequent `Γ ⟹[R] φ` over the rule set `R` (`Proves R Γ φ`). -/
syntax "dl{ " sepBy(dl_hyp, ", ") " ⟹[" term "] " dl_fml " }" : term
/-- A sequent `Γ ⟹ᶜ[I] φ` of the calculus with callbacks, every `transfer`
calling back into a contract with the invariant `I` (`ProvesC I Γ φ`,
`Calculus/Callback.lean`). -/
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
syntax:25 "⊨ " term:26 : term
/-- `σ ⊧ φ`: the formula `φ` holds in the state `σ`. -/
syntax:50 term:51 " ⊧ " term:51 : term
/-- A statement standing alone, as the printers show one. -/
syntax "stmt{ " sol_stmt "; " "}" : term

macro_rules
  | `(⊨ $φ:term) => `(Solidity.Valid $φ)
  | `($σ:term ⊧ $φ:term) => `(Solidity.holds $σ $φ)

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
  | mem (x : Lean.Term)
  /-- The mark of `tm{ … }`: every name is a Lean variable of a term sort. -/
  | raw

abbrev Scope := List (String × Decl)

/-- The scope of `tm{ … }`, whose names carry no kind. -/
def rawScope : Scope := [("‹raw›", .raw)]

/-- Whether names are read without their kinds (`tm{ … }`). -/
def Scope.isRaw (Γ : Scope) : Bool := Γ.any (·.1 == "‹raw›")

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
  | local (x : Lean.Term) | alias (x : Lean.Term) | mem (x : Lean.Term)
  | root (x h : Lean.Term) | simple (x : Lean.Term) | val (x : Lean.Term)
  | spath (x : Lean.Term) | mpath (x : Lean.Term) | loc (x : Lean.Term) | mloc (x : Lean.Term)
  | other (x : Lean.Term)

def headOf (Γ : Scope) (x : Ident) : Head :=
  let s := x.getId.toString
  match Γ.lookup s with
  | some (.val v) => .local v
  | some (.alias v) => .alias v
  | some (.mem v) => .mem v
  | some .raw => .other x
  | none => if Γ.isRaw then .other x else match stemOf s with
    | "v" | "lv" | "vp" | "pv" => .local x
    | "lsv" => .alias x
    | "mv" | "pmv" | "rmv" => .mem x
    | "gsp" => .root x (proofIdent x s)
    | "se" | "ie" | "sadr" => .simple x
    | "e" | "nse" | "nadr" => .val x
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
  | .mem v => match pos with
    | .mpath => `(MPath.var $v)
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

/-- Whether an expression is a memory path: its head is a memory local or a
memory path variable. -/
partial def isMem (Γ : Scope) : TSyntax `sol_expr → Bool
  | `(sol_expr| $x:ident) =>
    match nameParts x.getId with
    | h :: _ => match headOf Γ (mkIdent (Name.mkSimple h)) with
      | .mem _ | .mpath _ | .mloc _ => true
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
        | .mem _ | .mpath _ | .mloc _ => true
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
  | _ => Macro.throwErrorAt x "a taclet declares only fresh `se`, `sp`, `ie` or `mv`"

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
def isProgStem (s : String) : Bool := ["P", "Q", "ω"].contains (stemOf s)

/-- Whether `s` names a call with its body: `fbs` (KeY's `FunctionBody`) or
`ic` (`InternalCall`). -/
def isCallStem (s : String) : Bool := ["fbs", "ic"].contains (stemOf s)

/-- `fbs`, `ic`, a call with its body: `Stmt.call f args hsep ret body`, its
parts the taclet's schema variables. -/
def fbsCall : MacroM Lean.Term :=
  `(Stmt.call $(schemaIdent "f") $(schemaIdent "args") $(schemaIdent "hsep") $(schemaIdent "ret")
      $(schemaIdent "body"))

/-- The program of `items` in front of `tail`: `[s₁, …, sₙ]` when every item
is one statement and there is no tail (with the type ascribed if `ascribe`),
else the items consed and appended onto it, `s :: P ++ ω` (right-nested, as
`s :: ω` is written). -/
def progTerm (ascribe : Bool) (items : Array Item) (tail : Option Lean.Term) :
    MacroM Lean.Term := do
  let ones := items.filterMap fun | .one t => some t | .many _ => none
  if tail.isNone && ones.size == items.size then
    return ← if ascribe then `(([$ones,*] : List (Stmt _))) else `([$ones,*])
  let mut acc : Option Lean.Term := tail
  for it in items.reverse do
    acc ← match it, acc with
      | .one s, none => some <$> `([$s])
      | .one s, some r => some <$> `($s :: $r)
      | .many P, none => pure (some P)
      | .many P, some r => some <$> `($P ++ $r)
  match acc with
  | some t => pure t
  | none => `([])

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
    let some (.alias x) := lhsHead Γ l | Macro.throwErrorAt l "`= b.push()` binds a storage alias"
    return (← `(Stmt.rebind (R := $(schemaIdent "R")) $x (ARhs.push $(← schemaAt Γ .spath b) $(schemaIdent "hd"))), Γ)
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
  | `(sol_stmt| $l:sol_expr ⊕⊕) => do
    return (← `(Stmt.incDec (p := $(schemaIdent "p")) $(schemaIdent "op") $(schemaIdent "hp")
      $(← schemaAt Γ .oploc l)), Γ)
  | `(sol_stmt| $l:sol_expr ⊕= $r:sol_expr) => do
    return (← `(Stmt.opAssign (p := $(schemaIdent "p")) $(schemaIdent "op") $(schemaIdent "hop") $(schemaIdent "hp")
      $(← schemaAt Γ .oploc l) $(← schemaAt Γ .val r)), Γ)
  | `(sol_stmt| $l:sol_expr = $r:sol_expr) => do
    let R := schemaIdent "R"
    if let some n := newRhs? r then
      let n ← schemaAt Γ .simple n
      match lhsHead Γ l, stemOfExpr? l with
      | some (.mem x), _ =>
        return (← `(Stmt.rebindMem (R := $R) $x (MRhs.newArr (R := $R) $n $(schemaIdent "hn"))), Γ)
      | _, some "tgt" =>
        let `(sol_expr| $x:ident) := l | Macro.throwErrorAt l "a `tgt`"
        return (← `(Stmt.assignNew (R := $R) $x $n $(schemaIdent "hn")), Γ)
      | _, _ => Macro.throwErrorAt l "`new` lands in a memory local or a `tgt`"
    if stemOfExpr? l == some "tgt" then
      let `(sol_expr| $x:ident) := l | Macro.throwErrorAt l "a `tgt`"
      return (← `($(mkIdent `Solidity.NewLhs.fill) $x $(← schemaAt Γ .mpath r)), Γ)
    let t ← match lhsHead Γ l with
      | some (.local v) => `(Stmt.assignLocal $v $(← schemaAt Γ .val r))
      | some (.alias x) =>
        match rhsVar? "rhs" r with
        | some v => `(Stmt.rebind $x $v)
        | none => `(Stmt.rebind $x (ARhs.path $(← schemaAt Γ .spath r)))
      | some (.mem x) =>
        if let some v := rhsVar? "mrhs" r then `(Stmt.rebindMem $x $v) else
        if isMem Γ r then `(Stmt.rebindMem $x (MRhs.alias $(← schemaAt Γ .mpath r)))
        else `(Stmt.rebindMem $x (MRhs.copy $(← schemaAt Γ .spath r) $(schemaIdent "hm")))
      | some (.other h) =>
        match h with
        | `($x:ident) =>
          match stemOf x.getId.toString with
          | "lhs" =>
            if isMem Γ r then `($(mkIdent `Solidity.MHole.fill) $x $(← schemaAt Γ .mloc r))
            else if isPath Γ r then `($(mkIdent `Solidity.Hole.fill) $x $(← schemaAt Γ .spath r))
            else `($(mkIdent `Solidity.VHole.fill) $x $(← schemaAt Γ .val r))
          | _ => Macro.throwErrorAt l "not a left-hand side"
        | _ => Macro.throwErrorAt l "not a left-hand side"
      | _ =>
        if isMem Γ l then
          if let some v := rhsVar? "msrc" r then `(Stmt.assignMem $(← schemaAt Γ .mloc l) $v) else
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
        else if let some v := rhsVar? "src" r then `(Stmt.assign $(← schemaAt Γ .loc l) $v)
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
    let r : Lean.Term ← match rhsVar? "rhs" e with
      | some r => pure ⟨r.raw⟩
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
    let r : Lean.Term ← if let some r := rhsVar? "mrhs" e then pure ⟨r.raw⟩
      else if let some n := newRhs? e then
        `(MRhs.newArr (R := $(schemaIdent "R")) $(← schemaAt Γ .simple n) $(schemaIdent "hn"))
      else if isMem Γ e then `(MRhs.alias $(← schemaAt Γ .mpath e))
      else `(MRhs.copy $(← schemaAt Γ .spath e) $(schemaIdent "hm"))
    let t ← `(Stmt.declMem _ $v (some $r) rfl)
    return (t, (x.getId.toString, .mem v) :: Γ)
  | `(sol_stmt| $T:sol_ty memory $x:ident) => do
    let v ← declVar fresh x
    let _ := T
    let t ← `(Stmt.declMem $(schemaIdent "R") $v none $(schemaIdent "hd"))
    return (t, (x.getId.toString, .mem v) :: Γ)
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
    let v : Lean.Term ← if let some r := rhsVar? "src" a then pure ⟨r.raw⟩ else if isPath Γ a then `(Src.copy $(← schemaAt Γ .spath a) $(schemaIdent "hm"))
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
  | stx => do
    let k := stx.raw.getKind
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
    if k == Lean.choiceKind then
      let alts := stx.raw.getArgs
      for alt in alts.filter (·[0].isAtom) ++ alts do
        try return ← schemaStmt fresh Γ ⟨alt⟩ catch _ => pure ()
    Macro.throwUnsupported

/-- A statement of a program: one statement, or a program in its place — a
program schema variable (`P`), `expand_function_body(fbs)` (KeY's, the
statements a call runs: `Stmt.expandBody`; `expand_function_body(ic)`
alike). -/
partial def schemaItem (fresh : Bool) (Γ : Scope) (s : TSyntax `sol_stmt) :
    MacroM (Item × Scope) := do
  match s with
  | `(sol_stmt| $x:ident) =>
    if isProgStem x.getId.toString then return (.many x, Γ)
  | `(sol_stmt| $f:sol_expr ( $a:sol_expr )) =>
    if let `(sol_expr| $g:ident) := f then
      if g.getId.toString == "expand_function_body" then
        unless (stemOfExpr? a).any isCallStem do
          Macro.throwErrorAt a "`expand_function_body(fbs)`, of the call `fbs` (or `ic`)"
        return (.many (← `(Stmt.expandBody $(schemaIdent "args") $(schemaIdent "ret")
          $(schemaIdent "body"))), Γ)
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
    progTerm true ts none
  | `(sol_block| $x:ident) => pure x
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
  if (n == "true" || n == "false") && pos == .val then
    return ← `(Term.lit (.bool $(mkIdent (Name.mkSimple n))))
  if n == "storage" && pos == .storage then return ← `(STerm.storage)
  if n == "memory" && pos == .memory then return ← `(MTerm.memory)
  if n == "selfBalance" && pos == .val then return ← `(Term.env EnvKey.selfBalance)
  if (n == "this" || n == "self") && pos == .val then return ← `(Term.env EnvKey.selfAddress)
  match headOf Γ x, pos with
  | .local v, .val => `(Term.pv $v)
  | .local v, .svalue => `(SValT.val (Term.pv $v))
  | .local v, .mvalue => `(MValT.val (Term.pv $v))
  | .alias v, .path => `(PTerm.pv $v)
  | .mem v, .ident => `(ITerm.pv $v)
  | .mem v, .mvalue => `(MValT.ref (ITerm.pv $v))
  | .root r _, .val => `(Term.find STerm.storage (PTerm.root $r))
  | .root r _, .path => `(PTerm.root $r)
  | .simple s, .val => `(Simple.lower $s)
  | .simple s, .svalue => `(SValT.val (Simple.lower $s))
  | .simple s, .mvalue => `(MValT.val (Simple.lower $s))
  | .val e, .val => `(Val.lower $e)
  | .spath p, .path => `(SPath.lower $p)
  | .mpath p, .ident => `(MPath.lower $p)
  | .mpath p, .mvalue => `(MValT.ref (MPath.lower $p))
  | .loc l, .path => `(Loc.lower $l)
  | .other o, _ => pure o
  | _, _ => tposError x s!"`{n}`" pos

/-- `mv.f₁.….fₙ` at a term sort: the inner members are identities read. -/
def memMember (pos : TPos) (stx : Lean.Syntax) : Lean.Term → List Ident → MacroM Lean.Term
  | b, [] => pure b
  | b, [f] =>
    if f.getId.toString == "length" && pos == .val then `(Term.mlen MTerm.memory $b) else
    match pos with
    | .addr => `(MAddr.field $b $f)
    | .val => `(Term.read MTerm.memory (MAddr.field $b $f))
    | .ident => `(ITerm.read MTerm.memory (MAddr.field $b $f))
    | .mvalue => `(MValT.ref (ITerm.read MTerm.memory (MAddr.field $b $f)))
    | _ => tposError stx "a memory member" pos
  | b, f :: fs => do memMember pos stx (← `(ITerm.read MTerm.memory (MAddr.field $b $f))) fs

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
    | `(dl_term| $f:ident($_,*)) =>
      if ["find", "copyMem", "newArr"].contains f.getId.toString then schemaTerm0 Γ .svalue t
      else `(SValT.val $(← schemaTerm0 Γ .val t))
    | _ => `(SValT.val $(← schemaTerm0 Γ .val t))
  | .mvalue =>
    let memHead := match t with
      | `(dl_term| $x:ident) => match nameParts x.getId with
        | [h] => match headOf Γ (mkIdent (Name.mkSimple h)) with
          | .mem _ | .mpath _ => true
          | _ => false
        | _ => false
      | `(dl_term| $f:ident($_,*)) => f.getId.toString == "freshId"
      | _ => false
    if memHead then `(MValT.ref $(← schemaTerm0 Γ .ident t))
    else `(MValT.val $(← schemaTerm0 Γ .val t))
  | _ => schemaTerm0 Γ pos t

partial def schemaTerm0 (Γ : Scope) (pos : TPos) : TSyntax `dl_term → MacroM Lean.Term
  | stx@`(dl_term| $n:num) =>
    match pos with
    | .val => `(Term.lit (.int $n))
    | .svalue => `(SValT.val (Term.lit (.int $n)))
    | .mvalue => `(MValT.val (Term.lit (.int $n)))
    | _ => tposError stx "a number" pos
  | stx@`(dl_term| $x:ident) => do
    match nameParts x.getId with
    | [] => Macro.throwError "empty identifier"
    | [_] => headTerm Γ pos x
    | h :: fs =>
      -- `sp.fld`: a path, or (at a memory sort) a member of a memory object
      let hx := partIdent x h
      match headOf Γ hx with
      | .mem _ | .mpath _ =>
        memMember pos stx (← headTerm Γ .ident hx) (fs.map (partIdent x))
      | _ =>
        if fs.getLast? == some "length" then
          let p' ← (fs.dropLast).foldlM (init := ← headTerm Γ .path hx) fun acc f =>
            `(PTerm.field $acc $(partIdent x f))
          match pos with
          | .val => `(Term.len STerm.storage $p')
          | _ => tposError stx "a length" pos
        else
        let p ← fs.foldlM (init := ← headTerm Γ .path hx) fun acc f =>
          `(PTerm.field $acc $(partIdent x f))
        match pos with
        | .path => pure p
        | .val => `(Term.find STerm.storage $p)
        | .svalue => `(SValT.find STerm.storage $p)
        | _ => tposError stx "a storage path" pos
  | stx@`(dl_term| $t:dl_term . $f:ident) => do
    let p ← (nameParts f.getId).foldlM (init := ← schemaTerm Γ .path t) fun acc c =>
      `(PTerm.field $acc $(partIdent f c))
    match pos with
    | .path => pure p
    | _ => tposError stx "a member" pos
  | stx@`(dl_term| $t:dl_term [ $i:dl_term ]) => do
    let mem := match t with
      | `(dl_term| $x:ident) => match nameParts x.getId with
        | h :: _ => match headOf Γ (mkIdent (Name.mkSimple h)) with
          | .mem _ | .mpath _ => true
          | _ => false
        | [] => false
      | _ => false
    if mem then
      let a ← `(MAddr.at $(← schemaTerm Γ .ident t) $(← schemaTerm Γ .val i))
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
        else `(PTerm.at $(← schemaTerm Γ .path t) $(← schemaTerm Γ .val i))
      match pos with
      | .path => pure p
      | .val => `(Term.find STerm.storage $p)
      | .svalue => `(SValT.find STerm.storage $p)
      | _ => tposError stx "an entry" pos
  | `(dl_term| $a:dl_term ⊕ $b:dl_term) => do
    `(Term.binop $(schemaIdent "op") $(schemaIdent "p") $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| ⊖ $a:dl_term) => do
    `(Term.unop $(schemaIdent "op") $(schemaIdent "p") $(← schemaTerm Γ .val a))
  | `(dl_term| $a:dl_term ± $b:dl_term) => do
    `(Term.binop (IncDec.binOp $(schemaIdent "op")) $(schemaIdent "p")
        $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| $a:dl_term ⊕⊕) => do
    `(Term.bumped $(schemaIdent "op") $(schemaIdent "p") $(← schemaTerm Γ .val a))
  | `(dl_term| $a:dl_term + $b:dl_term) => do
    `(Term.binop BinOp.add PrimTy.uint $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| $a:dl_term - $b:dl_term) => do
    `(Term.binop BinOp.sub PrimTy.uint $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
  | `(dl_term| $a:dl_term / $b:dl_term) => do
    `(Term.binop BinOp.div PrimTy.uint $(← schemaTerm Γ .val a) $(← schemaTerm Γ .val b))
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
      | `(dl_term| at($k)) => `(MAddr.at $(← schemaTerm Γ .ident i) $(← schemaTerm Γ .val k))
      | `(dl_term| $g:ident) => `(MAddr.field $(← schemaTerm Γ .ident i) $g)
      | _ => tposError a "a member `f` or an element `at(k)`" .addr
    match f.getId.toString, args, pos with
    | "select", #[s, r], .val => `(Term.find $(← st s) $(← pa r))
    | "select", #[s, r], .storage | "selectSt", #[s, r], .storage =>
      let `(dl_term| $r:ident) := r | tposError r "a member name" .storage
      `(STerm.select $(← st s) $r)
    | "net", #[a], .val => `(Term.net $(← schemaTerm Γ .val a))
    | "selectSt", #[n, a], .val =>
      let `(dl_term| net) := n | tposError n "`net`" .val
      let `(dl_term| at($a)) := a | tposError a "`at(a)`" .val
      `(Term.net $(← schemaTerm Γ .val a))
    | "find", #[s, p], .val =>
      match ← lengthBase? p with
      | some b => `(Term.len $(← st s) $(← pa b))
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
        if past then `(PTerm.next $(← pa p)) else `(PTerm.at $(← pa p) $(← schemaTerm Γ .val i))
      | `(dl_term| atMap($i)) => `(PTerm.at $(← pa p) $(← schemaTerm Γ .val i))
      | `(dl_term| $g:ident) =>
        if g.getId.toString == "size" then tposError f "`consr(p, size)` outside `find`" .path
        else `(PTerm.field $(← pa p) $g)
      | _ => tposError f "a member, `at(i)` or `atMap(i)`" .path
    | "read", #[m, a], .val => `(Term.read $(← me m) $(← schemaTerm Γ .addr a))
    | "read", #[m, a], .ident => `(ITerm.read $(← me m) $(← schemaTerm Γ .addr a))
    | "read", #[m, i, a], .val =>
      if let `(dl_term| $g:ident) := a then
        if g.getId.toString == "size" then
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
        | `(dl_term| delAt($s', $q)), `(dl_term| $_ + 1) =>
          if elem q then return ← `(STerm.pushSlot $(← st s') $(← pa b) $(schemaIdent "E"))
        | `(dl_term| delAt($s', $q)), `(dl_term| $_ - 1) =>
          if elem q then return ← `(STerm.pop $(← st s') $(← pa b))
        | _, _ => pure ()
        match v with
        | `(dl_term| $_ + 1) =>
          -- a bare `rarr.push()` extends at its element type `E`, an alias's
          -- `lsv = sp.push()` at the alias's `R`
          let bare := match b with
            | `(dl_term| $x:ident) => stemOf x.getId.toString == "rarr"
            | _ => false
          if bare then `(STerm.extend $(← st s) $(← pa b) $(schemaIdent "E"))
          else `(STerm.extend $(← st s) $(← pa b) (Ty.ref $(schemaIdent "R")))
        | `(dl_term| $_ - 1) => `(STerm.shrink $(← st s) $(← pa b))
        | _ => `(STerm.save $(← st s) $(← pa p) $(← schemaTerm Γ .svalue v))
      | none => `(STerm.save $(← st s) $(← pa p) $(← schemaTerm Γ .svalue v))
    | "delAt", #[s, p], .storage => `(STerm.delAt $(← st s) $(← pa p))
    | "defVal", #[_], .val => `(Term.lit (PrimTy.default $(schemaIdent "p")))
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

/-- One elementary update: the sort of `x := t` is read off `x`. -/
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
    match headOf Γ x with
    | .local v => `(UpdElem.val $v $(← schemaTerm Γ .val r))
    | .alias v => `(UpdElem.path $v $(← schemaTerm Γ .path r))
    | .mem v => `(UpdElem.mref $v $(← schemaTerm Γ .ident r))
    | _ => Macro.throwErrorAt x "an update assigns a local, an alias, a memory local, \
        `storage` or `memory`"
  | _ => Macro.throwUnsupported

/-- An update schema variable among the elements: `u` (its elements), or
`{u}u2` (`u2` with `u` applied, `Upd.subst`). -/
def updVar? : TSyntax `dl_upd_elem → MacroM (Option Lean.Term)
  | `(dl_upd_elem| $u:ident) => pure (some u)
  | `(dl_upd_elem| { $u:ident } $v:ident) => some <$> `($(mkIdent `Solidity.Upd.subst) $v $u)
  | _ => pure none

/-- Whether an update has a schema variable among its elements: the formula
under it is then judged under the schema's modality `m`. -/
def hasUpdVar (U : TSyntax `dl_upd) : Bool :=
  match U with
  | `(dl_upd| ‹ $_:term ›) => false
  | _ => U.raw[1].getSepArgs.any fun e => match (⟨e⟩ : TSyntax `dl_upd_elem) with
    | `(dl_upd_elem| $_:ident) => true
    | `(dl_upd_elem| { $_:ident } $_:ident) => true
    | _ => false

def schemaUpd (Γ : Scope) (U : TSyntax `dl_upd) : MacroM Lean.Term := do
  if let `(dl_upd| ‹ $t:term ›) := U then return t
  -- the elements, read off the `sepBy1` node: `‖` does not splice in a pattern
  let mut segs : Array Lean.Term := #[]
  let mut run : Array Lean.Term := #[]
  for e in U.raw[1].getSepArgs do
    match ← updVar? ⟨e⟩ with
    | some u =>
      unless run.isEmpty do segs := segs.push (← `([$run,*]))
      run := #[]
      segs := segs.push u
    | none => run := run.push (← schemaUpdElem Γ ⟨e⟩)
  -- no schema variable: the list of the elements, as ever
  if segs.isEmpty then return ← `(([$run,*] : Upd _))
  unless run.isEmpty do segs := segs.push (← `([$run,*]))
  -- the parts appended, left-nested as `u ++ u2.subst u` is written
  segs[1:].foldlM (init := segs[0]!) fun acc t => `($acc ++ $t)

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

partial def schemaFml : TSyntax `dl_fml → MacroM Lean.Term
  | `(dl_fml| true) => `(Fml.tt)
  | `(dl_fml| false) => `(Fml.not Fml.tt)
  | `(dl_fml| $a:dl_term = $b:dl_term) | `(dl_fml| $a:dl_term ≐ $b:dl_term) => do
    `(Fml.eq $(← schemaTerm [] .val a) $(← schemaTerm [] .val b))
  | `(dl_fml| defined( $t:dl_term )) => do `(Fml.defined $(← schemaTerm [] .val t))
  | `(dl_fml| ¬ $φ:dl_fml) => do `(Fml.not $(← schemaFml φ))
  | `(dl_fml| $φ:dl_fml ∧ $ψ:dl_fml) | `(dl_fml| $φ:dl_fml && $ψ:dl_fml) => do
    `(Fml.and $(← schemaFml φ) $(← schemaFml ψ))
  | `(dl_fml| $φ:dl_fml → $ψ:dl_fml) => do `(Fml.imp $(← schemaFml φ) $(← schemaFml ψ))
  | `(dl_fml| $φ:dl_fml ∨ $ψ:dl_fml) => do
    `(Fml.not (Fml.and (Fml.not $(← schemaFml φ)) (Fml.not $(← schemaFml ψ))))
  | `(dl_fml| $φ:dl_fml ↔ $ψ:dl_fml) => do
    let φ ← schemaFml φ
    let ψ ← schemaFml ψ
    `(Fml.and (Fml.imp $φ $ψ) (Fml.imp $ψ $φ))
  | `(dl_fml| { havoc } $φ:dl_fml) => do `(Fml.havoc $(← schemaFml φ))
  | `(dl_fml| $U:dl_upd $φ:dl_fml) => do
    -- an update schema variable is judged under the schema's modality
    let m ← match ← fmlModality? (schemaIdent "m") φ with
      | some m => pure m
      | none => if hasUpdVar U then pure (schemaIdent "m") else `(Modality.diamond)
    `(Fml.upd $m $(← schemaUpd [] U) $(← schemaFml φ))
  | `(dl_fml| ⟨ $[$ss:sol_stmt;]* ⟩ $φ:dl_fml) => do
    let (ts, _) ← schemaProg false [] ss
    `(Fml.modal .diamond $(← progTerm false ts none) $(← schemaFml φ))
  | `(dl_fml| [ $[$ss:sol_stmt;]* ] $φ:dl_fml) => do
    let (ts, _) ← schemaProg false [] ss
    `(Fml.modal .box $(← progTerm false ts none) $(← schemaFml φ))
  | `(dl_fml| ⟨[ $[$ss:sol_stmt;]* ]⟩ $φ:dl_fml) => do
    let (ts, _) ← schemaProg false [] ss
    `(Fml.modal $(schemaIdent "m") $(← progTerm false ts none) $(← schemaFml φ))
  | `(dl_fml| ⟨[ $[$ss:sol_stmt;]* .. $ω:term ]⟩ $φ:dl_fml) => do
    let (ts, _) ← schemaProg false [] ss
    `(Fml.modal $(schemaIdent "m") $(← progTerm false ts (some ω)) $(← schemaFml φ))
  | `(dl_fml| ⟨ $[$ss:sol_stmt;]* .. $ω:term ⟩ $φ:dl_fml) => do
    let (ts, _) ← schemaProg false [] ss
    `(Fml.modal .diamond $(← progTerm false ts (some ω)) $(← schemaFml φ))
  | `(dl_fml| [ $[$ss:sol_stmt;]* .. $ω:term ] $φ:dl_fml) => do
    let (ts, _) ← schemaProg false [] ss
    `(Fml.modal .box $(← progTerm false ts (some ω)) $(← schemaFml φ))
  | `(dl_fml| ⟨[ $b:sol_block ]⟩ $φ:dl_fml) => do
    `(Fml.modal $(schemaIdent "m") $(← schemaBlock false [] b) $(← schemaFml φ))
  | `(dl_fml| ⟨ $b:sol_block ⟩ $φ:dl_fml) => do
    `(Fml.modal .diamond $(← schemaBlock false [] b) $(← schemaFml φ))
  | `(dl_fml| [ $b:sol_block ] $φ:dl_fml) => do
    `(Fml.modal .box $(← schemaBlock false [] b) $(← schemaFml φ))
  | `(dl_fml| ( $φ:dl_fml )) => schemaFml φ
  | `(dl_fml| ‹ $t:term ›) => pure t
  | `(dl_fml| $x:ident) => pure x
  | stx@`(dl_fml| $_:dl_term == $_:dl_term) | stx@`(dl_fml| $_:dl_term != $_:dl_term) =>
    Macro.throwErrorAt stx "a program comparison is read against a contract: write `dl{ … }`"
  | `(dl_fml| $a:dl_term <= $b:dl_term) => do
    -- in a taclet, between `uint`s: `se <= selfBalance`
    `(Fml.eqD (Term.binop BinOp.le PrimTy.uint $(← schemaTerm [] .val a) $(← schemaTerm [] .val b))
        (Term.lit (.bool true)))
  | stx@`(dl_fml| $_:dl_term < $_:dl_term)
  | stx@`(dl_fml| $_:dl_term > $_:dl_term) | stx@`(dl_fml| $_:dl_term >= $_:dl_term) =>
    Macro.throwErrorAt stx
      "an order between values is read against a contract: write `dl[C]{ … }` or `dl!{ … }`"
  | stx@`(dl_fml| ∀ $_:ident $_:ident; $_:dl_fml) | stx@`(dl_fml| ∃ $_:ident $_:ident; $_:dl_fml) =>
    Macro.throwErrorAt stx
      "a quantifier is read against a contract: write `dl[C]{ … }` or `dl!{ … }`"
  | _ => Macro.throwUnsupported

/-- One goal of `Premise.branches`: the locals it binds (`∀ rets.`; `∀ code.`
the `Panic` code's, `codeBinders`), and its block.  The label is dropped. -/
def schemaBranch (fresh : Bool) (Γ : Scope) (b : TSyntax `dl_branch) : MacroM Lean.Term := do
  let (x?, blk) ← match b with
    | `(dl_branch| $[$_:str :]? $[∀ $x?:ident .]? ⟨[ $blk:sol_block ]⟩) => pure (x?, blk)
    | `(dl_branch| $[$_:str :]? $[∀ $x?:ident .]? [ $blk:sol_block ]) => pure (x?, blk)
    | _ => Macro.throwUnsupported
  let xs ← match x? with
    | none => `([])
    | some x =>
      if stemOf x.getId.toString == "code" then `($(mkIdent `Solidity.codeBinders) $x) else pure x
  `(($xs, $(← schemaBlock fresh Γ blk)))

def schemaPremise (fresh : Bool) (Γ : Scope) : TSyntax `dl_premise → MacroM Lean.Term
  | `(dl_premise| $U:dl_upd ⟨[ ]⟩) => do `($(mkIdent `Solidity.Premise.update) $(← schemaUpd Γ U))
  | `(dl_premise| ⟨[ $[$ss:sol_stmt;]* ]⟩) => do
    let (ts, _) ← schemaProg fresh Γ ss
    `($(mkIdent `Solidity.Premise.unfold) $(← progTerm false ts none))
  | `(dl_premise| $[$_:str :]? $c:dl_fml ⟹ ⟨[ $t:sol_block ]⟩ ; $[$_:str :]? $nc:dl_fml ⟹ ⟨[ $f:sol_block ]⟩) => do
    `($(mkIdent `Solidity.Premise.split) $(← schemaFml c) $(← schemaFml nc)
        $(← schemaBlock fresh Γ t) $(← schemaBlock fresh Γ f))
  | `(dl_premise| $[$_:str :]? $c:dl_fml ⟹ ⟨[ $[$ts:sol_stmt;]* ]⟩ ;
      $[$_:str :]? $nc:dl_fml ⟹ ⟨[ $[$fs:sol_stmt;]* ]⟩) => do
    let (ts, _) ← schemaProg fresh Γ ts
    let (fs, _) ← schemaProg fresh Γ fs
    `($(mkIdent `Solidity.Premise.split) $(← schemaFml c) $(← schemaFml nc)
        $(← progTerm true ts none) $(← progTerm true fs none))
  | `(dl_premise| $[$_:str :]? $c:dl_fml ⟹ ⟨[ $[$ts:sol_stmt;]* ]⟩ ; $[$_:str :]? $c':dl_fml) => do
    unless c.raw.structEq c'.raw do
      Macro.throwErrorAt c' "a check assumes the condition it checks: write it on both sides"
    let (ts, _) ← schemaProg fresh Γ ts
    `($(mkIdent `Solidity.Premise.check) $(← schemaFml c) $(← progTerm true ts none))
  | `(dl_premise| true) => `($(mkIdent `Solidity.Premise.done) true)
  | `(dl_premise| false) => `($(mkIdent `Solidity.Premise.done) false)
  | `(dl_premise| $b:dl_branch ; $bs:dl_branch;*) => do
    let bs ← (#[b] ++ bs.getElems).mapM (schemaBranch fresh Γ)
    `($(mkIdent `Solidity.Premise.branches) [$bs,*])
  | `(dl_premise| $c:dl_case ; $cs:dl_case;*) => do
    let mut fs : Array Lean.Term := #[]
    let mut us : Array Lean.Term := #[]
    for c in #[c] ++ cs.getElems do
      match c with
      | `(dl_case| $[$_:str :]? $U:dl_upd ⟨[ ]⟩) => us := us.push (← schemaUpd Γ U)
      | `(dl_case| $[$_:str :]? $φ:dl_fml) =>
        unless us.isEmpty do Macro.throwErrorAt c "the formula goals come first"
        fs := fs.push (← schemaFml φ)
      | _ => Macro.throwUnsupported
    `($(mkIdent `Solidity.Premise.cases) [$fs,*] [$us,*])
  | _ => Macro.throwUnsupported

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
  match s with
  | `(sol_stmt| $x:ident) =>
    -- `fbs`, `ic`, a call: its arguments simple (`functionCallArgCapture`
    -- first), and with targets (`fbs`) or without (`ic`)
    let n := x.getId.toString
    unless isCallStem n do return out
    let b ← if stemOf n == "fbs" then `(true) else `(false)
    return out.push (mkIdent `hexp, ← `($(mkIdent `Solidity.Arg.firstNonSimple) $(schemaIdent "args") = none))
      |>.push (mkIdent `hrets, ← `($(mkIdent `Solidity.CallRet.isRets) $(schemaIdent "ret") = $b))
  | `(sol_stmt| $l:sol_expr = $r:sol_expr) =>
    match lhsHead [] l with
    | some (.other h) =>
      let some n := singleVar? l | return out
      unless stemOf n == "lhs" do return out
      if isMem [] r then return out.push (hyp n, ← `($(mkIdent `Solidity.MHole.isTarget) $h = true))
      if isPath [] r then return out.push (hyp n, ← `($(mkIdent `Solidity.Hole.isTarget) $h = true))
      return out.push (hyp n, ← `($(mkIdent `Solidity.VHole.isTarget) $h = true))
    | some (.local _) | some (.alias _) | some (.mem _) => return out
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

/-- The taclet `s ⇝ p` under the modality `m`: the `\find` binds its names;
the `\replacewith` sees them, and its own declarations are fresh, numbered by
the taclet's `k`.  The `\find`'s side conditions (`sideConds`) are
hypotheses that prove themselves. -/
def schemaTaclet (m : Lean.Term) (s : TSyntax `sol_stmt) (p : TSyntax `dl_premise)
    (J : Option Lean.Term := none) : MacroM Lean.Term := do
  let conds ← sideConds s
  let (s, Γ) ← schemaStmt false [] s
  let p ← schemaPremise true Γ p
  -- the judgement's own arguments first, one application (`J C k m s p`)
  let jArgs : Array Lean.Term := #[schemaIdent "C", schemaIdent "k"]
  let ((f, args) : Ident × Array Lean.Term) ← match J with
    | none => pure (mkIdent `Solidity.Taclet, jArgs)
    | some J => match J with
      | `($f:ident $args*) => pure (f, args)
      | `($f:ident) => pure (f, #[])
      | _ => Macro.throwErrorAt J "`dl[J]{ … }` names a judgement: `LeanTaclet C k`"
  let t ← `($f:ident $args* $m $s $p)
  if conds.isEmpty then return t
  let hs := conds.map (·.1)
  let cs := conds.map (·.2)
  `(taclet_side% $t $[($hs : $cs)]*)

/-- A primitive type of a schema: `uint`, `int`, `bool`, or a variable. -/
def schemaPrim (T : Ident) : MacroM Lean.Term :=
  match T.getId.toString with
  | "uint" => `(PrimTy.uint)
  | "int" => `(PrimTy.int)
  | "bool" => `(PrimTy.bool)
  | _ => pure T

def schemaHyp : TSyntax `dl_hyp → MacroM Lean.Term
  | `(dl_hyp| { havoc }) => `($(mkIdent `Solidity.Hyp.havoc))
  | `(dl_hyp| $U:dl_upd [ ]) => do `($(mkIdent `Solidity.Hyp.upd) .box $(← schemaUpd [] U))
  | `(dl_hyp| $U:dl_upd ⟨ ⟩) => do `($(mkIdent `Solidity.Hyp.upd) .diamond $(← schemaUpd [] U))
  | `(dl_hyp| $U:dl_upd) => do `($(mkIdent `Solidity.Hyp.upd) $(schemaIdent "m") $(← schemaUpd [] U))
  | `(dl_hyp| ∀ $T:ident $x:ident) => do `($(mkIdent `Solidity.Hyp.all) $x $(← schemaPrim T))
  | stx@`(dl_hyp| .. $_:term) => Macro.throwErrorAt stx "`..Γ`, the rest of the context, comes first"
  | `(dl_hyp| $φ:dl_fml) => do `($(mkIdent `Solidity.Hyp.pre) $(← schemaFml φ))
  | _ => Macro.throwUnsupported

/-- A context: `[h₁, …]`, or with the rest `..Γ` first, `Γ ++ [h₁] ++ …`
(left-nested, as the rules write `Γ ++ [.pre c]`). -/
def schemaHyps (hs : Array (TSyntax `dl_hyp)) : MacroM Lean.Term := do
  if let some (h : TSyntax `dl_hyp) := hs[0]? then
    if let `(dl_hyp| .. $Γ:term) := h then
      return ← (hs.extract 1 hs.size).foldlM (init := Γ) fun acc h => do
        `($acc ++ [$(← schemaHyp h)])
  `([$(← hs.mapM schemaHyp),*])

macro_rules
  | `(dl_schema{ $φ:dl_fml }) => schemaFml φ
  | `(dl{ $φ:dl_fml }) => schemaFml φ
  | `(dl{ $[$hs:dl_hyp],* ⟹ $φ:dl_fml }) => do
    `($(mkIdent `Solidity.Proves) $(mkIdent `Solidity.RuleSet.all) $(← schemaHyps hs)
      $(← schemaFml φ))
  | `(dl{ $[$hs:dl_hyp],* ⟹ₖ $φ:dl_fml }) => do
    `($(mkIdent `Solidity.Proves) $(mkIdent `Solidity.RuleSet.solkey) $(← schemaHyps hs)
      $(← schemaFml φ))
  | `(dl{ $[$hs:dl_hyp],* ⟹[ $R:term ] $φ:dl_fml }) => do
    `($(mkIdent `Solidity.Proves) $R $(← schemaHyps hs) $(← schemaFml φ))
  | `(dl{ $[$hs:dl_hyp],* ⟹ᶜ[ $I:term ] $φ:dl_fml }) => do
    `($(mkIdent `Solidity.ProvesC) $I $(← schemaHyps hs) $(← schemaFml φ))
  | `(tm{ $t:dl_term }) => schemaTerm rawScope (tmSort t) t
  | `(dl{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p:dl_premise }) => schemaTaclet (schemaIdent "m") s p
  | `(dl{ [ $s:sol_stmt; ] ⇝ $p:dl_premise }) => do schemaTaclet (← `(Modality.box)) s p
  | `(dl{ ⟨ $s:sol_stmt; ⟩ ⇝ $p:dl_premise }) => do schemaTaclet (← `(Modality.diamond)) s p
  | `(dl[ $J:term ]{ ⟨[ $s:sol_stmt; ]⟩ ⇝ $p:dl_premise }) => schemaTaclet (schemaIdent "m") s p J
  | `(dl[ $J:term ]{ [ $s:sol_stmt; ] ⇝ $p:dl_premise }) => do
    schemaTaclet (← `(Modality.box)) s p J
  | `(dl[ $J:term ]{ ⟨ $s:sol_stmt; ⟩ ⇝ $p:dl_premise }) => do
    schemaTaclet (← `(Modality.diamond)) s p J
  | `(dl{ $p:dl_premise }) => schemaPremise false [] p
  | `(stmt{ $s:sol_stmt; }) => return (← schemaStmt false [] s).1

end Expand

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

/-! ### Programs -/

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
    | RefTy.mapping K V => `(sol_ty| mapping($(← ppTy K) => $(← ppTy V)))
    | _ => `(sol_ty| T)

/-- A program expression of any sort; indices and proofs are not shown. -/
partial def ppExpr (e : Lean.Expr) : MetaM (TSyntax `sol_expr) := do
  let e ← instantiateMVars e
  if let some n ← fvarName? e then return ← `(sol_expr| $(nameIdent n):ident)
  let escape := do `(sol_expr| ‹$(← escapeTerm e):term›)
  let var (x : Lean.Expr) := do
    let some x ← ppVar? x | escape
    `(sol_expr| $x:ident)
  let name (r : Lean.Expr) := do
    let some r ← nameOf? r | escape
    `(sol_expr| $(nameIdent r):ident)
  let field (b f : Lean.Expr) := do
    let some f ← nameOf? f | escape
    dotExpr (← ppExpr b) f
  let index (b k : Lean.Expr) := do `(sol_expr| $(← ppExpr b):sol_expr[$(← ppExpr k):sol_expr])
  match_expr (← whnf e) with
  | Simple.lit _ _ n _ =>
    let some n ← intOf? n | escape
    if n < 0 then `(sol_expr| -$(Syntax.mkNumLit (toString n.natAbs)):num)
    else `(sol_expr| $(Syntax.mkNumLit (toString n)):num)
  | Simple.bool _ b =>
    match_expr (← whnf b) with
    | Bool.true => `(sol_expr| true)
    | Bool.false => `(sol_expr| false)
    | _ => escape
  | Simple.local _ _ x => var x
  | Simple.env _ _ k _ =>
    match_expr (← whnf k) with
    | EnvKey.msgSender => `(sol_expr| msg.sender)
    | EnvKey.msgValue => `(sol_expr| msg.value)
    | EnvKey.timestamp => `(sol_expr| block.timestamp)
    | EnvKey.selfBalance => `(sol_expr| address(this).balance)
    | EnvKey.selfAddress => `(sol_expr| address(this))
    | _ => escape
  | SPath.alias _ _ x => var x
  | SPath.loc _ _ l => ppExpr l
  | Loc.root _ _ r _ => name r
  | Loc.field _ _ _ b f _ => field b f
  | Loc.index _ _ _ _ _ b i => index b i
  | MPath.var _ _ x => var x
  | MPath.loc _ _ l => ppExpr l
  | MLoc.field _ _ _ b f _ => field b f
  | MLoc.index _ _ _ _ b i => index b i
  | Val.simple _ _ s => ppExpr s
  | Val.read _ _ l => ppExpr l
  | Val.readMem _ _ l => ppExpr l
  | Val.binop _ _ _ op _ _ a b =>
    let some sym ← binopSym? op | escape
    mkBinExpr sym (← ppExpr a) (← ppExpr b)
  | Val.unop _ _ _ op _ _ a =>
    if (← fvarName? op).isSome then return ← `(sol_expr| ⊖$(← ppExpr a))
    match_expr (← whnf op) with
    | UnOp.neg => `(sol_expr| -$(← ppExpr a))
    | UnOp.not => `(sol_expr| !$(← ppExpr a))
    | UnOp.bnot => `(sol_expr| ~$(← ppExpr a))
    | _ => escape
  | Val.ternary _ _ c a b => `(sol_expr| $(← ppExpr c) ? $(← ppExpr a) : $(← ppExpr b))
  | Val.len _ _ _ b _ => dotExpr (← ppExpr b) "length"
  | Val.mlen _ _ _ b _ => dotExpr (← ppExpr b) "length"
  | MRhs.newArr _ R n _ => `(sol_expr| new $(← ppTy.ppRef R):sol_ty ( $(← ppExpr n) ))
  | NewLhs.store _ _ l => ppExpr l
  | NewLhs.mem _ _ l => ppExpr l
  | Src.val _ _ v => ppExpr v
  | Src.copy _ _ p _ => ppExpr p
  | ARhs.path _ _ p => ppExpr p
  | MRhs.alias _ _ p => ppExpr p
  | MRhs.copy _ _ p _ => ppExpr p
  | MSrc.val _ _ v => ppExpr v
  | MSrc.ref _ _ p => ppExpr p
  | OpLoc.local _ _ x => var x
  | OpLoc.root _ _ r _ => name r
  | OpLoc.field _ _ _ b f _ => field b f
  | OpLoc.index _ _ _ _ _ b i => index b i
  | OpLoc.mfield _ _ _ b f _ => field b f
  | OpLoc.mindex _ _ _ _ b i => index b i
  | _ => escape

/-- `x++`, `--x`, or `x⊕⊕` for an operator schema variable. -/
def ppIncDec (op : Lean.Expr) (l : TSyntax `sol_expr) : MetaM (Option (TSyntax `sol_stmt)) := do
  if (← fvarName? op).isSome then return some (← `(sol_stmt| $l:sol_expr ⊕⊕))
  match_expr (← whnf op) with
  | IncDec.postInc => return some (← `(sol_stmt| $l:sol_expr ++))
  | IncDec.preInc => return some (← `(sol_stmt| ++ $l:sol_expr))
  | IncDec.postDec => return some (← `(sol_stmt| $l:sol_expr −−))
  | IncDec.preDec => return some (← `(sol_stmt| −− $l:sol_expr))
  | _ => return none

/-- A call's callee and its arguments, printed. -/
def ppCallParts? (f args : Lean.Expr) :
    MetaM (Option (TSyntax `sol_expr × Array (TSyntax `sol_expr))) := do
  let some f ← nameOf? f | return none
  let fe ← `(sol_expr| $(mkIdent (Lean.Name.mkSimple f)):ident)
  let some as ← listElems? args | return none
  let mut xs : Array (TSyntax `sol_expr) := #[]
  for a in as do
    match_expr (← whnf a) with
    | Arg.mk _ _ _ v => xs := xs.push (← ppExpr v)
    | _ => return none
  return some (fe, xs)

/-- A statement after a call of several returns that assigns one of them
(`lo = se2;`, `total = se3;`): its target and the return variable it reads. -/
def ppRetTarget? (t : Lean.Expr) : MetaM (Option (TSyntax `sol_expr × Lean.Expr)) := do
  let local? (v : Lean.Expr) : MetaM (Option Lean.Expr) := do
    let_expr Val.simple _ _ s := (← whnf v) | return none
    let_expr Simple.local _ _ r := (← whnf s) | return none
    return some r
  match_expr (← whnf (← instantiateMVars t)) with
  | Stmt.assignLocal _ _ x v =>
    let some x ← ppVar? x | return none
    let some r ← local? v | return none
    return some (← `(sol_expr| $x:ident), r)
  | Stmt.assign _ _ l src =>
    let_expr Src.val _ _ v := (← whnf src) | return none
    let some r ← local? v | return none
    return some (← ppExpr l, r)
  | _ => return none

/-- A call that returns to targets (`CallRet.rets`) and the statements after
it assigning them, as the one statement they are elaborated from:
`(lo, , sum) = returnStats(3, 1, 2);`, `result = inc(x);`
(`Stmt.tupleCallStr?`), with the number of statements after the call it
covers. -/
def ppTupleCall? (s : Lean.Expr) (rest : List Lean.Expr) :
    MetaM (Option (TSyntax `sol_stmt × Nat)) := do
  let_expr Stmt.call _ f args _ ret _ := (← whnf (← instantiateMVars s)) | return none
  let_expr CallRet.rets rs := (← whnf ret) | return none
  let some rs ← listElems? rs | return none
  let mut rvs : Array Lean.Expr := #[]
  for r in rs do
    let_expr Prod.mk _ _ _ v := (← whnf r) | return none
    rvs := rvs.push v
  let some (fe, xs) ← ppCallParts? f args | return none
  let mut slots : Array (Option (TSyntax `sol_expr)) := Array.replicate rvs.size none
  let mut start := 0
  let mut n := 0
  for t in rest do
    let some (tgt, r) ← ppRetTarget? t | break
    let mut hit : Option Nat := none
    for i in [start:rvs.size] do
      if ← isDefEq rvs[i]! r then
        hit := some i
        break
    let some i := hit | break
    slots := slots.set! i (some tgt)
    start := i + 1
    n := n + 1
  if n == 0 then return none
  let call ← `(sol_expr| $fe:sol_expr ( $xs,* ))
  if let #[some y] := slots then
    return some (← `(sol_stmt| $y:sol_expr = $call:sol_expr), n)
  let opt (x : Option (TSyntax `sol_expr)) : Syntax := mkNullNode ((x.map fun x => #[x.raw]).getD #[])
  let groups := (slots.extract 1 slots.size).map fun x => mkNode groupKind #[mkAtom ",", opt x]
  return some (⟨mkNode ``Solidity.solTupleAssign
    #[mkAtom "(", opt slots[0]!, mkNullNode groups, mkAtom ")", mkAtom "=", call.raw]⟩, n)

/-- A call of a function returning a memory reference and the statement
after it binding the callee's return variable (the one its body declares
first), as the one statement they are elaborated from:
`Person memory mv1 = choosePersonMem();`, `m = choosePersonMem();`
(`Stmt.memCallStr?`). -/
def ppMemCall? (s t : Lean.Expr) : MetaM (Option (TSyntax `sol_stmt)) := do
  let_expr Stmt.call _ f args _ ret body := (← whnf (← instantiateMVars s)) | return none
  let_expr CallRet.none := (← whnf ret) | return none
  let some bs ← listElems? body | return none
  let some b := bs[0]? | return none
  let_expr Stmt.declMem _ _ r init _ := (← whnf b) | return none
  let_expr Option.none _ := (← whnf init) | return none
  -- the local `t` binds to `r`, and the statement's form
  let bound (rhs : Lean.Expr) : MetaM Bool := do
    let_expr MRhs.alias _ _ p := (← whnf rhs) | return false
    let_expr MPath.var _ _ r' := (← whnf p) | return false
    isDefEq r r'
  let some (fe, xs) ← ppCallParts? f args | return none
  let call ← `(sol_expr| $fe:sol_expr ( $xs,* ))
  match_expr (← whnf (← instantiateMVars t)) with
  | Stmt.declMem _ R x init' _ =>
    let_expr Option.some _ rhs := (← whnf init') | return none
    unless ← bound rhs do return none
    let some x ← ppVar? x | return none
    return some (← `(sol_stmt| $(← ppTy.ppRef R):sol_ty memory $x:ident = $call:sol_expr))
  | Stmt.rebindMem _ _ x rhs =>
    unless ← bound rhs do return none
    let some x ← ppVar? x | return none
    return some (← `(sol_stmt| $x:ident = $call:sol_expr))
  | _ => return none

mutual

partial def ppStmt (e : Lean.Expr) : MetaM (TSyntax `sol_stmt) := do
  let e ← instantiateMVars e
  let escape := do `(sol_stmt| ‹$(← escapeTerm e):term›)
  let hole (h : Lean.Expr) (rhs : TSyntax `sol_expr) := do
    let some n ← fvarName? h | escape
    `(sol_stmt| $(nameIdent n):ident = $rhs)
  -- a hole that is a schema variable does not compute: print it by its name
  if [`Solidity.Hole.fill, `Solidity.MHole.fill, `Solidity.VHole.fill, `Solidity.NewLhs.fill].any
      (e.isAppOfArity · 4) then
    let args := e.getAppArgs
    if (← fvarName? args[2]!).isSome then return ← hole args[2]! (← ppExpr args[3]!)
  -- a statement schema variable `s`
  if let some n ← fvarName? e then return ← `(sol_stmt| $(nameIdent n):ident)
  match_expr (← whnf e) with
  | Stmt.assign _ _ l r => `(sol_stmt| $(← ppExpr l):sol_expr = $(← ppExpr r):sol_expr)
  | Stmt.rebind _ _ x r =>
    let some x ← ppVar? x | escape
    match_expr (← whnf r) with
    | ARhs.push _ _ b _ => `(sol_stmt| $x:ident = $(← ppExpr b):sol_expr .push())
    | _ =>
      if let some n ← fvarName? r then return ← `(sol_stmt| $x:ident = $(nameIdent n):ident)
      `(sol_stmt| $x:ident = $(← ppExpr r):sol_expr)
  | Stmt.assignLocal _ _ x r =>
    let some x ← ppVar? x | escape
    `(sol_stmt| $x:ident = $(← ppExpr r):sol_expr)
  | Stmt.declLocal _ p x init =>
    let some x ← ppVar? x | escape
    let T ← ppTy.ppPrim p
    match_expr (← whnf init) with
    | Option.none _ => `(sol_stmt| $T:sol_ty $x:ident)
    | Option.some _ v => `(sol_stmt| $T:sol_ty $x:ident = $(← ppExpr v):sol_expr)
    | _ => escape
  | Stmt.declStorage _ R x init =>
    let some x ← ppVar? x | escape
    let T ← ppTy.ppRef R
    match_expr (← whnf init) with
    | Option.none _ => `(sol_stmt| $T:sol_ty storage $x:ident)
    | Option.some _ r =>
      match_expr (← whnf r) with
      | ARhs.push _ _ b _ => `(sol_stmt| $T:sol_ty storage $x:ident = $(← ppExpr b):sol_expr .push())
      | _ => `(sol_stmt| $T:sol_ty storage $x:ident = $(← ppExpr r):sol_expr)
    | _ => escape
  | Stmt.declMem _ R x init _ =>
    let some x ← ppVar? x | escape
    let T ← ppTy.ppRef R
    match_expr (← whnf init) with
    | Option.none _ => `(sol_stmt| $T:sol_ty memory $x:ident)
    | Option.some _ r => `(sol_stmt| $T:sol_ty memory $x:ident = $(← ppExpr r):sol_expr)
    | _ => escape
  | Stmt.rebindMem _ _ x r =>
    let some x ← ppVar? x | escape
    `(sol_stmt| $x:ident = $(← ppExpr r):sol_expr)
  | Stmt.assignFromMem _ _ l p => `(sol_stmt| $(← ppExpr l):sol_expr = $(← ppExpr p):sol_expr)
  | Stmt.assignMem _ _ l r => `(sol_stmt| $(← ppExpr l):sol_expr = $(← ppExpr r):sol_expr)
  | Stmt.opAssign _ _ op _ _ l r =>
    let l ← ppExpr l
    let r ← ppExpr r
    if (← fvarName? op).isSome then return ← `(sol_stmt| $l:sol_expr ⊕= $r:sol_expr)
    match_expr (← whnf op) with
    | BinOp.add => `(sol_stmt| $l:sol_expr += $r:sol_expr)
    | BinOp.sub => `(sol_stmt| $l:sol_expr -= $r:sol_expr)
    | BinOp.mul => `(sol_stmt| $l:sol_expr *= $r:sol_expr)
    | BinOp.div => `(sol_stmt| $l:sol_expr /= $r:sol_expr)
    | BinOp.mod => `(sol_stmt| $l:sol_expr %= $r:sol_expr)
    | _ => escape
  | Stmt.incDec _ _ op _ l =>
    let some s ← ppIncDec op (← ppExpr l) | escape
    pure s
  | Stmt.assignIncDec _ _ x op _ l _ =>
    let some x ← ppVar? x | escape
    let l ← ppExpr l
    if (← fvarName? op).isSome then return ← `(sol_stmt| $x:ident = $l:sol_expr ⊕⊕)
    match_expr (← whnf op) with
    | IncDec.postInc => `(sol_stmt| $x:ident = $l:sol_expr ++)
    | IncDec.preInc => `(sol_stmt| $x:ident = ++ $l:sol_expr)
    | IncDec.postDec => `(sol_stmt| $x:ident = $l:sol_expr −−)
    | IncDec.preDec => `(sol_stmt| $x:ident = −− $l:sol_expr)
    | _ => escape
  | Stmt.push _ _ b v _ =>
    match_expr (← whnf v) with
    | Option.none _ => `(sol_stmt| $(← ppExpr b):sol_expr .push())
    | Option.some _ a =>
      if let some n ← fvarName? a then
        return ← `(sol_stmt| $(← ppExpr b):sol_expr .push( $(← `(sol_expr| $(nameIdent n):ident)) ))
      `(sol_stmt| $(← ppExpr b):sol_expr .push( $(← ppExpr a) ))
    | _ => escape
  | Stmt.pop _ _ b => `(sol_stmt| $(← ppExpr b):sol_expr .pop())
  | Stmt.transfer _ r a => `(sol_stmt| $(← ppExpr r):sol_expr .transfer( $(← ppExpr a) ))
  | Stmt.send _ x r a =>
    let some x ← ppVar? x | escape
    `(sol_stmt| $x:ident = $(← ppExpr r):sol_expr .send( $(← ppExpr a) ))
  | Stmt.delete _ _ l => `(sol_stmt| delete $(← ppExpr l):sol_expr)
  | Stmt.deleteMem _ _ p _ => `(sol_stmt| delete $(← ppExpr p):sol_expr)
  | Stmt.assignNew _ R l n _ =>
    let l ← if let some x ← fvarName? l then `(sol_expr| $(nameIdent x):ident) else ppExpr l
    `(sol_stmt| $l:sol_expr = new $(← ppTy.ppRef R):sol_ty ( $(← ppExpr n) ))
  | Stmt.ite _ c thn els =>
    `(sol_stmt| if ($(← ppExpr c)) $(← ppBlock thn):sol_block else $(← ppBlock els):sol_block)
  | Stmt.require _ c => `(sol_stmt| require($(← ppExpr c)))
  | Stmt.assert _ c => `(sol_stmt| assert($(← ppExpr c)))
  | Stmt.revert _ => `(sol_stmt| revert())
  | Stmt.call _ f args _ ret body =>
    -- KeY's `fbs` (`ic` under `pp.sol.ic`): a call whose parts are all schema variables
    if (← [f, args, ret, body].allM fun x => return (← fvarName? x).isSome) then
      return ← if (← getOptions).getBool `pp.sol.ic then `(sol_stmt| ic) else `(sol_stmt| fbs)
    let some (fe, xs) ← ppCallParts? f args | escape
    let res ← match_expr (← whnf ret) with
      | CallRet.val _ _ res =>
        match_expr (← whnf res) with
        | Option.some _ y => ppVar? y
        | _ => pure none
      | _ => pure none
    match res, xs.toList with
    | none, [] => `(sol_stmt| $fe:sol_expr ( ))
    | none, [a] => `(sol_stmt| $fe:sol_expr ( $a:sol_expr ))
    | none, a :: bs => `(sol_stmt| $fe:sol_expr ( $a:sol_expr, $(bs.toArray),* ))
    | some y, [] => `(sol_stmt| $y:ident = $fe:sol_expr ( ))
    | some y, bs => `(sol_stmt| $y:ident = $fe:sol_expr ( $(bs.toArray),* ))
  | Stmt.tryCall _ c rets ok err code pnc other =>
    if let some c ← fvarName? c then
      -- KeY's schema: `try call returns (rets) body catch Error errorBody …`
      let some code ← fvarName? code | return ← escape
      let catches : Array (TSyntax `sol_catch) := #[
        ← `(sol_catch| catch Error $(← ppBlock err):sol_block),
        ← `(sol_catch| catch Panic($(nameIdent code):ident) $(← ppBlock pnc):sol_block),
        ← `(sol_catch| catch $(← ppBlock other):sol_block)]
      let call ← `(sol_expr| $(nameIdent c):ident)
      let some r ← fvarName? rets |
        return ← `(sol_stmt| try $call:sol_expr $(← ppBlock ok):sol_block $catches:sol_catch*)
      let r ← `(sol_tparam| $(nameIdent r):ident)
      return ← `(sol_stmt| try $call:sol_expr returns ($r) $(← ppBlock ok):sol_block $catches:sol_catch*)
    let some call ← ppExtCall? c | escape
    let some rs ← listElems? rets | escape
    let some ps := (← rs.mapM ppRet?).mapM id | escape
    let some code ← ppCode? code | escape
    let catches : Array (TSyntax `sol_catch) := #[
      ← `(sol_catch| catch Error(string memory) $(← ppBlock err):sol_block),
      ← `(sol_catch| catch Panic($code) $(← ppBlock pnc):sol_block),
      ← `(sol_catch| catch $(← ppBlock other):sol_block)]
    if ps.isEmpty then
      `(sol_stmt| try $call:sol_expr $(← ppBlock ok):sol_block $catches:sol_catch*)
    else
      `(sol_stmt| try $call:sol_expr returns ($ps,*) $(← ppBlock ok):sol_block $catches:sol_catch*)
  | _ => escape

/-- A return local of a `try`: `uint v`. -/
partial def ppRet? (r : Lean.Expr) : MetaM (Option (TSyntax `sol_tparam)) := do
  let r ← whnf r
  unless r.isAppOfArity ``Prod.mk 4 do return none
  let some x ← ppVar? r.getAppArgs[3]! | return none
  return some (← `(sol_tparam| $(← ppTy.ppPrim r.getAppArgs[2]!):sol_ty $x:ident))

/-- The `Panic` clause's parameter: `uint c`, or `uint` with no name. -/
partial def ppCode? (code : Lean.Expr) : MetaM (Option (TSyntax `sol_tparam)) := do
  match_expr (← whnf code) with
  | Option.some _ x =>
    let some x ← ppVar? x | return none
    return some (← `(sol_tparam| uint $x:ident))
  | _ => return some (← `(sol_tparam| uint))

/-- `address(a).f(e₁, …)`: an external call. -/
partial def ppExtCall? (c : Lean.Expr) : MetaM (Option (TSyntax `sol_expr)) := do
  let c ← whnf c
  unless c.isAppOfArity ``ExtCall.mk 4 do return none
  let a := c.getAppArgs
  let some f ← nameOf? a[2]! | return none
  let some args ← listElems? a[3]! | return none
  let mut es : Array (TSyntax `sol_expr) := #[]
  for x in args do
    let x ← whnf x
    unless x.isAppOfArity ``Sigma.mk 4 do return none
    es := es.push (← ppExpr x.getAppArgs[3]!)
  let recv ← `(sol_expr| address($(← ppExpr a[1]!)))
  return some (← `(sol_expr| $recv:sol_expr . $(nameIdent f):ident ( $es,* )))

partial def ppProg? (e : Lean.Expr) : MetaM (Option (Array (TSyntax `sol_stmt))) := do
  -- KeY's `expand_function_body(fbs)`, the statements of a call `fbs` (`ic`)
  if (← instantiateMVars e).isAppOfArity ``Stmt.expandBody 4 then
    return some #[← if (← getOptions).getBool `pp.sol.ic then `(sol_stmt| expand_function_body(ic))
      else `(sol_stmt| expand_function_body(fbs))]
  let some ss ← listElems? e | return none
  let mut out : Array (TSyntax `sol_stmt) := #[]
  let mut i := 0
  while i < ss.size do
    if let some (st, n) ← ppTupleCall? ss[i]! (ss.extract (i + 1) ss.size).toList then
      out := out.push st
      i := i + 1 + n
      continue
    if let (some s, some t) := (ss[i]?, ss[i + 1]?) then
      if let some st ← ppMemCall? s t then
        out := out.push st
        i := i + 2
        continue
    out := out.push (← ppStmt ss[i]!)
    i := i + 1
  return some out

/-- A program with schema variables in it: `s :: ω`, `P ++ ω` — its
statements (a program variable as a statement, `P;`) and the rest `ω`, a
variable.  For a program `ppProg?` does not print. -/
partial def ppProgParts? (e : Lean.Expr) :
    MetaM (Option (Array (TSyntax `sol_stmt) × Option Ident)) := do
  let e ← instantiateMVars e
  if let some n ← fvarName? e then return some (#[], some (nameIdent n))
  if e.isAppOfArity ``List.cons 3 then
    let some (ss, t) ← ppProgParts? (e.getArg! 2) | return none
    return some (#[← ppStmt (e.getArg! 1)] ++ ss, t)
  if e.isAppOfArity ``HAppend.hAppend 6 then
    let some n ← fvarName? (e.getArg! 4) | return none
    let some (ss, t) ← ppProgParts? (e.getArg! 5) | return none
    return some (#[← `(sol_stmt| $(nameIdent n):ident)] ++ ss, t)
  let some ss ← ppProg? e | return none
  return some (ss, none)

/-- A branch: `{ s₁; …; sₙ; }`, or the name of a schema variable. -/
partial def ppBlock (e : Lean.Expr) : MetaM (TSyntax `sol_block) := do
  let e ← instantiateMVars e
  if let some n ← fvarName? e then return ← `(sol_block| $(nameIdent n):ident)
  let some ss ← ppProg? e | `(sol_block| ‹$(← escapeTerm e):term›)
  `(sol_block| { $[$ss;]* })

end

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

/-- A program expression lowered to a term (`se.lower`): the notation writes
the expression itself. -/
def loweredExpr? (e : Lean.Expr) : MetaM (Option (TSyntax `dl_term)) := do
  let e ← instantiateMVars e
  for (c, n) in [(``Simple.lower, 3), (``Val.lower, 3), (``SPath.lower, 3), (``Loc.lower, 3),
      (``MPath.lower, 3), (``MLoc.lower, 3)] do
    if e.isAppOfArity c n then
      let x := e.appArg!
      if let some n ← fvarName? x then return some (← `(dl_term| $(nameIdent n):ident))
  return none

def mkBinTerm (sym : String) (a b : TSyntax `dl_term) : MetaM (TSyntax `dl_term) :=
  match sym with
  | "+" => `(dl_term| $a + $b) | "-" => `(dl_term| $a - $b) | "/" => `(dl_term| $a / $b)
  | "±" => `(dl_term| $a ± $b)
  | _ => `(dl_term| $a ⊕ $b)

/-- The term of `t ⊕ u` with a concrete operator: `+`, `-` have term syntax;
the others print as the program operator, read back through `‹…›`. -/
def termOpSym? (op : Lean.Expr) : MetaM (Option String) := do
  if (← fvarName? op).isSome then return some "⊕"
  if op.isAppOfArity ``IncDec.binOp 1 then
    if (← fvarName? op.appArg!).isSome then return some "±"
  match_expr (← whnf op) with
  | BinOp.add => return "+"
  | BinOp.sub => return "-"
  | BinOp.div => return "/"
  | _ => return none

/-- A term's head symbol folded back to its constructor's name:
`Tm.app2 C Op2.find s p` is `Term.find C s p` (`Update.lean`).  Reduction
unfolds the constructor abbreviations; the printers and `rw` match on them.
With `red` off the symbol is not computed either: it is a constructor or
the term stays as it is. -/
def foldTmHead (e : Lean.Expr) (red : Bool := true) : MetaM Lean.Expr := do
  let mk (n : Lean.Name) (args : Array Lean.Expr) : Lean.Expr := mkAppN (mkConst n) args
  let args := e.getAppArgs
  let some f := e.getAppFn.constName? | return e
  if f == ``Tm.pvV && args.size == 2 then return mk ``Term.pv args
  if f == ``Tm.pvP && args.size == 2 then return mk ``PTerm.pv args
  if f == ``Tm.pvS && args.size == 2 then return mk ``STerm.pv args
  if f == ``Tm.pvI && args.size == 2 then return mk ``ITerm.pv args
  let opOf (o : Lean.Expr) : MetaM (Option (Lean.Name × Array Lean.Expr)) := do
    let o ← if red then whnf o else pure o.consumeMData
    let some n := o.getAppFn.constName? | return none
    return some (n, o.getAppArgs)
  if f == ``Tm.app0 && args.size == 3 then
    let C := args[0]!
    let some (n, oa) ← opOf args[2]! | return e
    return match n with
      | ``Op0.lit => mk ``Term.lit (#[C] ++ oa)
      | ``Op0.env => mk ``Term.env (#[C] ++ oa)
      | ``Op0.root => mk ``PTerm.root (#[C] ++ oa)
      | ``Op0.storage => mk ``STerm.storage #[C]
      | ``Op0.memory => mk ``MTerm.memory #[C]
      | _ => e
  if f == ``Tm.app1 && args.size == 5 then
    let C := args[0]!
    let x := args[4]!
    let some (n, oa) ← opOf args[3]! | return e
    return match n with
      | ``Op1.unop => mk ``Term.unop (#[C] ++ oa ++ #[x])
      | ``Op1.net => mk ``Term.net #[C, x]
      | ``Op1.netOf => mk ``Term.netOf (#[C] ++ oa ++ #[x])
      | ``Op1.delValue => mk ``Term.delValue #[C, x]
      | ``Op1.field => mk ``PTerm.field (#[C, x] ++ oa)
      | ``Op1.next => mk ``PTerm.next #[C, x]
      | ``Op1.select => mk ``STerm.select (#[C, x] ++ oa)
      | ``Op1.sval => mk ``SValT.val #[C, x]
      | ``Op1.newArr => mk ``SValT.newArr (#[C] ++ oa ++ #[x])
      | ``Op1.alloc => mk ``ITerm.alloc (#[C, x] ++ oa)
      | ``Op1.mfield => mk ``MAddr.field (#[C, x] ++ oa)
      | ``Op1.addM => mk ``MTerm.addM (#[C, x] ++ oa)
      | ``Op1.mval => mk ``MValT.val #[C, x]
      | ``Op1.ref => mk ``MValT.ref #[C, x]
      | ``Op1.wt => mk ``Term.wt (#[C] ++ oa ++ #[x])
      | _ => e
  if f == ``Tm.app2 && args.size == 7 then
    let C := args[0]!
    let x := args[5]!
    let y := args[6]!
    let some (n, oa) ← opOf args[4]! | return e
    return match n with
      | ``Op2.binop => mk ``Term.binop (#[C] ++ oa ++ #[x, y])
      | ``Op2.find => mk ``Term.find #[C, x, y]
      | ``Op2.len => mk ``Term.len #[C, x, y]
      | ``Op2.read => mk ``Term.read #[C, x, y]
      | ``Op2.mlen => mk ``Term.mlen #[C, x, y]
      | ``Op2.at => mk ``PTerm.at #[C, x, y]
      | ``Op2.nextIn => mk ``PTerm.nextIn #[C, x, y]
      | ``Op2.delAt => mk ``STerm.delAt #[C, x, y]
      | ``Op2.pushSlot => mk ``STerm.pushSlot (#[C, x, y] ++ oa)
      | ``Op2.pop => mk ``STerm.pop #[C, x, y]
      | ``Op2.shrink => mk ``STerm.shrink #[C, x, y]
      | ``Op2.extend => mk ``STerm.extend (#[C, x, y] ++ oa)
      | ``Op2.sfind => mk ``SValT.find #[C, x, y]
      | ``Op2.copyMem => mk ``SValT.copyMem #[C, x, y]
      | ``Op2.iread => mk ``ITerm.read #[C, x, y]
      | ``Op2.copy => mk ``ITerm.copy #[C, x, y]
      | ``Op2.mat => mk ``MAddr.at #[C, x, y]
      | ``Op2.copySt => mk ``MTerm.copySt #[C, x, y]
      | _ => e
  if f == ``Tm.app3 && args.size == 9 then
    let C := args[0]!
    let some (n, _) ← opOf args[5]! | return e
    let xs := #[C, args[6]!, args[7]!, args[8]!]
    return match n with
      | ``Op3.ite => mk ``Term.ite xs
      | ``Op3.save => mk ``STerm.save xs
      | ``Op3.push => mk ``STerm.push xs
      | ``Op3.atIn => mk ``PTerm.atIn xs
      | ``Op3.write => mk ``MTerm.write xs
      | _ => e
  return e

/-- `whnf`, then the head folded back to its constructor's name
(`foldTmHead`): what the printers match on. -/
def whnfTm (e : Lean.Expr) : MetaM Lean.Expr := do
  foldTmHead (← whnf e)

/-- A variable of a term sort, by its name, where a term prints as it is
written (`tm{ … }`, `pp.sol.reduce false`, whose names are such variables). -/
def tmVar? (e : Lean.Expr) : MetaM (Option (TSyntax `dl_term)) := do
  if pp.sol.reduce.get (← getOptions) then return none
  let some n ← fvarName? e | return none
  return some (← `(dl_term| $(nameIdent n):ident))

/-- What a term printer matches on: the term computed (`whnfTm`), or under
`pp.sol.reduce false` the term as it is written, its head folded back to its
constructor's name all the same. -/
def whnfPP (e : Lean.Expr) : MetaM Lean.Expr := do
  if pp.sol.reduce.get (← getOptions) then whnfTm e
  else foldTmHead (red := false) (← instantiateMVars e)

/-- Every term of `e` folded back to its constructors' names: what a `simp`
over the generic `Tm` functions leaves (`Tm.app2 C Op2.find s p`) read as it
was written (`Term.find C s p`), so that `rw` finds it and it prints. -/
def foldTms (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => return .done (← foldTmHead e))

mutual

partial def ppTerm (e : Lean.Expr) : MetaM (TSyntax `dl_term) := do
  if let some x ← loweredExpr? e then return x
  if let some x ← tmVar? e then return x
  let e ← instantiateMVars e
  if e.isAppOfArity ``Term.bumped 4 && (← fvarName? (e.getArg! 1)).isSome then
    return ← `(dl_term| $(← ppTerm e.appArg!):dl_term ⊕⊕)
  match_expr (← whnfPP e) with
  | Term.lit _ v =>
    match_expr (← whnfPP v) with
    | Semantics.PrimVal.int n =>
      let some n ← intOf? n | escapeDl e
      `(dl_term| $(Syntax.mkNumLit (toString n)):num)
    | Semantics.PrimVal.bool b =>
      match_expr (← whnfPP b) with
      | Bool.true => `(dl_term| true)
      | Bool.false => `(dl_term| false)
      | _ => escapeDl e
    | _ =>
      if v.isAppOfArity ``PrimTy.default 1 then
        return ← `(dl_term| defVal(T))
      if let some n ← fvarName? v then return ← `(dl_term| lit($(nameIdent n):ident))
      escapeDl e
  | Term.pv _ x =>
    let some x ← ppVar? x | escapeDl e
    `(dl_term| $x:ident)
  | Term.binop _ op _ a b =>
    let some sym ← termOpSym? op | escapeDl e
    mkBinTerm sym (← ppTerm a) (← ppTerm b)
  | Term.unop _ op _ a =>
    if (← fvarName? op).isSome then return ← `(dl_term| ⊖$(← ppTerm a))
    if (← whnf op).isConstOf ``UnOp.not then return ← `(dl_term| !$(← ppTerm a))
    escapeDl e
  | Term.find _ s p => `(dl_term| find($(← ppSTerm s), $(← ppPTerm p)))
  | Term.len _ s p =>
    let (lenPath, lenVal, _) ← lenTerms (← ppPTerm p)
    if !(← keyOn) && (← whnfPP s).isAppOfArity ``STerm.storage 1 then return lenVal
    `(dl_term| find($(← ppSTerm s), $lenPath))
  | Term.delValue _ t => `(dl_term| delValue($(← ppTerm t)))
  | Term.wt _ _ s => `(dl_term| wt($(← ppSTerm s)))
  | Term.read _ m a =>
    if ← keyOn then
      if let some (i, f) ← keyAddr? a then return ← `(dl_term| read($(← ppMTerm m), $i, $f))
    `(dl_term| read($(← ppMTerm m), $(← ppMAddr a)))
  | Term.mlen _ m i =>
    if ← keyOn then return ← `(dl_term| read($(← ppMTerm m), $(← ppITerm i), size))
    unless (← whnfPP m).isAppOfArity ``MTerm.memory 1 do return ← escapeDl e
    let `(dl_term| $x:ident) ← ppITerm i | escapeDl e
    `(dl_term| $(mkIdent (x.getId.str "length")):ident)
  | Term.env _ k =>
    match_expr (← whnf k) with
    | EnvKey.msgSender => `(dl_term| msg.sender)
    | EnvKey.msgValue => `(dl_term| msg.value)
    | EnvKey.timestamp => `(dl_term| block.timestamp)
    | EnvKey.selfBalance => `(dl_term| selfBalance)
    | EnvKey.selfAddress => if ← keyOn then `(dl_term| self) else `(dl_term| this)
    | _ => escapeDl e
  | Term.net _ a =>
    if ← keyOn then return ← `(dl_term| selectSt(net, at($(← ppTerm a))))
    `(dl_term| net($(← ppTerm a)))
  | Term.netOf _ x a =>
    let some x ← ppVar? x | escapeDl e
    `(dl_term| net($x:ident, $(← ppTerm a)))
  | _ => escapeDl e

/-- KeY's member or element of a memory location (`read(m, i, f)`,
`read(m, i, at(k))`): the identity and the field. -/
partial def keyAddr? (a : Lean.Expr) : MetaM (Option (TSyntax `dl_term × TSyntax `dl_term)) := do
  match_expr (← whnfPP a) with
  | MAddr.field _ i f =>
    let some f ← nameOf? f | return none
    return some (← ppITerm i, ← `(dl_term| $(nameIdent f):ident))
  | MAddr.at _ i k => return some (← ppITerm i, ← `(dl_term| at($(← ppTerm k))))
  | _ => return none

partial def ppPTerm (e : Lean.Expr) : MetaM (TSyntax `dl_term) := do
  if let some x ← loweredExpr? e then return x
  if let some x ← tmVar? e then return x
  match_expr (← whnfPP e) with
  | PTerm.root _ r =>
    let some r ← nameOf? r | escapeDl e
    `(dl_term| $(nameIdent r):ident)
  | PTerm.pv _ x =>
    let some x ← ppVar? x | escapeDl e
    `(dl_term| $x:ident)
  | PTerm.field _ p f =>
    let some f ← nameOf? f | escapeDl e
    if ← keyOn then return ← `(dl_term| consr($(← ppPTerm p), $(nameIdent f):ident))
    dotTerm (← ppPTerm p) f
  | PTerm.at _ p i => elemTerm (← ppPTerm p) (← ppTerm i)
  | PTerm.next _ p => return (← lenTerms (← ppPTerm p)).2.2
  | PTerm.atIn _ s p i =>
    `(dl_term| $(← recvTerm (← ppPTerm p)):dl_term[$(← ppTerm i):dl_term]@$(← ppSTerm s):dl_term)
  | PTerm.nextIn _ s p =>
    let p ← recvTerm (← ppPTerm p)
    let (_, len, _) ← withOptions (fun o => pp.sol.key.set o false) (lenTerms p)
    `(dl_term| $p:dl_term[$len:dl_term]@$(← ppSTerm s):dl_term)
  | _ => escapeDl e

/-- `p[i]`, KeY's `consr(p, at(i))`. -/
partial def elemTerm (p i : TSyntax `dl_term) : MetaM (TSyntax `dl_term) := do
  if ← keyOn then `(dl_term| consr($p, at($i))) else `(dl_term| $(← recvTerm p):dl_term[$i:dl_term])

/-- The push positions of the array `p`: its length as a path, as the value
read in `storage`, and the slot past the end — `p.length`, `p.length` and
`p[p.length]`, KeY's `consr(p, size)`, `find(storage, consr(p, size))` and
`consr(p, at(find(storage, consr(p, size))))`. -/
partial def lenTerms (p : TSyntax `dl_term) :
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

partial def ppSTerm (e : Lean.Expr) : MetaM (TSyntax `dl_term) := do
  if let some n ← fvarName? e then return ← `(dl_term| $(nameIdent n):ident)
  match_expr (← whnfPP e) with
  | STerm.storage _ => `(dl_term| storage)
  | STerm.pv _ x =>
    let some x ← ppVar? x | escapeDl e
    `(dl_term| $x:ident)
  | STerm.save _ s p v => `(dl_term| save($(← ppSTerm s), $(← ppPTerm p), $(← ppSVal v)))
  | STerm.delAt _ s p => `(dl_term| delAt($(← ppSTerm s), $(← ppPTerm p)))
  | STerm.push _ s p v =>
    let (len, val, slot) ← lenTerms (← ppPTerm p)
    `(dl_term| save(save($(← ppSTerm s), $slot, $(← ppSVal v)), $len, $val + 1))
  | STerm.pushSlot _ s p _ =>
    let (len, val, slot) ← lenTerms (← ppPTerm p)
    `(dl_term| save(delAt($(← ppSTerm s), $slot), $len, $val + 1))
  | STerm.pop _ s p =>
    let p ← ppPTerm p
    let (len, val, _) ← lenTerms p
    `(dl_term| save(delAt($(← ppSTerm s), $(← elemTerm p (← `(dl_term| $val - 1)))), $len, $val - 1))
  | STerm.extend _ s p _ =>
    let (len, val, _) ← lenTerms (← ppPTerm p)
    `(dl_term| save($(← ppSTerm s), $len, $val + 1))
  | STerm.shrink _ s p =>
    let (len, val, _) ← lenTerms (← ppPTerm p)
    `(dl_term| save($(← ppSTerm s), $len, $val - 1))
  | STerm.select _ s r =>
    let some r ← nameOf? r | escapeDl e
    if ← keyOn then return ← `(dl_term| selectSt($(← ppSTerm s), $(nameIdent r):ident))
    `(dl_term| select($(← ppSTerm s), $(nameIdent r):ident))
  | _ => escapeDl e

partial def ppSVal (e : Lean.Expr) : MetaM (TSyntax `dl_term) := do
  if let some x ← tmVar? e then return x
  match_expr (← whnfPP e) with
  | SValT.val _ t =>
    -- `find` here reads back as the copy below, so a value read prints as `select`
    if (← loweredExpr? t).isNone && (← tmVar? t).isNone then
      match_expr (← whnfPP t) with
      | Term.find _ s p => return ← `(dl_term| select($(← ppSTerm s), $(← ppPTerm p)))
      | _ => pure ()
    ppTerm t
  | SValT.find _ s p => `(dl_term| find($(← ppSTerm s), $(← ppPTerm p)))
  | SValT.copyMem _ m i => `(dl_term| copyMem(mtSt, $(← ppMTerm m), $(← ppITerm i)))
  | SValT.newArr _ R n =>
    match ← allocTy? R with
    | some T => `(dl_term| newArr($T, $(← ppTerm n)))
    | none => `(dl_term| newArr($(← ppTerm n)))
  | _ => escapeDl e

partial def ppITerm (e : Lean.Expr) : MetaM (TSyntax `dl_term) := do
  if let some x ← loweredExpr? e then return x
  if let some x ← tmVar? e then return x
  match_expr (← whnfPP e) with
  | ITerm.pv _ x =>
    let some x ← ppVar? x | escapeDl e
    `(dl_term| $x:ident)
  | ITerm.read _ m a =>
    if ← keyOn then
      if let some (i, f) ← keyAddr? a then return ← `(dl_term| read($(← ppMTerm m), $i, $f))
    `(dl_term| read($(← ppMTerm m), $(← ppMAddr a)))
  | ITerm.alloc _ m R =>
    let m ← ppMTerm m
    match ← allocTy? R with
    | some T => `(dl_term| freshId(addM($m, $T)))
    | none => `(dl_term| freshId(addM($m)))
  | ITerm.copy _ m v => `(dl_term| freshId(copySt($(← ppMTerm m), $(← ppSVal v))))
  | _ => escapeDl e

partial def ppMAddr (e : Lean.Expr) : MetaM (TSyntax `dl_term) := do
  if let some x ← tmVar? e then return x
  match_expr (← whnfPP e) with
  | MAddr.field _ i f =>
    let some f ← nameOf? f | escapeDl e
    dotTerm (← ppITerm i) f
  | MAddr.at _ i k => `(dl_term| $(← ppITerm i):dl_term[$(← ppTerm k):dl_term])
  | _ => escapeDl e

partial def ppMTerm (e : Lean.Expr) : MetaM (TSyntax `dl_term) := do
  if let some n ← fvarName? e then return ← `(dl_term| $(nameIdent n):ident)
  match_expr (← whnfPP e) with
  | MTerm.memory _ => `(dl_term| memory)
  | MTerm.write _ m a v =>
    if ← keyOn then
      if let some (i, f) ← keyAddr? a then
        return ← `(dl_term| write($(← ppMTerm m), $i, $f, $(← ppMVal v)))
    `(dl_term| write($(← ppMTerm m), $(← ppMAddr a), $(← ppMVal v)))
  | MTerm.addM _ m R =>
    let m ← ppMTerm m
    match ← allocTy? R with
    | some T => `(dl_term| addM($m, $T))
    | none => `(dl_term| addM($m))
  | MTerm.copySt _ m v => `(dl_term| copySt($(← ppMTerm m), $(← ppSVal v)))
  | _ => escapeDl e

partial def ppMVal (e : Lean.Expr) : MetaM (TSyntax `dl_term) := do
  if let some x ← tmVar? e then return x
  match_expr (← whnfPP e) with
  | MValT.val _ t => ppTerm t
  | MValT.ref _ i => ppITerm i
  | _ => escapeDl e

end

/-! ### Updates and formulas -/

def ppUpdElem? (e : Lean.Expr) : MetaM (Option (TSyntax `dl_upd_elem)) := do
  let var (x : Lean.Expr) : MetaM (Option (TSyntax `dl_term)) := do
    let some x ← ppVar? x | return none
    return some (← `(dl_term| $x:ident))
  match_expr (← whnf (← instantiateMVars e)) with
  | UpdElem.val _ x t =>
    let some x ← var x | return none
    let t' ← whnfTm t
    if t'.isAppOfArity ``Term.binop 5 then
      let a ← ppTerm (t'.getArg! 3)
      let b ← ppTerm (t'.getArg! 4)
      match_expr (← whnf (t'.getArg! 1)) with
      | BinOp.le => return some (← `(dl_upd_elem| $x:dl_term := $a:dl_term <= $b:dl_term))
      | BinOp.lt => return some (← `(dl_upd_elem| $x:dl_term := $a:dl_term < $b:dl_term))
      | BinOp.gt => return some (← `(dl_upd_elem| $x:dl_term := $a:dl_term > $b:dl_term))
      | BinOp.ge => return some (← `(dl_upd_elem| $x:dl_term := $a:dl_term >= $b:dl_term))
      | _ => pure ()
    return some (← `(dl_upd_elem| $x:dl_term := $(← ppTerm t):dl_term))
  | UpdElem.path _ x p =>
    let some x ← var x | return none
    return some (← `(dl_upd_elem| $x:dl_term := $(← ppPTerm p):dl_term))
  | UpdElem.mref _ x i =>
    let some x ← var x | return none
    return some (← `(dl_upd_elem| $x:dl_term := $(← ppITerm i):dl_term))
  | UpdElem.storage _ s => return some (← `(dl_upd_elem| storage := $(← ppSTerm s):dl_term))
  | UpdElem.store _ x s =>
    let some x ← var x | return none
    return some (← `(dl_upd_elem| $x:dl_term := $(← ppSTerm s):dl_term))
  | UpdElem.memory _ m => return some (← `(dl_upd_elem| memory := $(← ppMTerm m):dl_term))
  | UpdElem.selfBalance _ op a =>
    let a ← ppTerm a
    match_expr (← whnf op) with
    | IntOp.sub => return some (← `(dl_upd_elem| selfBalance := selfBalance - $a))
    | IntOp.add => return some (← `(dl_upd_elem| selfBalance := selfBalance + $a))
    | _ => return none
  | UpdElem.net _ r op a =>
    let r ← ppTerm r
    let a ← ppTerm a
    let key ← keyOn
    match_expr (← whnf op) with
    | IntOp.sub =>
      if key then return some (← `(dl_upd_elem| net := storeSt(net, at($r), selectSt(net, at($r)) - $a)))
      return some (← `(dl_upd_elem| net := store(net, at($r), net($r) - $a)))
    | IntOp.add =>
      if key then return some (← `(dl_upd_elem| net := storeSt(net, at($r), selectSt(net, at($r)) + $a)))
      return some (← `(dl_upd_elem| net := store(net, at($r), net($r) + $a)))
    | _ => return none
  | UpdElem.pay _ r a =>
    let r ← ppTerm r
    let a ← ppTerm a
    if ← keyOn then
      return some (← `(dl_upd_elem|
        net := if($r = $(mkIdent `self):ident) then $(mkIdent `net):ident
          else storeSt(net, at($r), selectSt(net, at($r)) - $a)))
    return some (← `(dl_upd_elem|
      net := if($r = $(mkIdent `this):ident) then $(mkIdent `net):ident
        else store(net, at($r), net($r) - $a)))
  | UpdElem.saveNet _ x =>
    let some x ← var x | return none
    return some (← `(dl_upd_elem| $x:dl_term := net))
  | _ => return none

/-- The elements of an update made of schema variables (`u`, `{u}u2`) and
lists of elements appended, as `{u ‖ {u}u2}` reads: none if it is not one. -/
partial def updParts? (e : Lean.Expr) : MetaM (Option (Array (TSyntax `dl_upd_elem))) := do
  let e ← instantiateMVars e
  if let some n ← fvarName? e then return some #[← `(dl_upd_elem| $(nameIdent n):ident)]
  if e.isAppOfArity ``HAppend.hAppend 6 then
    if let (some a, some b) := (← updParts? (e.getArg! 4), ← updParts? (e.getArg! 5)) then
      return some (a ++ b)
  if e.isAppOfArity `Solidity.Upd.subst 3 then
    if let (some v, some u) := (← fvarName? (e.getArg! 1), ← fvarName? (e.getArg! 2)) then
      return some #[← `(dl_upd_elem| { $(nameIdent u):ident } $(nameIdent v):ident)]
  -- anything else: the list it computes to
  let some xs ← listElems? e | return none
  let mut out := #[]
  for x in xs do
    let some u ← ppUpdElem? x | return none
    out := out.push u
  return some out

def ppUpd (e : Lean.Expr) : MetaM (TSyntax `dl_upd) := do
  let escape := do `(dl_upd| ‹$(← escapeTerm e):term›)
  let some out ← updParts? e | escape
  if out.isEmpty then return ← escape
  `(dl_upd| { $[$out]‖* })

/-- `defined(a) ∧ defined(b) ∧ a ≐ b`, which `Fml.eqD a b` unfolds to and
`a = b` prints: `a` and `b`. -/
def eqDParts? (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let_expr Fml.and _ l r := (← whnf (← instantiateMVars e)) | return none
  let_expr Fml.defined _ a := (← whnf l) | return none
  let_expr Fml.and _ l' r' := (← whnf r) | return none
  let_expr Fml.defined _ b := (← whnf l') | return none
  let_expr Fml.eq _ a' b' := (← whnf r') | return none
  let (a, b, a', b') := (← instantiateMVars a, ← instantiateMVars b, ← instantiateMVars a',
    ← instantiateMVars b')
  return if a == a' && b == b' then some (a, b) else none

/-- A connective, which the operand of `¬`, `{U}` and `⟨P⟩` parenthesises. -/
def isConnective (e : Lean.Expr) : MetaM Bool := do
  if (← eqDParts? e).isSome then return false
  let e ← whnf e
  return e.isAppOfArity ``Fml.and 3 || e.isAppOfArity ``Fml.imp 3 || e.isAppOfArity ``Fml.all 4

/-- `a < b = true`, a comparison as the specification writes one: its
operator and operands. -/
def cmpParts? (a b : Lean.Expr) : MetaM (Option (String × Lean.Expr × Lean.Expr)) := do
  let some (_, v) := (← whnfTm b).app2? ``Term.lit | return none
  unless (← whnf v).isAppOfArity ``Semantics.PrimVal.bool 1 &&
    (← whnf (← whnf v).appArg!).isConstOf ``Bool.true do return none
  let a ← whnfTm a
  unless a.isAppOfArity ``Term.binop 5 do return none
  let sym ← match_expr (← whnf (a.getArg! 1)) with
    | BinOp.lt => pure "<"
    | BinOp.le => pure "<="
    | BinOp.gt => pure ">"
    | BinOp.ge => pure ">="
    | _ => return none
  return some (sym, a.getArg! 3, a.getArg! 4)

/-- A quantifier's type, as the specification writes it. -/
def primName? (p : Lean.Expr) : MetaM (Option String) := do
  match_expr (← whnf p) with
  | PrimTy.uint => return "uint"
  | PrimTy.int => return "int"
  | PrimTy.bool => return "bool"
  | _ => return none

/-- `¬(¬φ ∧ ¬ψ)`, which `φ ∨ ψ` spells: `φ` and `ψ`. -/
def orParts? (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let_expr Fml.not _ a := (← whnf e) | return none
  let_expr Fml.and _ l r := (← whnf a) | return none
  let_expr Fml.not _ φ := (← whnf l) | return none
  let_expr Fml.not _ ψ := (← whnf r) | return none
  return some (φ, ψ)

/-- `¬(∀ T x; ¬φ)`, which `∃ T x; φ` spells: `x`, `T` and `φ`. -/
def exParts? (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  let_expr Fml.not _ a := (← whnf e) | return none
  let_expr Fml.all _ x p b := (← whnf a) | return none
  let_expr Fml.not _ φ := (← whnf b) | return none
  return some (x, p, φ)

/-- `(φ → ψ) ∧ (ψ → φ)`, which `φ ↔ ψ` spells: `φ` and `ψ`. -/
def iffParts? (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let_expr Fml.and _ l r := (← whnf e) | return none
  let_expr Fml.imp _ φ ψ := (← whnf l) | return none
  let_expr Fml.imp _ ψ' φ' := (← whnf r) | return none
  let (φ, ψ, φ', ψ') := (← instantiateMVars φ, ← instantiateMVars ψ, ← instantiateMVars φ',
    ← instantiateMVars ψ')
  return if φ == φ' && ψ == ψ' then some (φ, ψ) else none

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

partial def ppFml (e : Lean.Expr) : MetaM (TSyntax `dl_fml) := do
  let e ← instantiateMVars e
  if let some x ← fmlVar? e then return ← `(dl_fml| $x:ident)
  let escape := do `(dl_fml| ‹$(← escapeTerm e):term›)
  let arg (φ : Lean.Expr) : MetaM (TSyntax `dl_fml) := do
    let s ← ppFml φ
    if ← isConnective φ then `(dl_fml| ($s)) else pure s
  match_expr (← whnf e) with
  | Fml.tt _ => `(dl_fml| true)
  | Fml.not _ φ =>
    if (← whnf φ).isAppOfArity ``Fml.tt 1 then return ← `(dl_fml| false)
    if let some (a, b) ← orParts? e then
      return ← `(dl_fml| $(← ppFml a):dl_fml ∨ $(← ppFml b):dl_fml)
    if let some (x, p, a) ← exParts? e then
      if let (some x, some T) := (← ppVar? x, ← primName? p) then
        return ← `(dl_fml| ∃ $(mkIdent (Name.mkSimple T)):ident $x:ident; $(← ppFml a):dl_fml)
    `(dl_fml| ¬$(← arg φ):dl_fml)
  | Fml.eq _ a b => `(dl_fml| $(← ppTerm a):dl_term ≐ $(← ppTerm b):dl_term)
  | Fml.defined _ t => `(dl_fml| defined($(← ppTerm t):dl_term))
  | Fml.all _ x p φ =>
    let some x ← ppVar? x | escape
    let some T ← primName? p | escape
    `(dl_fml| ∀ $(mkIdent (Name.mkSimple T)):ident $x:ident; $(← ppFml φ):dl_fml)
  | Fml.and _ φ ψ =>
    if let some (a, b) ← eqDParts? e then
      if let some (sym, l, r) ← cmpParts? a b then
        let l ← ppTerm l
        let r ← ppTerm r
        return ← match sym with
          | "<" => `(dl_fml| $l:dl_term < $r:dl_term)
          | "<=" => `(dl_fml| $l:dl_term <= $r:dl_term)
          | ">" => `(dl_fml| $l:dl_term > $r:dl_term)
          | _ => `(dl_fml| $l:dl_term >= $r:dl_term)
      return ← `(dl_fml| $(← ppTerm a):dl_term = $(← ppTerm b):dl_term)
    if let some (a, b) ← iffParts? e then
      return ← `(dl_fml| $(← ppFml a):dl_fml ↔ $(← ppFml b):dl_fml)
    let ψ' ← ppFml ψ
    let ψ' ← if (← whnf ψ).isAppOfArity ``Fml.imp 3 then `(dl_fml| ($ψ')) else pure ψ'
    `(dl_fml| $(← arg φ):dl_fml ∧ $ψ')
  | Fml.imp _ φ ψ => `(dl_fml| $(← arg φ):dl_fml → $(← ppFml ψ):dl_fml)
  | Fml.upd _ _ U φ => `(dl_fml| $(← ppUpd U):dl_upd $(← arg φ):dl_fml)
  | Fml.havoc _ φ => `(dl_fml| { havoc } $(← arg φ):dl_fml)
  | Fml.modal _ m P φ =>
    let some ss ← ppProg? P |
      if let some n ← fvarName? P then
        let b ← `(sol_block| $(nameIdent n):ident)
        return ← match_expr (← whnf m) with
          | Modality.diamond => `(dl_fml| ⟨ $b:sol_block ⟩ $(← arg φ):dl_fml)
          | Modality.box => `(dl_fml| [ $b:sol_block ] $(← arg φ):dl_fml)
          | _ => `(dl_fml| ⟨[ $b:sol_block ]⟩ $(← arg φ):dl_fml)
      -- `⟨[ s; ..ω ]⟩ φ`: statements in front of the rest of the program
      let some (ss, t) ← ppProgParts? P | escape
      match t with
      | some ω =>
        if (← fvarName? m).isSome then
          return ← `(dl_fml| ⟨[ $[$ss;]* .. $ω:ident ]⟩ $(← arg φ):dl_fml)
        match_expr (← whnf m) with
        | Modality.diamond => `(dl_fml| ⟨ $[$ss;]* .. $ω:ident ⟩ $(← arg φ):dl_fml)
        | Modality.box => `(dl_fml| [ $[$ss;]* .. $ω:ident ] $(← arg φ):dl_fml)
        | _ => escape
      | none =>
        match_expr (← whnf m) with
        | Modality.diamond => `(dl_fml| ⟨ $[$ss;]* ⟩ $(← arg φ):dl_fml)
        | Modality.box => `(dl_fml| [ $[$ss;]* ] $(← arg φ):dl_fml)
        | _ => `(dl_fml| ⟨[ $[$ss;]* ]⟩ $(← arg φ):dl_fml)
    match_expr (← whnf m) with
    | Modality.diamond => `(dl_fml| ⟨ $[$ss;]* ⟩ $(← arg φ):dl_fml)
    | Modality.box => `(dl_fml| [ $[$ss;]* ] $(← arg φ):dl_fml)
    | _ => `(dl_fml| ⟨[ $[$ss;]* ]⟩ $(← arg φ):dl_fml)
  | _ => escape

/-- The name a variable prints as. -/
def varName? (x : Lean.Expr) : MetaM (Option String) := do
  return (← ppVar? x).map (·.getId.toString)

mutual

/-- The memory locals a formula's programs copy a storage path into without
declaring them, where no update in front binds them, with their types:
`carol = alice;`, what `memoryLocalDeclInitDrop` leaves of `Person memory
carol = alice;`.  `storageLocalDeclInitDrop` leaves the same line of `Person
storage carol = alice;`, and `dl[C]{ … }` reads a line on its own, so a line
says which it is: `φ where Person memory carol`.  `bound` holds the names
bound so far. -/
partial def copyDecls (bound : Array String) (e : Lean.Expr) :
    MetaM (Array (String × Lean.Expr)) := do
  match_expr (← whnf (← instantiateMVars e)) with
  | Fml.upd _ _ U φ =>
    let mut bound := bound
    if let some us ← listElems? U then
      for u in us do
        let_expr UpdElem.mref _ x _ := (← whnf u) | continue
        if let some x ← varName? x then bound := bound.push x
    copyDecls bound φ
  | Fml.modal _ _ P φ =>
    let some ss ← listElems? P | copyDecls bound φ
    let (bound, out) ← copyDeclsProg bound ss
    return out ++ (← copyDecls bound φ)
  | Fml.and _ φ ψ => return (← copyDecls bound φ) ++ (← copyDecls bound ψ)
  | Fml.imp _ φ ψ => return (← copyDecls bound φ) ++ (← copyDecls bound ψ)
  | Fml.not _ φ => copyDecls bound φ
  | Fml.all _ _ _ φ => copyDecls bound φ
  | Fml.havoc _ φ => copyDecls bound φ
  | _ => return #[]

/-- `copyDecls` over a program's statements, and the names bound after them. -/
partial def copyDeclsProg (bound : Array String) (ss : Array Lean.Expr) :
    MetaM (Array String × Array (String × Lean.Expr)) := do
  let mut bound := bound
  let mut out := #[]
  for s in ss do
    match_expr (← whnf (← instantiateMVars s)) with
    | Stmt.declMem _ _ x _ _ => if let some x ← varName? x then bound := bound.push x
    | Stmt.rebindMem _ R x r =>
      let some x ← varName? x | continue
      if !bound.contains x && (← whnf r).isAppOfArity ``MRhs.copy 4 then
        out := out.push (x, R)
        bound := bound.push x
    | Stmt.ite _ _ t f =>
      for b in [t, f] do
        let some bs ← listElems? b | continue
        out := out ++ (← copyDeclsProg bound bs).2
    | _ => pure ()
  return (bound, out)

end

/-! ### The delaborators

Each stands aside (`failure`, and Lean prints the term its own way) when all
it would print is one `‹…›`, and `⊨`, `⊧` when it is a name: `⊨ φ`. -/

/-- Printed as `‹…›` as a whole. -/
def isEscape (s : Syntax) : Bool := s[0].isToken "‹"

/-- Printed as `‹…›` or as a name (`fmlVar?`): what Lean prints as well. -/
def isEscapeOrVar (s : Syntax) : Bool := isEscape s || s.isOfKind ``dlFmlVar

/-- `φ`, the formula `e` prints as, with its `where` clause (`copyDecls`). -/
def withDecls (e : Lean.Expr) (φ : TSyntax `dl_fml) : MetaM (TSyntax `dl_fml) := do
  let mut seen : Array String := #[]
  let mut ds : Array (TSyntax `sol_stmt) := #[]
  for (x, R) in ← copyDecls #[] e do
    if seen.contains x then continue
    seen := seen.push x
    ds := ds.push (← `(sol_stmt| $(← ppTy.ppRef R):sol_ty memory $(nameIdent x):ident))
  if ds.isEmpty then return φ
  `(dl_fml| $φ:dl_fml where $ds,*)

/-- Only a full application: `Fml.modal m P` alone is a function. -/
def fullApp : DelabM Unit := do
  let e ← getExpr
  let some c := e.getAppFn.constName? | failure
  if c == ``Fml.eqD then
    guard (e.getAppNumArgs == 3)
    return
  let info ← getConstInfoCtor c
  guard (e.getAppNumArgs == info.numParams + info.numFields)

/-- A formula standing alone: `dl{ φ }`. -/
def delabFml : Delab := do
  unless ← ppOn do failure
  fullApp
  let e ← getExpr
  let φ ← ppFml e
  guard !(isEscape φ)
  `(dl{ $(← withDecls e φ):dl_fml })

attribute [delab app.Solidity.Fml.eq, delab app.Solidity.Fml.eqD, delab app.Solidity.Fml.defined,
  delab app.Solidity.Fml.not,
  delab app.Solidity.Fml.and, delab app.Solidity.Fml.imp, delab app.Solidity.Fml.upd,
  delab app.Solidity.Fml.modal, delab app.Solidity.Fml.all, delab app.Solidity.Fml.havoc] delabFml

/-- `Valid φ`: `⊨ φ`. -/
@[delab app.Solidity.Valid]
def delabValid : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  guard (e.getAppNumArgs == 2)
  let φ ← ppFml e.appArg!
  guard !(isEscapeOrVar φ)
  `(⊨ dl{ $(← withDecls e.appArg! φ):dl_fml })

/-- `holds σ φ`: `σ ⊧ φ`, what `Valid` leaves once its state is introduced. -/
@[delab app.Solidity.holds]
def delabHolds : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  guard (e.getAppNumArgs == 3)
  let φ ← ppFml e.appArg!
  guard !(isEscapeOrVar φ)
  let σ ← withNaryArg 1 delab
  `($σ ⊧ dl{ $(← withDecls e.appArg! φ):dl_fml })

/-- A statement standing alone: `stmt{ s; }`. -/
def delabStmt : Delab := do
  unless ← ppOn do failure
  fullApp
  let s ← ppStmt (← getExpr)
  guard !(isEscape s)
  `(stmt{ $s:sol_stmt; })

attribute [delab app.Solidity.Stmt.assign, delab app.Solidity.Stmt.rebind,
  delab app.Solidity.Stmt.assignLocal, delab app.Solidity.Stmt.declLocal,
  delab app.Solidity.Stmt.declStorage, delab app.Solidity.Stmt.opAssign,
  delab app.Solidity.Stmt.incDec, delab app.Solidity.Stmt.assignIncDec,
  delab app.Solidity.Stmt.push, delab app.Solidity.Stmt.pop, delab app.Solidity.Stmt.transfer,
  delab app.Solidity.Stmt.send,
  delab app.Solidity.Stmt.declMem, delab app.Solidity.Stmt.rebindMem,
  delab app.Solidity.Stmt.assignFromMem, delab app.Solidity.Stmt.assignMem,
  delab app.Solidity.Stmt.delete, delab app.Solidity.Stmt.deleteMem,
  delab app.Solidity.Stmt.assignNew, delab app.Solidity.Stmt.ite, delab app.Solidity.Stmt.require,
  delab app.Solidity.Stmt.assert, delab app.Solidity.Stmt.revert,
  delab app.Solidity.Stmt.call] delabStmt

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

/-- A term of the logic standing alone, over schema variables: `tm{ t }`.
Printed as it is written (`pp.sol.reduce false`: no `whnf`), and only up to
`tmCutoff` nodes. -/
def delabTm : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  let some c := e.getAppFn.constName? | failure
  guard (e.getAppNumArgs == (← getConstInfo c).type.getNumHeadForalls)
  -- a schema's term, over variables (the contract aside): a closed one reads
  -- better as Lean prints it (`PTerm.root "alice"`, a root, not a variable)
  -- the bounded tests first: the delaborator runs at every node of a term it refuses
  guard (sizeAtMost tmCutoff e)
  let e' ← instantiateMVars e
  guard e'.hasFVar
  let fvs := (collectFVars {} e').fvarIds
  guard (← fvs.anyM fun fv => return !(← fv.getType).isConstOf ``Contract)
  let_expr Tm _ s := (← whnfR (← inferType e)) | failure
  let some srt := (← whnf s).constName? | failure
  let printer : Lean.Expr → MetaM (TSyntax `dl_term) ← match srt with
    | ``Srt.val => pure ppTerm
    | ``Srt.path => pure ppPTerm
    | ``Srt.st => pure ppSTerm
    | ``Srt.sv => pure ppSVal
    | ``Srt.ident => pure ppITerm
    | ``Srt.addr => pure ppMAddr
    | ``Srt.mem => pure ppMTerm
    | ``Srt.mv => pure ppMVal
    | _ => failure
  let t ← withOptions (fun o => pp.sol.reduce.set o false) (printer e)
  guard !(isEscape t)
  `(tm{ $t })

attribute [delab app.Solidity.Tm.pvV, delab app.Solidity.Tm.pvP, delab app.Solidity.Tm.pvS,
  delab app.Solidity.Tm.pvI, delab app.Solidity.Tm.app0, delab app.Solidity.Tm.app1,
  delab app.Solidity.Tm.app2, delab app.Solidity.Tm.app3,
  delab app.Solidity.Term.lit, delab app.Solidity.Term.pv, delab app.Solidity.Term.binop,
  delab app.Solidity.Term.unop, delab app.Solidity.Term.find, delab app.Solidity.Term.len,
  delab app.Solidity.Term.read, delab app.Solidity.Term.ite, delab app.Solidity.Term.mlen,
  delab app.Solidity.Term.env, delab app.Solidity.Term.net, delab app.Solidity.Term.netOf,
  delab app.Solidity.Term.delValue, delab app.Solidity.Term.wt,
  delab app.Solidity.PTerm.root, delab app.Solidity.PTerm.pv, delab app.Solidity.PTerm.field,
  delab app.Solidity.PTerm.at, delab app.Solidity.PTerm.next, delab app.Solidity.PTerm.nextIn,
  delab app.Solidity.PTerm.atIn,
  delab app.Solidity.STerm.storage, delab app.Solidity.STerm.pv, delab app.Solidity.STerm.save,
  delab app.Solidity.STerm.delAt, delab app.Solidity.STerm.push, delab app.Solidity.STerm.pushSlot,
  delab app.Solidity.STerm.pop, delab app.Solidity.STerm.shrink, delab app.Solidity.STerm.extend,
  delab app.Solidity.STerm.select,
  delab app.Solidity.SValT.val, delab app.Solidity.SValT.find, delab app.Solidity.SValT.copyMem,
  delab app.Solidity.SValT.newArr,
  delab app.Solidity.ITerm.pv, delab app.Solidity.ITerm.read, delab app.Solidity.ITerm.alloc,
  delab app.Solidity.ITerm.copy, delab app.Solidity.MAddr.field, delab app.Solidity.MAddr.at,
  delab app.Solidity.MTerm.memory, delab app.Solidity.MTerm.write, delab app.Solidity.MTerm.addM,
  delab app.Solidity.MTerm.copySt, delab app.Solidity.MValT.val, delab app.Solidity.MValT.ref] delabTm

end Print

end Solidity
