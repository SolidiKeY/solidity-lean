import Solidity.Calculus.RuleSyntax.Grammar
import Solidity.Calculus.RuleSyntax.Schemas
import Solidity.Calculus.RuleSyntax.Print

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
| `dl{ ..Γ ⟹ᶜ[I; noCallback] φ }` | printing only: the same where a `transfer` and a `send` do not call back (`ProvesC I false`) |
| `tm{ find(save(s, p, v), q) }` | a scoped term `Tm`, every name a Lean variable (where `Calculus/TermLib/Rules.lean` is imported) |
| `⊨ᶠ φ` | `Fml.Valid φ` of a scoped `φ` (`Calculus/Logic.lean`) |
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
| `ic` | any other call with its body (KeY's `InternalCall`), `expand_function_body(ic)` its statements | `Stmt.call f args ret body` | its arguments simple; not `CallRet.isRets` (a result, if any, assigned inside the expansion: `y = f(a);`); no summary (`CallRet.summary?`, `internalCallSummary`) |
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

The module is split by topic, each piece importing the one before
(`Calculus/RuleSyntax/Grammar.lean`, `Calculus/RuleSyntax/Schemas.lean`, `Calculus/RuleSyntax/Print.lean`);
this module imports them all.
-/
