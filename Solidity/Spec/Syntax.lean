import Solidity.Spec.Assertion

/-!
# `solspec!`: the specification language in Lean

The NatSpec specification language of `docs/spec-language.md`, as a Lean
notation. The same clauses a `.sol` file writes in `@custom:` comments
are written here as keywords:

```lean
theorem move_spec (age total amount : Int) :
    solspec!{ requires (amount <= age)
              ensures  (age == old(age) - amount)
              modifies age
              < age -= amount > }
      (myStore age total amount) := by
  sol_spec [myStore]
```

`solspec!{ clauses < body > }` elaborates to a `Semantics.State -> Prop`
— apply it to the entry state you want to quantify over. Everything else
follows: the precondition is checked at that state, `old(e)` reads it,
and the postcondition reads the final one. The modality is the bracket,
as in `sol!`: `< body >` is total correctness, `[ body ]` partial (a
revert discharges the obligation), which is what `@custom:partial` means
in a `.sol` file.

## What it reuses

Almost everything. A specification is written in the *program's* own
language, so:

* the body is `sol_stmt`, wrapped by `sol_ann` only to make room for the
  ghost steps;
Every clause proposition is parenthesized — `requires (amount <= age)`,
not `requires amount <= age`. That is not decoration: a clause is
followed by the body's `<` or `[`, and an unparenthesized trailing
comparison would swallow it — `ensures a == b < body >` parses
`b < body` as a comparison, and `reverts_when a < b [ … ]` parses
`b [ … ]` as an index. The parentheses are exactly what lets comparisons
be unparenthesized *inside* a clause, which is the point of `sol_prop`.

* clause expressions are `sol_expr`, wrapped by `sol_prop` only to add
  what a specification needs and a program cannot express —
  unparenthesized comparisons (a clause is not inside the modality
  brackets, so there is no trailing `>` to swallow), `==>`, `<==>`, and
  bounded quantifiers;
* a path with no specification-level index is handed straight to
  `sexpr!`.

It is a separate notation rather than another `sol!` form because the
two say different things: `sol!` is a judgment about one run of a
program, `solspec!` an obligation over every entry state satisfying a
precondition. Keeping them apart leaves the `sol!` grammar untouched.

## What is not shared with the `.sol` front-end

**Name resolution.** A `.sol` file declares its state variables, so the
front-end emits the AST with explicit types and needs no name table. A
`solspec!{…}` specification is written in the program's vocabulary, so it
resolves names exactly as the program does — through
`SoliditySyntax.rootExpr`. That is a fixed table (`age`, `total`,
`balance`, `values`, `alice`, …); for a root it does not know, use the
`name@@Type` form (`balSender@@uint`), which is the program language's
own escape hatch and works for any name.

Two consequences of reading through the program's expression language
rather than a typed path:

* `==` is **integer** equality; write `<==>` for boolean equivalence
  (`a == true` is recognized and treated as boolean, as a convenience).
* the automatic `uintN` range obligation the front-end generates cannot
  be generated here — nothing declares the widths — so state the bound
  you want as an ordinary `ensures`.

## `old` and quantifiers

`old(e)` is written as an ordinary call and intercepted in the expander;
it reads `e` in the entry state. It may not appear inside a path *index*
(`values[old(i)]`), which would need the entry state to build a program
expression; the interpreter treats such a read as stuck, so the
obligation stays unproved rather than proving something else.

A quantifier's binder is a Lean `Int`, usable in arithmetic and as a
path index: `forall i in 0 .. total :: values[i] <= total` reads
`values[i]` by injecting `i` as an integer literal into the program
expression. That is the one place a specification path cannot defer to
`sexpr!`, and the reason `specPath` exists.

## Reserved words

Importing this module reserves `requires`, `ensures`, `invariant`,
`modifies`, `reverts_when`, `ghost` and `assume` as Lean tokens, so they
stop being usable as identifiers in any file that imports it. That is
the same trade `AST.lean` already makes for `assert`, `require`,
`delete` and `revert`; the difference is that this module is opt-in
(`SoliditySpec`, not `Solidity`), so the cost is paid
only where specifications are written.
-/

namespace Solidity

open Lean

/-! ## Syntax categories -/

/-- Specification propositions: `sol_expr` plus the logical vocabulary
Solidity does not have. -/
declare_syntax_cat sol_prop

syntax:20 sol_prop:21 " <==> " sol_prop:20 : sol_prop
syntax:25 sol_prop:26 " ==> " sol_prop:25 : sol_prop
syntax:50 sol_expr:51 " == " sol_expr:51 : sol_prop
syntax:50 sol_expr:51 " != " sol_expr:51 : sol_prop
syntax:50 sol_expr:51 " < " sol_expr:51 : sol_prop
syntax:50 sol_expr:51 " > " sol_expr:51 : sol_prop
syntax:50 sol_expr:51 " <= " sol_expr:51 : sol_prop
syntax:50 sol_expr:51 " >= " sol_expr:51 : sol_prop
syntax:max "forall " ident " in " sol_expr " .. " sol_expr " :: " sol_prop :
  sol_prop
syntax:max "exists " ident " in " sol_expr " .. " sol_expr " :: " sol_prop :
  sol_prop
/-- A `sol_expr` used as a proposition: a boolean-valued path, a `&&`/`||`
combination, or a parenthesized comparison — all of which the program
language already has. -/
syntax:60 sol_expr:60 : sol_prop

/-- An annotated statement: a program statement, or a ghost step. -/
declare_syntax_cat sol_ann

syntax "ghost " "assert " "(" sol_prop ")" : sol_ann
syntax "ghost " "assume " "(" sol_prop ")" : sol_ann
syntax sol_stmt : sol_ann

/-- One specification clause, the keyword form of a `@custom:` tag. -/
declare_syntax_cat sol_clause

syntax "requires " "(" sol_prop ")" : sol_clause
syntax "ensures " "(" sol_prop ")" : sol_clause
syntax "invariant " "(" sol_prop ")" : sol_clause
syntax "reverts_when " "(" sol_prop ")" : sol_clause
syntax "modifies " ident,* : sol_clause

/-! ## Expansion

Binder sets are `List Lean.Name`, spelled out: inside this namespace
`Name` is the project's own `abbrev Name := String` from `AST.lean`.

`solS0` and `solS` are the entry and current state. They are built with
`mkIdent` rather than written inside a quotation on purpose: each piece
of a specification is expanded in its own quotation, and hygiene would
otherwise give every piece a *different* `solS0`. -/

/-- The entry state of a `solspec!` specification, as a binder. -/
def specEntryStateId : Ident := mkIdent `solS0

/-- The state a postcondition or ghost step is read in, as a binder. -/
def specCurrentStateId : Ident := mkIdent `solS

/-- The same two, in term position. Identical raw syntax, so a binder
introduced with the `Id` version binds the occurrences built with this
one — which is the whole reason they are `mkIdent`s and not hygienic
quotation variables. -/
def specEntryState : TSyntax `term := ⟨specEntryStateId.raw⟩

def specCurrentState : TSyntax `term := ⟨specCurrentStateId.raw⟩

/-- Recognize `old(e)`. It parses as an ordinary call, so the
interception happens here rather than in the grammar. -/
private def asOld : TSyntax `sol_expr -> Option (TSyntax `sol_expr)
  | `(sol_expr| $f:ident($args,*)) =>
      if f.getId == `old && args.getElems.size == 1 then args.getElems[0]?
      else none
  | _ => none

/-- Is this expression the literal `true` or `false`? -/
private def asBoolLit : TSyntax `sol_expr -> Option Bool
  | `(sol_expr| $x:ident) =>
      if x.getId == `true then some true
      else if x.getId == `false then some false
      else none
  | _ => none

private def conjoin (ts : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
  match ts.toList with
  | [] => `(True)
  | t :: rest => rest.foldlM (fun acc u => `($acc ∧ $u)) t

mutual

/-- A specification expression read as an `Int`. Arithmetic is done at
the Lean level (so `omega` sees it); anything else is a program
expression evaluated in `st`. -/
partial def specVal (s0 st : TSyntax `term) (bs : List Lean.Name)
    (e : TSyntax `sol_expr) : MacroM (TSyntax `term) := do
  if let some inner := asOld e then
    return (<- specVal s0 s0 bs inner)
  match e with
  | `(sol_expr| ($inner:sol_expr)) => specVal s0 st bs inner
  | `(sol_expr| $n:num) => `(($(quote n.getNat) : Int))
  | `(sol_expr| $a:sol_expr ** $b:sol_expr) => do
      let x <- specVal s0 st bs a
      let y <- specVal s0 st bs b
      `($x ^ ($y).toNat)
  | `(sol_expr| $a:sol_expr * $b:sol_expr) => do
      let x <- specVal s0 st bs a
      let y <- specVal s0 st bs b
      `($x * $y)
  | `(sol_expr| $a:sol_expr / $b:sol_expr) => do
      let x <- specVal s0 st bs a
      let y <- specVal s0 st bs b
      `(Int.tdiv $x $y)
  | `(sol_expr| $a:sol_expr % $b:sol_expr) => do
      let x <- specVal s0 st bs a
      let y <- specVal s0 st bs b
      `(Int.tmod $x $y)
  | `(sol_expr| $a:sol_expr + $b:sol_expr) => do
      let x <- specVal s0 st bs a
      let y <- specVal s0 st bs b
      `($x + $y)
  | `(sol_expr| $a:sol_expr - $b:sol_expr) => do
      let x <- specVal s0 st bs a
      let y <- specVal s0 st bs b
      `($x - $y)
  | `(sol_expr| - $a:sol_expr) => do
      let x <- specVal s0 st bs a
      `(-$x)
  | `(sol_expr| $x:ident) =>
      if bs.contains x.getId then
        pure ⟨x.raw⟩
      else do
        let p <- specPath s0 st bs e
        `(Spec.valInt $st $p)
  | _ => do
      let p <- specPath s0 st bs e
      `(Spec.valInt $st $p)

/-- A specification expression read as a `Prop`. -/
partial def specBool (s0 st : TSyntax `term) (bs : List Lean.Name)
    (e : TSyntax `sol_expr) : MacroM (TSyntax `term) := do
  if let some inner := asOld e then
    return (<- specBool s0 s0 bs inner)
  match e with
  | `(sol_expr| ($inner:sol_expr)) => specBool s0 st bs inner
  | `(sol_expr| $a:sol_expr && $b:sol_expr) => do
      let x <- specBool s0 st bs a
      let y <- specBool s0 st bs b
      `($x ∧ $y)
  | `(sol_expr| $a:sol_expr || $b:sol_expr) => do
      let x <- specBool s0 st bs a
      let y <- specBool s0 st bs b
      `($x ∨ $y)
  | `(sol_expr| ! $a:sol_expr) => do
      let x <- specBool s0 st bs a
      `(¬ $x)
  | `(sol_expr| ($a:sol_expr < $b:sol_expr)) => do
      let x <- specVal s0 st bs a
      let y <- specVal s0 st bs b
      `($x < $y)
  | `(sol_expr| ($a:sol_expr > $b:sol_expr)) => do
      let x <- specVal s0 st bs a
      let y <- specVal s0 st bs b
      `($y < $x)
  | `(sol_expr| ($a:sol_expr <= $b:sol_expr)) => do
      let x <- specVal s0 st bs a
      let y <- specVal s0 st bs b
      `($x ≤ $y)
  | `(sol_expr| ($a:sol_expr >= $b:sol_expr)) => do
      let x <- specVal s0 st bs a
      let y <- specVal s0 st bs b
      `($y ≤ $x)
  | `(sol_expr| ($a:sol_expr == $b:sol_expr)) => specEq s0 st bs a b true
  | `(sol_expr| ($a:sol_expr != $b:sol_expr)) => specEq s0 st bs a b false
  | _ =>
      match asBoolLit e with
      | some true => `(True)
      | some false => `(False)
      | none => do
          let p <- specPath s0 st bs e
          `(Spec.valBool $st $p = true)

/-- `a == b` / `a != b`. Integer equality, except when one side is a
boolean literal — the one case where the intent is unambiguous without a
type. Use `<==>` for boolean equivalence in general. -/
partial def specEq (s0 st : TSyntax `term) (bs : List Lean.Name)
    (a b : TSyntax `sol_expr) (positive : Bool) : MacroM (TSyntax `term) := do
  if (asBoolLit a).isSome || (asBoolLit b).isSome then
    let x <- specBool s0 st bs a
    let y <- specBool s0 st bs b
    if positive then `($x ↔ $y) else `(¬ ($x ↔ $y))
  else
    let x <- specVal s0 st bs a
    let y <- specVal s0 st bs b
    if positive then `($x = $y) else `($x ≠ $y)

/-- The program expression a specification path denotes. Indices are
specification integers (so a quantifier binder can be one), injected as
integer literals; everything else is the program language verbatim. -/
partial def specPath (s0 st : TSyntax `term) (bs : List Lean.Name)
    (e : TSyntax `sol_expr) : MacroM (TSyntax `term) := do
  match e with
  | `(sol_expr| ($inner:sol_expr)) => specPath s0 st bs inner
  | `(sol_expr| $base:sol_expr[$idx:sol_expr]) => do
      let b <- specPath s0 st bs base
      let i <- specVal s0 st bs idx
      `(SoliditySyntax.indexExpr $b (SoliditySyntax.intLitExpr $i))
  | `(sol_expr| $base:sol_expr . $f:ident) => do
      let b <- specPath s0 st bs base
      `(SoliditySyntax.fieldExpr $b $(quote f.getId.toString))
  | `(sol_expr| $x:ident) =>
      if bs.contains x.getId then
        Macro.throwErrorAt x.raw
          s!"`{x.getId}` is a quantifier variable, not a program location"
      else
        `(sexpr!{ $e })
  | _ => `(sexpr!{ $e })

/-- A specification proposition. -/
partial def specProp (s0 st : TSyntax `term) (bs : List Lean.Name)
    (p : TSyntax `sol_prop) : MacroM (TSyntax `term) := do
  match p with
  | `(sol_prop| $a:sol_prop <==> $b:sol_prop) => do
      let x <- specProp s0 st bs a
      let y <- specProp s0 st bs b
      `($x ↔ $y)
  | `(sol_prop| $a:sol_prop ==> $b:sol_prop) => do
      let x <- specProp s0 st bs a
      let y <- specProp s0 st bs b
      `($x -> $y)
  | `(sol_prop| $a:sol_expr == $b:sol_expr) => specEq s0 st bs a b true
  | `(sol_prop| $a:sol_expr != $b:sol_expr) => specEq s0 st bs a b false
  | `(sol_prop| $a:sol_expr < $b:sol_expr) => do
      let x <- specVal s0 st bs a
      let y <- specVal s0 st bs b
      `($x < $y)
  | `(sol_prop| $a:sol_expr > $b:sol_expr) => do
      let x <- specVal s0 st bs a
      let y <- specVal s0 st bs b
      `($y < $x)
  | `(sol_prop| $a:sol_expr <= $b:sol_expr) => do
      let x <- specVal s0 st bs a
      let y <- specVal s0 st bs b
      `($x ≤ $y)
  | `(sol_prop| $a:sol_expr >= $b:sol_expr) => do
      let x <- specVal s0 st bs a
      let y <- specVal s0 st bs b
      `($y ≤ $x)
  | `(sol_prop| forall $i:ident in $lo:sol_expr .. $hi:sol_expr ::
        $body:sol_prop) => do
      let l <- specVal s0 st bs lo
      let h <- specVal s0 st bs hi
      let b <- specProp s0 st (i.getId :: bs) body
      `(Spec.forallIn $l $h (fun $i => $b))
  | `(sol_prop| exists $i:ident in $lo:sol_expr .. $hi:sol_expr ::
        $body:sol_prop) => do
      let l <- specVal s0 st bs lo
      let h <- specVal s0 st bs hi
      let b <- specProp s0 st (i.getId :: bs) body
      `(Spec.existsIn $l $h (fun $i => $b))
  | `(sol_prop| $e:sol_expr) => specBool s0 st bs e
  | _ => Macro.throwUnsupported

end

/-- One annotated step. Ghost predicates read the current state, and may
still mention `old(e)` — hence the entry state parameter. -/
def specAnn (s0 : TSyntax `term) (a : TSyntax `sol_ann) :
    MacroM (TSyntax `term) := do
  let st := specCurrentState
  let stId := specCurrentStateId
  match a with
  | `(sol_ann| ghost assert ($p:sol_prop)) => do
      let t <- specProp s0 st [] p
      `(Spec.Ann.assert (fun $stId => $t))
  | `(sol_ann| ghost assume ($p:sol_prop)) => do
      let t <- specProp s0 st [] p
      `(Spec.Ann.assume (fun $stId => $t))
  | `(sol_ann| $s:sol_stmt) => `(Spec.Ann.stmt (sstmt!{ $s }))
  | _ => Macro.throwUnsupported

/-! ## The `solspec!` notation

Two forms, differing only in the bracket: `< body >` is total
correctness (the function must not revert), `[ body ]` is partial (a
revert discharges the obligation vacuously) — the same convention `sol!`
uses for its two modalities, and what `@custom:partial` means in a
`.sol` file. Both go through `buildSpec`. -/

syntax "solspec!" "{" sol_clause* "<" sepBy(sol_ann, ";", ";") ">" "}" : term
syntax "solspec!" "{" sol_clause* "[" sepBy(sol_ann, ";", ";") "]" "}" : term

/-- Assemble the obligation from the clauses and the annotated body.
Shared by the two bracket forms, which differ only in which halts they
tolerate. -/
def buildSpec (isPartial : Bool) (clauses : Array (TSyntax `sol_clause))
    (anns : Array (TSyntax `sol_ann)) : MacroM (TSyntax `term) := do
  let s0 := specEntryState
  let st := specCurrentState
  let s0Id := specEntryStateId
  let stId := specCurrentStateId
  let mut pres : Array (TSyntax `term) := #[]
  let mut posts : Array (TSyntax `term) := #[]
  let mut triggers : Array (TSyntax `term) := #[]
  for c in clauses do
    match c with
    | `(sol_clause| requires ($p:sol_prop)) =>
        pres := pres.push (<- specProp s0 s0 [] p)
    | `(sol_clause| ensures ($p:sol_prop)) =>
        posts := posts.push (<- specProp s0 st [] p)
    -- An invariant is assumed on entry and proved on exit; the one
    -- clause that appears on both sides.
    | `(sol_clause| invariant ($p:sol_prop)) =>
        pres := pres.push (<- specProp s0 s0 [] p)
        posts := posts.push (<- specProp s0 st [] p)
    | `(sol_clause| reverts_when ($p:sol_prop)) =>
        triggers := triggers.push (<- specProp s0 s0 [] p)
    | `(sol_clause| modifies $ids,*) =>
        let names : Array (TSyntax `term) :=
          ids.getElems.map fun i => quote i.getId.toString
        posts := posts.push (<- `(Spec.modifiesOnly [$names,*] $s0 $st))
    | _ => Macro.throwErrorAt c.raw "unknown specification clause"

  let preT <- conjoin pres
  let postT <- conjoin posts
  let annTerms <- anns.mapM (specAnn s0)
  let halt <-
    if isPartial then `(fun h => h = Semantics.Halt.revert)
    else `(fun _ => False)
  let pre <- `(fun $s0Id => $preT)
  let body <- `(fun $s0Id => [$annTerms,*])
  let post <- `(fun $s0Id $stId => $postT)
  let main <- `(Spec.Obligation $halt $pre $body $post)
  if triggers.isEmpty then
    return main
  -- One `RevertObligation` per trigger: conjoining the triggers would
  -- assume all of them at once, which is weaker than asking each to
  -- force a revert on its own.
  let mut acc <- `($main $s0)
  for t in triggers do
    let trig <- `(fun $s0Id => $t)
    acc <- `($acc ∧ Spec.RevertObligation $pre $trig $body $s0)
  `(fun $s0Id => $acc)

macro_rules
  | `(solspec!{ $cs:sol_clause* < $anns;* > }) =>
      buildSpec false cs anns.getElems
  | `(solspec!{ $cs:sol_clause* [ $anns;* ] }) =>
      buildSpec true cs anns.getElems

end Solidity
