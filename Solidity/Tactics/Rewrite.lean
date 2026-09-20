import Solidity.Theory.Rewrite
import Solidity.Tactics.Derivation

/-!
# `sol_rewrite`: the paper's term-evaluation lines

A worked example of the paper does not stop when the program is gone.  The
calculus's chain leaves an update whose right-hand sides are still terms, and
the paper keeps rewriting them — `find(store(storage, alice, copyMem(…)), …)`
to `readR(…)` to `42` — by the rules of the data-structure theories.  Those
lines are `sol_derivation`'s missing tail, and they are not `⇝` lines: no
taclet fires, an equation between terms is applied.

`sol_rewrite` is the chain of those lines.  It is `sol_derivation`'s sibling,
sharing its arrow category (`Tactics/Derivation.lean`) and using only the equality
arrows of it:

```
sol_rewrite deepFieldWriteValue :
    find (save mtSt [alice, account, balance] (.int 10)) [alice, account, balance]
  =[.findOnSave]  StValue.int 10
```

`=[r]` names a `TheoryRule` (`Theory/Rewrite.lean`), which is checked: the rule
is resolved to the theorem it is and *that* theorem is what discharges the
line, so a wrong name does not elaborate.  `=` leaves the rule to the
automation, and `=*` collapses several — the paper's `⇝*`.

## Why this is a separate command and not a longer `sol_derivation`

`Sequent.upd` is a state function.  `{u}{v := alice.age}` and `{u ‖ v := 34}`
are *not* equal as state functions — at a pre-state where the memory variable
is unbound the first errors where the second does not — so the paper's terminal
evaluation is not a `Frontier.Equiv` and no tactic could make it one.  It is a
theorem of the free-term algebra, where `read(write(m, id, f, v), id, f) = v`
holds for a symbolic `m`.  That is where the paper proves it too; the split
between the two commands is the split the paper already has between its
calculus and its signature.

`docs/paper-parity.md` names both chains of an example, and that pair is the
example.
-/

namespace Solidity.Examples

open Lean Elab Command Term Meta Solidity.Theory

/-- One line of a chain, by the theorem the rule names.  A theory taclet often
carries a side condition (`find_save_same` wants a non-empty path), so the
rewrite's leftovers get the algebra's own automation. -/
macro "theory_rule_step " t:term : tactic =>
  `(tactic|
    first
      | (rw [$t:term] <;> first | rfl | assumption | simp | decide | omega)
      | (simp only [$t:term] <;> first | rfl | assumption | simp | decide | omega)
      | (simp [$t:term] <;> first | rfl | assumption | decide | omega)
      | (conv => rw [$t:term]))

/-- One line with the rule left to the automation. -/
macro "theory_step" : tactic =>
  `(tactic| first | rfl | decide | simp | (simp; rfl))

/-- Several lines at once: the paper's `⇝*`. -/
macro "theory_steps" : tactic =>
  `(tactic| first | rfl | decide | simp | (simp <;> rfl) | (simp <;> decide))

/-- The theorem a `TheoryRule` denotes, as an identifier a tactic can take.
Evaluating `TheoryRule.lemmaName` at elaboration time is what makes the name on
the arrow load-bearing rather than a comment. -/
private def ruleLemmaIdents (rule : Term) : CommandElabM (Array Ident) := do
  let ns : List Lean.Name <- liftTermElabM do
    let e <- Term.elabTerm (<- `(Solidity.Theory.TheoryRule.lemmaNames $rule))
      (some (mkApp (mkConst ``List [levelZero]) (mkConst ``Lean.Name)))
    Term.synthesizeSyntheticMVarsNoPostponing
    let e <- instantiateMVars e
    let ns : List Lean.Name <-
      unsafe evalExpr (List Lean.Name) (mkApp (mkConst ``List [levelZero]) (mkConst ``Lean.Name)) e
    return ns
  if ns.isEmpty then throwErrorAt rule "this rule names no theorem"
  return (ns.map mkIdent).toArray

/-- The line's tactic: the rule at whichever sort the line is written in, tried
in the table's order. -/
private def ruleStepTactic (lems : Array Ident) : CommandElabM (TSyntax `tactic) := do
  let mut tac <- `(tactic| theory_rule_step $(lems[0]!))
  for l in lems.toList.tail! do
    tac <- `(tactic| first | $tac:tactic | theory_rule_step $l)
  return tac

/-- The lines are parsed at precedence 51, above `=`, for the reason
`sol_derivation`'s blocks are: otherwise the first `=` arrow is read as part of
the line before it and the chain collapses into a single proposition. -/
syntax (docComment)? "sol_rewrite " ident (ppSpace bracketedBinder)*
  (" let " sol_where_bind,+)?
  " : " term:51 (sol_arrow term:51)+ (" where " sol_where_bind,+)? : command

elab_rules : command
  | `(command| $[$doc:docComment]? sol_rewrite $name:ident $binders:bracketedBinder*
        $[let $lets:sol_where_bind,*]? : $first:term
        $[$arrows:sol_arrow $targets:term]*
        $[where $binds:sol_where_bind,*]?) => do
      for group in [lets, binds] do
        if let some group := group then
          for bind in group.getElems do
            match bind with
            | `(sol_where_bind| $bindName:ident := $value:term) =>
                elabCommand (<- `(command| abbrev $bindName := $value))
            | _ => throwErrorAt bind "malformed `sol_rewrite` binding"
      let mut prev := first
      let mut proofs : Array Term := #[]
      for (arrow, target) in arrows.zip targets do
        let proof <-
          match arrow with
          | `(sol_arrow| ≡[$rule:term]) | `(sol_arrow| =[$rule:term])
          | `(sol_arrow| ⇝≡[$rule:term]) => do
              let tac <- ruleStepTactic (<- ruleLemmaIdents rule)
              `(show $prev = $target from by $tac:tactic)
          | `(sol_arrow| ≡*[$rules:term,*]) | `(sol_arrow| =*[$rules:term,*]) => do
              let lems := (<- rules.getElems.mapM ruleLemmaIdents).flatten
              `(show $prev = $target from by
                  first | rfl | simp [$[$lems:ident],*] | simp only [$[$lems:ident],*])
          | `(sol_arrow| ≡) | `(sol_arrow| =) | `(sol_arrow| ⇝≡)
          | `(sol_arrow| ~>=) =>
              `(show $prev = $target from by theory_step)
          | `(sol_arrow| ≡*) | `(sol_arrow| =*) =>
              `(show $prev = $target from by theory_steps)
          | _ => throwErrorAt arrow
              "a `sol_rewrite` chain is written with the equality arrows \
               (`=`, `=[r]`, `=*`); `~>` is a rule of the calculus and belongs \
               to a `sol_derivation`"
        proofs := proofs.push proof
        prev := target
      let some proof := proofs.back? | throwErrorAt name
        "`sol_rewrite` needs at least one step"
      let mut folded := proof
      for p in proofs.pop.reverse do
        folded <- `(Eq.trans $p $folded)
      elabCommand (<-
        `(command| $[$doc:docComment]? theorem $name $binders:bracketedBinder* :
            $first = $prev := $folded))

end Solidity.Examples
