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

## `theory_rw`: the same lines with the terms left to the goal

`theory_rw [.findDelAt, .findOnSave]` is to `sol_rewrite` what `seq_steps` is
to `sol_derivation`: the endpoints in the statement and the rules in the proof,
each rule a rewrite by its theorem, so the cursor walks the chain as it walks
`rw [a, b]`.  Use it to find a chain, or when the intermediate terms are not
the artefact.
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
private def ruleLemmaNames (rule : Term) : TermElabM (List Lean.Name) := do
  let e <- Term.elabTerm (<- `(Solidity.Theory.TheoryRule.lemmaNames $rule))
    (some (mkApp (mkConst ``List [levelZero]) (mkConst ``Lean.Name)))
  Term.synthesizeSyntheticMVarsNoPostponing
  let e <- instantiateMVars e
  let ns : List Lean.Name <-
    unsafe evalExpr (List Lean.Name) (mkApp (mkConst ``List [levelZero]) (mkConst ``Lean.Name)) e
  if ns.isEmpty then throwErrorAt rule "this rule names no theorem"
  return ns

private def ruleLemmaIdents (rule : Term) : CommandElabM (Array Ident) := do
  return ((<- liftTermElabM (ruleLemmaNames rule)).map mkIdent).toArray

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

open Tactic in
/-- One element of a `theory_rw` list: the first of the rule's theorems that
rewrites the goal, its side conditions closed.  `rewrite` leaves the rewritten
goal first and the side conditions after it; a side condition that does not
close fails the theorem, and the next one is tried.  `erewrite` is the
fallback because a rule stated over `p ++ q` meets a literal path, and only
default transparency takes `[a, b, c]` apart as `[a, b] ++ ?q`. -/
private def theoryRwRule (rule : Term) : TacticM Unit := do
  let lems <- Tactic.runTermElab (ruleLemmaNames rule)
  let goal <- getMainGoal
  let saved <- Tactic.saveState
  for lem in lems do
    for useE in [false, true] do
      let id := mkIdent lem
      try
        if useE then evalTactic (<- `(tactic| rewrite (config := { transparency := .default }) [$id:ident]))
        else evalTactic (<- `(tactic| rewrite [$id:ident]))
        let main :: sides <- getGoals | throwError "no goal left"
        for g in sides do
          setGoals [g]
          evalTactic (<- `(tactic| first | rfl | assumption | decide | simp | omega))
          unless (<- getGoals).isEmpty do throwError "side condition left open"
        setGoals [main]
        return
      catch _ => saved.restore
  throwErrorAt rule "no theorem of this rule rewrites the goal (tried {lems}){indentExpr (<- goal.getType)}"

open Tactic in
/-- Rewrite by the listed theory rules in order, the goal left to the page
between them: `sol_rewrite`'s chain as `rw` spells a proof, the way
`seq_steps` spells a `sol_derivation`.  Each element is a `TheoryRule` under the
paper's name and is resolved to its theorem, so a wrong name does not
elaborate; each carries its own info node, widened as `seq_steps`'s are, so the
cursor on `.b` in `theory_rw [.a, .b, .c]` shows the goal `.a` left and the end
of `.b`'s line the goal after it.  `rfl` closes the goal at the end if it can,
as `rw` does. -/
elab "theory_rw " "[" rs:term,* "]" : tactic => do
  let elems := rs.getElems
  for (r, ref) in elems.zip (widenedElemRefs elems) do
    withTacticInfoContext ref (theoryRwRule r)
  evalTactic (<- `(tactic| try rfl))

end Solidity.Examples
