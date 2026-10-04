---
name: chain-authoring
description: Write or extend a worked chain in Examples/Chains/ (a calc of dl![m]{…} lines ending at one parallel update). Use when a chain must be created, finished to its last line, shortened, or renamed to the printed fresh names.
---

# Writing a chain

Generate, then edit. Never search for a chain line by line.

1. **Generate.** In the example's namespace, with its `InContract` and
   `FreshNames` in scope and `variable (m : Modality) (φ : Post C)`, write
   `#chain dl![m]{ … first line … }` and read the info message
   (`lean_diagnostic_messages` on that file, that line): the last line, the
   `calc`, and the fresh variables as table rows. On an existing statement
   `A ~~> B`, `by sol_chain?` does the same and offers the `calc`
   (`lean_code_actions` applies it).
2. **Paste** the `calc` and state the last line as the chain's right end
   (`theorem chain … : A ~~> B`); add `#last_line chain` after it.
3. **Prune** what the printed trace does not show: consecutive strategy lines
   become one `_ ~*> line := by sol_chain`; consecutive rewrite lines become
   one `_ ~~> line := by sol_rws [r₁, …]` (`sol_rws?` writes the list).
   Keep every line the trace prints.
4. **Rename** fresh variables to the trace's names with a table,
   `def names : FreshTable := [("acc", "mv1")]`,
   `local instance : FreshNames := .ofTable names`, guarded by
   `#guard (FreshNames.clashes C names).isEmpty`; re-run `#chain` to see the
   lines in the new names.
5. **Check** the one file with `lean_diagnostic_messages` (`severity=error`),
   then remove the `#chain` command.

Conventions (which reads to resolve, `simplifyUpdate` last, segments past ten
updates) are in `.claude/rules/derivations.md`. One agent at a time: the
machine has no RAM for parallel Lean checks.
