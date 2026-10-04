---
name: chain-authoring
description: Write or extend a worked chain in Examples/Chains/ (one chain term `A ~[r]~> B ~*> … := by sol_chain`, every line written, ending at one parallel update with every binding kept). Use when a chain must be created, finished to its last line, split into segments, or renamed to the printed fresh names.
---

# Writing a chain

Generate, then paste. Never search for a chain line by line.

1. **First line.** The paper's program, with a concrete starting state in
   front of it as an update: each free parameter a small distinct int, the
   storage the program reads written with `save`, e.g.
   `dl![m]{ { ageVal := 42 ‖ storage := save(storage, alice.age, 10) } ⟨[ … ]⟩ φ }`.
2. **Generate.** In the example's namespace, with its `InContract` and
   `FreshNames` in scope, `variable (m : Modality) (φ : Post C)` and any
   premise a law needs as a `variable (hk : …)`, write `#chain <first line>`
   and read the info message (`lean_diagnostic_messages` on that file, that
   line): `theorem chain : … := by sol_chain`, every line written — or, past
   ten links, `theorem chain1`, `theorem chain2`, … and `theorem chain : A ~~> Z`
   composing them (`Fml.Leads.via`) — and the fresh variables as table rows.
   A chain `c` that stops short: `#chain_rest c` prints the lines to append
   to its statement. On a statement `A ~~> Z`, `by sol_chain?` offers the
   chain term; on a chain term, it says how it goes on.
3. **Paste** the declarations, give each a docstring with its Solidity, and
   add `#last_line chain` after the chain (or after the composed theorem).
4. **Match the paper.** Steps are grouped as the paper prints them: `⇝` a
   `~[rule]~>` (one `~*>` where Lean takes several rules for it), `⇝*` a
   `~*>`. Where the paper folds more steps into one `⇝*` than `#chain` did,
   join those links into one `~*>`; where it prints a step on its own that
   `#chain` folded into a run (a dropped declaration before its binding),
   split it out. Never delete a rewrite link, never add
   `~[simplifyUpdate]~>` or `sol_rws`.
5. **Rename** fresh variables to the trace's names with a table,
   `def names : FreshTable := [("acc", "sp1")]`,
   `local instance : FreshNames := .ofTable names`, guarded by
   `#guard (FreshNames.clashes C names).isEmpty`; re-run `#chain` to see the
   lines in the new names.
6. **Check** the one file with `lean_diagnostic_messages` (`severity=error`),
   then remove the `#chain` command. No `set_option maxHeartbeats`: a chain
   that needs more is split into more segments.

The convention (rules 1–7) is in `.claude/rules/derivations.md`. One agent
at a time: the machine has no RAM for parallel Lean checks.
