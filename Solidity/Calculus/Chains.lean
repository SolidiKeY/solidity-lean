import Solidity.Calculus.Chains.Strategy
import Solidity.Calculus.Chains.Proofs
import Solidity.Calculus.Chains.Elab

/-!
# Chains on scoped formulas: `φ ~> ψ`, `φ ~[r]~> ψ`, `φ ~*> ψ`

The chains of `.claude/rules/derivations.md` on the scoped formulas of
`Calculus/Fml.lean` (W2 of `docs/intrinsic.md`); the relations are
`Calculus/ChainKit.lean`'s.  The notation is the same: a chain whose
first line is a scoped formula (`cdl![m]{ … }`) is read here, any other is
refused (`Calculus/RewriteChains.lean`), and `sol_chain` and `#derivation`
dispatch on the goal's head constant the same way.

**The lines are computed.**  A scoped line keeps what its print does not
show: the scope ends of a rule's fresh locals (`Frames.pop .capture`), the
rest of the program as a frame, the hidden binder.  So a written line after
the first is not read into the chain: the strategy computes it, and the
written text must be the computed line read in names: the two compare by
their keys (`Fml.lineKey`; `matchWritten`), the line as text in names (its
terms and updates, `Tm.keyStr`, `Upd.keyStrs`, and a modality's program,
`Prog.keyStrs`), what prints as nothing (a hidden binder, a scope end) left
out, the text read scoped with its parameters open (`elabDlOpen`), a
postcondition by its slot.  A line printed with a block's end
(`}`, `Delab`'s `core_item`) reads without it.  The statement holds
the computed lines, which `Delab` prints as written.

**While the program is open**, `~[sequentialToParallel]~>` merges the
scoped line's update spine (`Fml.MergeBy`, `Calculus/Merge.lean`), and a
literal law or a term taclet (in an update's right-hand sides or in the
line's equations), `applyOnRigid`, `concrete` and `simplifyUpdate` rewrite
the scoped line (`Fml.RwBy`, `Calculus/RewriteScoped.lean`;
`scopedRwCands`); `~=>` takes the first merge or rewrite that gives the
line written (`openRwSteps`).  The strategy goes on from the line a rewrite
leaves, so a step and a rewrite are links of one chain.

**`~~>` and `calc`**: `A ~~> B` reads `B` as a line of `A`'s derivation (or
one with its spine merged, or up to `openRwDepth` merges and rewrites past
one while the program is open, `openRwPath`, a bounded search that
`sol_chain?` writes out as links), else past the program as the line it
names (`Fml.LeadsK`: a line the rewrites reach that is `B`, read where it
stands, up to its binders' names); a
`calc` step `_ R B` leaves `B` a metavariable that `sol_chain` computes
from the line before and checks against the text (`pendingLines`), a
rewrite's too while the program is open (`Fml.RwBy`).

**Past the program** every rewrite arrow (`~[sequentialToParallel]~>`,
`~[findOnSave]~>`, `~=>`) rewrites the scoped line too: the merges and
`simplifyUpdate` of `Calculus/RewritePast.lean`, the laws in an update's
right-hand sides of `Calculus/RewriteLaws.lean` (the laws of
`Calculus/TermLaws.lean`, found at the update's scope), and the rewrites of
`Calculus/RewriteScoped.lean`.
A rewrite that gives no line written says why (`pastRefusal`): it applies
nowhere (a side condition, a modality), or what it gives.

**Proving a link** is the kernel's: `sol_chain` runs the strategy as
compiled code (`Fml.chainLines`, the postconditions in slots and a
modality `m` run as the diamond and the box), and proves each step
`Fml.stepFocusR k φ = some (f, ψ)` by `rfl` where no postcondition stands in
the way; where one does, along the line's connectives (`focusProof`, the
postcondition's `Post.inactive` past a goal that is done), with the fresh
index from `Post.noFresh` (`maxIdxProof`).  A rule that looks at a variable
modality is proved by `Modality.casesOn`, both cases by `rfl`.

The module is split by topic, each piece importing the one before
(`Calculus/Chains/Strategy.lean`, `Calculus/Chains/Proofs.lean`, `Calculus/Chains/Elab.lean`);
this module imports them all.
-/
