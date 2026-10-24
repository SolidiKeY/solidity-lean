import Solidity.Calculus.RewritePast.Scope
import Solidity.Calculus.RewritePast.Merge
import Solidity.Calculus.RewritePast.Apply

/-!
# Rewrites of a scoped line past the program

The rewrites a chain takes once its program is done, on the scoped line
(`Fml C Γ`), where `Calculus/RewriteScoped.lean`'s stop: the line the
strategy leaves past a declaration keeps a hidden binder between two
updates, a merge leaves a storage write the next one shadows, a capture
stays declared after its scope ended.  Each rewrite is a `FmlRw`, sound one
way (`holds σ ψ → holds σ φ`).

| `FmlRw` | line before ⇝ line after | sound by | solkey |
|---|---|---|---|
| `mergePast k n` | the `n + 1` updates from position `k` merged into one, through hidden binders (`Fml.merge2P`), over a storage or memory write, a shadowed state write dropped (`Upd.dropSh`) | `Fml.mergeRunP_sound` | `sequentialToParallel1-3` |

**A hidden binder absorbed.**  `bind x ({x := e ‖ U} φ)`, `e` and `U` not
reading `x`, is `{x :=decl e ‖ U} φ` (`Upd.absorb`, `holds_bind_absorb`):
the binder reads every value of `x`, and the update overwrites it before
anything reads it.  Decision 101's merge across a hidden binder: the
binder's local declared by the update, the two updates then merge as any
two do.  An update of locals only moves under the binder instead
(`Upd.lift?`, `Calculus/Merge.lean`), where it declares nothing.

**A shadowed state write.**  `{… ‖ storage := S ‖ … ‖ storage := T ‖ …}`,
`S` read before anything else of `T` (`Tm.onSpineS`), is the update without
`storage := S` (`Upd.dropSh`): no element reads the state it writes into
but the ledger, `T` writes the storage over `S`'s, and `T` halts where `S`
does.  So for memory writes (`Tm.onMemSpineS`).

These functions run once a link and use `match` on the indexed families,
under the exemption of `Calculus/RewriteScoped.lean`'s walks (proposal 104).

The module is split by topic, each piece importing the one before
(`Calculus/RewritePast/Scope.lean`, `Calculus/RewritePast/Merge.lean`, `Calculus/RewritePast/Apply.lean`);
this module imports them all.
-/
