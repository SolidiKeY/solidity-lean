import Solidity.Calculus.TermLaws.Storage
import Solidity.Calculus.TermLaws.Reads
import Solidity.Calculus.TermLaws.Fresh

/-!
# The term laws at an update's right-hand sides, scoped

solkey's term laws, read on the scoped terms `Tm C Γ s` (`Calculus/Fml.lean`)
and the scoped updates `Upd C Γ Δ`, over `State C Γ`: what makes each exact
inside an update's right-hand sides, under either modality.  A law `t ⇝ t'`
rewrites there when the right side returns what the left side does
(`Tm.EvalRefinesAt`), and, wherever the update returns, the left side
returns what the right side does: the update holds the write the law reads
back.  `LawCov` bundles the two with the syntactic check that gives the
second, decided by `rfl`.

* **The literal laws** (`LitLaw`): KeY's `*_literals` taclets, exact
  everywhere (`LitLaw.exact`), at their typed literals: each side condition
  is the operator's typed evaluation (`BinOp.evalT`), its range check
  included.
* **A storage law onto a literal** (`LawCov.findOnSave`):
  `find(save(s, p, sval(w)), p)` over `storage := save(s, p, sval(w))`.
* **Two member-wise forms of one read** (`LawCov.findMemberCons`):
  `find(s, r.p)` and `find(select(s, r), p)` return alike in every state
  (`Storage.find_selectT`).

**Typed sorts** (W9.8.3c).  A term reads the typed state directly
(`Tm.eval`), so the laws are proved on the typed storage
(`Storage.findOnSave`, `Storage.find_selectT`), with no erased state.  The frame and
delete-value laws past an update are `TermTaclet.RefLaw` (`Upd.coversRef`);
the memory laws are `EvalLaw` (`Upd.coversEval`).

The module is split by topic, each piece importing the one before
(`Calculus/TermLaws/Storage.lean`, `Calculus/TermLaws/Reads.lean`, `Calculus/TermLaws/Fresh.lean`);
this module imports them all.
-/
