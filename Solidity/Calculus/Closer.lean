import Solidity.Calculus.Closer.Facts
import Solidity.Calculus.Closer.Normal
import Solidity.Calculus.Closer.Bytes
import Solidity.Calculus.Closer.Leaf

/-!
# The closer: a reduction closed by its terms

`sol_prove`'s leaves, reduced (`Fml.reduceS`), are typed first-order
formulas over the starting state (`LFml`, `Calculus/DecideLang.lean`).
KeY closes them with its simplification taclets, each a proof step; here
they are clauses of one function, `LFml.close`, proved sound once
(`LFml.close_valid`), so that the kernel checks a leaf by evaluation.

What it knows at a point of a leaf is a `Facts`: terms that return, pairs
of terms equal (a rewrite, left to right: KeY's `applyEq`) or apart.  A
premise adds to it (`LFml.yesM`: an equation, its `assert`s and guards
read `true`, its `bool` sides taken apart); a term is read in its normal
form under the facts (`Facts.nf`): every symbol on literals evaluated
(KeY's literal and `intSimplification` taclets), a guard that returns
dropped, a key compared with itself or with one it is apart from read as
its branch (`select(store(h, k, v), j)` under `k = j` or `k ≠ j`), a
comparison of two terms apart folded, `(a - b) + b` and `(a + b) - b`
cancelled, `2 * a` read as `a + a`, `a < a + c` read `true` (Lean only),
and a subterm (a constant included) the premises know rewritten.  A conclusion `a = b` holds where the two normal
forms are one term that returns; where a key comparison is left open, the
closer splits on it (`LTm.pick`, KeY's `cut` on `k = j`).

Since W10.4 the terms are typed: a value is in range by its type, the
storage has the shape its contract declares, so no layout premise and no
kind test is left to the closer.

The functions the kernel evaluates are written with their recursors, each
with a `match` twin for compiled code (Gate G0).

The module is split by topic, each piece importing the one before
(`Calculus/Closer/Facts.lean`, `Calculus/Closer/Normal.lean`, `Calculus/Closer/Bytes.lean`, `Calculus/Closer/Leaf.lean`);
this module imports them all.
-/
