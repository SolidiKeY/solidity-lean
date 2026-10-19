# Automation: expansions, sizes and the road to a decision procedure

Milestones M0–M5 towards a closer that decides a fragment. M0, M1, M2 and M5
are built; M3 and M4 are planned. Each section says what is proved and where.

## M0 · The leaves of a type (`Theory/Typed/Leaves.lean`)

A type of *finite shape* (`Ty.Finite`, decided by `Ty.finiteShape`: words,
members, fixed arrays of finite shape up to `2^256`, mappings kept whole, no
dynamic array outside a mapping) is its words at its leaves: `Ty.leaves`,
the paths through members and in-range fixed indices that end at a word,
computed by fuel over `rankBound`; `Ty.leafCount` is their number.  The
leaves are exactly the direct paths to a word that stay inside the value
(`Ty.mem_leaves`, by `Path.direct`/`Path.out`), and two distinct leaves
diverge (`Ty.leaves_strip?_ne`, `Leaf.diverges`).  A fixed array's length is
part of its type, so a `uint[2^200]` has that many leaves: every user bounds
the count.

## M1 · The expansions, in the Theory and the interpreter (`Theory/Typed/Leaves.lean`)

* Theory, where a value is its observations, under `TVal.Shaped` (true of
  every typed value, `SVal.obs_shaped`, `Storage.obs_shaped`): a delete and
  a copy at a finite shape are a word written per leaf (`Obs.delAt_expand`,
  `Obs.copyTo_find_expand`); a push and a pop of a word (`Obs.push_prim`,
  `Obs.pop_prim`).
* Interpreter, with no premise on the storage, at a finite shape with a leaf
  (`T.leaves ≠ []`): `Storage.delete_expand`, `Storage.write_expand`,
  `Storage.write_find_expand` (the source read before the copy), and
  `Storage.push_prim` (one more slot, then the save at `len`),
  `Storage.pop_prim` (the save of the default at `len - 1`, then the length
  shrunk keeping it).

## M2 · The expansions as chain links past the program (`Calculus/ExpandLaws.lean`)

`Tm.expand?` rewrites a storage term at its head, one of four kinds
(`ExpandKind`, `Tm.expandK?`):

| link | from | to |
|---|---|---|
| `delAtExpand` | `delAt(s, p)` | `save(…save(s, p.l₁, 0)…, p.lₙ, 0)` |
| `copyExpand` | `save(s, p, find(s, q))` | `save(…save(s, p.l₁, select(s, q.l₁))…, p.lₙ, select(s, q.lₙ))` |
| `pushExpand` | `push(s, p, x)` | `save(pushSlot(s, p), p[p.length]@s, x)` |
| `popExpand` | `pop(s, p)` | `shrink(save(s, p[p.length - 1]@s, 0), p)` |

A delete and a copy fire at a type `Ty.expandable` accepts: finite shape,
between one and `expandBound` (64) words, counted by arithmetic
(`Ty.leafCountAt`, equal to the leaves' number by `Ty.length_leavesAt`), so
a huge fixed array is refused without listing it (`Ty.expandable_spec`).  A
copy fires only at a type that is no word, and only from the storage it
writes to (`s` both times, `Tm.beqR`).  A push and a pop fire only on an
array of words.  No argument may push (`Tm.pushFree`).

A leaf's path is `p` followed by its members (`.f`, unchecked as the
program's) and its fixed indices, written `p[i]@s` (`atIn`): checked in the
storage written to, where an in-range fixed index passes; the push's slot is
`p[p.length]@s` (`nextIn`, unchecked), the pop's `p[p.length - 1]@s`, whose
`- 1` reverts on an empty array exactly as the pop does.

**Proved.**

* `Tm.eval_expand?` (and per kind `Tm.eval_delAtLeaves`, `Tm.eval_copyLeaves`,
  `Tm.eval_pushWord`, `Tm.eval_popWord`): `t.expand? = some t' → t'.eval σ =
  t.eval σ` in every typed state, reverts included, from M1's interpreter
  lemmas and the symbols' evaluation equations.
* `Tm.exhB_expandK?`: the expansion is out of gas exactly where the term is
  (only the push can be: at a full array, `Tm.exhB_pushWord`).
* `holds_upd_expand_iff`: the rewrite of an update's right-hand sides
  (`Upd.rwBy (Tm.pickExpand k)`) is an equivalence under either modality
  (`Upd.rwBy_afterT`); `FmlRw.expandPast k i` is the rewrite of the update
  at position `i` of a scoped line.
* `Tm.spineSaves_expand?`: at most `expandBound` more `save`s on the storage
  spine (`Tm.spineSaves`); a delete exactly `T.leafCount` more
  (`Tm.spineSaves_delAtLeaves`).  A fixed index repeats `s` in its path.

**Chains.**  `~[delAtExpand]~>`, `~[copyExpand]~>`, `~[pushExpand]~>`,
`~[popExpand]~>` name the rewrite past the program (`rwExpandLinks`,
`Calculus/RewriteChains.lean`; the candidates in `Calculus/Chains.lean`).
They are Lean only and never tried by `~=>`, `#chain` or `#last_line`: a
worked chain's last line keeps a `delete` whole, as solkey does.
`Examples/ChainExpand.lean` shows each, and `sol_decide` closing the
expanded lines.

## M3 · Reads reduce write-free (planned)

The closer's read reduction (`LTm.elim`, `Calculus/Decide.lean`) leaves no
storage symbol on the fragment of saves: a theorem `LTm.elim_stoFree`, and
per statement that a step emits saves only.

## M4 · Completeness (planned)

Conditions lifted out of equations, fixed literal indices in the read
flattening, the exact fragment `Fml.inExact`, and `dependentReduction?`
total on it.

## M5 · The size of what a rule emits (`Calculus/TermSize.lean`)

`Tm.size`, `Upd.length`, `Upd.tmSize`, `Fml.tmSize`, `Stmt.size` count
nodes, never a type.  Every rule writes at most two elements an update
(`Stmt.step_upds_le`), and every term it emits is at most
`16 * s.size + 16` (`Stmt.step_tmSize_le`), one lemma per arm.
