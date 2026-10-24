import Solidity.Calculus.CloseScoped.Leaf
import Solidity.Calculus.CloseScoped.Steps

/-!
# `sol_close` on a scoped leaf

`sol_symex` on a scoped goal (`⊨ᶠ dl!{ … }` under `open scoped Solidity.Scoped`)
leaves leaves `Fml.Valid ψ`, `ψ : Fml C []` with no modality.  `sol_close`,
`sol_close_mt` and `sol_spec_close` close them here, on the scoped formula,
by the elaborators below, which read it with `close_rw_s`
(`Calculus/Close.lean` declares the syntax and the simp sets).

**The leaf as the closer reads it**: `holds` itself, over the typed state.
A term reads the state's global part a field at a time (`State.glob`: the
storage, the ledger, the balance, the transaction) and its locals by
position (`State.locV`, a stack of `LocsV.push`es over the root state's),
every symbol by its typed equation (`Calculus/CloseLemmas.lean`'s
`Close.Op2.eval_find`, …, under `Tm.eval_app*`); a read is an `Option`,
`none` where it reverts, carried into the closer's weakest preconditions by
`Close.optRes`.  An update is computed on the state it is applied in
(`Upd.applyV`: its typed global part and its locals' values), and its rest
is read in every typed state it lands on (`CloseS.holds_upd`, from
`Upd.afterT_applyV`): `LandedAll g ℓ`, the states `Landed g ℓ` whose type
carries what they read, so a plain rewrite reads them (`Landed.storage_eq`,
`Landed.locV_eq`) with no contextual pass and no hypothesis.  The rest is a
constant until the update's result is known (`LandedRest`), and the binder
a constant, not a `∀` (`LandedAll`, opened at the end, `landedAll_def`).
The binders range over the values of their types: a `uint` over
`[0, 2²⁵⁶)` (`forall_uint`).

**The set** states lemmas about `Calculus/Lands.lean`'s typed readers
only (`Tm.eval`, `Tm.denote`, `Rhs.eval`, `Upd.applyV`, `UpdElem.globT`)
and the typed state's operations as `State.locV` and the global part's
fields read them.  A storage write under the box is named on the spot with
the typed laws in `Calculus/CloseFrame.lean` (above `TermLaws`, whose frame
laws it reads).

The module is split by topic, each piece importing the one before
(`Calculus/CloseScoped/Leaf.lean`, `Calculus/CloseScoped/Steps.lean`);
this module imports them all.
-/
