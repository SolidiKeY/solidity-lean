import Solidity.Semantics.State

/-!
# The shape of a run invariant

The typed syntax rules out every *static* mismatch: a member exists, an
operator takes its operand, a copy holds no mapping, a pushed default is
well-formed, and, since the scoped syntax (`Syntax/Scoped.lean`), a local is a
position in a context `Γ`, read and written at the type `Γ` gives it.  The
typed run (`Semantics/Run.lean`) rules out the dynamic ones: its states hold
values of their types, its storage the contract's roots at their types, its
heap objects at the types its typing lists.

What a run keeps beyond its types is a `RunInv`: a part on the storage and a
part on each local at its type, kept as the heap grows (`RunInv.loc_wk`).
`Typing/TypedRunInv.lean` carries one along the typed run;
`heredInv` (`Typing/HeredRun.lean`) instantiates it, at
`Typing/Reachability.lean`, `Typing/Tight.lean` and `Typing/Fits.lean`.
-/

namespace Solidity

/-- An invariant of runs: a part on the storage, a part on each local at its
type, kept when the heap grows (a memory local is weakened along it). -/
structure RunInv (C : Contract) where
  glob : Storage C → Prop
  loc : {H : HTy} → (t : LTy) → t.TDenote C H → Prop
  loc_wk : ∀ {H H' : HTy} (e : H <+: H') {t : LTy} {v : t.TDenote C H}, loc t v →
    loc t (LTy.TDenote.wk e t v)

end Solidity
