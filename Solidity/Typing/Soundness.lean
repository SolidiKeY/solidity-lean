import Solidity.Semantics.State


namespace Solidity

structure RunInv (C : Contract) where
  glob : Storage C → Prop
  loc : {H : HTy} → (t : LTy) → t.TDenote C H → Prop
  loc_wk : ∀ {H H' : HTy} (e : H <+: H') {t : LTy} {v : t.TDenote C H}, loc t v →
    loc t (LTy.TDenote.wk e t v)

end Solidity
