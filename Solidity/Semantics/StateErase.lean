import Solidity.Semantics.State
import Solidity.Semantics.Agree

/-!
# A local's binding, untyped

What the decision procedure's untyped state binds a scoped local to
(`Calculus/DecideRel.lean`): a local's value encoded as `Semantics.lean`'s
binding (`LTy.enc`), under the name a position takes in a list of names
(`Idx.name`).
-/

namespace Solidity

open Semantics (Value SVal MVal Seg Halt Res Binding lookupBy setBy copyStToM allocDefault
  copyMem applyBinOp applyUnOp checkArith)
open SemanticsProperties (lookupBy_setBy_self lookupBy_setBy_ne)

variable {C : Contract}

/-! ## Erased locals -/

/-- A local's value as `Semantics.lean` binds it. -/
def LTy.enc (C : Contract) : (t : LTy) → t.Denote C → Binding
  | .val _, v => .val v
  | .alias _, some (r, segs) => .spath r segs
  | .alias _, none => .unset
  | .mem _, some id => .mref id
  | .mem _, none => .unset
  | .old, st => .store st
  | .oldNet, l => .ledger l

/-- A global part with these bindings. -/
abbrev withLocals (τ : Semantics.State) (e : List (Var × Binding)) : Semantics.State :=
  { τ with env := e }

theorem Idx.name_mem {Γ : Ctx} {t : LTy} (i : Idx Γ t) (ns : List Var)
    (h : ns.length = Γ.length) : i.name ns ∈ ns := by
  unfold Idx.name
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (h ▸ i.toNat_lt)]
  exact List.getElem_mem _

theorem Idx.name_there {Γ : Ctx} {t u : LTy} (i : Idx Γ t) (x : Var) (ns : List Var) :
    (Idx.there (u := u) i).name (x :: ns) = i.name ns := by
  simp only [Idx.name, Idx.toNat, List.getD_cons_succ]

end Solidity
