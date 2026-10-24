import Solidity.Calculus.Problem
import Solidity.Tools.Common

/-!
# Storages too large to write down

A counterexample whose array has `2^255` elements cannot be built element by
element.  `SVec.rep v n` is `n` copies of `v`, written as the function that
makes them: the kernel unfolds it only as far as a reader goes, and a run
that reads the array's length (`Storage.len`, the vector's index) or its
first slots never goes far.  The test `wt(storage)` reads every element, so
it is not evaluated on such a storage but proved: the elements' test once
(`SVec.allB_rep`, by induction), the array node's by evaluation (its tests
read the length, not the elements), and the other roots by evaluation
(`SFields.allB_cons_true`, `holds_wt_of`), assembled by
`Tools/Counterexample.lean`'s certificate.
-/

namespace Solidity

variable {C : Contract}

/-- `n` copies of `v`. -/
def SVec.rep {E : Ty} (v : SVal E) : (n : Nat) → SVec E n
  | 0 => .nil
  | n + 1 => .cons v (SVec.rep v n)

section AllB

variable (B : HeredB)

theorem SVec.allB_rep {E : Ty} (v : SVal E) (hv : v.allB B = true) :
    (n : Nat) → (SVec.rep v n).allB B = true
  | 0 => SVec.allB_nil B
  | n + 1 => by
    rw [show SVec.rep v (n + 1) = .cons v (SVec.rep v n) from rfl, SVec.allB_cons, hv,
      SVec.allB_rep v hv n]
    rfl

theorem SFields.allB_cons_true {f : Name} {T : Ty} {fs : List (Name × Ty)} {v : SVal T}
    {rest : SFields fs} (hv : v.allB B = true) (hr : rest.allB B = true) :
    (SFields.cons (f := f) v rest).allB B = true := by
  rw [SFields.allB_cons, hv, hr]
  rfl

/-- A dynamic array of `n` copies of `v`, no slot past its end, passes `B`
where `v` and the array node do. -/
theorem SVal.allB_arrayOf_rep {E : Ty} (v : SVal E) (n : Nat) (hn : n < 2 ^ 256)
    (hv : v.allB B = true) (ha : B.arr (SVec.rep v n) SList.nil = true) :
    (SVal.arrayOf (SVec.rep v n) SList.nil).allB B = true := by
  unfold SVal.arrayOf
  rw [dif_pos hn, SVal.allB_array, ha, SVec.allB_rep B v hv, SList.allB_nil]
  rfl

end AllB

/-- `wt(storage)` from its two tests. -/
theorem holds_wt_of {Γ : Ctx} {σ : State C Γ} (h1 : SFields.allB canonHB σ.storage = true)
    (h2 : SFields.allB tightHB σ.storage = true) : holds σ (Fml.wt C) :=
  holds_wt.2 (by simp only [Storage.wtB, Storage.shapeB, h1, h2, Bool.and_self])

end Solidity
