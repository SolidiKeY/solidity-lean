import Solidity.Update

/-!
# The closers' simp sets, and the type declared at a path

The `simp` sets the closers rewrite with, and the declared type at a path
of member names and literal indices (`Ty.memberTy`), which the memory
elimination reads below a fresh allocation (`Calculus/TermLaws.lean`'s
`Srt.FreshRead`, `Calculus/MemRead.lean`).  The untyped heap and storage
read through a copy, which the memory laws read here until W10.5.4, are
gone: the laws are proved on the typed heap (`Theory/Typed/Mem.lean`,
`docs/intrinsic.md`).
-/

/-- The rewrites `sol_close` closes a scoped leaf with
(`Calculus/CloseScoped.lean`): the weakest preconditions and symbols of
`Calculus/CloseLemmas.lean`, the leaf's terms and updates read by position. -/
register_simp_attr close_rw_s

/-- The bare box and diamond, which `sol_close` tries after every lemma of
`close_rw_s`: a `simp` set listed later is consulted later. -/
register_simp_attr close_rw_s_last

/-- The evaluation of the reduced formulas `sol_decide` closes (`Decide.lean`). -/
register_simp_attr decide_eval

/-- The same over free reads, for `sol_decide`'s constraints (`DecideComplete.lean`). -/
register_simp_attr decide_evalA

namespace Solidity

open Semantics

/-- The declared type of a member or a fixed element: a struct's member, a
fixed array's element in range. -/
def Ty.at : Ty → Selector → Option Ty
  | .ref (.struct sn), .field f => lookupBy f (structDef sn)
  | .ref (.fixed E n), .at k => if 0 ≤ k ∧ k < n then some E else none
  | _, _ => none

/-- The declared type at the end of a path, member by member. -/
def Ty.memberTy : Ty → List Selector → Option Ty
  | T, [] => some T
  | T, s :: rest => (T.at s).bind (·.memberTy rest)

theorem Ty.memberTy_append (T : Ty) : (p q : List Selector) →
    T.memberTy (p ++ q) = (T.memberTy p).bind (·.memberTy q)
  | [], q => rfl
  | s :: p, q => by
    simp only [List.cons_append, Ty.memberTy]
    cases T.at s <;> simp only [Option.bind, Ty.memberTy_append]

theorem Ty.at_prim (q : PrimTy) (s : Selector) : (Ty.prim q).at s = none := by
  cases s <;> rfl

end Solidity
