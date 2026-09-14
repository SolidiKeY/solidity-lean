import Solidity.Semantics

/-!
# Decidable equality for the semantic carriers

`SVal` is a nested inductive (lists of pairs of itself), which the
`DecidableEq` deriving handler does not support on this toolchain — so
the instance is written out by hand (mutual structural recursion), and
`MObj`/`State`/`Except` derive on top of it. Shared by every module
that closes a concrete interpreter run by `native_decide`
(`Counterexamples/`, `Reachability`).
-/

namespace Solidity
namespace Semantics

mutual

private def svalDecEq : (a b : SVal) -> Decidable (a = b)
  | .prim x, .prim y =>
      if h : x = y then .isTrue (by rw [h])
      else .isFalse (fun he => h (SVal.prim.inj he))
  | .struct fs, .struct gs =>
      match svalFieldsDecEq fs gs with
      | .isTrue h => .isTrue (by rw [h])
      | .isFalse h => .isFalse (fun he => h (SVal.struct.inj he))
  | .array xs, .array ys =>
      match svalElemsDecEq xs ys with
      | .isTrue h => .isTrue (by rw [h])
      | .isFalse h => .isFalse (fun he => h (SVal.array.inj he))
  | .map es d, .map fs e =>
      match svalEntriesDecEq es fs, svalDecEq d e with
      | .isTrue h1, .isTrue h2 => .isTrue (by rw [h1, h2])
      | .isFalse h1, _ => .isFalse (fun he => h1 (SVal.map.inj he).1)
      | _, .isFalse h2 => .isFalse (fun he => h2 (SVal.map.inj he).2)
  | .prim _, .struct _ => .isFalse (fun he => SVal.noConfusion he)
  | .prim _, .array _ => .isFalse (fun he => SVal.noConfusion he)
  | .prim _, .map _ _ => .isFalse (fun he => SVal.noConfusion he)
  | .struct _, .prim _ => .isFalse (fun he => SVal.noConfusion he)
  | .struct _, .array _ => .isFalse (fun he => SVal.noConfusion he)
  | .struct _, .map _ _ => .isFalse (fun he => SVal.noConfusion he)
  | .array _, .prim _ => .isFalse (fun he => SVal.noConfusion he)
  | .array _, .struct _ => .isFalse (fun he => SVal.noConfusion he)
  | .array _, .map _ _ => .isFalse (fun he => SVal.noConfusion he)
  | .map _ _, .prim _ => .isFalse (fun he => SVal.noConfusion he)
  | .map _ _, .struct _ => .isFalse (fun he => SVal.noConfusion he)
  | .map _ _, .array _ => .isFalse (fun he => SVal.noConfusion he)

private def svalFieldsDecEq :
    (a b : List (Name × SVal)) -> Decidable (a = b)
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (fun he => List.noConfusion he)
  | _ :: _, [] => .isFalse (fun he => List.noConfusion he)
  | (n, v) :: xs, (m, w) :: ys =>
      if hn : n = m then
        match svalDecEq v w, svalFieldsDecEq xs ys with
        | .isTrue hv, .isTrue ht => .isTrue (by rw [hn, hv, ht])
        | .isFalse hv, _ =>
            .isFalse (fun he =>
              hv (Prod.mk.inj (List.cons.inj he).1).2)
        | _, .isFalse ht =>
            .isFalse (fun he => ht (List.cons.inj he).2)
      else
        .isFalse (fun he => hn (Prod.mk.inj (List.cons.inj he).1).1)

private def svalElemsDecEq : (a b : List SVal) -> Decidable (a = b)
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (fun he => List.noConfusion he)
  | _ :: _, [] => .isFalse (fun he => List.noConfusion he)
  | x :: xs, y :: ys =>
      match svalDecEq x y, svalElemsDecEq xs ys with
      | .isTrue hx, .isTrue ht => .isTrue (by rw [hx, ht])
      | .isFalse hx, _ =>
          .isFalse (fun he => hx (List.cons.inj he).1)
      | _, .isFalse ht =>
          .isFalse (fun he => ht (List.cons.inj he).2)

private def svalEntriesDecEq :
    (a b : List (Int × SVal)) -> Decidable (a = b)
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (fun he => List.noConfusion he)
  | _ :: _, [] => .isFalse (fun he => List.noConfusion he)
  | (i, v) :: xs, (j, w) :: ys =>
      if hi : i = j then
        match svalDecEq v w, svalEntriesDecEq xs ys with
        | .isTrue hv, .isTrue ht => .isTrue (by rw [hi, hv, ht])
        | .isFalse hv, _ =>
            .isFalse (fun he =>
              hv (Prod.mk.inj (List.cons.inj he).1).2)
        | _, .isFalse ht =>
            .isFalse (fun he => ht (List.cons.inj he).2)
      else
        .isFalse (fun he => hi (Prod.mk.inj (List.cons.inj he).1).1)

end

instance : DecidableEq SVal := svalDecEq

deriving instance DecidableEq for MObj
deriving instance DecidableEq for State
deriving instance DecidableEq for Except

end Semantics
end Solidity
