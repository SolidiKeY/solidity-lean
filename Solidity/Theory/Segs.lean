import Solidity.Semantics


namespace Solidity
namespace Theory

open Semantics

abbrev lengthSeg : Selector := .len

def diverges : List Selector -> List Selector -> Bool
  | [], _ => false
  | _ :: _, [] => false
  | a :: p, b :: q => if a = b then diverges p q else true

theorem diverges_append_right (p q : List Selector) : diverges p (p ++ q) = false := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [List.cons_append, diverges, ↓reduceIte, ih]

theorem diverges_append_left (p q : List Selector) : diverges (p ++ q) p = false := by
  induction p with
  | nil => cases q <;> rfl
  | cons a p ih => simp only [List.cons_append, diverges, ↓reduceIte, ih]

end Theory
end Solidity
