import Solidity.Semantics.RecursiveStorage.Defaults

/-!
Deletion follows existing well-founded value children, not declaration rank.
Mappings are barriers. Arrays clear only their former live prefix and retain
the allocated extent and every old shadow slot. Slot functions stay lazy.
-/

namespace Solidity.TypeGraph

mutual
def Value.clear {n : Nat} {G : Schema n} : {T : Ty n} → Value G T → Value G T
  | _, @Value.prim _ _ p _ => .prim p.dflt
  | _, .node fields => .node (fun p => (fields p).clear)
  | _, .array extent length _ slots =>
    .array extent ⟨0, by decide⟩ (Nat.zero_le _)
      (fun i => if i.val < length.val then (slots i).clear else slots i)
  | _, .fixed slots => .fixed (fun i => (slots i).clear)
  | _, .mapping slots => .mapping slots

def Slot.clear {n : Nat} {G : Schema n} : {T : Ty n} → Slot G T → Slot G T
  | _, .absent => .absent
  | _, .present v => .present v.clear
end

theorem Value.clear_mapping {n : Nat} {G : Schema n} {K : PrimTy} {V : Ty n}
    (slots : K.Denote → Slot G V) : (Value.mapping slots).clear = .mapping slots := rfl

theorem Value.clear_tail {n : Nat} {G : Schema n} {E : Ty n}
    (extent : Extent) (length : Index) (h : length.val ≤ extent.val)
    (slots : Fin extent.val → Slot G E) (i : Fin extent.val)
    (tail : length.val ≤ i.val) :
    (Value.array extent length h slots).clear.slots i = slots i :=
  if_neg (Nat.not_lt_of_ge tail)

mutual
theorem Value.clear_idem {n : Nat} {G : Schema n} :
    {T : Ty n} → (v : Value G T) → v.clear.clear = v.clear
  | _, .prim _ => rfl
  | _, .node fields => congrArg Value.node
      (funext fun _ => funext fun p => Value.clear_idem (fields p))
  | _, .array _ _ _ _ => by
      simp only [Value.clear, Nat.not_lt_zero, if_false]
  | _, .fixed slots => congrArg Value.fixed
      (funext fun i => Slot.clear_idem (slots i))
  | _, .mapping _ => rfl

theorem Slot.clear_idem {n : Nat} {G : Schema n} :
    {T : Ty n} → (slot : Slot G T) → slot.clear.clear = slot.clear
  | _, .absent => rfl
  | _, .present v => congrArg Slot.present (Value.clear_idem v)
end

theorem Value.clear_defaultBelow {n : Nat} {G : Schema n} (fuel : Nat) :
    (T : Ty n) → (h : T.inlineRank G.rank < fuel) →
    (Value.defaultBelow fuel T h).clear = Value.defaultBelow fuel T h := by
  induction fuel with
  | zero => intro T h; exact False.elim ((Nat.not_lt_zero _) h)
  | succ fuel ih =>
    intro T h
    cases T with
    | prim p => rfl
    | node i =>
      apply congrArg Value.node
      funext T p
      exact ih T _
    | array E => rfl
    | fixed E m => rfl
    | mapping K V => rfl

theorem Value.clear_dflt {n : Nat} {G : Schema n} (T : Ty n) :
    (Value.dflt T : Value G T).clear = Value.dflt T :=
  Value.clear_defaultBelow _ T _

end Solidity.TypeGraph
