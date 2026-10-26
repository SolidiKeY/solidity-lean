import Solidity.Semantics.RecursiveStorage.Values

namespace Solidity.TypeGraph

def Value.defaultBelow {n : Nat} {G : Schema n} :
    (fuel : Nat) → (T : Ty n) → T.inlineRank G.rank < fuel → Value G T
  | 0, _, h => False.elim ((Nat.not_lt_zero _) h)
  | fuel + 1, .prim p, _ => .prim p.dflt
  | fuel + 1, .node i, h =>
    .node (fun {_} p => Value.defaultBelow fuel _ (p.rank_lt
      (fun f hf => Nat.lt_of_lt_of_le (G.guarded i f hf) (Nat.le_of_lt_succ h))))
  | fuel + 1, .array _, _ => .array ⟨0, by decide⟩ ⟨0, by decide⟩
      (Nat.le_refl 0) (fun _ => .absent)
  | fuel + 1, .fixed _ _, _ => .fixed (fun _ => .absent)
  | fuel + 1, .mapping _ _, _ => .mapping (fun _ => .absent)

def Value.dflt {n : Nat} {G : Schema n} (T : Ty n) : Value G T :=
  Value.defaultBelow (T.inlineRank G.rank + 1) T (Nat.lt_succ_self _)

end Solidity.TypeGraph
