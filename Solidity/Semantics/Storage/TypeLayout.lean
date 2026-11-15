import Solidity.AST

/-! Shared full-word type layout. The established Evm names retain their
reduction and equation lemmas; this module imports no machine semantics. -/
namespace Solidity.Evm

open Semantics

/-- Size in slots, with fuel for the struct table: a fixed-size array takes
its elements' slots, inline. -/
def sizeF : Nat → Ty → Nat
  | fuel + 1, .ref (.struct n) => (structDef n).foldr (fun f acc => sizeF fuel f.2 + acc) 0
  | 0, .ref (.struct _) => 0
  | fuel + 1, .ref (.fixed E n) => n * sizeF fuel E
  | 0, .ref (.fixed _ _) => 0
  | _, _ => 1

/-- Size in slots: `Person` (an `Account`, a `uint`) takes `3`. -/
def size (T : Ty) : Nat := sizeF (tyRank T + 1) T

/-- The sizes of a member list added up. -/
def sumSizes (l : List (Name × Ty)) : Nat := l.foldr (fun f acc => size f.2 + acc) 0

/-- Where member `f` starts in a member list: the sizes of those before it. -/
def offsetIn : List (Name × Ty) → Name → Nat
  | [], _ => 0
  | (g, T) :: fs, f => if f = g then 0 else size T + offsetIn fs f

/-- Where member `f` of struct `n` starts. -/
def offset (n f : Name) : Nat := offsetIn (structDef n) f

/-- A member's rank is at most its list's: in `Person`, `account` (an `Account`, rank `2`) is at
most `fieldsRank` of `Person`'s members. -/
theorem tyRank_le_of_mem {l : List (Name × Ty)} {x : Name × Ty} (h : x ∈ l) :
    tyRank x.2 ≤ fieldsRank l := by
  induction l with
  | nil => cases h
  | cons y l ih =>
    obtain ⟨g, T⟩ := y
    simp only [fieldsRank]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- A member's type ranks below its struct: `Person.account` is an `Account`,
of rank `2`, below `Person`'s `3`. -/
theorem tyRank_member {n : Name} {x : Name × Ty} (h : x ∈ structDef n) :
    tyRank x.2 < structRank n :=
  Nat.lt_of_le_of_lt (tyRank_le_of_mem h) (structDef_rank_lt n)

/-- Two sums over the same members agree when their terms do: `size Person` computed at two
fuels. -/
theorem foldr_congr_add {l : List (Name × Ty)} {f g : Name × Ty → Nat}
    (h : ∀ x ∈ l, f x = g x) :
    l.foldr (fun x acc => f x + acc) 0 = l.foldr (fun x acc => g x + acc) 0 := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    simp only [List.foldr]
    rw [h y (List.mem_cons_self), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- Enough fuel is enough: any two fuels above `T`'s rank give its size. -/
theorem sizeF_eq : ∀ (a b : Nat) (T : Ty), tyRank T < a → tyRank T < b → sizeF a T = sizeF b T
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | a + 1, b + 1, T, ha, hb => by
    match T with
    | .prim _ | .ref (.array _) | .ref (.mapping _ _) => rfl
    | .ref (.fixed E n) =>
      simp only [sizeF, tyRank] at ha hb ⊢
      rw [sizeF_eq a b E (by omega) (by omega)]
    | .ref (.struct n) =>
      simp only [sizeF]
      apply foldr_congr_add
      intro x hx
      have := tyRank_member hx
      simp only [tyRank] at ha hb
      exact sizeF_eq a b x.2 (by omega) (by omega)

/-- A struct's size is its members' sizes added up: `size Person = size Account
+ size uint = 2 + 1`. -/
theorem size_struct (n : Name) : size (.ref (.struct n)) = sumSizes (structDef n) := by
  simp only [size, tyRank, sizeF, sumSizes]
  apply foldr_congr_add
  intro x hx
  exact sizeF_eq _ _ _ (tyRank_member hx) (Nat.lt_succ_self _)

/-- A `uint` or a `bool` takes one slot: `uint total;` is slot `0` alone. -/
@[simp] theorem size_prim (p : PrimTy) : size (.prim p) = 1 := rfl
/-- An array takes one slot, its length: `uint[] values;` is slot `4`, its elements live at
`keccak(4)`. -/
@[simp] theorem size_array (E : Ty) : size (.ref (.array E)) = 1 := rfl
/-- A mapping takes one slot, never written: `mapping(uint => uint) balances;` is slot `5`. -/
@[simp] theorem size_mapping (K : PrimTy) (V : Ty) : size (.ref (.mapping K V)) = 1 := rfl
/-- A fixed-size array takes its elements' slots, one after the other, and no
length slot: `uint[3] fixedValues;` takes three, `Token[2] fixedTokens;` two. -/
@[simp] theorem size_fixed (E : Ty) (n : Nat) : size (.ref (.fixed E n)) = n * size E := by
  simp only [size, tyRank, sizeF]

/-- A member ends within its list: its offset plus its size is at most the sum
of the sizes.

Example: in `Person` (`Account account; uint age;`) `age` starts at `2` and
takes `1` slot, and `2 + 1 ≤ 3`. -/
theorem offsetIn_bound {l : List (Name × Ty)} {f : Name} {T : Ty}
    (h : lookupBy f l = some T) : offsetIn l f + size T ≤ sumSizes l := by
  induction l with
  | nil => simp [lookupBy] at h
  | cons g l ih =>
    obtain ⟨g, Tg⟩ := g
    simp only [lookupBy] at h
    simp only [offsetIn, sumSizes, List.foldr] at ih ⊢
    by_cases hg : f = g
    · simp only [hg, if_true] at h ⊢
      cases h; omega
    · simp only [hg, if_false] at h ⊢
      have := ih h
      omega

end Solidity.Evm
