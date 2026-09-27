import Solidity.Evm.Machine
import Solidity.Semantics.Properties

/-!
# Storage layout and the compiler

## Layout (what solc does)

The contract is laid out as a struct whose fields are its state variables.
A struct occupies consecutive slots, its members in declaration order; a
`uint`, a `bool`, an array and a mapping take one slot each, a nested struct
as many as its own members.  An array's slot holds its length and element `i`
starts at `keccak256(slot) + i·size(E)`; entry `k` of a mapping starts at
`keccak256(k ‖ slot)`, and the mapping's own slot is never written.  So in
`StandardExample`, `alice` starts at slot `11` (after four `uint`s, `values`,
three mappings, `matrix`, `persons`, `people`), `alice.age` is slot `13`, and
`folks[7].age` is `keccak(7, 7) + 2`.

`size T` and `offset n f` read the struct table `structDef` with fuel: the
struct table refers to itself by name, and `tyRank` (`AST.lean`) is the
certificate that `tyRank T + 1` is enough (`size_struct`).

## The layout is injective

`Occ T s x`: slot `x` belongs to a value of type `T` laid out at `s` (a
`uint`'s own slot, an array's length slot and every element's, every entry of
a mapping).  Two different members, two different mapping keys, two
different array elements, and an array's length and its elements occupy
disjoint sets of slots (`occ_members_disjoint`, `occ_entries_disjoint`,
`occ_elems_disjoint`, `occ_len_elem`).  The proof reads a slot's ancestry:
every slot `Occ T s` names *descends* from `s` plus an offset below `size T`
(`occ_desc`), and a slot has one ancestor per depth (`desc_unique`); the rest
is the prefix-sum arithmetic of mini-solkey's `offset_disjoint`.

## The compiler

`compileVal e` leaves `e`'s value on the stack, `compileLoc l` the slot of the
location `l`.  Every Solidity guard solc emits is emitted here: a checked
`+`/`-`/`*` reverts on overflow (`binTail`), `/`/`%` on a zero divisor, an
array index out of bounds (`boundsCheck`), `pop` on an empty array, a
`transfer` the balance cannot cover; `&&`/`||`, `?:` and `if` jump.

**The fragment** is what `Stmt.wt` accepts, so a program outside it has no
claim (see `docs/compiler-verification.md` for why each exclusion):

* types: `uint` and `bool` values; storage of any shape; mappings keyed by
  `uint`.  Not `int` (signed arithmetic and its guards are not compiled);
* expressions: literals below `2^256`, locals, storage reads, the operators but
  `**` and unary minus, `?:`.  Not memory reads;
* statements: `=` of a value into storage, `=` to a local, `uint x = e;`,
  storage aliases bound to a path that indexes no array, `op=`, `x++;`/`--x;`,
  `delete` at any type, `pop`, `transfer`, `if`, `require`, `assert`,
  `revert();`.  Not storage-to-storage copies, `push`, `v = x++;`, and nothing
  in memory.

`Stmt.wt` also types the locals, as mini-solkey's does: a local lives in one
memory cell, a word for a `uint x` and a slot for a `T storage x`.
-/

namespace Solidity
namespace Evm

open Semantics

/-! ## Layout -/

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

/-- The slot of state variable `r`. -/
def rootSlot (C : Contract) (r : Name) : Slot := .root (offsetIn C.vars r)

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
@[simp] theorem size_mapping (K V : Ty) : size (.ref (.mapping K V)) = 1 := rfl
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

/-- Two different members occupy disjoint ranges of slots.

Example: in `Person`, `account` occupies `[0, 2)` and `age` `[2, 3)`; in
`StandardExample`, `alice` occupies `[11, 14)` and `bob` `[14, 17)`. -/
theorem offsetIn_disjoint {l : List (Name × Ty)} {f₁ f₂ : Name} {T₁ T₂ : Ty}
    (h₁ : lookupBy f₁ l = some T₁) (h₂ : lookupBy f₂ l = some T₂) (hne : f₁ ≠ f₂) :
    offsetIn l f₁ + size T₁ ≤ offsetIn l f₂ ∨ offsetIn l f₂ + size T₂ ≤ offsetIn l f₁ := by
  induction l with
  | nil => simp [lookupBy] at h₁
  | cons g l ih =>
    obtain ⟨g, Tg⟩ := g
    simp only [lookupBy] at h₁ h₂
    simp only [offsetIn]
    by_cases hg₁ : f₁ = g <;> by_cases hg₂ : f₂ = g
    · exact absurd (hg₁.trans hg₂.symm) hne
    · simp only [hg₁, if_true] at h₁ ⊢; cases h₁; simp [hg₂]
    · simp only [hg₂, if_true] at h₂ ⊢; cases h₂; simp [hg₁]
    · simp only [hg₁, hg₂, if_false] at h₁ h₂ ⊢
      rcases ih h₁ h₂ with h | h <;> omega

/-! ## Slots, their ancestry, and what a value occupies -/

/-- How many `keccak`s deep a slot is: `alice.age` is `0` deep, `folks[7].age`
one, `matrix[1][2]` two. -/
def Slot.depth : Slot → Nat
  | .root _ => 0
  | .hash _ s _ => s.depth + 1
  | .data s _ => s.depth + 1

/-- Adding an offset keeps the depth: `folks[7]` and `folks[7].age` are both one `keccak` deep. -/
@[simp] theorem Slot.depth_add (s : Slot) (i : Nat) : (s.add i).depth = s.depth := by
  cases s <;> rfl

/-- Adding `0` is nothing: `alice.account.balance` is `alice.account` plus `0`. -/
@[simp] theorem Slot.add_zero (s : Slot) : s.add 0 = s := by
  cases s <;> rfl

/-- Adding two offsets, one after the other, adds their sum: `bob.account` is
`bob`'s slot plus `0`, then `balance` adds `0` more. -/
theorem Slot.add_add (s : Slot) (i j : Nat) : (s.add i).add j = s.add (i + j) := by
  cases s <;> simp [Slot.add, Nat.add_assoc]

/-- Different offsets from one slot are different slots: `alice.account` (`11`) and `alice.age`
(`13`). -/
theorem Slot.add_inj {s : Slot} {i j : Nat} (h : s.add i = s.add j) : i = j := by
  cases s <;> simp_all [Slot.add]

/-- `Desc x y`: `y` is `x` or one of the slots `x` is derived from by `keccak`. -/
inductive Desc : Slot → Slot → Prop
  | refl {x : Slot} : Desc x x
  | hash {k : Nat} {s y : Slot} {o : Nat} : Desc s y → Desc (.hash k s o) y
  | data {s y : Slot} {o : Nat} : Desc s y → Desc (.data s o) y

/-- An ancestor is no deeper: `folks` (depth `0`) is an ancestor of `folks[7].age` (depth `1`). -/
theorem Desc.depth_le {x y : Slot} (h : Desc x y) : y.depth ≤ x.depth := by
  induction h with
  | refl => exact Nat.le_refl _
  | hash _ ih => simp only [Slot.depth]; omega
  | data _ ih => simp only [Slot.depth]; omega

/-- Ancestry composes: `matrix` is an ancestor of `matrix[1]`, which is one of `matrix[1][2]`. -/
theorem Desc.trans {x y z : Slot} (h₁ : Desc x y) (h₂ : Desc y z) : Desc x z := by
  induction h₁ with
  | refl => exact h₂
  | hash _ ih => exact .hash (ih h₂)
  | data _ ih => exact .data (ih h₂)

/-- A slot has one ancestor at each depth.

Example: `keccak(7, 7) + 2` (`folks[7].age`) has the ancestor `7` (`folks`) at
depth `0`, and no other slot of depth `0` is one. -/
theorem Desc.unique : ∀ {x y₁ y₂ : Slot}, Desc x y₁ → Desc x y₂ → y₁.depth = y₂.depth → y₁ = y₂
  | .root _, _, _, .refl, .refl, _ => rfl
  | .hash _ _ _, _, _, .refl, .refl, _ => rfl
  | .data _ _, _, _, .refl, .refl, _ => rfl
  | .hash _ _ _, _, _, .refl, .hash h, hd => by
    have := h.depth_le; simp only [Slot.depth] at hd; omega
  | .hash _ _ _, _, _, .hash h, .refl, hd => by
    have := h.depth_le; simp only [Slot.depth] at hd; omega
  | .data _ _, _, _, .refl, .data h, hd => by
    have := h.depth_le; simp only [Slot.depth] at hd; omega
  | .data _ _, _, _, .data h, .refl, hd => by
    have := h.depth_le; simp only [Slot.depth] at hd; omega
  | .hash _ _ _, _, _, .hash h₁, .hash h₂, hd => Desc.unique h₁ h₂ hd
  | .data _ _, _, _, .data h₁, .data h₂, hd => Desc.unique h₁ h₂ hd

/-- `Occ T s x`: slot `x` belongs to a value of type `T` laid out at `s`. -/
inductive Occ : Ty → Slot → Slot → Prop
  | prim {p : PrimTy} {s : Slot} : Occ (.prim p) s s
  | field {n f : Name} {T : Ty} {s x : Slot} :
      lookupBy f (structDef n) = some T → Occ T (s.add (offset n f)) x → Occ (.ref (.struct n)) s x
  | len {E : Ty} {s : Slot} : Occ (.ref (.array E)) s s
  | elem {E : Ty} {s x : Slot} (i : Nat) :
      Occ E (.data s (i * size E)) x → Occ (.ref (.array E)) s x
  | entry {K V : Ty} {s x : Slot} (k : Nat) : Occ V (.hash k s 0) x → Occ (.ref (.mapping K V)) s x
  | felem {E : Ty} {n : Nat} {s x : Slot} (i : Nat) :
      i < n → Occ E (s.add (i * size E)) x → Occ (.ref (.fixed E n)) s x

/-- Everything a value occupies descends from its own range of slots.

Example: `alice` (a `Person` at `11`) occupies `11`, `12` and `13`; a
`mapping(uint => Person)` at `7` occupies `keccak(k, 7) + o` for `o < 3`,
all of which descend from `7`. -/
theorem occ_desc {T : Ty} {s x : Slot} (h : Occ T s x) : ∃ o, o < size T ∧ Desc x (s.add o) := by
  induction h with
  | prim => exact ⟨0, by simp, by simpa using Desc.refl⟩
  | @field n f T s x hf _ ih =>
    obtain ⟨o, ho, hd⟩ := ih
    refine ⟨offset n f + o, ?_, by rwa [← Slot.add_add]⟩
    have := offsetIn_bound hf
    rw [size_struct]; simp only [offset]; omega
  | len => exact ⟨0, by simp, by simpa using Desc.refl⟩
  | elem i _ ih =>
    obtain ⟨o, _, hd⟩ := ih
    exact ⟨0, by simp, by simpa using hd.trans (.data .refl)⟩
  | entry k _ ih =>
    obtain ⟨o, _, hd⟩ := ih
    exact ⟨0, by simp, by simpa using hd.trans (.hash .refl)⟩
  | @felem E n s x i hi _ ih =>
    obtain ⟨o, ho, hd⟩ := ih
    refine ⟨i * size E + o, ?_, by rwa [← Slot.add_add]⟩
    rw [size_fixed]
    have : (i + 1) * size E ≤ n * size E := Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at this
    omega

/-- Two different members of a list laid out at `s` share no slot.

Example: `alice.age = 1;` writes slot `13`, which belongs to `alice.age` alone:
not to `alice.account` (slots `11`, `12`), nor to `bob` (`[14, 17)`). -/
theorem occ_members_disjoint {l : List (Name × Ty)} {s x : Slot} {f₁ f₂ : Name} {T₁ T₂ : Ty}
    (h₁ : lookupBy f₁ l = some T₁) (h₂ : lookupBy f₂ l = some T₂) (hne : f₁ ≠ f₂)
    (o₁ : Occ T₁ (s.add (offsetIn l f₁)) x) (o₂ : Occ T₂ (s.add (offsetIn l f₂)) x) : False := by
  obtain ⟨a, ha, da⟩ := occ_desc o₁
  obtain ⟨b, hb, db⟩ := occ_desc o₂
  rw [Slot.add_add] at da db
  have := Slot.add_inj (Desc.unique da db (by simp))
  have := offsetIn_disjoint h₁ h₂ hne
  omega

/-- Two entries of a mapping share no slot: `balances[1]` and `balances[2]`
are `keccak(1, 5)` and `keccak(2, 5)`. -/
theorem occ_entries_disjoint {V : Ty} {s x : Slot} {k₁ k₂ : Nat} (hne : k₁ ≠ k₂)
    (o₁ : Occ V (.hash k₁ s 0) x) (o₂ : Occ V (.hash k₂ s 0) x) : False := by
  obtain ⟨a, _, da⟩ := occ_desc o₁
  obtain ⟨b, _, db⟩ := occ_desc o₂
  have := Desc.unique da db (by simp [Slot.add, Slot.depth])
  simp [Slot.add] at this
  exact hne this.1

/-- Elements of `z` slots each start at different multiples of `z`: `persons[0].age` (`0·3 + 2`) is
not `persons[1].age` (`1·3 + 2`). -/
theorem mul_add_inj {i j z a b : Nat} (ha : a < z) (hb : b < z) (h : i * z + a = j * z + b) :
    i = j := by
  have hz : 0 < z := Nat.lt_of_le_of_lt (Nat.zero_le _) ha
  have e : ∀ c d, d < z → (c * z + d) / z = c := fun c d hd => by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hz, Nat.div_eq_of_lt hd, Nat.zero_add]
  rw [← e i a ha, ← e j b hb, h]

/-- Two elements of an array share no slot: `persons[0].age` is
`keccak(9) + 2`, `persons[1].age` `keccak(9) + 5`. -/
theorem occ_elems_disjoint {E : Ty} {s x : Slot} {i j : Nat} (hne : i ≠ j)
    (o₁ : Occ E (.data s (i * size E)) x) (o₂ : Occ E (.data s (j * size E)) x) : False := by
  obtain ⟨a, ha, da⟩ := occ_desc o₁
  obtain ⟨b, hb, db⟩ := occ_desc o₂
  have := Desc.unique da db (by simp [Slot.add, Slot.depth])
  simp only [Slot.add, Slot.data.injEq, true_and] at this
  exact hne (mul_add_inj ha hb this)

/-- Two elements of a fixed-size array share no slot: `fixedTokens[0].value`
is `fixedTokens`'s slot plus `0`, `fixedTokens[1].value` plus `1`. -/
theorem occ_felems_disjoint {E : Ty} {s x : Slot} {i j : Nat} (hne : i ≠ j)
    (o₁ : Occ E (s.add (i * size E)) x) (o₂ : Occ E (s.add (j * size E)) x) : False := by
  obtain ⟨a, ha, da⟩ := occ_desc o₁
  obtain ⟨b, hb, db⟩ := occ_desc o₂
  rw [Slot.add_add] at da db
  have := Slot.add_inj (Desc.unique da db (by simp))
  exact hne (mul_add_inj ha hb this)

/-- An array's elements never occupy its length slot: `values.pop();` writes
slot `4` and no `values[i]`. -/
theorem occ_len_elem {E : Ty} {s : Slot} {n : Nat} (o : Occ E (.data s n) s) : False := by
  obtain ⟨a, _, d⟩ := occ_desc o
  have := d.depth_le
  simp only [Slot.add, Slot.depth] at this
  omega

/-! ## What `delete` clears

`delete` resets a value to its type's default: every `uint` and `bool` to `0`,
every array to empty (its length slot to `0`), and a mapping not at all
(`SVal.defaultOf`).  So the slots to write are a static list, `leaves T`,
relative to where the value starts. -/

/-- The slots `delete` writes, relative to the value's own slot, with fuel:
every element of a fixed-size array, which keeps its length. -/
def leavesF : Nat → Ty → List Nat
  | _, .prim _ => [0]
  | _, .ref (.array _) => [0]
  | 0, .ref (.fixed _ _) => []
  | fuel + 1, .ref (.fixed E n) =>
      (List.range n).flatMap fun i => (leavesF fuel E).map (i * size E + ·)
  | _, .ref (.mapping _ _) => []
  | 0, .ref (.struct _) => []
  | fuel + 1, .ref (.struct n) => (structDef n).flatMap fun f =>
      match lookupBy f.1 (structDef n) with
      | some T => (leavesF fuel T).map (offset n f.1 + ·)
      | none => []

/-- The slots `delete` writes: `delete alice;` writes `alice`'s three, `delete
wallet;` only `wallet.owner` (its `stash` is a mapping). -/
def leaves (T : Ty) : List Nat := leavesF (tyRank T + 1) T

/-- Every slot `delete` writes belongs to the value deleted.

Example: `delete alice.account;` writes `11` and `12`, both slots of
`alice.account`, and nothing of `alice.age`. -/
theorem leavesF_occ : ∀ (fuel : Nat) (T : Ty) (s : Slot) (o : Nat), o ∈ leavesF fuel T →
    Occ T s (s.add o)
  | _, .prim _, s, o, h => by simp [leavesF] at h; subst h; simpa using Occ.prim
  | _, .ref (.array _), s, o, h => by simp [leavesF] at h; subst h; simpa using Occ.len
  | _, .ref (.mapping _ _), _, _, h => by simp [leavesF] at h
  | 0, .ref (.fixed _ _), _, _, h => by simp [leavesF] at h
  | fuel + 1, .ref (.fixed E n), s, o, h => by
    simp only [leavesF, List.mem_flatMap, List.mem_range, List.mem_map] at h
    obtain ⟨i, hi, o', ho', rfl⟩ := h
    exact Occ.felem i hi (by rw [← Slot.add_add]; exact leavesF_occ fuel E _ o' ho')
  | 0, .ref (.struct _), _, _, h => by simp [leavesF] at h
  | fuel + 1, .ref (.struct n), s, o, h => by
    simp only [leavesF, List.mem_flatMap] at h
    obtain ⟨⟨f, _⟩, _, hf⟩ := h
    simp only at hf
    split at hf
    · rename_i T hT
      obtain ⟨o', ho', rfl⟩ := List.mem_map.1 hf
      exact Occ.field hT (by rw [← Slot.add_add]; exact leavesF_occ fuel T _ o' ho')
    · cases hf

/-! ## Typing the locals -/

/-- What a local holds: a value of a primitive type, or a storage alias. -/
inductive LTy where
  | val (p : PrimTy)
  | alias (R : RefTy)
  deriving DecidableEq, Repr

/-- `Γ x = some (.val uint)`: `x` is a `uint` local; `some (.alias R)`: a
`R storage` alias; `none`: nothing the fragment may read. -/
abbrev TyCtx := Var → Option LTy

def TyCtx.set (Γ : TyCtx) (x : Var) (t : Option LTy) : TyCtx := upd Γ x t

/-- After an `if`: what both branches agree on. -/
def TyCtx.meet (Γ₁ Γ₂ : TyCtx) : TyCtx := fun x => if Γ₁ x = Γ₂ x then Γ₁ x else none

/-- The primitive types compiled: `uint` and `bool`, not `int`. -/
def primInFrag : PrimTy → Bool
  | .uint | .bool => true
  | .int => false

/-- The operators compiled at operand type `p`: all but `**`, at `uint`
(and `==`/`!=` at `bool`, `&&`/`||` at `bool`). -/
def binInFrag : BinOp → PrimTy → Bool
  | .add, p | .sub, p | .mul, p | .div, p | .mod, p => p == .uint
  | .lt, p | .gt, p | .le, p | .ge, p => p == .uint
  | .eqB, p | .neB, p => p != .int
  | .and, p | .or, p => p == .bool
  | .pow, _ => false

variable {C : Contract}

/-- A literal is a `uint` below `2^256`, a local is read at its type. -/
def wtSimple (Γ : TyCtx) : {p : PrimTy} → Simple C p → Bool
  | p, .lit n _ => p == .uint && decide (0 ≤ n) && decide (n < (W : Int))
  | _, .bool _ => true
  | p, .local x => Γ x == some (.val p)

mutual
/-- `free`: the path indexes no array (what an alias may be bound to). -/
def wtSPath (Γ : TyCtx) (free : Bool) : {T : Ty} → SPath C T → Bool
  | _, @SPath.alias _ R x => Γ x == some (.alias R)
  | _, .loc l => wtLoc Γ free l
def wtLoc (Γ : TyCtx) (free : Bool) : {T : Ty} → Loc C T → Bool
  | _, .root .. => true
  | _, .field b _ _ => wtSPath Γ free b
  | _, @Loc.index _ _ k _ .map b i => k == .uint && wtSPath Γ free b && wtVal Γ i
  | _, .index (.arr .dyn) b i => !free && wtSPath Γ free b && wtVal Γ i
  | _, .index (.arr .fixed) b i => !free && wtSPath Γ free b && wtVal Γ i
def wtVal (Γ : TyCtx) : {p : PrimTy} → Val C p → Bool
  | _, .simple s => wtSimple Γ s
  | p, .read l => primInFrag p && wtLoc Γ false l
  | _, @Val.binop _ p _ op _ _ a b => binInFrag op p && wtVal Γ a && wtVal Γ b
  | _, .unop op _ _ a => op == .not && wtVal Γ a
  | p, .ternary c a b => primInFrag p && wtVal Γ c && wtVal Γ a && wtVal Γ b
  | _, .readMem _ | _, .len .. | _, .mlen .. => false
end

/-- The storage location an `op=` target names, if it is one. -/
def opLocToLoc : {p : PrimTy} → OpLoc C p → Option (Loc C (.prim p))
  | _, .root r h => some (.root r h)
  | _, .field b f h => some (.field b f h)
  | _, .index it b i => some (.index it b (.simple i))
  | _, .local _ | _, .mfield .. | _, .mindex .. => none

def wtOpLoc (Γ : TyCtx) : {p : PrimTy} → OpLoc C p → Bool
  | p, .local x => Γ x == some (.val p)
  | _, l => match opLocToLoc l with
    | some loc => wtLoc Γ false loc
    | none => false

mutual
/-- A statement of the fragment, and the context it leaves. -/
def wtStmt (Γ : TyCtx) : Stmt C → Option TyCtx
  | @Stmt.assign _ (.prim p) l (.val v) =>
    if primInFrag p && wtLoc Γ false l && wtVal Γ v then some Γ else none
  | @Stmt.rebind _ R x (.path q) =>
    if wtSPath Γ true q then some (Γ.set x (some (.alias R))) else none
  | @Stmt.assignLocal _ p x r => if Γ x == some (.val p) && wtVal Γ r then some Γ else none
  | .declLocal p x none => if primInFrag p then some (Γ.set x (some (.val p))) else none
  | .declLocal p x (some e) =>
    if primInFrag p && wtVal Γ e then some (Γ.set x (some (.val p))) else none
  | .declStorage _ x none => some (Γ.set x none)
  | .declStorage R x (some (.path q)) =>
    if wtSPath Γ true q then some (Γ.set x (some (.alias R))) else none
  | @Stmt.opAssign _ p _ _ _ l r => if p == .uint && wtOpLoc Γ l && wtVal Γ r then some Γ else none
  | @Stmt.incDec _ p _ _ l => if p == .uint && wtOpLoc Γ l then some Γ else none
  | .pop b => if wtSPath Γ false b then some Γ else none
  | .transfer r a => if wtVal Γ r && wtVal Γ a then some Γ else none
  | .delete l => if wtLoc Γ false l then some Γ else none
  | .ite c t e =>
    if wtVal Γ c then
      match wtProg Γ t, wtProg Γ e with
      | some Γ₁, some Γ₂ => some (Γ₁.meet Γ₂)
      | _, _ => none
    else none
  | .require c | .assert c => if wtVal Γ c then some Γ else none
  | .revert => some Γ
  | _ => none
def wtProg (Γ : TyCtx) : List (Stmt C) → Option TyCtx
  | [] => some Γ
  | s :: P => match wtStmt Γ s with
    | some Γ' => wtProg Γ' P
    | none => none
end

/-! ## The compiler -/

/-- `JUMPI +1; REVERT`: go on if the top word is non-zero, else revert. -/
def assertTop : List Instr := [.jumpi 1, .revert]

/-- With `… s i` on the stack (`i` on top), revert unless `i` is below the
length stored at `s` (solc's `Panic(0x32)`). -/
def boundsCheck : List Instr := [.dup 2, .sload, .dup 2, .lt] ++ assertTop

/-- `… s i → … s i`, reverting unless `i < n`: a fixed-size array's bound is
its type's, a constant. -/
def fixedCheck (n : Nat) : List Instr := [.push (.val n), .dup 2, .lt] ++ assertTop

/-- `z` times `DUP2; ADD`. -/
def addRep : Nat → List Instr
  | 0 => []
  | z + 1 => [.dup 2, .add] ++ addRep z

/-- `… s i → … keccak256(s) + i·z`: element `i` of the array at `s`, whose
elements take `z` slots.  The multiplication is `z` additions to a slot, which
does not wrap (slots are terms, as in mini-solkey). -/
def elemSlot (z : Nat) : List Instr := [.swap 1, .keccakArr] ++ addRep z ++ [.swap 1, .pop]

/-- `… s i → … s + i·z`: element `i` of the fixed-size array laid out inline
from `s`, whose elements take `z` slots. -/
def fixedSlot (z : Nat) : List Instr := [.swap 1] ++ addRep z ++ [.swap 1, .pop]

/-- `… a b → … a ⊕ b` (`b` on top), with solc's guards: `+` reverts when the
sum wraps below `a`, `-` when `b > a`, `*` when `a ≠ 0` and the product
divided by `a` is not `b`, `/` and `%` on a zero divisor. -/
def binTail : BinOp → List Instr
  | .add => [.dup 2, .add, .dup 1, .dup 3, .gt, .iszero] ++ assertTop ++ [.swap 1, .pop]
  | .sub => [.dup 2, .dup 2, .gt, .iszero] ++ assertTop ++ [.swap 1, .sub]
  | .mul => [.dup 2, .dup 2, .mul, .dup 3, .dup 2, .div, .dup 3, .eq, .dup 4, .iszero, .or] ++
      assertTop ++ [.swap 2, .pop, .pop]
  | .div => [.dup 1] ++ assertTop ++ [.swap 1, .div]
  | .mod => [.dup 1] ++ assertTop ++ [.swap 1, .mod]
  | .lt => [.gt]
  | .gt => [.lt]
  | .le => [.lt, .iszero]
  | .ge => [.gt, .iszero]
  | .eqB => [.eq]
  | .neB => [.eq, .iszero]
  | .pow | .and | .or => []

def compileSimple : {p : PrimTy} → Simple C p → List Instr
  | _, .lit n _ => [.push (.val n.toNat)]
  | _, .bool b => [.push (.val (bword b))]
  | _, .local x => [.mload x]

mutual
/-- Push the slot a storage path names. -/
def compileSPath : {T : Ty} → SPath C T → List Instr
  | _, .alias x => [.mload x]
  | _, .loc l => compileLoc l
/-- Push the slot of a location. -/
def compileLoc : {T : Ty} → Loc C T → List Instr
  | _, .root r _ => [.push (.slot (rootSlot C r))]
  | _, @Loc.field _ s _ b f _ => compileSPath b ++ [.push (.val (offset s f)), .add]
  | _, .index .map b i => compileSPath b ++ compileVal i ++ [.keccakMap]
  | _, @Loc.index _ _ _ E (.arr .dyn) b i =>
    compileSPath b ++ compileVal i ++ boundsCheck ++ elemSlot (size E)
  | _, @Loc.index _ _ _ E (@IndexTy.arr _ _ (@ArrTy.fixed _ n)) b i =>
    compileSPath b ++ compileVal i ++ fixedCheck n ++ fixedSlot (size E)
/-- Push the value of an expression. -/
def compileVal : {p : PrimTy} → Val C p → List Instr
  | _, .simple s => compileSimple s
  | _, .read l => compileLoc l ++ [.sload]
  | _, .binop op _ _ a b =>
    match op with
    | .and => compileVal a ++ [.dup 1, .iszero, .jumpi ((compileVal b).length + 1), .pop] ++
        compileVal b
    | .or => compileVal a ++ [.dup 1, .jumpi ((compileVal b).length + 1), .pop] ++ compileVal b
    | op => compileVal a ++ compileVal b ++ binTail op
  | _, .unop _ _ _ a => compileVal a ++ [.iszero]
  | _, .ternary c a b =>
    compileVal c ++ [.iszero, .jumpi ((compileVal a).length + 1)] ++ compileVal a ++
      [.jump (compileVal b).length] ++ compileVal b
  | _, .readMem _ | _, .len .. | _, .mlen .. => []
end

/-- `… s → … s` with `0` written at `s + o` for each `o`. -/
def zeroCode (os : List Nat) : List Instr :=
  os.flatMap fun o => [.push (.val 0), .dup 2, .push (.val o), .add, .sstore]

/-- `… s → …`: the length at `s` decremented, reverting at `0` (solc's
`Panic(0x31)`). -/
def popCode : List Instr :=
  [.dup 1, .sload, .dup 1] ++ assertTop ++ [.push (.val 1), .swap 1, .sub, .swap 1, .sstore]

mutual
/-- The code of a statement; `[]` outside the fragment (which `wtStmt` rejects). -/
def compileStmt : Stmt C → List Instr
  | .assign l (.val v) => compileVal v ++ compileLoc l ++ [.sstore]
  | .rebind x (.path q) => compileSPath q ++ [.mstore x]
  | .assignLocal x r => compileVal r ++ [.mstore x]
  | .declLocal _ x none => [.push (.val 0), .mstore x]
  | .declLocal _ x (some e) => compileVal e ++ [.mstore x]
  | .declStorage _ x (some (.path q)) => compileSPath q ++ [.mstore x]
  | .opAssign op _ _ (.local x) r => [.mload x] ++ compileVal r ++ binTail op ++ [.mstore x]
  | .opAssign op _ _ l r => match opLocToLoc l with
    | some loc =>
      compileLoc loc ++ [.dup 1, .sload] ++ compileVal r ++ binTail op ++ [.swap 1, .sstore]
    | none => []
  | .incDec op _ (.local x) => [.mload x, .push (.val 1)] ++ binTail op.binOp ++ [.mstore x]
  | .incDec op _ l => match opLocToLoc l with
    | some loc =>
      compileLoc loc ++ [.dup 1, .sload, .push (.val 1)] ++ binTail op.binOp ++ [.swap 1, .sstore]
    | none => []
  | .pop b => compileSPath b ++ popCode
  | .transfer r a => compileVal r ++ compileVal a ++ [.call] ++ assertTop
  | @Stmt.delete _ T l => compileLoc l ++ zeroCode (leaves T) ++ [.pop]
  | .ite c t e =>
    compileVal c ++ [.iszero, .jumpi ((compileProg t).length + 1)] ++ compileProg t ++
      [.jump (compileProg e).length] ++ compileProg e
  | .require c | .assert c => compileVal c ++ assertTop
  | .revert => [.revert]
  | _ => []
/-- The code of a block: its statements' codes in order. -/
def compileProg : List (Stmt C) → List Instr
  | [] => []
  | s :: P => compileStmt s ++ compileProg P
end

end Evm
end Solidity
