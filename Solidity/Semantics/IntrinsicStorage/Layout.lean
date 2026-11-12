import Solidity.Semantics.Storage.Ops
import Solidity.Storage.HashedKeccak

/-! Typed full-word layout for the actual dependent storage paths.
The size calculation follows Evm/Layout without importing the target semantics.
Symbolic locations and encoded hash inputs remain separate. -/
namespace Solidity.Semantics.IntrinsicStorage

open Solidity.Storage
/-- The existing primitive ABI word, converted explicitly to a natural. -/
def keyWord {p : PrimTy} (k : p.Denote) : Nat := (PrimTy.toWord k).val.toNat

theorem keyWord_lt {p : PrimTy} (k : p.Denote) : keyWord k < 2 ^ 256 := by
  have h : PrimTy.inRange .uint (PrimTy.toWord k).val = true := (PrimTy.toWord k).property
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  unfold keyWord
  omega

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
  simpa only [List.foldr_map] using
    congrArg (List.foldr Nat.add 0) (List.map_congr_left h)

/-- Enough fuel is enough: any two fuels above `T`'s rank give its size. -/
theorem sizeF_eq : ∀ (a b : Nat) (T : Ty), tyRank T < a → tyRank T < b → sizeF a T = sizeF b T
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | a + 1, b + 1, T, ha, hb => by
    match T with
    | .prim _ | .ref (.array _) | .ref (.mapping _ _) => rfl
    | .ref (.fixed E n) =>
      exact congrArg (n * ·) (sizeF_eq a b E
        (Nat.lt_of_succ_lt_succ ha) (Nat.lt_of_succ_lt_succ hb))
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
  exact foldr_congr_add fun x hx =>
    sizeF_eq _ _ _ (tyRank_member hx) (Nat.lt_succ_self _)

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


/-- Interpret only intrinsically well-typed paths; no erased selector lookup. -/
noncomputable def locate {T U : Ty} (p : Path T U) : Storage.Loc → Storage.Loc :=
  @Path.rec (fun _ _ _ => Storage.Loc → Storage.Loc)
    (fun {_} l => l)
    (fun {s f _ _} _ _ ih l => ih (l.add (offset s f)))
    (fun {E _} i _ ih l => ih (.data l (i.val.toNat * size E)))
    (fun {E _ _} i _ ih l => ih (l.add (i.val.toNat * size E)))
    (fun {_ _ _} k _ ih l => ih (.hash (keyWord k) l 0)) T U p

/-- Hash inputs include the entire nested ancestry, in evaluation order. -/
def ancestry (l : Storage.Loc) : List Pre := l.pres (2 ^ 256) keccakH

theorem locate_append {T U V : Ty} (p : Path T U) (q : Path U V) (l : Storage.Loc) :
    locate (p.append q) l = locate q (locate p l) := by
  induction p generalizing l with
  | nil => rw [Path.append_nil]; rfl
  | field h p ih => rw [Path.append_field]; exact ih q _
  | «at» i p ih => rw [Path.append_at]; exact ih q _
  | atF i p ih => rw [Path.append_atF]; exact ih q _
  | key k p ih => rw [Path.append_key]; exact ih q _

theorem ancestry_add (l : Storage.Loc) (i : Nat) : ancestry (l.add i) = ancestry l :=
  Storage.Loc.pres_add _ _ _ _

theorem ancestry_locate {T U : Ty} (p : Path T U) (l : Storage.Loc) :
    ancestry l <+: ancestry (locate p l) := by
  induction p generalizing l with
  | nil => exact List.prefix_refl _
  | field h p ih => simpa only [locate, ancestry_add] using ih (l.add (offset _ _))
  | «at» i p ih =>
    exact List.IsPrefix.trans (List.prefix_append _ _) (ih (.data l (i.val.toNat * size _)))
  | atF i p ih => simpa only [locate, ancestry_add] using ih (l.add (i.val.toNat * size _))
  | key k p ih =>
    exact List.IsPrefix.trans (List.prefix_append _ _) (ih (.hash (keyWord k) l 0))

/-- Every ancestry item has bounded word components; this is not hash injectivity. -/
def BoundedKeys : Storage.Loc → Prop
  | .root _ => True
  | .hash k l _ => k < 2 ^ 256 ∧ BoundedKeys l
  | .data l _ => BoundedKeys l

theorem boundedKeys_add (l : Storage.Loc) (i : Nat) :
    BoundedKeys (l.add i) = BoundedKeys l := by cases l <;> rfl

theorem boundedKeys_locate {T U : Ty} (p : Path T U) (l : Storage.Loc)
    (h : BoundedKeys l) : BoundedKeys (locate p l) := by
  induction p generalizing l with
  | nil => exact h
  | field hf p ih => exact ih _ (by rwa [boundedKeys_add])
  | «at» i p ih => exact ih _ h
  | atF i p ih => exact ih _ (by rwa [boundedKeys_add])
  | key k p ih => exact ih _ ⟨keyWord_lt k, h⟩

theorem word_lt (l : Storage.Loc) : l.word (2 ^ 256) keccakH < 2 ^ 256 := by
  cases l <;> exact Nat.mod_lt _ (by decide)

theorem ancestry_words (l : Storage.Loc) (h : BoundedKeys l) :
    ∀ p ∈ ancestry l, p.Words := by
  induction l with
  | root o => simp [ancestry, Storage.Loc.pres]
  | hash k l o ih =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ih h.2 p hp
    · have e := List.mem_singleton.mp hp
      subst p
      exact ⟨h.1, word_lt l⟩
  | data l o ih =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ih h p hp
    · have e := List.mem_singleton.mp hp
      subst p
      exact word_lt l

/-- A reference starts at the actual contract variable's full-word offset. -/
noncomputable def reference {C : Contract} {T : Ty} (r : SRef C T) : Storage.Loc :=
  locate r.path (.root (offsetIn C.vars r.root))

theorem reference_bounded {C : Contract} {T : Ty} (r : SRef C T) :
    BoundedKeys (reference r) := boundedKeys_locate r.path _ True.intro

/-- Explicit conversion from the layout's natural bytes to runtime bytes. -/
def encoded (p : Pre) : List UInt8 := (Storage.encode p).map UInt8.ofNat

theorem bytesBE_bound (n v : Nat) : ∀ b ∈ bytesBE n v, b < 256 := by
  induction n generalizing v with
  | zero => simp [bytesBE]
  | succ n ih =>
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact ih _ b hb
    · have e := List.mem_singleton.mp hb
      subst b
      exact Nat.mod_lt _ (by decide)

theorem encode_bound (p : Pre) : ∀ b ∈ Storage.encode p, b < 256 := by
  cases p with
  | data w => exact bytesBE_bound 32 w
  | entry k w =>
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact bytesBE_bound 32 k b hb
    · exact bytesBE_bound 32 w b hb

theorem encoded_toNat (p : Pre) : (encoded p).map UInt8.toNat = Storage.encode p := by
  unfold encoded
  rw [List.map_map]
  calc
    _ = (Storage.encode p).map id := List.map_congr_left
      (fun b hb => UInt8.toNat_ofNat_of_lt' (encode_bound p b hb))
    _ = _ := List.map_id _

theorem encoded_inj {p q : Pre} (hp : p.Words) (hq : q.Words)
    (h : encoded p = encoded q) : p = q := by
  apply Storage.encode_inj hp hq
  have e := congrArg (List.map UInt8.toNat) h
  simpa only [encoded_toNat] using e


end Solidity.Semantics.IntrinsicStorage
