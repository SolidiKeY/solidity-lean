import Solidity.Calculus.KIntBinder

/-! Finite typed ledger witnesses for pure partial UInt call functions.
The full-domain list is a logical witness, never enumerated by tools. This
prerequisite alone does not compress a call-family leaf or prove a source call.
-/
namespace Solidity.CallFunctionTable
open Semantics
abbrev Key := PrimTy.uint.Denote

/-- Finite prefix of a typed total graph; newest keys are first. -/
private noncomputable def entries (f : Key → Int) : Nat → Ledger
  | 0 => []
  | n+1 => (uintOfNat n, f (uintOfNat n)) :: entries f n

private theorem entries_length (f : Key → Int) (n : Nat) : (entries f n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

private theorem lookup_entries (f : Key → Int) (n : Nat) (hn : n ≤ 2^256)
    (k : Nat) (hk : k < n) :
    lookupBy (uintOfNat k) (entries f n) = some (f (uintOfNat k)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : k = n
    · subst k
      simp only [entries, lookupBy, if_true]
    · have hkn : k < n := by omega
      have hne : uintOfNat k ≠ uintOfNat n := by
        intro he
        exact h (zAddr_inj (by omega) (by omega) he)
      simp only [entries, lookupBy, hne, if_false]
      exact ih (by omega) hkn

/-- Every typed UInt key is covered; this proves existence, not feasible allocation. -/
theorem realize (f : Key → Int) : ∃ L : Ledger, ∀ x : Key, L.at x = f x := by
  refine ⟨entries f (2^256), ?_⟩
  intro x
  have hx : 0 ≤ x.val ∧ x.val < ((2^256 : Nat) : Int) := by
    have h : PrimTy.inRange .uint x.val = true := x.property
    simp only [PrimTy.inRange, decide_eq_true_eq] at h
    exact h
  have hk : x.val.toNat < 2^256 := by omega
  have he : uintOfNat x.val.toNat = x := by
    apply Subtype.ext
    rw [uintOfNat_val hk]
    omega
  have hl : lookupBy (uintOfNat x.val.toNat) (entries f (2^256)) =
      some (f (uintOfNat x.val.toNat)) :=
    lookup_entries f (2^256) (Nat.le_refl _) x.val.toNat hk
  rw [he] at hl
  show (lookupBy x (entries f (2^256))).getD 0 = f x
  rw [hl]
  rfl

/-- Minus one is distinct from every returning UInt, retaining failure. -/
def encode : Option Key → Int
  | none => -1
  | some x => x.val

def Represents (L : Ledger) (f : Key → Option Key) : Prop :=
  ∀ x : Key, L.at x = encode (f x)

theorem exists_represents (f : Key → Option Key) : ∃ L : Ledger, Represents L f :=
  realize (fun x => encode (f x))

theorem encode_injective : Function.Injective encode := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      have hb : 0 ≤ b.val := by
        have hr : PrimTy.inRange .uint b.val = true := b.property
        simp only [PrimTy.inRange, decide_eq_true_eq] at hr
        exact hr.1
      change (-1 : Int) = b.val at h
      omega
  | some a =>
    cases b with
    | none =>
      have ha : 0 ≤ a.val := by
        have hr : PrimTy.inRange .uint a.val = true := a.property
        simp only [PrimTy.inRange, decide_eq_true_eq] at hr
        exact hr.1
      change a.val = (-1 : Int) at h
      omega
    | some b => exact congrArg some (Subtype.ext h)

theorem returns_iff {L : Ledger} {f : Key → Option Key}
    (h : Represents L f) (x y : Key) : L.at x = y.val ↔ f x = some y := by
  constructor
  · intro he
    exact encode_injective ((h x).symm.trans he)
  · intro he
    rw [h x, he]
    rfl

theorem failure_iff {L : Ledger} {f : Key → Option Key}
    (h : Represents L f) (x : Key) : L.at x = -1 ↔ f x = none := by
  constructor
  · intro he
    exact encode_injective ((h x).symm.trans he)
  · intro he
    rw [h x, he]
    rfl

/-- First read a returning argument, then read the second table at that value.
The first failure is propagated before the second lookup. This is a semantic
composition invariant, not yet an intrinsic leaf or a source-call theorem. -/
def Composes (first second next : Ledger) : Prop :=
  ∀ x : Key, (first.at x = -1 → next.at x = -1) ∧
    ∀ r : Key, first.at x = r.val → next.at x = second.at r

abbrev Squares (previous next : Ledger) : Prop := Composes previous previous next

theorem composes_iff {first second next : Ledger} {f g : Key → Option Key}
    (hp : Represents first f) (hq : Represents second g) :
    Composes first second next ↔ Represents next (fun x => (f x).bind g) := by
  constructor
  · intro hs x
    change next.at x = encode ((f x).bind g)
    cases hx : f x with
    | none =>
      have he : first.at x = -1 := (failure_iff hp x).mpr hx
      have hn : next.at x = -1 := (hs x).1 he
      exact hn
    | some r =>
      have he : first.at x = r.val := (returns_iff hp x r).mpr hx
      have hn : next.at x = second.at r := (hs x).2 r he
      exact hn.trans (hq r)
  · intro hn x
    constructor
    · intro he
      have hx : f x = none := (failure_iff hp x).mp he
      simpa only [hx, Option.bind_none, encode] using hn x
    · intro r he
      have hx : f x = some r := (returns_iff hp x r).mp he
      simpa only [hx, Option.bind_some, hq r] using hn x

theorem squares_iff {previous next : Ledger} {f : Key → Option Key}
    (hp : Represents previous f) :
    Squares previous next ↔ Represents next (fun x => (f x).bind f) :=
  composes_iff hp hp

end Solidity.CallFunctionTable
