import Solidity.Backend.Scalar.Slice

/-! Compositional successful stack-height laws for every admitted instruction,
including all DUP/SWAP indices. These are mathematical effects, not a waiver
of the eventual EVM's 1024-word prefix capacity obligation. -/
namespace Solidity.Backend.Scalar

def numericDelta (o : Op) : Int :=
  if (unary o).isSome then 0 else if (binary o).isSome then -1
  else if (ternary o).isSome then -2 else 0

def stackDelta : Instr → Int
  | .push .. => 1
  | .op (.DUP _) => 1
  | .op (.SWAP _) => 0
  | .op .POP => -1
  | .op o => numericDelta o

theorem duplicate_length (n : Nat) {s t : Stack} (h : duplicate n s = some t) :
    t.length = s.length + 1 := by
  cases hh : s[n]? with
  | none => simp only [duplicate, hh, Option.map_none, reduceCtorEq] at h
  | some a =>
    simp only [duplicate, hh, Option.map_some, Option.some.injEq] at h
    subst t
    rfl

theorem exchange_length (a : Word) (n : Nat) {s t : Stack} {b : Word}
    (h : exchange a n s = some (b, t)) : t.length = s.length := by
  induction n generalizing s t with
  | zero =>
    cases s with
    | nil => cases h
    | cons x s => cases h; rfl
  | succ n ih =>
    cases s with
    | nil => cases h
    | cons x s =>
      obtain ⟨⟨y, ys⟩, hh, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      rcases he with ⟨rfl, rfl⟩
      exact congrArg Nat.succ (ih hh)

theorem swap_length (n : Nat) {s t : Stack} (h : swap n s = some t) :
    t.length = s.length := by
  cases s with
  | nil => cases h
  | cons a s =>
    obtain ⟨⟨b, bs⟩, hh, he⟩ := Option.map_eq_some_iff.mp h
    subst t
    exact congrArg Nat.succ (exchange_length a n hh)

theorem applyUnary_length (f : Word → Word) {s t : Stack}
    (h : applyUnary f s = some t) : t.length = s.length := by
  cases s with
  | nil => cases h
  | cons a s => cases h; rfl

theorem applyBinary_length (f : Word → Word → Word) {s t : Stack}
    (h : applyBinary f s = some t) : t.length + 1 = s.length := by
  cases s with
  | nil => cases h
  | cons a s =>
    cases s with
    | nil => cases h
    | cons b s => cases h; rfl

theorem applyTernary_length (f : Word → Word → Word → Word) {s t : Stack}
    (h : applyTernary f s = some t) : t.length + 2 = s.length := by
  cases s with
  | nil => cases h
  | cons a s =>
    cases s with
    | nil => cases h
    | cons b s =>
      cases s with
      | nil => cases h
      | cons k s => cases h; rfl

theorem numericStep_height {o : Op} {s t : Stack} (h : numericStep o s = some t) :
    (t.length : Int) = (s.length : Int) + numericDelta o := by
  cases hu : unary o with
  | some f =>
    simp only [numericStep, hu] at h
    simp only [numericDelta, hu, Option.isSome_some, if_true, Int.add_zero]
    exact congrArg Int.ofNat (applyUnary_length f h)
  | none =>
    cases hb : binary o with
    | some f =>
      simp only [numericStep, hu, hb] at h
      simp only [numericDelta, hu, hb, Option.isSome_none, Option.isSome_some,
        Bool.false_eq_true, if_true, if_false]
      have hl := applyBinary_length f h
      omega
    | none =>
      cases ht : ternary o with
      | some f =>
        simp only [numericStep, hu, hb, ht] at h
        simp only [numericDelta, hu, hb, ht, Option.isSome_none, Option.isSome_some,
          Bool.false_eq_true, if_true, if_false]
        have hl := applyTernary_length f h
        omega
      | none => simp only [numericStep, hu, hb, ht, reduceCtorEq] at h

theorem step_height {i : Instr} {s t : Stack} (h : step i s = some t) :
    (t.length : Int) = (s.length : Int) + stackDelta i := by
  cases i with
  | push n bs =>
    cases h
    simp only [List.length_cons, stackDelta, Int.natCast_add, Int.natCast_one]
  | op o =>
    cases o <;> simp only [step, stackDelta] at h ⊢
    case DUP n =>
      have hl := duplicate_length n.val h
      omega
    case SWAP n =>
      have hl := swap_length n.val h
      omega
    case POP =>
      cases s with
      | nil => cases h
      | cons a s => cases h; simp only [List.length_cons, Int.natCast_add, Int.natCast_one]; omega
    all_goals exact numericStep_height h

/-- The height difference of a successful slice is the sum of its opcode effects. -/
theorem run_height {p : Program} {s t : Stack} (h : run p s = some t) :
    (t.length : Int) = (s.length : Int) + (p.map stackDelta).sum := by
  induction p generalizing s with
  | nil => cases h; simp only [List.map_nil, List.sum_nil, Int.add_zero]
  | cons i p ih =>
    cases hs : step i s with
    | none => simp only [run, hs, Option.bind_none, reduceCtorEq] at h
    | some u =>
      simp only [run, hs, Option.bind_some] at h
      have hi := step_height hs
      have hp := ih h
      simp only [List.map_cons, List.sum_cons]
      omega

/-- Heights at every instruction boundary, including entry and exit. -/
def heightTrace : Program → Int → List Int
  | [], h => [h]
  | i :: p, h => h :: heightTrace p (h + stackDelta i)

def safeHeight (h : Int) : Bool := decide (0 ≤ h ∧ h ≤ 1024)

/-- Executable capacity witness. Successful operand/tail contracts separately
establish that DUP/SWAP have their required positions; this tests heights only. -/
def stackBound (p : Program) (h : Int) : Bool := (heightTrace p h).all safeHeight

theorem stackBound_prefix (p q : Program) (h : Int)
    (hb : stackBound (p ++ q) h = true) : stackBound p h = true := by
  induction p generalizing h with
  | nil =>
    cases q with
    | nil => exact hb
    | cons i q =>
      simp only [stackBound, List.nil_append, heightTrace, List.all_cons,
        Bool.and_eq_true] at hb
      simp only [stackBound, heightTrace, List.all_cons, List.all_nil, Bool.and_true]
      exact hb.1
  | cons i p ih =>
    simp only [List.cons_append, stackBound, heightTrace, List.all_cons,
      Bool.and_eq_true] at hb ⊢
    exact ⟨hb.1, ih (h + stackDelta i) hb.2⟩

/-- A checked successful slice finishes within Osaka's physical stack capacity. -/
theorem run_capacity {p : Program} {s t : Stack} (hr : run p s = some t)
    (hb : stackBound p (s.length : Int) = true) : t.length ≤ 1024 := by
  induction p generalizing s with
  | nil =>
    cases hr
    simp only [stackBound, heightTrace, List.all_cons, List.all_nil, Bool.and_true,
      safeHeight, decide_eq_true_eq] at hb
    omega
  | cons i p ih =>
    simp only [stackBound, heightTrace, List.all_cons, Bool.and_eq_true] at hb
    cases hs : step i s with
    | none => simp only [run, hs, Option.bind_none, reduceCtorEq] at hr
    | some u =>
      simp only [run, hs, Option.bind_some] at hr
      have hi := step_height hs
      apply ih hr
      change (heightTrace p (u.length : Int)).all safeHeight = true
      rw [hi]
      exact hb.2

/-- Every successful prefix is capacity-safe, not merely the final stack. -/
theorem prefix_capacity (p q : Program) {s u : Stack}
    (hr : run p s = some u) (hb : stackBound (p ++ q) (s.length : Int) = true) :
    u.length ≤ 1024 :=
  run_capacity hr (stackBound_prefix p q _ hb)

/-- Positive and negative capacity controls preserve the real 1024-word limit. -/
example : stackBound [.op (.DUP ⟨0, by decide⟩)] 1023 = true := by decide +kernel
example : stackBound [.op (.DUP ⟨0, by decide⟩)] 1024 = false := by decide +kernel

#print axioms run_capacity
#print axioms prefix_capacity

#print axioms step_height
#print axioms run_height

end Solidity.Backend.Scalar
