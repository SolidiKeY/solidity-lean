import Lean
import Solidity.Calculus.VisitedSet

/-!
# Complete decision of linear equations and inequalities over naturals

Local adaptation of mini-solkey's Chapter 19 binary-derivative algorithm.
A derivative reads one low bit of every variable; the reachable formulas
have a finite, proved universe. Validity is equivalent to every reachable
formula holding at zero. Search exhaustion is proved impossible at the
computed bound, so a negative answer is semantic falsity, not failure of a
bounded proof tactic.

This arithmetic intermediate language is separate from Solidity's typed
leaf language. Its later translation must retain range checks, definedness
and alias constraints; this module alone makes no Solidity validity claim.
There are no external dependencies.
-/

namespace Solidity.Linear

/-! ## Linear forms -/

/-- `a₀·x₀ + a₁·x₁ + …`: the coefficient of the variable `xᵢ` at position `i`. -/
abbrev Lin := List Int

/-- The variables moved down by one: `x₁, x₂, …` become `x₀, x₁, …`. -/
def shift (x : Nat → Nat) : Nat → Nat := fun i => x (i + 1)

/-- The value of a linear form. -/
def Lin.eval : Lin → (Nat → Nat) → Int
  | [], _ => 0
  | a :: as, x => a * x 0 + Lin.eval as (shift x)

/-- The low bits of the first `n` variables. -/
def lowBits : Nat → (Nat → Nat) → List Bool
  | 0, _ => []
  | n + 1, x => (x 0 % 2 == 1) :: lowBits n (shift x)

/-- Every variable halved: its low bit dropped. -/
def halve (x : Nat → Nat) : Nat → Nat := fun i => x i / 2

/-- The form at a choice of bits: the coefficients whose bit is set, summed. -/
def Lin.dotBits : Lin → List Bool → Int
  | a :: as, b :: bs => (if b then a else 0) + Lin.dotBits as bs
  | _, _ => 0

/-- **A form splits at the low bits**: its value is its value at the bits plus
twice its value at the halved variables.

Example: `balances[a] + 2·balances[b]` with the reads `5` and `2` is `9`:
`1 + 2·0` at the low bits `1, 0`, plus twice `2 + 2·1`, its value at `2, 1`. -/
theorem Lin.eval_split : ∀ (as : Lin) (n : Nat) (x : Nat → Nat), as.length ≤ n →
    as.eval x = as.dotBits (lowBits n x) + 2 * as.eval (halve x)
  | [], _, _, _ => by simp only [eval, dotBits, Int.mul_zero, Int.add_zero]
  | _ :: _, 0, _, h => by simp only [List.length_cons, Nat.le_zero_eq, Nat.add_eq_zero, List.length_eq_zero_iff, Nat.succ_ne_self, and_false] at h
  | a :: as, n + 1, x, h => by
    have ih := Lin.eval_split as n (shift x) (by simp only [List.length_cons, Nat.add_le_add_iff_right] at h; omega)
    have hs : shift (halve x) = halve (shift x) := rfl
    simp only [Lin.eval, lowBits, Lin.dotBits, hs, ih, halve]
    have hx : ((x 0 : Nat) : Int) = 2 * ((x 0 / 2 : Nat) : Int) + ((x 0 % 2 : Nat) : Int) := by omega
    rw [hx]
    rcases Nat.mod_two_eq_zero_or_one (x 0) with h0 | h0 <;> simp only [Int.natCast_ediv, Int.cast_ofNat_Int, h0, Int.add_zero, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, Int.zero_add, BEq.rfl] <;> grind

/-! ## Formulas -/

/-- Linear arithmetic over `Nat`: equations `a·x = c` and inequalities `a·x ≤ c` under the connectives.
`ff` is an equation found false. -/
inductive AFml where
  | tt
  | ff
  | eq (a : Lin) (c : Int)          -- `a·x = c`
  | le (a : Lin) (c : Int)          -- `a·x ≤ c`
  | not (φ : AFml)
  | and (φ ψ : AFml)
  | imp (φ ψ : AFml)
  deriving DecidableEq, Repr, Inhabited

/-- A formula holds at a choice of the variables. -/
def AFml.holds (x : Nat → Nat) : AFml → Prop
  | .tt => True
  | .ff => False
  | .eq a c => a.eval x = c
  | .le a c => a.eval x ≤ c
  | .not φ => ¬ φ.holds x
  | .and φ ψ => φ.holds x ∧ ψ.holds x
  | .imp φ ψ => φ.holds x → ψ.holds x

/-- Fml.Valid: true at every choice of the variables. -/
def AFml.Valid (φ : AFml) : Prop := ∀ x, φ.holds x

/-- How many variables the formula reads: its longest form. -/
def AFml.width : AFml → Nat
  | .eq a _ | .le a _ => a.length
  | .not φ => φ.width
  | .and φ ψ | .imp φ ψ => max φ.width ψ.width
  | _ => 0

/-- `¬φ`, with `¬true` and `¬false` worked out. -/
def AFml.mkNot : AFml → AFml
  | .tt => .ff
  | .ff => .tt
  | φ => .not φ

/-- `φ ∧ ψ`, with `false ∧ _`, `_ ∧ false` and `true ∧ true` worked out. -/
def AFml.mkAnd (φ ψ : AFml) : AFml :=
  match φ, ψ with
  | .ff, _ => .ff
  | _, .ff => .ff
  | .tt, .tt => .tt
  | φ, ψ => .and φ ψ

/-- `φ → ψ`, with `false → _`, `_ → true` and `true → false` worked out. -/
def AFml.mkImp (φ ψ : AFml) : AFml :=
  match φ, ψ with
  | .ff, _ => .tt
  | _, .tt => .tt
  | .tt, .ff => .ff
  | φ, ψ => .imp φ ψ

/-- `mkNot` means `¬`.  Example: what is left of `balances[a] ≠ 1` once the
equation is found false is `true`. -/
@[simp] theorem AFml.holds_mkNot (x : Nat → Nat) (φ : AFml) :
    (φ.mkNot).holds x ↔ ¬ φ.holds x := by
  unfold AFml.mkNot; split <;> simp only [holds, not_true_eq_false, not_false_eq_true]

/-- `mkAnd` means `∧`.  Example: `balances[a] = 1 ∧ false` is `false`. -/
@[simp] theorem AFml.holds_mkAnd (x : Nat → Nat) (φ ψ : AFml) :
    (φ.mkAnd ψ).holds x ↔ φ.holds x ∧ ψ.holds x := by
  unfold AFml.mkAnd; split <;> simp_all only [holds, false_and, imp_false, and_false, and_self]

/-- `mkImp` means `→`.  Example: `false → balances[a] = 1` is `true`. -/
@[simp] theorem AFml.holds_mkImp (x : Nat → Nat) (φ ψ : AFml) :
    (φ.mkImp ψ).holds x ↔ (φ.holds x → ψ.holds x) := by
  unfold AFml.mkImp; split <;> simp_all only [holds, false_implies, imp_false, implies_true, not_true_eq_false]

/-- `mkNot φ` is `true`, `false` or `¬φ`. -/
theorem AFml.mkNot_cases (φ : AFml) : φ.mkNot = .tt ∨ φ.mkNot = .ff ∨ φ.mkNot = .not φ := by
  unfold AFml.mkNot; split <;> simp only [reduceCtorEq, or_false, or_true, or_self]

/-- `mkAnd φ ψ` is `true`, `false` or `φ ∧ ψ`. -/
theorem AFml.mkAnd_cases (φ ψ : AFml) :
    φ.mkAnd ψ = .tt ∨ φ.mkAnd ψ = .ff ∨ φ.mkAnd ψ = .and φ ψ := by
  unfold AFml.mkAnd; split <;> simp only [reduceCtorEq, or_false, or_true, or_self]

/-- `mkImp φ ψ` is `true`, `false` or `φ → ψ`. -/
theorem AFml.mkImp_cases (φ ψ : AFml) :
    φ.mkImp ψ = .tt ∨ φ.mkImp ψ = .ff ∨ φ.mkImp ψ = .imp φ ψ := by
  unfold AFml.mkImp; split <;> simp only [reduceCtorEq, or_self, or_false, or_true]

/-- What is left of a formula once the low bits `v` are read: each equation
`a·x = c` becomes `a·y = (c - a·v) / 2` about the halved variables, or `ff`
when `c - a·v` is odd; a connective whose value is then known becomes `tt`
or `ff`. -/
def AFml.deriv (v : List Bool) : AFml → AFml
  | .eq a c => if (c - a.dotBits v) % 2 = 0 then .eq a ((c - a.dotBits v) / 2) else .ff
  | .le a c => .le a ((c - a.dotBits v) / 2)
  | .not φ => (φ.deriv v).mkNot
  | .and φ ψ => (φ.deriv v).mkAnd (ψ.deriv v)
  | .imp φ ψ => (φ.deriv v).mkImp (ψ.deriv v)
  | φ => φ

/-- `D + 2·L = c` says that `c - D` is even and `L` is half of it.  Example:
`1 + 2·balances[b] = balances[a]` says `balances[a]` is odd and
`balances[b]` is half of `balances[a] - 1`. -/
theorem add_two_mul_eq_iff (D L c : Int) : D + 2 * L = c ↔ (c - D) % 2 = 0 ∧ L = (c - D) / 2 := by
  omega

/-- Integer floor division preserves an inequality while consuming a low
bit, including when the residual target is negative or odd. -/
theorem add_two_mul_le_iff (D L c : Int) : D + 2 * L ≤ c ↔ L ≤ (c - D) / 2 := by
  omega

/-- **Reading the low bits keeps the meaning**: a formula holds at `x` exactly
when what is left of it at the low bits of `x` holds at `x` halved.

Example: `balances[a] = 2·balances[b] + 1` at the low bits `1, 0` leaves
`balances[a] = 2·balances[b]` about the halved reads; at the low bits `0, 0`
it leaves `ff`: an even `balances[a]` is never odd. -/
theorem AFml.holds_deriv (n : Nat) (x : Nat → Nat) :
    (φ : AFml) → φ.width ≤ n → (φ.holds x ↔ (φ.deriv (lowBits n x)).holds (halve x))
  | .tt, _ | .ff, _ => Iff.rfl
  | .eq a c, h => by
    simp only [AFml.width] at h
    rw [AFml.holds, Lin.eval_split a n x h, add_two_mul_eq_iff]
    simp only [AFml.deriv]
    split <;> simp_all only [true_and, holds, false_and]
  | .le a c, h => by
    rw [AFml.holds, Lin.eval_split a n x h, add_two_mul_le_iff]
    rfl
  | .not φ, h => by
    simp only [AFml.width] at h
    simp only [holds, AFml.holds_deriv n x φ h, deriv, holds_mkNot]
  | .and φ ψ, h => by
    simp only [AFml.width, Nat.max_le] at h
    simp only [holds, AFml.holds_deriv n x φ h.1, AFml.holds_deriv n x ψ h.2, deriv, holds_mkAnd]
  | .imp φ ψ, h => by
    simp only [AFml.width, Nat.max_le] at h
    simp only [holds, AFml.holds_deriv n x φ h.1, AFml.holds_deriv n x ψ h.2, deriv, holds_mkImp]

/-- The formula at zero: every equation reduced to its constant being `0`. -/
def AFml.atZero : AFml → Bool
  | .tt => true
  | .ff => false
  | .eq _ c => c == 0
  | .le _ c => decide (0 ≤ c)
  | .not φ => !φ.atZero
  | .and φ ψ => φ.atZero && ψ.atZero
  | .imp φ ψ => !φ.atZero || ψ.atZero

/-- A form is `0` where its variables are.  Example: `balances[a] + 2·balances[b]`
with both reads `0`. -/
theorem Lin.eval_zero : ∀ (as : Lin) (x : Nat → Nat), (∀ i < as.length, x i = 0) → as.eval x = 0
  | [], _, _ => rfl
  | a :: as, x, h => by
    have h0 : x 0 = 0 := h 0 (by simp only [List.length_cons, Nat.zero_lt_succ])
    have := Lin.eval_zero as (shift x) (fun i hi => h (i + 1) (by simp only [List.length_cons, Nat.add_lt_add_iff_right]; omega))
    simp only [eval, h0, Int.cast_ofNat_Int, Int.mul_zero, this, Int.add_zero]

/-- **At zero, a formula is its `atZero`**.  Example: `balances[a] = 1` is false
where the read is `0`, and `atZero` says `1 == 0`, false. -/
theorem AFml.holds_zero (x : Nat → Nat) :
    (φ : AFml) → (∀ i < φ.width, x i = 0) → (φ.holds x ↔ φ.atZero = true)
  | .tt, _ | .ff, _ => by simp only [holds, atZero, Bool.false_eq_true]
  | .eq a c, h => by
    simp only [AFml.holds, AFml.atZero, Lin.eval_zero a x h, beq_iff_eq]
    exact eq_comm
  | .le a c, h => by
    simp only [AFml.holds, AFml.atZero, Lin.eval_zero a x h, decide_eq_true_eq]
  | .not φ, h => by
    simp only [holds, AFml.holds_zero x φ h, Bool.not_eq_true, atZero, Bool.not_eq_eq_eq_not, Bool.not_true]
  | .and φ ψ, h => by
    simp only [AFml.width] at h
    simp only [holds, AFml.holds_zero x φ (fun i hi => h i (by omega)), AFml.holds_zero x ψ (fun i hi => h i (by omega)), atZero, Bool.and_eq_true]
  | .imp φ ψ, h => by
    simp only [AFml.width] at h
    simp only [AFml.holds, AFml.atZero, Bool.or_eq_true, Bool.not_eq_true',
      AFml.holds_zero x φ (fun i hi => h i (by omega)),
      AFml.holds_zero x ψ (fun i hi => h i (by omega))]
    cases φ.atZero <;> simp only [Bool.false_eq_true, false_implies, true_or, forall_const, Bool.true_eq_false, false_or]

/-! ## Every choice of bits -/

/-- Every list of `n` bits. -/
def vecs : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (vecs n).flatMap fun v => [false :: v, true :: v]

/-- The library enumeration at length zero. -/
@[simp] theorem vecs_zero : vecs 0 = [[]] := rfl

/-- The library enumeration extends every vector by either bit. -/
theorem vecs_succ (n : Nat) : vecs (n + 1) = (vecs n).flatMap
    (fun v => [false :: v, true :: v]) := rfl

/-- Every list of `n` bits is among `vecs n`.  Example: the low bits of the
reads `balances[a]` and `balances[b]` are one of the four in `vecs 2`. -/
theorem mem_vecs : ∀ {n : Nat} {v : List Bool}, v.length = n → v ∈ vecs n
  | 0, [], _ => by simp only [vecs_zero, List.mem_cons, List.not_mem_nil, or_false]
  | n + 1, b :: v, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [vecs_succ, List.mem_flatMap]
    exact ⟨v, mem_vecs h, by cases b <;> simp only [List.mem_cons, List.cons.injEq, Bool.false_eq_true, and_true, List.not_mem_nil, or_self, or_false, Bool.true_eq_false, or_true]⟩

/-- Every list in `vecs n` has `n` bits.  Example: `vecs 2` holds four lists
of two bits, the low bits of `balances[a]` and `balances[b]`. -/
theorem length_of_mem_vecs : ∀ {n : Nat} {v : List Bool}, v ∈ vecs n → v.length = n
  | 0, v, h => by simp only [vecs_zero, List.mem_cons, List.not_mem_nil, or_false] at h; simp only [h, List.length_nil]
  | n + 1, v, h => by
    simp only [vecs_succ, List.mem_flatMap] at h
    obtain ⟨w, hw, hv⟩ := h
    have := length_of_mem_vecs hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl <;> simp only [List.length_cons, this]

/-- The low bits of `x` have `n` bits.  Example: the low bits of the reads
`balances[a]` and `balances[b]` are two. -/
theorem length_lowBits : ∀ (n : Nat) (x : Nat → Nat), (lowBits n x).length = n
  | 0, _ => rfl
  | n + 1, x => by simp only [lowBits, List.length_cons, length_lowBits n]

/-- The variables with the bits `v` put back in front: `xᵢ = vᵢ + 2·yᵢ`. -/
def withBits : List Bool → (Nat → Nat) → Nat → Nat
  | [], y => fun i => 2 * y i
  | b :: bs, y => fun i => match i with
    | 0 => (if b then 1 else 0) + 2 * y 0
    | i + 1 => withBits bs (shift y) i

/-- The low bits of `withBits v y` are `v`.  Example: the reads `5` and `2`
are `withBits [1, 0]` of `2` and `1`, and their low bits are `1, 0`. -/
theorem lowBits_withBits : ∀ (v : List Bool) (y : Nat → Nat), lowBits v.length (withBits v y) = v
  | [], _ => rfl
  | b :: bs, y => by
    simp only [List.length_cons, lowBits]
    have : shift (withBits (b :: bs) y) = withBits bs (shift y) := rfl
    rw [this, lowBits_withBits bs]
    cases b <;> simp only [withBits, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.mul_mod_right, Nat.reduceBEq, Nat.add_mul_mod_self_left, Nat.mod_succ, BEq.rfl]

/-- Halving `withBits v y` gives back `y`.  Example: the reads `5` and `2`
halved are `2` and `1`. -/
theorem halve_withBits : ∀ (v : List Bool) (y : Nat → Nat), halve (withBits v y) = y
  | [], y => by funext i; simp only [halve, withBits, Nat.zero_lt_succ, Nat.mul_div_right]
  | b :: bs, y => by
    funext i
    cases i with
    | zero => cases b <;> simp only [halve, withBits, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.zero_lt_succ, Nat.mul_div_right]; omega
    | succ i =>
      have := congrFun (halve_withBits bs (shift y)) i
      simpa only [halve, withBits, shift] using this

/-- **What is left of a valid formula is valid**, whatever the bits.  Example:
`balances[a] + balances[a] ≠ 2·balances[b] + 1` is valid, and so is what is
left of it at any low bits. -/
theorem AFml.deriv_valid {φ : AFml} (h : φ.Valid) {v : List Bool} (hw : φ.width ≤ v.length) :
    (φ.deriv v).Valid := by
  intro y
  have := AFml.holds_deriv v.length (withBits v y) φ hw
  rw [lowBits_withBits, halve_withBits] at this
  exact this.1 (h _)

/-! ## A set closed under reading bits -/

/-- The sum of the first `n` variables. -/
def sumTo : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, x => x 0 + sumTo n (shift x)

/-- The variables sum to `0` only when each is `0`.  Example: the reads
`balances[a]` and `balances[b]` sum to `0` only when both are `0`. -/
theorem sumTo_eq_zero : ∀ (n : Nat) (x : Nat → Nat), sumTo n x = 0 → ∀ i < n, x i = 0
  | 0, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, x, h, i, hi => by
    simp only [sumTo] at h
    cases i with
    | zero => omega
    | succ i => exact sumTo_eq_zero n (shift x) (by omega) i (by omega)

/-- Halving never makes the sum bigger.  Example: the reads `5` and `2`
become `2` and `1`. -/
theorem sumTo_halve_le : ∀ (n : Nat) (x : Nat → Nat), sumTo n (halve x) ≤ sumTo n x
  | 0, _ => Nat.le_refl _
  | n + 1, x => by
    have := sumTo_halve_le n (shift x)
    have hs : shift (halve x) = halve (shift x) := rfl
    simp only [sumTo, hs, halve] at *
    omega

/-- Halving makes a nonzero sum smaller.  Example: the reads `5` and `2`,
summing to `7`, become `2` and `1`, summing to `3`. -/
theorem sumTo_halve_lt : ∀ (n : Nat) (x : Nat → Nat), 0 < sumTo n x → sumTo n (halve x) < sumTo n x
  | 0, _, h => absurd h (Nat.lt_irrefl 0)
  | n + 1, x, h => by
    have hle := sumTo_halve_le n (shift x)
    have hs : shift (halve x) = halve (shift x) := rfl
    simp only [sumTo, hs, halve] at *
    by_cases h0 : x 0 = 0
    · have := sumTo_halve_lt n (shift x) (by omega)
      omega
    · omega

/-- **A set closed under reading bits, all of whose formulas hold at zero,
holds of every choice of the variables.**  By induction on the sum of the
variables: at zero `atZero` says it, and otherwise the halved variables sum
to less.

Example: `{ x + x ≠ 2·y + 1 }` alone is closed (its equation at any bits is
`ff` or itself again), and it holds at zero, so it is valid. -/
theorem AFml.valid_of_closed (n : Nat) (S : List AFml) (hw : ∀ G ∈ S, G.width ≤ n)
    (hz : ∀ G ∈ S, G.atZero = true) (hc : ∀ G ∈ S, ∀ v ∈ vecs n, G.deriv v ∈ S) :
    ∀ G ∈ S, G.Valid := by
  suffices ∀ m x, sumTo n x = m → ∀ G ∈ S, G.holds x from fun G hG x => this _ x rfl G hG
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro x hm G hG
    by_cases h0 : m = 0
    · subst h0
      exact (AFml.holds_zero x G fun i hi => sumTo_eq_zero n x hm i (by have := hw G hG; omega)).2
        (hz G hG)
    · rw [AFml.holds_deriv n x G (hw G hG)]
      exact ih _ (hm ▸ sumTo_halve_lt n x (by omega)) _ rfl _
        (hc G hG _ (mem_vecs (length_lowBits n x)))

/-! ## Finitely many formulas

Reading bits changes only the constants, and keeps each within a range fixed
by the formula reading started from: if `|c| ≤ M` and the coefficients sum
to at most `M` in absolute value, then `|(c - a·v) / 2| ≤ M` too. -/

/-- The coefficients summed in absolute value. -/
def Lin.absSum : Lin → Nat
  | [] => 0
  | a :: as => a.natAbs + Lin.absSum as

/-- The form at bits is at most its coefficients summed in absolute value.
Example: `balances[a] - 2·balances[b]` at any bits is between `-2` and `1`. -/
theorem Lin.dotBits_le : ∀ (as : Lin) (v : List Bool),
    -(as.absSum : Int) ≤ as.dotBits v ∧ as.dotBits v ≤ as.absSum
  | [], _ => by simp only [absSum, Int.cast_ofNat_Int, Int.neg_zero, dotBits, Int.le_refl, and_self]
  | _ :: _, [] => by simp only [dotBits, Int.neg_le_zero_iff, Int.ofNat_zero_le, and_self]
  | a :: as, b :: bs => by
    have := Lin.dotBits_le as bs
    simp only [Lin.absSum, Lin.dotBits]
    cases b <;> simp only [Int.natCast_add, Bool.false_eq_true, ↓reduceIte, Int.zero_add] <;> omega

/-- The constants from `-M` to `M`. -/
def consts (M : Nat) : List Int := (List.range (2 * M + 1)).map fun k : Nat => (k : Int) - M

/-- Every constant between `-M` and `M` is among `consts M`.  Example: `1`
and `-1` are among `consts 1`. -/
theorem mem_consts {M : Nat} {c : Int} (h₁ : -(M : Int) ≤ c) (h₂ : c ≤ M) : c ∈ consts M := by
  simp only [consts, List.mem_map, List.mem_range]
  exact ⟨(c + M).toNat, by omega, by omega⟩

/-- A constant of `consts M` is between `-M` and `M`.  Example: `consts 1`
is `-1, 0, 1`. -/
theorem bounds_of_mem_consts {M : Nat} {c : Int} (h : c ∈ consts M) : -(M : Int) ≤ c ∧ c ≤ M := by
  simp only [consts, List.mem_map, List.mem_range] at h
  obtain ⟨k, hk, rfl⟩ := h
  omega

/-- The range of the constant of `a·x = c`. -/
def bound (a : Lin) (c : Int) : Nat := max c.natAbs a.absSum

/-- Every formula reading bits can lead to: the same shape and coefficients,
each equation `ff` or with its constant in its range, and any connective
possibly worked out to `tt` or `ff`. -/
def AFml.universe : AFml → List AFml
  | .eq a c => .ff :: (consts (bound a c)).map (.eq a)
  | .le a c => .ff :: (consts (bound a c)).map (.le a)
  | .not φ => .tt :: .ff :: φ.universe.map .not
  | .and φ ψ => .tt :: .ff :: φ.universe.flatMap fun G => ψ.universe.map (.and G)
  | .imp φ ψ => .tt :: .ff :: φ.universe.flatMap fun G => ψ.universe.map (.imp G)
  | φ => [φ]

/-- How many formulas `universe` lists. -/
def AFml.count : AFml → Nat
  | .eq a c | .le a c => 2 * bound a c + 2
  | .not φ => φ.count + 2
  | .and φ ψ | .imp φ ψ => φ.count * ψ.count + 2
  | _ => 1

/-- A list of lists all of length `k`, joined, has `k` times as many. -/
theorem length_flatMap_const {α β : Type} (f : α → List β) (k : Nat) :
    (l : List α) → (∀ a ∈ l, (f a).length = k) → (l.flatMap f).length = l.length * k
  | [], _ => by simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | a :: l, h => by
    rw [List.flatMap_cons, List.length_append, h a (.head _),
      length_flatMap_const f k l (fun b hb => h b (.tail _ hb)), List.length_cons, Nat.succ_mul,
      Nat.add_comm]

/-- `universe` lists `count` formulas.  Example: `balances[a] = 1` has the
range `1`, so `ff` and three equations. -/
theorem AFml.length_universe : (F : AFml) → F.universe.length = F.count
  | .tt | .ff => rfl
  | .eq a c | .le a c => by simp only [«universe», consts, List.map_map, List.length_cons, List.length_map, List.length_range, count]
  | .not φ => by simp only [«universe», List.length_cons, List.length_map, AFml.length_universe φ, count]
  | .and φ ψ => by
    simp only [AFml.universe, AFml.count, List.length_cons]
    rw [length_flatMap_const _ ψ.count _ (fun _ _ => by simp only [List.length_map, AFml.length_universe ψ]),
      AFml.length_universe φ]
  | .imp φ ψ => by
    simp only [AFml.universe, AFml.count, List.length_cons]
    rw [length_flatMap_const _ ψ.count _ (fun _ _ => by simp only [List.length_map, AFml.length_universe ψ]),
      AFml.length_universe φ]

/-- A formula is among the formulas it can lead to.  Example: `balances[a] = 1`
is among `ff`, `balances[a] = -1`, `= 0` and `= 1`. -/
theorem AFml.self_mem_universe : (F : AFml) → F ∈ F.universe
  | .tt | .ff => .head _
  | .eq a c | .le a c => by
    simp only [AFml.universe, List.mem_cons, List.mem_map]
    exact .inr ⟨c, mem_consts (by simp only [bound]; omega) (by simp only [bound]; omega), rfl⟩
  | .not φ => .tail _ (.tail _ (List.mem_map.2 ⟨φ, AFml.self_mem_universe φ, rfl⟩))
  | .and φ ψ => .tail _ (.tail _ (List.mem_flatMap.2 ⟨φ, AFml.self_mem_universe φ,
      List.mem_map.2 ⟨ψ, AFml.self_mem_universe ψ, rfl⟩⟩))
  | .imp φ ψ => .tail _ (.tail _ (List.mem_flatMap.2 ⟨φ, AFml.self_mem_universe φ,
      List.mem_map.2 ⟨ψ, AFml.self_mem_universe ψ, rfl⟩⟩))

/-- **Reading bits stays among the formulas**: what is left of a formula of
`F.universe` is one too.  Example: `balances[a] = 1` at the bit `1` leaves
`balances[a] = 0`, at the bit `0` leaves `ff`. -/
theorem AFml.deriv_mem_universe (v : List Bool) :
    (F G : AFml) → G ∈ F.universe → G.deriv v ∈ F.universe
  | .tt, G, h | .ff, G, h => by
    simp only [AFml.universe, List.mem_singleton] at h; subst h; exact .head _
  | .eq a c, G, h => by
    simp only [AFml.universe, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨k, hk, rfl⟩
    · exact .head _
    · have hb := bounds_of_mem_consts hk
      have hd := Lin.dotBits_le a v
      have hM : a.absSum ≤ bound a c := Nat.le_max_right _ _
      simp only [AFml.deriv]
      split
      · simp only [AFml.universe, List.mem_cons, List.mem_map]
        exact .inr ⟨_, mem_consts (by omega) (by omega), rfl⟩
      · exact .head _
  | .le a c, G, h => by
    simp only [AFml.universe, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨k, hk, rfl⟩
    · exact .head _
    · have hb := bounds_of_mem_consts hk
      have hd := Lin.dotBits_le a v
      have hM : a.absSum ≤ bound a c := Nat.le_max_right _ _
      simp only [AFml.deriv, AFml.universe, List.mem_cons, List.mem_map]
      exact .inr ⟨_, mem_consts (by omega) (by omega), rfl⟩
  | .not φ, G, h => by
    simp only [AFml.universe, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · exact .head _
    · exact .tail _ (.head _)
    obtain ⟨G', hG', rfl⟩ := List.mem_map.1 h
    simp only [AFml.deriv]
    rcases AFml.mkNot_cases (G'.deriv v) with e | e | e <;> rw [e]
    · exact .head _
    · exact .tail _ (.head _)
    · exact .tail _ (.tail _ (List.mem_map.2 ⟨_, AFml.deriv_mem_universe v φ G' hG', rfl⟩))
  | .and φ ψ, G, h => by
    simp only [AFml.universe, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · exact .head _
    · exact .tail _ (.head _)
    obtain ⟨G₁, h₁, h'⟩ := List.mem_flatMap.1 h
    obtain ⟨G₂, h₂, rfl⟩ := List.mem_map.1 h'
    simp only [AFml.deriv]
    rcases AFml.mkAnd_cases (G₁.deriv v) (G₂.deriv v) with e | e | e <;> rw [e]
    · exact .head _
    · exact .tail _ (.head _)
    · exact .tail _ (.tail _ (List.mem_flatMap.2 ⟨_, AFml.deriv_mem_universe v φ G₁ h₁,
        List.mem_map.2 ⟨_, AFml.deriv_mem_universe v ψ G₂ h₂, rfl⟩⟩))
  | .imp φ ψ, G, h => by
    simp only [AFml.universe, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · exact .head _
    · exact .tail _ (.head _)
    obtain ⟨G₁, h₁, h'⟩ := List.mem_flatMap.1 h
    obtain ⟨G₂, h₂, rfl⟩ := List.mem_map.1 h'
    simp only [AFml.deriv]
    rcases AFml.mkImp_cases (G₁.deriv v) (G₂.deriv v) with e | e | e <;> rw [e]
    · exact .head _
    · exact .tail _ (.head _)
    · exact .tail _ (.tail _ (List.mem_flatMap.2 ⟨_, AFml.deriv_mem_universe v φ G₁ h₁,
        List.mem_map.2 ⟨_, AFml.deriv_mem_universe v ψ G₂ h₂, rfl⟩⟩))

/-- The formulas reading bits leads to read no more variables.  Example:
`ff`, what `balances[a] = 1` leaves at the bit `0`, reads none. -/
theorem AFml.width_of_mem_universe : (F G : AFml) → G ∈ F.universe → G.width ≤ F.width
  | .tt, G, h | .ff, G, h => by
    simp only [AFml.universe, List.mem_singleton] at h; subst h; exact Nat.le_refl _
  | .eq a c, G, h | .le a c, G, h => by
    simp only [AFml.universe, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨k, -, rfl⟩ <;> simp only [width, Nat.zero_le, Nat.le_refl]
  | .not φ, G, h => by
    simp only [AFml.universe, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · simp only [width, Nat.zero_le]
    · simp only [width, Nat.zero_le]
    obtain ⟨G', hG', rfl⟩ := List.mem_map.1 h
    exact AFml.width_of_mem_universe φ G' hG'
  | .and φ ψ, G, h => by
    simp only [AFml.universe, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · simp only [width, Nat.zero_le]
    · simp only [width, Nat.zero_le]
    obtain ⟨G₁, h₁, h'⟩ := List.mem_flatMap.1 h
    obtain ⟨G₂, h₂, rfl⟩ := List.mem_map.1 h'
    have := AFml.width_of_mem_universe φ G₁ h₁
    have := AFml.width_of_mem_universe ψ G₂ h₂
    simp only [AFml.width]; omega
  | .imp φ ψ, G, h => by
    simp only [AFml.universe, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · simp only [width, Nat.zero_le]
    · simp only [width, Nat.zero_le]
    obtain ⟨G₁, h₁, h'⟩ := List.mem_flatMap.1 h
    obtain ⟨G₂, h₂, rfl⟩ := List.mem_map.1 h'
    have := AFml.width_of_mem_universe φ G₁ h₁
    have := AFml.width_of_mem_universe ψ G₂ h₂
    simp only [AFml.width]; omega

/-- A list without repeats, all of whose elements are in `U`, is no longer
than `U`.  Example: the formulas `explore` finds for `balances[a] = 1` are at
most the four of its universe. -/
theorem length_le_of_nodup {α : Type} [DecidableEq α] :
    {l : List α} → (U : List α) → l.Nodup → (∀ a ∈ l, a ∈ U) → l.length ≤ U.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l, U, hn, hs => by
    have ha := hs a (.head _)
    have hl := List.nodup_cons.1 hn
    have := length_le_of_nodup (U.erase a) hl.2 fun b hb =>
      (List.mem_erase_of_ne (a := b) (b := a) (fun e => hl.1 (by subst e; exact hb))).2
        (hs b (.tail _ hb))
    rw [List.length_erase_of_mem ha] at this
    have : 0 < U.length := List.length_pos_of_mem ha
    simp only [List.length_cons, ge_iff_le]; omega

/-! ## The search -/

/-- `acc` extended by the formulas of `Gs` neither in `seen` nor already in it. -/
def addNew (seen : List AFml) : List AFml → List AFml → List AFml
  | acc, [] => acc
  | acc, G :: Gs => if G ∈ seen ∨ G ∈ acc then addNew seen acc Gs else addNew seen (G :: acc) Gs

/-- What `addNew` keeps: what was there, and the new formulas not seen
before.  Example: adding `balances[a] = 0` twice keeps one copy. -/
theorem mem_addNew (seen : List AFml) (x : AFml) :
    (acc Gs : List AFml) → (x ∈ addNew seen acc Gs ↔ x ∈ acc ∨ (x ∈ Gs ∧ x ∉ seen))
  | acc, [] => by simp only [addNew, List.not_mem_nil, false_and, or_false]
  | acc, G :: Gs => by
    simp only [addNew]
    split
    · next h =>
      rw [mem_addNew seen x acc Gs, List.mem_cons]
      constructor
      · rintro (h' | ⟨h', hs⟩)
        · exact .inl h'
        · exact .inr ⟨.inr h', hs⟩
      · rintro (h' | ⟨rfl | h', hs⟩)
        · exact .inl h'
        · exact h.elim (fun h => absurd h hs) .inl
        · exact .inr ⟨h', hs⟩
    · next h =>
      rw [mem_addNew seen x (G :: acc) Gs]
      simp only [List.mem_cons]
      constructor
      · rintro ((rfl | h') | ⟨h', hs⟩)
        · exact .inr ⟨.inl rfl, fun hx => h (.inl hx)⟩
        · exact .inl h'
        · exact .inr ⟨.inr h', hs⟩
      · rintro (h' | ⟨rfl | h', hs⟩)
        · exact .inl (.inr h')
        · exact .inl (.inl rfl)
        · exact .inr ⟨h', hs⟩

/-- `addNew` adds no repeats and nothing seen.  Example: adding
`balances[a] = 0` to a search that has seen it adds nothing. -/
theorem nodup_addNew (seen : List AFml) :
    (acc Gs : List AFml) → acc.Nodup → (∀ x ∈ acc, x ∉ seen) →
      (addNew seen acc Gs).Nodup ∧ ∀ x ∈ addNew seen acc Gs, x ∉ seen
  | acc, [], hn, hs => ⟨hn, hs⟩
  | acc, G :: Gs, hn, hs => by
    simp only [addNew]
    split
    · exact nodup_addNew seen acc Gs hn hs
    · next h =>
      refine nodup_addNew seen (G :: acc) Gs (List.nodup_cons.2 ⟨fun hx => h (.inr hx), hn⟩) ?_
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact fun h' => h (.inl h')
      · exact hs x hx

/-- What is left of `G` at each choice of bits. -/
def AFml.succs (vs : List (List Bool)) (G : AFml) : List AFml := vs.map (G.deriv ·)

/-- Breadth first: `seen` the formulas found, `frontier` those whose
successors are not looked at yet.  At most `fuel` rounds. -/
def explore (vs : List (List Bool)) : Nat → List AFml → List AFml → Option (List AFml)
  | 0, _, _ => none
  | _ + 1, seen, [] => some seen
  | fuel + 1, seen, G :: Gs =>
    let new := addNew seen [] ((G :: Gs).flatMap (AFml.succs vs))
    explore vs fuel (new ++ seen) new

/-- **What `explore` returns is closed**: it keeps what was seen, holds every
successor of what it holds, and only formulas the bits lead to.

Example: from `balances[a] = 1` it returns `balances[a] = 1`,
`balances[a] = 0` and `ff`. -/
theorem explore_spec (vs : List (List Bool)) (P : AFml → Prop)
    (hP : ∀ G, P G → ∀ v ∈ vs, P (G.deriv v)) :
    (fuel : Nat) → (seen frontier S : List AFml) → explore vs fuel seen frontier = some S →
    (∀ G ∈ frontier, G ∈ seen) → (∀ G ∈ seen, G ∉ frontier → ∀ v ∈ vs, G.deriv v ∈ seen) →
    (∀ G ∈ seen, P G) →
    (∀ G ∈ seen, G ∈ S) ∧ (∀ G ∈ S, ∀ v ∈ vs, G.deriv v ∈ S) ∧ (∀ G ∈ S, P G)
  | 0, _, _, _, h, _, _, _ => by simp only [explore, reduceCtorEq] at h
  | _ + 1, seen, [], S, h, _, hc, hp => by
    simp only [explore, Option.some.injEq] at h
    subst h
    exact ⟨fun _ h => h, fun G hG => hc G hG (by simp only [List.not_mem_nil, not_false_eq_true]), hp⟩
  | fuel + 1, seen, G₀ :: Gs, S, h, hf, hc, hp => by
    simp only [explore] at h
    generalize hn : addNew seen [] ((G₀ :: Gs).flatMap (AFml.succs vs)) = new at h
    have hnew : ∀ x, x ∈ new ↔ x ∈ (G₀ :: Gs).flatMap (AFml.succs vs) ∧ x ∉ seen := by
      intro x; rw [← hn, mem_addNew]; simp only [List.not_mem_nil, List.flatMap_cons, List.mem_append, List.mem_flatMap, false_or]
    have ih := explore_spec vs P hP fuel (new ++ seen) new S h
      (fun G hG => List.mem_append_left _ hG)
      (by
        intro G hG hGn v hv
        have hGs : G ∈ seen := (List.mem_append.1 hG).resolve_left hGn
        by_cases hfr : G ∈ G₀ :: Gs
        · by_cases hs : G.deriv v ∈ seen
          · exact List.mem_append_right _ hs
          · exact List.mem_append_left _ ((hnew _).2
              ⟨List.mem_flatMap.2 ⟨G, hfr, List.mem_map.2 ⟨v, hv, rfl⟩⟩, hs⟩)
        · exact List.mem_append_right _ (hc G hGs hfr v hv))
      (by
        intro G hG
        rcases List.mem_append.1 hG with hG | hG
        · obtain ⟨hm, -⟩ := (hnew G).1 hG
          obtain ⟨G', hG', hd⟩ := List.mem_flatMap.1 hm
          obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hd
          exact hP G' (hp G' (hf G' hG')) v hv
        · exact hp G hG)
    exact ⟨fun G hG => ih.1 G (List.mem_append_right _ hG), ih.2⟩

/-- **`explore` finishes** within as many rounds as there are formulas the
bits can lead to (plus one): each round adds a new one, or is the last.

Example: from `balances[a] = 1`, whose universe has four formulas, five rounds
are enough. -/
theorem explore_isSome (vs : List (List Bool)) (U : List AFml) (P : AFml → Prop)
    (hP : ∀ G, P G → ∀ v ∈ vs, P (G.deriv v)) (hU : ∀ G, P G → G ∈ U) :
    (fuel : Nat) → (seen frontier : List AFml) → seen.Nodup → (∀ G ∈ frontier, G ∈ seen) →
    (∀ G ∈ seen, P G) → U.length + 2 ≤ fuel + seen.length → (explore vs fuel seen frontier).isSome
  | 0, seen, _, hn, _, hp, hl => by
    have := length_le_of_nodup U hn (fun G hG => hU G (hp G hG))
    omega
  | _ + 1, _, [], _, _, _, _ => rfl
  | fuel + 1, seen, G₀ :: Gs, hn, hf, hp, hl => by
    have hU' := length_le_of_nodup U hn (fun G hG => hU G (hp G hG))
    simp only [explore]
    generalize hn' : addNew seen [] ((G₀ :: Gs).flatMap (AFml.succs vs)) = new
    have ⟨hnd, hns⟩ := nodup_addNew seen [] ((G₀ :: Gs).flatMap (AFml.succs vs)) List.nodup_nil
      (by simp only [List.not_mem_nil, false_implies, implies_true])
    rw [hn'] at hnd hns
    have hnew : ∀ x, x ∈ new ↔ x ∈ (G₀ :: Gs).flatMap (AFml.succs vs) ∧ x ∉ seen := by
      intro x; rw [← hn', mem_addNew]; simp only [List.not_mem_nil, List.flatMap_cons, List.mem_append, List.mem_flatMap, false_or]
    cases new with
    | nil =>
      cases fuel with
      | zero => omega
      | succ fuel => rfl
    | cons N Ns =>
      refine explore_isSome vs U P hP hU fuel _ _ ?_ (fun G hG => List.mem_append_left _ hG) ?_ ?_
      · exact List.nodup_append.2 ⟨hnd, hn, fun a ha b hb e => hns a ha (e ▸ hb)⟩
      · intro G hG
        rcases List.mem_append.1 hG with hG | hG
        · obtain ⟨hm, -⟩ := (hnew G).1 hG
          obtain ⟨G', hG', hd⟩ := List.mem_flatMap.1 hm
          obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hd
          exact hP G' (hp G' (hf G' hG')) v hv
        · exact hp G hG
      · simp only [List.length_append, List.length_cons] at *; omega

/-! ## Simplifying first

Symbolic execution leaves many equations that are trivially true or false
(`balances[a] = balances[a]`, `2 = 1`): their forms are zero.  Working them
out first makes the formula smaller, and so the search faster. -/

/-- A form without its trailing zero coefficients. -/
def Lin.trim : Lin → Lin
  | [] => []
  | a :: as => if a = 0 ∧ Lin.trim as = [] then [] else a :: Lin.trim as

/-- Trimming keeps the value.  Example: `balances[a] - balances[a]` is the zero
form, trimmed to nothing. -/
theorem Lin.eval_trim : (as : Lin) → (x : Nat → Nat) → (as.trim).eval x = as.eval x
  | [], _ => rfl
  | a :: as, x => by
    have ih := Lin.eval_trim as (shift x)
    simp only [Lin.trim]
    split
    · next h => rw [h.2] at ih; simp only [eval, h.1, Int.zero_mul, ← ih, Int.add_zero]
    · simp only [eval, ih]

/-- `a·x = c`, worked out when the form is zero. -/
def AFml.mkEq (a : Lin) (c : Int) : AFml :=
  match a.trim with
  | [] => if c = 0 then .tt else .ff
  | a' => .eq a' c

/-- `mkEq` means `=`.  Example: `balances[a] = balances[a]` is `true`. -/
theorem AFml.holds_mkEq (x : Nat → Nat) (a : Lin) (c : Int) :
    (AFml.mkEq a c).holds x ↔ a.eval x = c := by
  rw [← Lin.eval_trim a x]
  unfold AFml.mkEq
  split
  · next h => rw [h]; split <;> simp_all only [holds, Lin.eval, false_iff]; omega
  · simp only [holds]

/-- A linear inequality, simplified when every coefficient is zero. -/
def AFml.mkLe (a : Lin) (c : Int) : AFml :=
  match a.trim with
  | [] => if 0 ≤ c then .tt else .ff
  | a' => .le a' c

theorem AFml.holds_mkLe (x : Nat → Nat) (a : Lin) (c : Int) :
    (AFml.mkLe a c).holds x ↔ a.eval x ≤ c := by
  rw [← Lin.eval_trim a x]
  unfold AFml.mkLe
  split
  · next h => rw [h]; split <;> simp_all only [holds, Lin.eval]
  · rfl

/-- Work out the trivial equations, and the connectives they decide. -/
def AFml.simp : AFml → AFml
  | .eq a c => AFml.mkEq a c
  | .le a c => AFml.mkLe a c
  | .not φ => φ.simp.mkNot
  | .and φ ψ => φ.simp.mkAnd ψ.simp
  | .imp φ ψ => φ.simp.mkImp ψ.simp
  | φ => φ

/-- **Simplifying keeps the meaning.**  Example: `balances[a] = balances[a] →
balances[a] = 1` simplifies to `balances[a] = 1`'s `true → …`, which holds
exactly where the original does. -/
theorem AFml.holds_simp (x : Nat → Nat) : (φ : AFml) → (φ.simp.holds x ↔ φ.holds x)
  | .tt | .ff => Iff.rfl
  | .eq a c => AFml.holds_mkEq x a c
  | .le a c => AFml.holds_mkLe x a c
  | .not φ => by simp only [simp, holds_mkNot, AFml.holds_simp x φ, holds]
  | .and φ ψ => by simp only [simp, holds_mkAnd, AFml.holds_simp x φ, AFml.holds_simp x ψ, holds]
  | .imp φ ψ => by simp only [simp, holds_mkImp, AFml.holds_simp x φ, AFml.holds_simp x ψ, holds]

/-! ## The decision -/

/-- Collect every formula reading bits leads to, and check each at zero. -/
def AFml.search (F : AFml) : Bool :=
  match explore (vecs F.width) (F.count + 1) [F] [F] with
  | some S => S.all (·.atZero)
  | none => false

/-- The computed graph bound always suffices; the search's `none` arm
cannot stand for an unsuccessful validity check. -/
theorem AFml.exploration_isSome (F : AFml) :
    (explore (vecs F.width) (F.count + 1) [F] [F]).isSome = true := by
  apply explore_isSome (vecs F.width) F.universe (fun G => G ∈ F.universe)
    (fun G hG v _ => deriv_mem_universe v F G hG) (fun _ h => h)
  · exact List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩
  · exact fun _ h => h
  · intro G hG
    cases List.mem_singleton.1 hG
    exact self_mem_universe F
  · rw [length_universe]
    simp only [List.length_singleton]
    omega

/-- **The search decides validity**.  Each formula it finds holds at zero
when the formula is valid (each is valid too, `AFml.deriv_valid`);
conversely the set it finds is closed, so `AFml.valid_of_closed` applies.
The search always finishes (`explore_isSome`), so the answer is never a
default.

Example: from `balances[a] + balances[a] ≠ 2·balances[b] + 1` it finds only
formulas true at zero; from `balances[a] ≠ 2·balances[b]` it finds the
formula itself, false at zero. -/
theorem AFml.search_iff (F : AFml) : F.search = true ↔ F.Valid := by
  let P : AFml → Prop := fun G => G ∈ F.universe ∧ (F.Valid → G.Valid)
  have hP : ∀ G, P G → ∀ v ∈ vecs F.width, P (G.deriv v) := fun G ⟨hu, hv⟩ v hv' =>
    ⟨AFml.deriv_mem_universe v F G hu, fun hF => AFml.deriv_valid (hv hF)
      (by rw [length_of_mem_vecs hv']; exact AFml.width_of_mem_universe F G hu)⟩
  have hinit : ∀ G ∈ [F], P G := by
    intro G hG
    rw [List.mem_singleton] at hG
    exact hG ▸ ⟨AFml.self_mem_universe F, id⟩
  unfold AFml.search
  split
  · next S hS =>
    have ⟨hseen, hcl, hp⟩ := explore_spec (vecs F.width) P hP _ [F] [F] S hS
      (fun _ h => h) (fun _ hG hn => absurd hG hn) hinit
    constructor
    · intro hall
      exact AFml.valid_of_closed F.width S (fun G hG => AFml.width_of_mem_universe F G (hp G hG).1)
        (fun G hG => List.all_eq_true.1 hall G hG) hcl F (hseen F (.head _))
    · intro hF
      exact List.all_eq_true.2 fun G hG =>
        (AFml.holds_zero (fun _ => 0) G (fun _ _ => rfl)).1 ((hp G hG).2 hF _)
  · next hS =>
    have := explore_isSome (vecs F.width) F.universe P hP (fun _ h => h.1) (F.count + 1) [F] [F]
      (List.nodup_cons.2 ⟨by simp only [List.not_mem_nil, not_false_eq_true], List.nodup_nil⟩) (fun _ h => h) hinit
      (by rw [AFml.length_universe]; simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.le_refl])
    rw [hS] at this
    exact absurd this (by simp only [Option.isSome_none, Bool.false_eq_true, not_false_eq_true])

/-! ## Normal forms

What the search walks is simplified at every state, not only at the start
(`AFml.norm`): `true` and `false` absorbed by the connectives (`tt ∧ φ` is
`φ`, `φ → ff` is `¬φ`, `¬¬φ` is `φ`); an atom whose sign settles it worked
out (`a·x ≤ c` with every coefficient at most `0` and `c ≥ 0` is `true`;
with every coefficient at least `0` and `c < 0` it is `false`, and so is
such an equation); an atom divided by the greatest common divisor of its
coefficients (`16·x - 2^256·q ≤ c` is `x - 2^252·q ≤ ⌊c/16⌋`, an equation
whose constant it does not divide is `false`).  Each step keeps the
meaning (`AFml.holds_norm`) and reads no more variables
(`AFml.width_norm`).  A hypothesis that a bit read makes false
(`x ≤ 15` once a fifth bit of `x` is `1`) so closes its branch at once. -/

/-- The greatest common divisor of the coefficients (`0` for the zero form). -/
def Lin.gcdAll : Lin → Nat
  | [] => 0
  | a :: as => Nat.gcd a.natAbs (Lin.gcdAll as)

/-- Every coefficient divided by `g`. -/
def Lin.divBy (g : Int) (as : Lin) : Lin := as.map (· / g)

theorem Lin.gcdAll_dvd : ∀ (as : Lin), ∀ a ∈ as, ((Lin.gcdAll as : Nat) : Int) ∣ a
  | [], _, h => nomatch h
  | b :: as, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Int.dvd_natAbs.1 (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _))
    · exact Int.dvd_trans (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _)) (Lin.gcdAll_dvd as a h)

theorem Lin.eval_divBy (g : Int) : ∀ (as : Lin), (∀ a ∈ as, g ∣ a) → ∀ x,
    as.eval x = g * (as.divBy g).eval x
  | [], _, _ => by simp only [eval, divBy, List.map_nil, Int.mul_zero]
  | a :: as, h, x => by
    have ih := Lin.eval_divBy g as (fun b hb => h b (.tail _ hb)) (shift x)
    have ha : g * (a / g) = a := Int.mul_ediv_cancel' (h a (.head _))
    simp only [divBy, List.map_cons] at ih ⊢
    simp only [eval, ih, Int.mul_add, ← Int.mul_assoc, ha]

theorem Lin.length_divBy (g : Int) (as : Lin) : (as.divBy g).length = as.length := List.length_map _

theorem Lin.eval_nonneg : ∀ (as : Lin), (∀ a ∈ as, 0 ≤ a) → ∀ x, 0 ≤ as.eval x
  | [], _, _ => Int.le_refl 0
  | a :: as, h, x => by
    have := Lin.eval_nonneg as (fun b hb => h b (.tail _ hb)) (shift x)
    have ha := h a (.head _)
    simp only [eval]
    have : 0 ≤ a * (x 0 : Int) := Int.mul_nonneg ha (Int.natCast_nonneg _)
    omega

theorem Lin.eval_nonpos : ∀ (as : Lin), (∀ a ∈ as, a ≤ 0) → ∀ x, as.eval x ≤ 0
  | [], _, _ => Int.le_refl 0
  | a :: as, h, x => by
    have := Lin.eval_nonpos as (fun b hb => h b (.tail _ hb)) (shift x)
    have ha := h a (.head _)
    simp only [eval]
    have : a * (x 0 : Int) ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg ha (Int.natCast_nonneg _)
    omega

theorem Lin.length_trim_le : ∀ (as : Lin), as.trim.length ≤ as.length
  | [] => Nat.le_refl _
  | a :: as => by
    have := Lin.length_trim_le as
    simp only [Lin.trim]
    split <;> simp only [List.length_nil, List.length_cons] <;> omega

/-- Every coefficient a multiple of `g`. -/
def Lin.allDvd (g : Int) (a : Lin) : Bool := a.all (· % g = 0)

theorem Lin.dvd_of_allDvd {g : Int} {a : Lin} (h : a.allDvd g = true) : ∀ b ∈ a, g ∣ b := by
  intro b hb
  simp only [Lin.allDvd, List.all_eq_true, decide_eq_true_eq] at h
  exact Int.dvd_of_emod_eq_zero (h b hb)

/-- `a·x = c`, worked out by sign, divided by `g` where `g` divides every
coefficient (`false` where it does not divide `c`). -/
def AFml.atomEqBy (g : Int) (a : Lin) (c : Int) : AFml :=
  if (a.all (0 ≤ ·) && c < 0) || (a.all (· ≤ 0) && 0 < c) then .ff
  else if 1 < g && a.allDvd g then (if c % g = 0 then .eq (a.divBy g) (c / g) else .ff)
  else .eq a c

/-- `a·x ≤ c`, worked out by sign, divided by `g` where `g` divides every
coefficient. -/
def AFml.atomLeBy (g : Int) (a : Lin) (c : Int) : AFml :=
  if a.all (· ≤ 0) && 0 ≤ c then .tt
  else if a.all (0 ≤ ·) && c < 0 then .ff
  else if 1 < g && a.allDvd g then .le (a.divBy g) (c / g)
  else .le a c

/-- `a·x = c` on a trimmed form: the zero form worked out, the rest divided
by the coefficients' divisor. -/
def AFml.atomEq (a : Lin) (c : Int) : AFml :=
  if a = [] then (if c = 0 then .tt else .ff) else AFml.atomEqBy a.gcdAll a c

/-- `a·x ≤ c` on a trimmed form. -/
def AFml.atomLe (a : Lin) (c : Int) : AFml :=
  if a = [] then (if 0 ≤ c then .tt else .ff) else AFml.atomLeBy a.gcdAll a c

theorem AFml.holds_atomEqBy (x : Nat → Nat) (g : Int) (a : Lin) (c : Int) :
    (AFml.atomEqBy g a c).holds x ↔ a.eval x = c := by
  unfold AFml.atomEqBy
  split
  · next h =>
    simp only [holds, false_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨h, hc⟩ | ⟨h, hc⟩
    · have := Lin.eval_nonneg a h x; omega
    · have := Lin.eval_nonpos a h x; omega
  · split
    · next hg =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
      have hd := Lin.eval_divBy g a (Lin.dvd_of_allDvd hg.2) x
      split
      · next hc =>
        simp only [holds]
        rw [hd]
        have hc' : g * (c / g) = c := Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hc)
        constructor
        · intro h; rw [h, hc']
        · intro h
          rw [← hc'] at h
          exact Int.eq_of_mul_eq_mul_left (by omega) h
      · next hc =>
        simp only [holds, false_iff]
        intro h
        rw [hd] at h
        exact hc (Int.emod_eq_zero_of_dvd ⟨_, h.symm⟩)
    · rfl

theorem AFml.holds_atomLeBy (x : Nat → Nat) (g : Int) (a : Lin) (c : Int) :
    (AFml.atomLeBy g a c).holds x ↔ a.eval x ≤ c := by
  unfold AFml.atomLeBy
  split
  · next h =>
    simp only [holds, true_iff]
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    have := Lin.eval_nonpos a h.1 x; omega
  · split
    · next h =>
      simp only [holds, false_iff]
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
      have := Lin.eval_nonneg a h.1 x; omega
    · split
      · next hg =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
        have hd := Lin.eval_divBy g a (Lin.dvd_of_allDvd hg.2) x
        simp only [holds]
        rw [hd, Int.le_ediv_iff_mul_le (by omega), Int.mul_comm]
      · rfl

theorem AFml.holds_atomEq (x : Nat → Nat) (a : Lin) (c : Int) :
    (AFml.atomEq a c).holds x ↔ a.eval x = c := by
  unfold AFml.atomEq
  split
  · next he => subst he; split <;> simp only [holds, Lin.eval] <;> grind
  · exact holds_atomEqBy x _ a c

theorem AFml.holds_atomLe (x : Nat → Nat) (a : Lin) (c : Int) :
    (AFml.atomLe a c).holds x ↔ a.eval x ≤ c := by
  unfold AFml.atomLe
  split
  · next he => subst he; split <;> simp only [holds, Lin.eval] <;> grind
  · exact holds_atomLeBy x _ a c

theorem AFml.width_atomEqBy (g : Int) (a : Lin) (c : Int) : (AFml.atomEqBy g a c).width ≤ a.length := by
  unfold AFml.atomEqBy
  split
  · simp only [width, Nat.zero_le]
  · split
    · split <;> simp only [width, Lin.length_divBy, Nat.le_refl, Nat.zero_le]
    · simp only [width, Nat.le_refl]

theorem AFml.width_atomLeBy (g : Int) (a : Lin) (c : Int) : (AFml.atomLeBy g a c).width ≤ a.length := by
  unfold AFml.atomLeBy
  split
  · simp only [width, Nat.zero_le]
  · split
    · simp only [width, Nat.zero_le]
    · split
      · simp only [width, Lin.length_divBy, Nat.le_refl]
      · simp only [width, Nat.le_refl]

theorem AFml.width_atomEq (a : Lin) (c : Int) : (AFml.atomEq a c).width ≤ a.length := by
  unfold AFml.atomEq
  split
  · split <;> simp only [width, Nat.zero_le]
  · exact width_atomEqBy _ a c

theorem AFml.width_atomLe (a : Lin) (c : Int) : (AFml.atomLe a c).width ≤ a.length := by
  unfold AFml.atomLe
  split
  · split <;> simp only [width, Nat.zero_le]
  · exact width_atomLeBy _ a c

/-- `¬φ`, with `¬¬φ` worked out too. -/
def AFml.nNot : AFml → AFml
  | .tt => .ff
  | .ff => .tt
  | .not φ => φ
  | φ => .not φ

/-- `φ ∧ ψ`, `true` absorbed. -/
def AFml.nAnd (φ ψ : AFml) : AFml :=
  match φ, ψ with
  | .ff, _ => .ff
  | _, .ff => .ff
  | .tt, ψ => ψ
  | φ, .tt => φ
  | φ, ψ => .and φ ψ

/-- `φ → ψ`, `true` and `false` absorbed. -/
def AFml.nImp (φ ψ : AFml) : AFml :=
  match φ, ψ with
  | .ff, _ => .tt
  | _, .tt => .tt
  | .tt, ψ => ψ
  | φ, .ff => φ.nNot
  | φ, ψ => .imp φ ψ

theorem AFml.holds_nNot (x : Nat → Nat) (φ : AFml) : (φ.nNot).holds x ↔ ¬ φ.holds x := by
  unfold AFml.nNot; split <;> simp only [holds, not_true_eq_false, not_false_eq_true, Classical.not_not]

theorem AFml.holds_nAnd (x : Nat → Nat) (φ ψ : AFml) : (φ.nAnd ψ).holds x ↔ φ.holds x ∧ ψ.holds x := by
  unfold AFml.nAnd; split <;> simp only [holds, false_and, and_false, true_and, and_true]

theorem AFml.holds_nImp (x : Nat → Nat) (φ ψ : AFml) : (φ.nImp ψ).holds x ↔ (φ.holds x → ψ.holds x) := by
  unfold AFml.nImp; split <;> simp only [holds, holds_nNot, false_implies, implies_true, true_implies, imp_false]

theorem AFml.width_nNot (φ : AFml) : φ.nNot.width ≤ φ.width := by
  unfold AFml.nNot; split <;> simp only [width, Nat.le_refl]

theorem AFml.width_nAnd (φ ψ : AFml) : (φ.nAnd ψ).width ≤ max φ.width ψ.width := by
  unfold AFml.nAnd; split <;> simp only [width] <;> omega

theorem AFml.width_nImp (φ ψ : AFml) : (φ.nImp ψ).width ≤ max φ.width ψ.width := by
  unfold AFml.nImp; split
  all_goals first
    | (simp only [width]; omega)
    | exact Nat.le_trans (width_nNot _) (Nat.le_max_left _ _)

/-- **The normal form**: every atom and connective worked out. -/
def AFml.norm : AFml → AFml
  | .eq a c => AFml.atomEq a.trim c
  | .le a c => AFml.atomLe a.trim c
  | .not φ => φ.norm.nNot
  | .and φ ψ => φ.norm.nAnd ψ.norm
  | .imp φ ψ => φ.norm.nImp ψ.norm
  | φ => φ

theorem AFml.holds_norm (x : Nat → Nat) : (φ : AFml) → (φ.norm.holds x ↔ φ.holds x)
  | .tt | .ff => Iff.rfl
  | .eq a c => by rw [norm, holds_atomEq, Lin.eval_trim]; rfl
  | .le a c => by rw [norm, holds_atomLe, Lin.eval_trim]; rfl
  | .not φ => by rw [norm, holds_nNot, AFml.holds_norm x φ]; rfl
  | .and φ ψ => by rw [norm, holds_nAnd, AFml.holds_norm x φ, AFml.holds_norm x ψ]; rfl
  | .imp φ ψ => by rw [norm, holds_nImp, AFml.holds_norm x φ, AFml.holds_norm x ψ]; rfl

theorem AFml.width_norm : (φ : AFml) → φ.norm.width ≤ φ.width
  | .tt | .ff => Nat.le_refl _
  | .eq a c => Nat.le_trans (width_atomEq _ _) (Lin.length_trim_le a)
  | .le a c => Nat.le_trans (width_atomLe _ _) (Lin.length_trim_le a)
  | .not φ => Nat.le_trans (width_nNot _) (AFml.width_norm φ)
  | .and φ ψ => by
    have := width_nAnd φ.norm ψ.norm
    have := AFml.width_norm φ; have := AFml.width_norm ψ
    simp only [norm, width] at *; omega
  | .imp φ ψ => by
    have := width_nImp φ.norm ψ.norm
    have := AFml.width_norm φ; have := AFml.width_norm ψ
    simp only [norm, width] at *; omega

/-! ## One variable at a time

`AFml.deriv` reads the low bit of every variable at once: `2^n` successors
a state, past reach at ten variables.  The walk reads one variable's bit at
a time instead (`AFml.pderiv`): `xⱼ = b + 2·yⱼ` substituted, so `a·x = c`
becomes `a'·x = c - aⱼ·b`, `a'` the form with `aⱼ` doubled.  Two
successors a state; after a round of every variable each form is doubled,
and the normal form's divisor (`AFml.norm`) halves it back.  A state is a
formula and the variable read next (`AFml.Reached`). -/

/-- `x` with the variable `j` set to `n`. -/
def setAt (x : Nat → Nat) (j n : Nat) : Nat → Nat := fun i => if i = j then n else x i

/-- The coefficient of the variable `j`. -/
def Lin.coef : Nat → Lin → Int
  | _, [] => 0
  | 0, a :: _ => a
  | j + 1, _ :: as => Lin.coef j as

/-- The coefficient of the variable `j` doubled. -/
def Lin.dbl : Nat → Lin → Lin
  | _, [] => []
  | 0, a :: as => (2 * a) :: as
  | j + 1, a :: as => a :: Lin.dbl j as

theorem Lin.length_dbl : ∀ (j : Nat) (as : Lin), (Lin.dbl j as).length = as.length
  | 0, [] | _ + 1, [] => rfl
  | 0, _ :: _ => rfl
  | j + 1, _ :: as => by simp only [dbl, List.length_cons, Lin.length_dbl j as]

theorem shift_setAt (x : Nat → Nat) (j n : Nat) : shift (setAt x (j + 1) n) = setAt (shift x) j n := by
  funext i; simp only [shift, setAt, Nat.add_right_cancel_iff]

theorem shift_setAt_zero (x : Nat → Nat) (n : Nat) : shift (setAt x 0 n) = shift x := by
  funext i; simp only [shift, setAt, Nat.add_one_ne_zero, ↓reduceIte]

/-- **A form splits at one bit**: `xⱼ` is its low bit plus twice its half. -/
theorem Lin.eval_dbl : ∀ (j : Nat) (as : Lin) (x : Nat → Nat),
    as.eval x = Lin.coef j as * ((x j % 2 : Nat) : Int) + (Lin.dbl j as).eval (setAt x j (x j / 2))
  | 0, [], _ | _ + 1, [], _ => by simp only [eval, coef, dbl, Int.zero_mul, Int.add_zero]
  | 0, a :: as, x => by
    simp only [eval, coef, dbl, shift_setAt_zero]
    have hx : ((x 0 : Nat) : Int) = 2 * ((x 0 / 2 : Nat) : Int) + ((x 0 % 2 : Nat) : Int) := by omega
    have h0 : setAt x 0 (x 0 / 2) 0 = x 0 / 2 := by simp only [setAt, ↓reduceIte]
    rw [h0, hx]
    grind
  | j + 1, a :: as, x => by
    simp only [eval, coef, dbl, shift_setAt]
    have h0 : setAt x (j + 1) (x (j + 1) / 2) 0 = x 0 := by
      simp only [setAt, Nat.right_eq_add, Nat.add_one_ne_zero, ↓reduceIte]
    rw [h0, Lin.eval_dbl j as (shift x)]
    simp only [shift]
    omega

/-- What is left of a formula once the low bit `b` of the variable `j` is
read. -/
def AFml.pderiv (j : Nat) (b : Bool) : AFml → AFml
  | .eq a c => .eq (Lin.dbl j a) (c - if b then Lin.coef j a else 0)
  | .le a c => .le (Lin.dbl j a) (c - if b then Lin.coef j a else 0)
  | .not φ => .not (φ.pderiv j b)
  | .and φ ψ => .and (φ.pderiv j b) (ψ.pderiv j b)
  | .imp φ ψ => .imp (φ.pderiv j b) (ψ.pderiv j b)
  | φ => φ

theorem AFml.width_pderiv (j : Nat) (b : Bool) : (φ : AFml) → (φ.pderiv j b).width = φ.width
  | .tt | .ff => rfl
  | .eq a c | .le a c => by simp only [pderiv, width, Lin.length_dbl]
  | .not φ => by simp only [pderiv, width, AFml.width_pderiv j b φ]
  | .and φ ψ | .imp φ ψ => by simp only [pderiv, width, AFml.width_pderiv j b φ, AFml.width_pderiv j b ψ]

/-- **Reading one bit keeps the meaning**: `φ` holds where `xⱼ` is
`b + 2·yⱼ` exactly when what is left of it at `b` holds at `y`. -/
theorem AFml.holds_pderiv (j : Nat) (b : Bool) (y : Nat → Nat) :
    (φ : AFml) → (φ.holds (setAt y j ((if b then 1 else 0) + 2 * y j)) ↔ (φ.pderiv j b).holds y)
  | .tt | .ff => Iff.rfl
  | .eq a c => by
    have hs : setAt (setAt y j ((if b then 1 else 0) + 2 * y j)) j
        ((setAt y j ((if b then 1 else 0) + 2 * y j)) j / 2) = y := by
      funext i; simp only [setAt]; split <;> (try subst i) <;> (cases b <;> simp only [↓reduceIte, Bool.false_eq_true]) <;> omega
    have hm : (setAt y j ((if b then 1 else 0) + 2 * y j)) j % 2 = if b then 1 else 0 := by
      simp only [setAt, ↓reduceIte]; cases b <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
    simp only [holds, pderiv]
    rw [Lin.eval_dbl j a, hs, hm]
    cases b <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
  | .le a c => by
    have hs : setAt (setAt y j ((if b then 1 else 0) + 2 * y j)) j
        ((setAt y j ((if b then 1 else 0) + 2 * y j)) j / 2) = y := by
      funext i; simp only [setAt]; split <;> (try subst i) <;> (cases b <;> simp only [↓reduceIte, Bool.false_eq_true]) <;> omega
    have hm : (setAt y j ((if b then 1 else 0) + 2 * y j)) j % 2 = if b then 1 else 0 := by
      simp only [setAt, ↓reduceIte]; cases b <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
    simp only [holds, pderiv]
    rw [Lin.eval_dbl j a, hs, hm]
    cases b <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
  | .not φ => by simp only [holds, pderiv, AFml.holds_pderiv j b y φ]
  | .and φ ψ => by simp only [holds, pderiv, AFml.holds_pderiv j b y φ, AFml.holds_pderiv j b y ψ]
  | .imp φ ψ => by simp only [holds, pderiv, AFml.holds_pderiv j b y φ, AFml.holds_pderiv j b y ψ]

theorem Lin.dbl_of_coef_zero : ∀ (j : Nat) (as : Lin), Lin.coef j as = 0 → Lin.dbl j as = as
  | 0, [], _ | _ + 1, [], _ => rfl
  | 0, a :: as, h => by simp only [coef] at h; simp only [dbl, h, Int.mul_zero]
  | j + 1, a :: as, h => by simp only [coef] at h; simp only [dbl, Lin.dbl_of_coef_zero j as h]

/-- **One step of the walk**: `AFml.pderiv` with the atoms that read the
variable worked out (`AFml.atomEqBy 2`: halved where every coefficient
became even), the others kept, and the connectives worked out. -/
def AFml.pstep (j : Nat) (b : Bool) : AFml → AFml
  | .eq a c =>
    if Lin.coef j a = 0 then .eq a c
    else AFml.atomEqBy 2 (Lin.dbl j a) (c - if b then Lin.coef j a else 0)
  | .le a c =>
    if Lin.coef j a = 0 then .le a c
    else AFml.atomLeBy 2 (Lin.dbl j a) (c - if b then Lin.coef j a else 0)
  | .not φ => (φ.pstep j b).nNot
  | .and φ ψ => (φ.pstep j b).nAnd (ψ.pstep j b)
  | .imp φ ψ => (φ.pstep j b).nImp (ψ.pstep j b)
  | φ => φ

theorem AFml.holds_pstep (j : Nat) (b : Bool) (y : Nat → Nat) :
    (φ : AFml) → ((φ.pstep j b).holds y ↔ (φ.pderiv j b).holds y)
  | .tt | .ff => Iff.rfl
  | .eq a c => by
    simp only [pstep, pderiv]
    split
    · next h => simp only [holds, Lin.dbl_of_coef_zero j a h, h, ite_self, Int.sub_zero]
    · rw [holds_atomEqBy]; rfl
  | .le a c => by
    simp only [pstep, pderiv]
    split
    · next h => simp only [holds, Lin.dbl_of_coef_zero j a h, h, ite_self, Int.sub_zero]
    · rw [holds_atomLeBy]; rfl
  | .not φ => by simp only [pstep, pderiv, holds_nNot, holds, AFml.holds_pstep j b y φ]
  | .and φ ψ => by
    simp only [pstep, pderiv, holds_nAnd, holds, AFml.holds_pstep j b y φ, AFml.holds_pstep j b y ψ]
  | .imp φ ψ => by
    simp only [pstep, pderiv, holds_nImp, holds, AFml.holds_pstep j b y φ, AFml.holds_pstep j b y ψ]

theorem AFml.width_pstep (j : Nat) (b : Bool) : (φ : AFml) → (φ.pstep j b).width ≤ φ.width
  | .tt | .ff => Nat.le_refl _
  | .eq a c => by
    simp only [pstep]; split
    · exact Nat.le_refl _
    · exact Nat.le_trans (width_atomEqBy _ _ _) (by rw [Lin.length_dbl]; exact Nat.le_refl _)
  | .le a c => by
    simp only [pstep]; split
    · exact Nat.le_refl _
    · exact Nat.le_trans (width_atomLeBy _ _ _) (by rw [Lin.length_dbl]; exact Nat.le_refl _)
  | .not φ => Nat.le_trans (width_nNot _) (AFml.width_pstep j b φ)
  | .and φ ψ => by
    have := width_nAnd (φ.pstep j b) (ψ.pstep j b)
    have := AFml.width_pstep j b φ; have := AFml.width_pstep j b ψ
    simp only [pstep, width] at *; omega
  | .imp φ ψ => by
    have := width_nImp (φ.pstep j b) (ψ.pstep j b)
    have := AFml.width_pstep j b φ; have := AFml.width_pstep j b ψ
    simp only [pstep, width] at *; omega

/-- The variables of a round: at least one, so that a formula reading none
still steps. -/
def AFml.roundLen (F : AFml) : Nat := max F.width 1

/-- The variable read after `j` in a round of `m`. -/
def nextVar (m j : Nat) : Nat := if j + 1 < m then j + 1 else 0

theorem sumTo_congr : ∀ (n : Nat) (x y : Nat → Nat), (∀ i < n, x i = y i) → sumTo n x = sumTo n y
  | 0, _, _, _ => rfl
  | n + 1, x, y, h => by
    simp only [sumTo]
    rw [h 0 (Nat.zero_lt_succ n), sumTo_congr n (shift x) (shift y)
      (fun i hi => h (i + 1) (Nat.add_lt_add_right hi 1))]

/-- The variables from `k` to `m` halved. -/
def halveFrom (m k : Nat) (x : Nat → Nat) : Nat → Nat := fun i => if k ≤ i ∧ i < m then x i / 2 else x i

/-- **A round**: from a state at the variable `k`, the bits of `x` read to
the end of the round reach a state at the first variable, about `x` with
the variables from `k` on halved. -/
theorem AFml.round (m : Nat) (S : AFml × Nat → Prop)
    (hc : ∀ G j, S (G, j) → j < m → ∀ b, S (G.pstep j b, nextVar m j)) :
    ∀ d k G, k + d = m → k < m → S (G, k) → ∀ x, ∃ G', S (G', 0) ∧ (G.holds x ↔ G'.holds (halveFrom m k x))
  | 0, k, _, h, hk, _, _ => by omega
  | d + 1, k, G, h, hk, hS, x => by
    have hstep : G.holds x ↔ (G.pstep k (x k % 2 == 1)).holds (setAt x k (x k / 2)) := by
      rw [holds_pstep, ← holds_pderiv]
      have : setAt (setAt x k (x k / 2)) k ((if (x k % 2 == 1) then 1 else 0) + 2 * setAt x k (x k / 2) k) = x := by
        funext i
        simp only [setAt]
        split
        · subst i
          rcases Nat.mod_two_eq_zero_or_one (x k) with h0 | h0 <;> simp only [h0] <;> simp <;> omega
        · rfl
      rw [this]
    have hS' := hc G k hS hk (x k % 2 == 1)
    unfold nextVar at hS'
    split at hS'
    · next hlt =>
      obtain ⟨G', h1, h2⟩ := AFml.round m S hc d (k + 1) _ (by omega) hlt hS' (setAt x k (x k / 2))
      refine ⟨G', h1, hstep.trans (h2.trans ?_)⟩
      have : halveFrom m (k + 1) (setAt x k (x k / 2)) = halveFrom m k x := by
        funext i; simp only [halveFrom, setAt]
        by_cases hi : i = k
        · subst hi; simp only [Nat.le_refl, hk, and_self, ↓reduceIte, Nat.not_succ_le_self, false_and]
        · simp only [hi, ↓reduceIte]
          by_cases h' : k + 1 ≤ i ∧ i < m
          · rw [if_pos h', if_pos ⟨by omega, h'.2⟩]
          · rw [if_neg h', if_neg (by omega)]
      rw [this]
    · next hlt =>
      refine ⟨_, hS', hstep.trans ?_⟩
      have : setAt x k (x k / 2) = halveFrom m k x := by
        funext i; simp only [halveFrom, setAt]
        by_cases hi : i = k
        · subst hi; simp only [Nat.le_refl, hk, and_self, ↓reduceIte]
        · simp only [hi, ↓reduceIte]
          rw [if_neg (by omega)]
      rw [this]

/-- **A set closed under reading one bit at a time, all of whose formulas
hold at zero, holds everywhere** (at its states at the first variable): by
induction on the sum of the variables, a round halving them all. -/
theorem AFml.valid_of_rounds (m : Nat) (hm : 0 < m) (S : AFml × Nat → Prop)
    (hw : ∀ G j, S (G, j) → G.width ≤ m) (hz : ∀ G j, S (G, j) → G.atZero = true)
    (hc : ∀ G j, S (G, j) → j < m → ∀ b, S (G.pstep j b, nextVar m j)) :
    ∀ G, S (G, 0) → G.Valid := by
  suffices ∀ s x, sumTo m x = s → ∀ G, S (G, 0) → G.holds x from fun G hG x => this _ x rfl G hG
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
    intro x hs G hG
    by_cases h0 : s = 0
    · subst h0
      exact (AFml.holds_zero x G fun i hi => sumTo_eq_zero m x hs i (by have := hw G 0 hG; omega)).2
        (hz G 0 hG)
    · obtain ⟨G', h1, h2⟩ := AFml.round m S hc m 0 G (by omega) hm hG x
      refine h2.2 (ih _ ?_ _ rfl G' h1)
      rw [← hs, sumTo_congr m (halveFrom m 0 x) (halve x)
        (fun i hi => by simp only [halveFrom, Nat.zero_le, hi, and_self, ↓reduceIte, halve])]
      exact sumTo_halve_lt m x (by omega)

/-! ## The walk

A depth-first walk (`walk`, `Calculus/VisitedSet.lean`) over the
normalized one-bit derivatives, the states seen in an `HSet` keyed by
`AFml.hashN`.  Each state carries how to put its bits back
(`AFml.Reached`, as `AFml.Node` of `Calculus/LinearCountermodel.lean`), so
the first state false at zero is a counterassignment at once, without
walking the rest.  If the walk closes, every state it saw holds at zero and
the set is closed under reading bits (`walk_closed`), so the formula is
valid (`AFml.valid_of_rounds`).  Its fuel is not proved to suffice (the
normalized states' universe is not computed); where it runs out, the
decision is the breadth-first `AFml.search`, whose bound is proved. -/

/-- Mix a hash with a number, modulo the prime `2^31 - 1`: every product
stays a machine word. -/
def hmix (h x : Nat) : Nat := (h * 1000003 + x % 2147483647) % 2147483647

/-- An integer as a natural, injectively. -/
def intCode : Int → Nat
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

/-- A formula's hash: its shape, the forms' lengths and the constants.  The
coefficients are left out: the walk's states differ in their constants, and
reading every coefficient of every state would cost more than the rare
comparison of two states that differ only there. -/
def AFml.hashN : AFml → Nat
  | .tt => 1
  | .ff => 2
  | .eq a c => hmix (hmix 3 a.length) (intCode c)
  | .le a c => hmix (hmix 5 a.length) (intCode c)
  | .not φ => hmix 7 φ.hashN
  | .and φ ψ => hmix (hmix 11 φ.hashN) ψ.hashN
  | .imp φ ψ => hmix (hmix 13 φ.hashN) ψ.hashN

/-- A state of the walk, the variable it reads next, and its assignment
reconstruction (the proofs erased). -/
structure AFml.Reached (root : AFml) where
  formula : AFml
  idx : Nat
  embed : (Nat → Nat) → Nat → Nat
  width : formula.width ≤ root.width
  idxLt : idx < root.roundLen
  correct : ∀ x, root.holds (embed x) ↔ formula.holds x

namespace AFml.Reached

variable {root : AFml}

/-- The formula itself, at the first variable. -/
def initial (root : AFml) : Reached root :=
  ⟨root, 0, id, Nat.le_refl _, Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _),
    fun _ => Iff.rfl⟩

/-- Its state. -/
def st (r : Reached root) : AFml × Nat := (r.formula, r.idx)

/-- Reading the bit `b` of the next variable, normalized. -/
def child (r : Reached root) (b : Bool) : Reached root where
  formula := r.formula.pstep r.idx b
  idx := nextVar root.roundLen r.idx
  embed := fun y => r.embed (setAt y r.idx ((if b then 1 else 0) + 2 * y r.idx))
  width := Nat.le_trans (width_pstep _ _ _) r.width
  idxLt := by
    unfold nextVar; split
    · assumption
    · exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _)
  correct := fun y => (r.correct _).trans ((holds_pderiv _ _ y _).trans (holds_pstep _ _ y _).symm)

/-- Both bits. -/
def kids (r : Reached root) : List (Reached root) := [r.child false, r.child true]

end AFml.Reached

/-- A state's hash. -/
def AFml.stateHash (s : AFml × Nat) : Nat := hmix s.1.hashN s.2

/-- The walk from `F`. -/
def AFml.walkFrom (F : AFml) : Walk (AFml × Nat) (AFml.Reached F) :=
  walk AFml.Reached.st AFml.stateHash AFml.Reached.kids (fun r => r.formula.atZero) (2 ^ 64)
    (HSet.leaf.insert (AFml.stateHash (Reached.initial F).st) (Reached.initial F).st)
    [Reached.initial F]

/-- A closed walk proves its formula. -/
theorem AFml.walkFrom_closed {F : AFml} {V : HSet (AFml × Nat)} (h : F.walkFrom = .closed V) :
    F.Valid := by
  obtain ⟨hk, hall⟩ := walk_closed _ _ _ _ _ _ _ V h (walkInv_initial _ _ _ _ _)
  refine AFml.valid_of_rounds F.roundLen (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _))
    V.Mem ?_ ?_ ?_ F (hk _ (HSet.mem_insert.2 (.inl rfl)))
  · intro G j hG
    obtain ⟨n, hn, -, -⟩ := hall _ hG
    simp only [Reached.st, Prod.mk.injEq] at hn
    rw [← hn.1]
    exact Nat.le_trans n.width (Nat.le_max_left _ _)
  · intro G j hG
    obtain ⟨n, hn, hz, -⟩ := hall _ hG
    simp only [Reached.st, Prod.mk.injEq] at hn
    rw [← hn.1]; exact hz
  · intro G j hG _ b
    obtain ⟨n, hn, -, hs⟩ := hall _ hG
    simp only [Reached.st, Prod.mk.injEq] at hn
    obtain ⟨rfl, rfl⟩ := hn
    have := hs (n.child b) (by cases b <;> simp only [Reached.kids, List.mem_cons, true_or, or_true])
    exact this

/-- **Proof or counterassignment by the walk**, `none` where its fuel runs
out.  The walk is of the normal form. -/
def AFml.fastVerify (F : AFml) : Option (Sum (PLift F.Valid) { x : Nat → Nat // ¬ F.holds x }) :=
  match h : F.norm.walkFrom with
  | .closed _ => some (.inl ⟨fun x => (holds_norm x F).1 (AFml.walkFrom_closed h x)⟩)
  | .refuted r => some (.inr ⟨r.embed (fun _ => 0), fun hv => by
      have hz := walk_refuted _ _ _ _ _ _ _ _ h
      have := (holds_zero (fun _ => 0) r.formula (fun _ _ => rfl)).1
        ((r.correct _).1 ((holds_norm _ F).2 hv))
      rw [hz] at this; exact Bool.noConfusion this⟩)
  | .out => none

/-- **Decide** a formula: the walk, or where its fuel runs out the search. -/
def AFml.decide (F : AFml) : Bool :=
  match F.fastVerify with
  | some (.inl _) => true
  | some (.inr _) => false
  | none => F.simp.search

/-- **`decide` decides validity**: it says `true` exactly for the valid
formulas.  The walk's answers are certified (`AFml.fastVerify`); the
search's, the simplified formula valid exactly when the formula is
(`AFml.holds_simp`), are `AFml.search_iff`.

Example: `balances[a] + balances[a] ≠ 2·balances[b] + 1` (an even number is
never odd) is decided `true`, and `balances[a] ≠ 2·balances[b]` is decided
`false`. -/
theorem AFml.decide_iff (F : AFml) : F.decide = true ↔ F.Valid := by
  unfold AFml.decide
  split
  · next v _ => exact ⟨fun _ => v.down, fun _ => rfl⟩
  · next cm _ => exact ⟨fun h => (nomatch h), fun hv => absurd (hv cm.1) cm.2⟩
  · rw [AFml.search_iff]
    exact forall_congr' fun x => AFml.holds_simp x F

end Solidity.Linear
