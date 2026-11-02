import Solidity.Calculus.CallFunctionLeaf

/-! # Compact checked evaluation certificates for affine call families
These producer-side facts retain early overflow. They add no validity
premise and do not change the existing arithmetic dispatcher or calculus.
-/
namespace Solidity.CallFunctionAffine
open CallFunctionTable CallFunctionLeaf

/-- Checked arithmetic, with no modular wraparound. -/
def apply (a b : Int) (x : Key) : Option Key :=
  PrimTy.uint.ofInt? (a*x.val+b)

/-- A later nondecreasing checked application cannot hide prior overflow. -/
theorem bind_checked (u a b : Int) (hu : 0 ≤ u) (ha : 1 ≤ a) (hb : 0 ≤ b) :
    (PrimTy.uint.ofInt? u).bind (fun x => PrimTy.uint.ofInt? (a*x.val+b)) =
      PrimTy.uint.ofInt? (a*u+b) := by
  by_cases hr : PrimTy.uint.inRange u = true
  · simp only [PrimTy.ofInt?, hr, dif_pos, Option.bind_some]
  · have hle : u ≤ a*u+b := by
      have hn : 0 ≤ (a-1)*u := Int.mul_nonneg (by omega) hu
      rw [Int.sub_mul, Int.one_mul] at hn
      omega
    have hn : PrimTy.uint.inRange (a*u+b) ≠ true := by
      intro hfinal
      apply hr
      simp only [PrimTy.inRange, decide_eq_true_eq] at hfinal ⊢
      omega
    simp only [PrimTy.ofInt?]
    rw [dif_neg hr, Option.bind_none, dif_neg hn]

/-- Exact ordered composition, including every failed intermediate result. -/
theorem compose (a b c d : Int) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 1 ≤ c) (hd : 0 ≤ d) (x : Key) :
    (apply a b x).bind (apply c d) = apply (c*a) (c*b+d) x := by
  have hx : 0 ≤ x.val := by
    have hr : PrimTy.inRange .uint x.val = true := x.property
    simp only [PrimTy.inRange, decide_eq_true_eq] at hr
    exact hr.1
  have hu : 0 ≤ a*x.val+b := Int.add_nonneg (Int.mul_nonneg ha hx) hb
  unfold apply
  rw [bind_checked (a*x.val+b) c d hu hc hd]
  rw [Int.mul_add, Int.mul_assoc, Int.add_assoc]

/-- Coefficients are composed once per call-family level. -/
def coefficients (a b : Int) : Nat → Int × Int
  | 0 => (a,b)
  | k+1 => let p := coefficients a b k; (p.1*p.1, p.1*p.2+p.2)

/-- The producer's checked nondecreasing profile is preserved by squaring. -/
theorem coefficients_bounds (a b : Int) (ha : 1 ≤ a) (hb : 0 ≤ b) (k : Nat) :
    1 ≤ (coefficients a b k).1 ∧ 0 ≤ (coefficients a b k).2 := by
  induction k with
  | zero => exact ⟨ha,hb⟩
  | succ k ih =>
    change 1 ≤ (coefficients a b k).1*(coefficients a b k).1 ∧ _
    constructor
    · have hn : 0 ≤ ((coefficients a b k).1-1)*(coefficients a b k).1 :=
        Int.mul_nonneg (by omega) (by omega)
      rw [Int.sub_mul, Int.one_mul] at hn
      omega
    · exact Int.add_nonneg (Int.mul_nonneg (by omega) ih.2) ih.2

/-- Whole doubling-family evaluation via linear-depth coefficient proofs;
no expansion of the 2^k sequential applications is needed. -/
theorem power_eq (a b : Int) (ha : 1 ≤ a) (hb : 0 ≤ b) (k : Nat) (x : Key) :
    power (apply a b) k x = apply (coefficients a b k).1 (coefficients a b k).2 x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [power_succ]
    have hf : power (apply a b) k =
        apply (coefficients a b k).1 (coefficients a b k).2 := by
      funext y
      exact ih y
    rw [hf]
    have hpos : 0 ≤ (coefficients a b k).1 := by
      have h : 1 ≤ (coefficients a b k).1 := (coefficients_bounds a b ha hb k).1
      omega
    exact compose _ _ _ _ hpos
      (coefficients_bounds a b ha hb k).2 (coefficients_bounds a b ha hb k).1
      (coefficients_bounds a b ha hb k).2 x

/-- The actual intrinsic base term, in the caller's captured old context. -/
def term {C : Contract} {Γ : Ctx} (a b : Key) : Tm C (.val .uint :: Γ) (.val .uint) :=
  .app2 (.binop .add rfl)
    (.app2 (.binop .mul rfl) (.pvV .here) (.app0 (.lit a))) (.app0 (.lit b))

/-- Exact operational evaluation of the actual two-operation intrinsic base;
a failed multiplication is not lost by folding its following addition. -/
theorem eval_term {C : Contract} {Γ : Ctx} (a b : Key) (σ : State C Γ) (x : Key) :
    (term a b).eval (σ.push (t := .val .uint) x) = apply a.val b.val x := by
  have hx : 0 ≤ x.val := by
    have hr : PrimTy.inRange .uint x.val = true := x.property
    simp only [PrimTy.inRange, decide_eq_true_eq] at hr
    exact hr.1
  have ha : 0 ≤ a.val := by
    have hr : PrimTy.inRange .uint a.val = true := a.property
    simp only [PrimTy.inRange, decide_eq_true_eq] at hr
    exact hr.1
  have hb : 0 ≤ b.val := by
    have hr : PrimTy.inRange .uint b.val = true := b.property
    simp only [PrimTy.inRange, decide_eq_true_eq] at hr
    exact hr.1
  change (PrimTy.uint.ofInt? (x.val*a.val)).bind
    (fun y => PrimTy.uint.ofInt? (y.val+b.val)) = apply a.val b.val x
  have hh : (PrimTy.uint.ofInt? (x.val*a.val)).bind
      (fun y => PrimTy.uint.ofInt? (1*y.val+b.val)) =
      PrimTy.uint.ofInt? (1*(x.val*a.val)+b.val) :=
    bind_checked (x.val*a.val) 1 b.val (Int.mul_nonneg hx ha) (by decide) hb
  simp only [Int.one_mul] at hh
  rw [hh]
  unfold apply
  rw [Int.mul_comm x.val a.val]

/-- Consume complete fresh function-table definitions through their proved
semantics, retaining the actual caller post and both failure modalities. -/
theorem holds_shared_affine {C : Contract} {Γ : Ctx} (m : Modality)
    (tableName inputName resultName : Var) (a b : Key) (ha : 1 ≤ a.val)
    (k : Nat) (j x : Idx Γ (.val .uint)) (φ : Fml C Γ) (σ : State C Γ) :
    holds σ (leaf m tableName inputName resultName (term a b) k j x φ) ↔
      afterOption m (apply (coefficients a.val b.val k).1
        (coefficients a.val b.val k).2 (σ.locV (.val .uint) x))
        (fun r => holds (σ.setLocal j r) φ) := by
  have hb : 0 ≤ b.val := by
    have hr : PrimTy.inRange .uint b.val = true := b.property
    simp only [PrimTy.inRange, decide_eq_true_eq] at hr
    exact hr.1
  rw [holds_leaf m tableName inputName resultName (term a b) rfl k j x φ σ]
  have hf : (fun y => (term a b).eval (σ.push (t := .val .uint) y)) = apply a.val b.val := by
    funext y
    exact eval_term a b σ y
  rw [hf, power_eq a.val b.val ha hb k]
  rfl

/-- A premise-free specialization for the measured actual 3*x+1 producer.
The coefficient-profile fact is discharged here, not asked of the caller. -/
theorem holds_three_one {C : Contract} {Γ : Ctx} (m : Modality)
    (tableName inputName resultName : Var) (k : Nat)
    (j x : Idx Γ (.val .uint)) (φ : Fml C Γ) (σ : State C Γ) :
    holds σ (leaf m tableName inputName resultName (term (uintOfNat 3) (uintOfNat 1)) k j x φ) ↔
      afterOption m (apply (coefficients 3 1 k).1 (coefficients 3 1 k).2 (σ.getV x))
        (fun r => holds (σ.setLocal j r) φ) :=
  holds_shared_affine m tableName inputName resultName (uintOfNat 3) (uintOfNat 1)
    (by decide) k j x φ σ

/-- Expose the checked range before inspecting the Option, retaining its
proof-dependent value and the exact original failure observation. -/
theorem afterOption_ofInt (m : Modality) (z : Int) (P : Key → Prop) :
    afterOption m (PrimTy.uint.ofInt? z) P ↔
      if hz : PrimTy.uint.inRange z = true then P ⟨z,hz⟩ else m.onHalt := by
  simp only [PrimTy.ofInt?]
  split <;> rfl

/-- The complete affine leaf as two checked cases, without expanding its
quantified table definitions or dropping any overflow branch. -/
theorem holds_shared_affine_cases {C : Contract} {Γ : Ctx} (m : Modality)
    (tableName inputName resultName : Var) (a b : Key) (ha : 1 ≤ a.val)
    (k : Nat) (j x : Idx Γ (.val .uint)) (φ : Fml C Γ) (σ : State C Γ) :
    holds σ (leaf m tableName inputName resultName (term a b) k j x φ) ↔
      if hz : PrimTy.uint.inRange
          ((coefficients a.val b.val k).1*(σ.locV (.val .uint) x).val+
            (coefficients a.val b.val k).2) = true then
        holds (σ.setLocal j ⟨_,hz⟩) φ else m.onHalt := by
  rw [holds_shared_affine m tableName inputName resultName a b ha k j x φ σ]
  exact afterOption_ofInt m _ _
end Solidity.CallFunctionAffine
