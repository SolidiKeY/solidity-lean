import Solidity.Calculus.QuantHoist

/-!
# Two exact preparations of a quantified body (M7, features 16 and 17)

Both run ahead of array property instantiation (`bodyPrep`,
`Calculus/QuantReduction.lean`), and both are exact at every state and
every valuation of the atoms, so a refuting state of the prepared body is
one of the body, unchanged.

* **`bool` quantifiers expanded** (`LFml.expandB`, `boolPrep`): `∀ bool b. φ`
  is `φ[true/b] ∧ φ[false/b]`, at any polarity.  A block over a
  `bool`-keyed mapping (`(∀ bool b; flags[b] == 0) → flags[true] == 0`)
  becomes its two instances, quantifier-free.
* **Positive quantifiers dropped** (`LFml.dropOne`, `dropPrep`): a `∀` in a
  positive position outside every negative-position `∀` is the prefix's,
  read at a fresh atom (prenexing past `∧`, `→` and `¬`: `B ∧ ∀ k. C` is
  `∀ k. B ∧ C`, `(¬ ∀ k. C) → D` is `∀ k. ¬ C → D`).  One binder at a
  time, the outermost first, renamed to the position past every atom
  (`LFml.ren`), so the body is valid exactly where the result is for every
  value of the new atom (`LFml.dropOne_spec`).  A `∀` under a negative one
  stays: its variable may depend on the outer one.
-/

namespace Solidity.Decide

variable {C : Contract}

/-! ## Valuations -/

theorem AEnv.get_set_other (ν : AEnv) (p q : PrimTy) {k j : Nat} (v : p.Denote)
    (h : ¬ (q = p ∧ j = k)) : (ν.set p k v).get q j = ν.get q j := by
  cases p <;> cases q <;> simp only [AEnv.set, AEnv.get] <;>
    first | rfl | (rw [if_neg (fun e => h ⟨rfl, e⟩)])

/-- Valuations that read alike at every position. -/
def AEnv.Same (ν μ : AEnv) : Prop := ∀ (p : PrimTy) (k : Nat), ν.get p k = μ.get p k

theorem LFml.holds_same (g : State C []) (φ : LFml C) {ν μ : AEnv} (h : ν.Same μ) :
    φ.holds g ν ↔ φ.holds g μ :=
  LFml.holds_agree_below g φ fun p k _ => h p k

theorem AEnv.same_set_set (ν : AEnv) (p : PrimTy) (k : Nat) (v w : p.Denote) :
    ((ν.set p k v).set p k w).Same (ν.set p k w) := by
  intro q j
  by_cases h : q = p ∧ j = k
  · obtain ⟨rfl, rfl⟩ := h
    rw [AEnv.get_set_self, AEnv.get_set_self]
  · rw [AEnv.get_set_other _ p q _ h, AEnv.get_set_other _ p q _ h, AEnv.get_set_other _ p q _ h]

theorem AEnv.same_set_comm (ν : AEnv) (p q : PrimTy) {k j : Nat} (v : p.Denote) (w : q.Denote)
    (h : ¬ (q = p ∧ j = k)) : ((ν.set p k v).set q j w).Same ((ν.set q j w).set p k v) := by
  intro r i
  by_cases h1 : r = q ∧ i = j
  · obtain ⟨rfl, rfl⟩ := h1
    rw [AEnv.get_set_self, AEnv.get_set_other _ p r _ h, AEnv.get_set_self]
  · by_cases h2 : r = p ∧ i = k
    · obtain ⟨rfl, rfl⟩ := h2
      rw [AEnv.get_set_other _ q r _ h1, AEnv.get_set_self, AEnv.get_set_self]
    · rw [AEnv.get_set_other _ q r _ h1, AEnv.get_set_other _ p r _ h2, AEnv.get_set_other _ p r _ h2,
        AEnv.get_set_other _ q r _ h1]

theorem AEnv.same_set (ν μ : AEnv) (h : ν.Same μ) (p : PrimTy) (k : Nat) (v : p.Denote) :
    (ν.set p k v).Same (μ.set p k v) := by
  intro q j
  by_cases h1 : q = p ∧ j = k
  · obtain ⟨rfl, rfl⟩ := h1
    rw [AEnv.get_set_self, AEnv.get_set_self]
  · rw [AEnv.get_set_other _ p q _ h1, AEnv.get_set_other _ p q _ h1]
    exact h q j

theorem AEnv.same_set_get (ν : AEnv) (p : PrimTy) (k : Nat) : (ν.set p k (ν.get p k)).Same ν := by
  intro q j
  by_cases h1 : q = p ∧ j = k
  · obtain ⟨rfl, rfl⟩ := h1
    rw [AEnv.get_set_self]
  · rw [AEnv.get_set_other _ p q _ h1]

/-! ## `bool` quantifiers expanded -/

/-- `t[b/k]`: the `bool` position `k` replaced by the literal `b`. -/
def LTm.substB (k : Nat) (b : Bool) : {s : Srt} → LTm C s → LTm C s
  | _, @LTm.var _ .bool j => if j = k then .app0 (.lit (p := .bool) b) else .var j
  | _, .var j => .var j
  | _, .app0 o => .app0 o
  | _, .app1 o a => .app1 o (LTm.substB k b a)
  | _, .app2 o a c => .app2 o (LTm.substB k b a) (LTm.substB k b c)
  | _, .app3 o a c d => .app3 o (LTm.substB k b a) (LTm.substB k b c) (LTm.substB k b d)
  | _, .index it q i => .index it (LTm.substB k b q) (LTm.substB k b i)
  | _, .obsW q => .obsW (LTm.substB k b q)
  | _, .obsL q => .obsL (LTm.substB k b q)
  | _, .obsH q => .obsH (LTm.substB k b q)
  | _, .seq d a => .seq (LTm.substB k b d) (LTm.substB k b a)
  | _, .orElse a c => .orElse (LTm.substB k b a) (LTm.substB k b c)
  | _, .kite a c t e => .kite (LTm.substB k b a) (LTm.substB k b c) (LTm.substB k b t) (LTm.substB k b e)
  | _, .err => .err

theorem LTm.eval_substB (g : State C []) (ν : AEnv) (k : Nat) (b : Bool) {s : Srt} (t : LTm C s) :
    (LTm.substB k b t).eval g ν = t.eval g (ν.set .bool k b) := by
  induction t with
  | @var p j =>
    cases p with
    | bool =>
      show ((if j = k then LTm.app0 (.lit (p := .bool) b) else LTm.var j).eval g ν : Option _) =
        some ((ν.set .bool k b).get .bool j)
      by_cases hj : j = k
      · subst hj; rw [if_pos rfl, AEnv.get_set_self]; rfl
      · rw [if_neg hj, AEnv.get_set_ne ν .bool .bool b hj]; rfl
    | uint => rfl
    | int => rfl
  | app0 o => rfl
  | app1 o a ih => show (LTm.app1 o _).eval g ν = _; rw [LTm.eval_app1, LTm.eval_app1, ih]
  | app2 o a c iha ihc => show (LTm.app2 o _ _).eval g ν = _; rw [LTm.eval_app2, LTm.eval_app2, iha, ihc]
  | app3 o a c d iha ihc ihd =>
    show (LTm.app3 o _ _ _).eval g ν = _; rw [LTm.eval_app3, LTm.eval_app3, iha, ihc, ihd]
  | index it q i ihq ihi => show (LTm.index it _ _).eval g ν = _; rw [LTm.eval_index, LTm.eval_index, ihq, ihi]
  | obsW q ih => show (LTm.obsW _).eval g ν = _; rw [LTm.eval_obsW, LTm.eval_obsW, ih]
  | obsL q ih => show (LTm.obsL _).eval g ν = _; rw [LTm.eval_obsL, LTm.eval_obsL, ih]
  | obsH q ih => show (LTm.obsH _).eval g ν = _; rw [LTm.eval_obsH, LTm.eval_obsH, ih]
  | seq d a ihd iha => show (LTm.seq _ _).eval g ν = _; rw [LTm.eval_seq, LTm.eval_seq, ihd, iha]
  | orElse a c iha ihc => show (LTm.orElse _ _).eval g ν = _; rw [LTm.eval_orElse, LTm.eval_orElse, iha, ihc]
  | kite a c t e iha ihc iht ihe =>
    show (LTm.kite _ _ _ _).eval g ν = _; rw [LTm.eval_kite, LTm.eval_kite, iha, ihc, iht, ihe]
  | err => rfl

/-- `φ[b/k]`, stopping at a binder of the `bool` position `k`. -/
def LFml.substB (k : Nat) (b : Bool) : LFml C → LFml C
  | .tt => .tt
  | .eq x y => .eq (LTm.substB k b x) (LTm.substB k b y)
  | .not φ => .not (φ.substB k b)
  | .and φ ψ => .and (φ.substB k b) (ψ.substB k b)
  | .imp φ ψ => .imp (φ.substB k b) (ψ.substB k b)
  | .all j p φ => if p = .bool ∧ j = k then .all j p φ else .all j p (φ.substB k b)

theorem LFml.holds_substB (g : State C []) (k : Nat) (b : Bool) :
    ∀ (φ : LFml C) (ν : AEnv), (φ.substB k b).holds g ν ↔ φ.holds g (ν.set .bool k b)
  | .tt, _ => Iff.rfl
  | .eq x y, ν => by simp only [LFml.substB, LFml.holds, LTm.eval_substB]
  | .not φ, ν => not_congr (LFml.holds_substB g k b φ ν)
  | .and φ ψ, ν => and_congr (LFml.holds_substB g k b φ ν) (LFml.holds_substB g k b ψ ν)
  | .imp φ ψ, ν => imp_congr (LFml.holds_substB g k b φ ν) (LFml.holds_substB g k b ψ ν)
  | .all j p φ, ν => by
    unfold LFml.substB
    split
    · rename_i h
      obtain ⟨rfl, rfl⟩ := h
      exact forall_congr' fun v => (LFml.holds_same g φ (AEnv.same_set_set ν .bool j b v)).symm
    · rename_i h
      exact forall_congr' fun v => (LFml.holds_substB g k b φ _).trans
        (LFml.holds_same g φ (AEnv.same_set_comm ν .bool p b v h)).symm

/-- **Every `bool` quantifier expanded** into its two instances. -/
def LFml.expandB : LFml C → LFml C
  | .all k .bool φ => .and (φ.expandB.substB k true) (φ.expandB.substB k false)
  | .all k p φ => .all k p φ.expandB
  | .not φ => .not φ.expandB
  | .and φ ψ => .and φ.expandB ψ.expandB
  | .imp φ ψ => .imp φ.expandB ψ.expandB
  | φ => φ

theorem LFml.holds_expandB (g : State C []) : ∀ (φ : LFml C) (ν : AEnv), φ.expandB.holds g ν ↔ φ.holds g ν
  | .all k .bool φ, ν => by
    show ((φ.expandB.substB k true).holds g ν ∧ (φ.expandB.substB k false).holds g ν) ↔
      ∀ v : Bool, φ.holds g (ν.set .bool k v)
    rw [LFml.holds_substB, LFml.holds_substB, LFml.holds_expandB g φ, LFml.holds_expandB g φ]
    refine ⟨fun h v => ?_, fun h => ⟨h true, h false⟩⟩
    cases v with
    | false => exact h.2
    | true => exact h.1
  | .all k .uint φ, ν => forall_congr' fun v => LFml.holds_expandB g φ _
  | .all k .int φ, ν => forall_congr' fun v => LFml.holds_expandB g φ _
  | .not φ, ν => not_congr (LFml.holds_expandB g φ ν)
  | .and φ ψ, ν => and_congr (LFml.holds_expandB g φ ν) (LFml.holds_expandB g ψ ν)
  | .imp φ ψ, ν => imp_congr (LFml.holds_expandB g φ ν) (LFml.holds_expandB g ψ ν)
  | .tt, _ | .eq _ _, _ => Iff.rfl

/-- **The `bool` expansion as a preparation**, exact at every state. -/
def boolPrep (B : LFml C) : Prep B where
  body := B.expandB
  sound := fun hv g ν => (LFml.holds_expandB g B ν).1 (hv g ν)
  refute := fun g ν hn => ⟨g, fun hB => hn ((LFml.holds_expandB g B ν).2 hB)⟩

/-! ## Positive quantifiers dropped -/

/-- `t` with the position `k` of type `p` read at the position `n`. -/
def LTm.ren (p : PrimTy) (k n : Nat) : {s : Srt} → LTm C s → LTm C s
  | _, @LTm.var _ q j => if q = p ∧ j = k then .var n else .var j
  | _, .app0 o => .app0 o
  | _, .app1 o a => .app1 o (LTm.ren p k n a)
  | _, .app2 o a c => .app2 o (LTm.ren p k n a) (LTm.ren p k n c)
  | _, .app3 o a c d => .app3 o (LTm.ren p k n a) (LTm.ren p k n c) (LTm.ren p k n d)
  | _, .index it q i => .index it (LTm.ren p k n q) (LTm.ren p k n i)
  | _, .obsW q => .obsW (LTm.ren p k n q)
  | _, .obsL q => .obsL (LTm.ren p k n q)
  | _, .obsH q => .obsH (LTm.ren p k n q)
  | _, .seq d a => .seq (LTm.ren p k n d) (LTm.ren p k n a)
  | _, .orElse a c => .orElse (LTm.ren p k n a) (LTm.ren p k n c)
  | _, .kite a c t e => .kite (LTm.ren p k n a) (LTm.ren p k n c) (LTm.ren p k n t) (LTm.ren p k n e)
  | _, .err => .err

theorem LTm.eval_ren (g : State C []) (ν : AEnv) (p : PrimTy) (k n : Nat) {s : Srt} (t : LTm C s) :
    (LTm.ren p k n t).eval g ν = t.eval g (ν.set p k (ν.get p n)) := by
  induction t with
  | @var q j =>
    show ((if q = p ∧ j = k then LTm.var n else LTm.var j).eval g ν : Option _) =
      some ((ν.set p k (ν.get p n)).get q j)
    by_cases h : q = p ∧ j = k
    · obtain ⟨rfl, rfl⟩ := h
      rw [if_pos ⟨rfl, rfl⟩, AEnv.get_set_self]; rfl
    · rw [if_neg h, AEnv.get_set_other _ p q _ h]; rfl
  | app0 o => rfl
  | app1 o a ih => show (LTm.app1 o _).eval g ν = _; rw [LTm.eval_app1, LTm.eval_app1, ih]
  | app2 o a c iha ihc => show (LTm.app2 o _ _).eval g ν = _; rw [LTm.eval_app2, LTm.eval_app2, iha, ihc]
  | app3 o a c d iha ihc ihd =>
    show (LTm.app3 o _ _ _).eval g ν = _; rw [LTm.eval_app3, LTm.eval_app3, iha, ihc, ihd]
  | index it q i ihq ihi => show (LTm.index it _ _).eval g ν = _; rw [LTm.eval_index, LTm.eval_index, ihq, ihi]
  | obsW q ih => show (LTm.obsW _).eval g ν = _; rw [LTm.eval_obsW, LTm.eval_obsW, ih]
  | obsL q ih => show (LTm.obsL _).eval g ν = _; rw [LTm.eval_obsL, LTm.eval_obsL, ih]
  | obsH q ih => show (LTm.obsH _).eval g ν = _; rw [LTm.eval_obsH, LTm.eval_obsH, ih]
  | seq d a ihd iha => show (LTm.seq _ _).eval g ν = _; rw [LTm.eval_seq, LTm.eval_seq, ihd, iha]
  | orElse a c iha ihc => show (LTm.orElse _ _).eval g ν = _; rw [LTm.eval_orElse, LTm.eval_orElse, iha, ihc]
  | kite a c t e iha ihc iht ihe =>
    show (LTm.kite _ _ _ _).eval g ν = _; rw [LTm.eval_kite, LTm.eval_kite, iha, ihc, iht, ihe]
  | err => rfl

theorem LTm.atomBound_ren (p : PrimTy) (k n : Nat) {s : Srt} (t : LTm C s) :
    (LTm.ren p k n t).atomBound ≤ max t.atomBound (n + 1) := by
  induction t with
  | @var q j =>
    show (if q = p ∧ j = k then LTm.var n else LTm.var j : LTm C (.val q)).atomBound ≤ _
    split
    · exact Nat.le_max_right _ _
    · exact Nat.le_max_left _ _
  | app0 | err => exact Nat.zero_le _
  | app1 o a ih | obsW a ih | obsL a ih | obsH a ih => exact ih
  | app2 o a c iha ihc | index _ a c iha ihc | seq a c iha ihc | orElse a c iha ihc =>
    show max _ _ ≤ max (max _ _) _
    omega
  | app3 o a c d iha ihc ihd =>
    show max _ (max _ _) ≤ max (max _ (max _ _)) _
    omega
  | kite a c t e iha ihc iht ihe =>
    show max _ (max _ (max _ _)) ≤ max (max _ (max _ (max _ _))) _
    omega

/-- `φ` with the position `k` of type `p` read at `n`, stopping at a binder
of it. -/
def LFml.ren (p : PrimTy) (k n : Nat) : LFml C → LFml C
  | .tt => .tt
  | .eq x y => .eq (LTm.ren p k n x) (LTm.ren p k n y)
  | .not φ => .not (φ.ren p k n)
  | .and φ ψ => .and (φ.ren p k n) (ψ.ren p k n)
  | .imp φ ψ => .imp (φ.ren p k n) (ψ.ren p k n)
  | .all j q φ => if q = p ∧ j = k then .all j q φ else .all j q (φ.ren p k n)

theorem LFml.atomBound_ren (p : PrimTy) (k n : Nat) :
    ∀ φ : LFml C, (φ.ren p k n).atomBound ≤ max φ.atomBound (n + 1)
  | .tt => Nat.zero_le _
  | .eq x y => by
    have := LTm.atomBound_ren p k n x
    have := LTm.atomBound_ren p k n y
    show max _ _ ≤ max (max _ _) _
    omega
  | .not φ => LFml.atomBound_ren p k n φ
  | .and φ ψ | .imp φ ψ => by
    have := LFml.atomBound_ren p k n φ
    have := LFml.atomBound_ren p k n ψ
    show max _ _ ≤ max (max _ _) _
    omega
  | .all j q φ => by
    have := LFml.atomBound_ren p k n φ
    unfold LFml.ren
    split
    · exact Nat.le_max_left _ _
    · show max _ _ ≤ max (max _ _) _
      omega

/-- **Renaming is reading at the new position**, where no binder of `φ`
is at or past it. -/
theorem LFml.holds_ren (g : State C []) (p : PrimTy) (k n : Nat) :
    ∀ (φ : LFml C), φ.atomBound ≤ n → ∀ ν : AEnv,
      ((φ.ren p k n).holds g ν ↔ φ.holds g (ν.set p k (ν.get p n)))
  | .tt, _, _ => Iff.rfl
  | .eq x y, _, ν => by simp only [LFml.ren, LFml.holds, LTm.eval_ren]
  | .not φ, h, ν => not_congr (LFml.holds_ren g p k n φ h ν)
  | .and φ ψ, h, ν => by
    have h1 : φ.atomBound ≤ n := Nat.le_trans (Nat.le_max_left _ _) h
    have h2 : ψ.atomBound ≤ n := Nat.le_trans (Nat.le_max_right _ _) h
    exact and_congr (LFml.holds_ren g p k n φ h1 ν) (LFml.holds_ren g p k n ψ h2 ν)
  | .imp φ ψ, h, ν => by
    have h1 : φ.atomBound ≤ n := Nat.le_trans (Nat.le_max_left _ _) h
    have h2 : ψ.atomBound ≤ n := Nat.le_trans (Nat.le_max_right _ _) h
    exact imp_congr (LFml.holds_ren g p k n φ h1 ν) (LFml.holds_ren g p k n ψ h2 ν)
  | .all j q φ, h, ν => by
    have hj : j + 1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) h
    have hφ : φ.atomBound ≤ n := Nat.le_trans (Nat.le_max_right _ _) h
    unfold LFml.ren
    split
    · rename_i e
      obtain ⟨rfl, rfl⟩ := e
      exact forall_congr' fun v => (LFml.holds_same g φ (AEnv.same_set_set ν q j _ v)).symm
    · rename_i e
      refine forall_congr' fun v => (LFml.holds_ren g p k n φ hφ _).trans ?_
      rw [AEnv.get_set_ne ν q p v (show n ≠ j by omega)]
      exact (LFml.holds_same g φ (AEnv.same_set_comm ν p q (ν.get p n) v e)).symm

/-- **The first positive quantifier dropped**, outside every negative one:
its variable read at the position `n`; the type it ranged over. -/
def LFml.dropOne : Bool → LFml C → Nat → Option (PrimTy × LFml C)
  | true, .all k p φ, n => some (p, φ.ren p k n)
  | pol, .not φ, n => (LFml.dropOne (!pol) φ n).map fun r => (r.1, .not r.2)
  | pol, .and φ ψ, n =>
    match LFml.dropOne pol φ n with
    | some r => some (r.1, .and r.2 ψ)
    | none => (LFml.dropOne pol ψ n).map fun r => (r.1, .and φ r.2)
  | pol, .imp φ ψ, n =>
    match LFml.dropOne (!pol) φ n with
    | some r => some (r.1, .imp r.2 ψ)
    | none => (LFml.dropOne pol ψ n).map fun r => (r.1, .imp φ r.2)
  | _, _, _ => none

/-- What a dropped formula is, at a polarity. -/
def DropSpec (g : State C []) (pol : Bool) (φ : LFml C) (n : Nat) (p : PrimTy) (φ' : LFml C) : Prop :=
  φ'.atomBound ≤ n + 1 ∧ ∀ ν : AEnv,
    (pol = true → (φ.holds g ν ↔ ∀ v : p.Denote, φ'.holds g (ν.set p n v))) ∧
    (pol = false → (φ.holds g ν ↔ ∃ v : p.Denote, φ'.holds g (ν.set p n v)))

theorem holds_set_fresh (g : State C []) (φ : LFml C) {n : Nat} (h : φ.atomBound ≤ n) (ν : AEnv)
    (p : PrimTy) (v : p.Denote) : φ.holds g (ν.set p n v) ↔ φ.holds g ν :=
  (LFml.holds_agree_below g φ (fun q j hj => (AEnv.get_set_ne ν p q v (show j ≠ n by omega)).symm)).symm

/-- **A dropped quantifier is the prefix's.** -/
theorem LFml.dropOne_spec (g : State C []) :
    ∀ (pol : Bool) (φ : LFml C) (n : Nat) (p : PrimTy) (φ' : LFml C),
      φ.atomBound ≤ n → LFml.dropOne pol φ n = some (p, φ') → DropSpec g pol φ n p φ'
  | true, .all k p φ, n, p', φ', hb, hd => by
    simp only [LFml.dropOne, Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨h1, h2⟩ := hd
    subst h1
    subst h2
    have hk : k + 1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hb
    have hφ : φ.atomBound ≤ n := Nat.le_trans (Nat.le_max_right _ _) hb
    refine ⟨Nat.le_trans (LFml.atomBound_ren p k n φ) (by omega), fun ν => ⟨fun _ => ?_, nofun⟩⟩
    refine forall_congr' fun v => ?_
    rw [LFml.holds_ren g p k n φ hφ, AEnv.get_set_self]
    exact (LFml.holds_agree_below g φ (fun r j hj => by
      by_cases e : r = p ∧ j = k
      · obtain ⟨rfl, rfl⟩ := e
        rw [AEnv.get_set_self, AEnv.get_set_self]
      · rw [AEnv.get_set_other _ p r _ e, AEnv.get_set_other _ p r _ e,
          AEnv.get_set_ne ν p r v (by omega)])).symm
  | pol, .not φ, n, p, φ', hb, hd => by
    cases h : LFml.dropOne (!pol) φ n with
    | none => simp only [LFml.dropOne, h, Option.map_none, reduceCtorEq] at hd
    | some r =>
      simp only [LFml.dropOne, h, Option.map_some, Option.some.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      obtain ⟨hr, ih⟩ := LFml.dropOne_spec g (!pol) φ n r.1 r.2 hb h
      refine ⟨hr, fun ν => ⟨fun hp => ?_, fun hp => ?_⟩⟩
      · subst hp
        show ¬ φ.holds g ν ↔ ∀ v, ¬ r.2.holds g _
        rw [(ih ν).2 rfl]
        exact not_exists
      · subst hp
        show ¬ φ.holds g ν ↔ ∃ v, ¬ r.2.holds g _
        rw [(ih ν).1 rfl]
        exact Classical.not_forall
  | pol, .and φ ψ, n, p, φ', hb, hd => by
    have h1 : φ.atomBound ≤ n := Nat.le_trans (Nat.le_max_left _ _) hb
    have h2 : ψ.atomBound ≤ n := Nat.le_trans (Nat.le_max_right _ _) hb
    have hi : Inhabited p.Denote := ⟨PrimTy.dflt p⟩
    cases h : LFml.dropOne pol φ n with
    | some r =>
      simp only [LFml.dropOne, h, Option.some.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      obtain ⟨hr, ih⟩ := LFml.dropOne_spec g pol φ n r.1 r.2 h1 h
      refine ⟨Nat.max_le.2 ⟨hr, by omega⟩, fun ν => ⟨fun hp => ?_, fun hp => ?_⟩⟩
      · show φ.holds g ν ∧ ψ.holds g ν ↔ ∀ v, r.2.holds g _ ∧ ψ.holds g _
        simp only [holds_set_fresh g ψ h2, (ih ν).1 hp]
        exact ⟨fun h v => ⟨h.1 v, h.2⟩, fun h => ⟨fun v => (h v).1, (h default).2⟩⟩
      · show φ.holds g ν ∧ ψ.holds g ν ↔ ∃ v, r.2.holds g _ ∧ ψ.holds g _
        simp only [holds_set_fresh g ψ h2, (ih ν).2 hp]
        exact ⟨fun ⟨⟨v, hv⟩, h⟩ => ⟨v, hv, h⟩, fun ⟨v, hv, h⟩ => ⟨⟨v, hv⟩, h⟩⟩
    | none =>
      cases h' : LFml.dropOne pol ψ n with
      | none => simp only [LFml.dropOne, h, h', Option.map_none, reduceCtorEq] at hd
      | some r =>
        simp only [LFml.dropOne, h, h', Option.map_some, Option.some.injEq] at hd
        obtain ⟨rfl, rfl⟩ := hd
        obtain ⟨hr, ih⟩ := LFml.dropOne_spec g pol ψ n r.1 r.2 h2 h'
        refine ⟨Nat.max_le.2 ⟨by omega, hr⟩, fun ν => ⟨fun hp => ?_, fun hp => ?_⟩⟩
        · show φ.holds g ν ∧ ψ.holds g ν ↔ ∀ v, φ.holds g _ ∧ r.2.holds g _
          simp only [holds_set_fresh g φ h1, (ih ν).1 hp]
          exact ⟨fun h v => ⟨h.1, h.2 v⟩, fun h => ⟨(h default).1, fun v => (h v).2⟩⟩
        · show φ.holds g ν ∧ ψ.holds g ν ↔ ∃ v, φ.holds g _ ∧ r.2.holds g _
          simp only [holds_set_fresh g φ h1, (ih ν).2 hp]
          exact ⟨fun ⟨h, v, hv⟩ => ⟨v, h, hv⟩, fun ⟨v, h, hv⟩ => ⟨h, v, hv⟩⟩
  | pol, .imp φ ψ, n, p, φ', hb, hd => by
    have h1 : φ.atomBound ≤ n := Nat.le_trans (Nat.le_max_left _ _) hb
    have h2 : ψ.atomBound ≤ n := Nat.le_trans (Nat.le_max_right _ _) hb
    have hi : Inhabited p.Denote := ⟨PrimTy.dflt p⟩
    cases h : LFml.dropOne (!pol) φ n with
    | some r =>
      simp only [LFml.dropOne, h, Option.some.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      obtain ⟨hr, ih⟩ := LFml.dropOne_spec g (!pol) φ n r.1 r.2 h1 h
      refine ⟨Nat.max_le.2 ⟨hr, by omega⟩, fun ν => ⟨fun hp => ?_, fun hp => ?_⟩⟩
      · subst hp
        show (φ.holds g ν → ψ.holds g ν) ↔ ∀ v, r.2.holds g _ → ψ.holds g _
        simp only [holds_set_fresh g ψ h2, (ih ν).2 rfl]
        exact ⟨fun h v hv => h ⟨v, hv⟩, fun h ⟨v, hv⟩ => h v hv⟩
      · subst hp
        show (φ.holds g ν → ψ.holds g ν) ↔ ∃ v, r.2.holds g _ → ψ.holds g _
        simp only [holds_set_fresh g ψ h2, (ih ν).1 rfl]
        refine ⟨fun h => ?_, fun ⟨v, hv⟩ h => hv (h v)⟩
        by_cases hψ : ψ.holds g ν
        · exact ⟨default, fun _ => hψ⟩
        · obtain ⟨v, hv⟩ := Classical.not_forall.1 (fun h' => hψ (h h'))
          exact ⟨v, fun h'' => absurd h'' hv⟩
    | none =>
      cases h' : LFml.dropOne pol ψ n with
      | none => simp only [LFml.dropOne, h, h', Option.map_none, reduceCtorEq] at hd
      | some r =>
        simp only [LFml.dropOne, h, h', Option.map_some, Option.some.injEq] at hd
        obtain ⟨rfl, rfl⟩ := hd
        obtain ⟨hr, ih⟩ := LFml.dropOne_spec g pol ψ n r.1 r.2 h2 h'
        refine ⟨Nat.max_le.2 ⟨by omega, hr⟩, fun ν => ⟨fun hp => ?_, fun hp => ?_⟩⟩
        · show (φ.holds g ν → ψ.holds g ν) ↔ ∀ v, φ.holds g _ → r.2.holds g _
          simp only [holds_set_fresh g φ h1, (ih ν).1 hp]
          exact ⟨fun h v hv => h hv v, fun h hv v => h v hv⟩
        · show (φ.holds g ν → ψ.holds g ν) ↔ ∃ v, φ.holds g _ → r.2.holds g _
          simp only [holds_set_fresh g φ h1, (ih ν).2 hp]
          refine ⟨fun h => ?_, fun ⟨v, hv⟩ h => ⟨v, hv h⟩⟩
          by_cases hφ : φ.holds g ν
          · obtain ⟨v, hv⟩ := h hφ
            exact ⟨v, fun _ => hv⟩
          · exact ⟨default, fun h' => absurd h' hφ⟩
  | false, .all .., _, _, _, _, hd | _, .tt, _, _, _, _, hd | _, .eq _ _, _, _, _, _, hd => by
    simp only [LFml.dropOne, reduceCtorEq] at hd

/-- One positive quantifier dropped, as a preparation. -/
def dropStep (B : LFml C) (p : PrimTy) (B' : LFml C)
    (h : LFml.dropOne true B B.atomBound = some (p, B')) : Prep B where
  body := B'
  sound := fun hv g ν =>
    ((LFml.dropOne_spec g true B B.atomBound p B' (Nat.le_refl _) h).2 ν).1 rfl |>.2 fun _ => hv g _
  refute := fun g ν hn => ⟨g, fun hB => hn <| by
    have := (((LFml.dropOne_spec g true B B.atomBound p B' (Nat.le_refl _) h).2 ν).1 rfl).1 hB
      (ν.get p B.atomBound)
    exact (LFml.holds_same g B' (AEnv.same_set_get ν p _)).1 this⟩

/-- **The positive quantifiers dropped**, one after another (at most
`fuel`). -/
def dropPrep : Nat → (B : LFml C) → Prep B
  | 0, B => Prep.id B
  | fuel + 1, B =>
    match h : LFml.dropOne true B B.atomBound with
    | some (p, B') => (dropStep B p B' h).trans (dropPrep fuel B')
    | none => Prep.id B

/-- The number of quantifiers of a formula: enough fuel for `dropPrep`. -/
def LFml.allCount : LFml C → Nat
  | .tt | .eq _ _ => 0
  | .not φ => φ.allCount
  | .and φ ψ | .imp φ ψ => φ.allCount + ψ.allCount
  | .all _ _ φ => φ.allCount + 1

/-- **The expansions**: `bool` quantifiers expanded, then the positive
quantifiers dropped. -/
def expandPrep (B : LFml C) : Prep B :=
  (boolPrep B).trans (dropPrep (B.expandB.allCount + 1) _)

theorem expandPrep_valid_iff (B : LFml C) : (expandPrep B).body.Valid ↔ B.Valid := (expandPrep B).valid_iff

/-- info: 'Solidity.Decide.expandPrep_valid_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms expandPrep_valid_iff

end Solidity.Decide
