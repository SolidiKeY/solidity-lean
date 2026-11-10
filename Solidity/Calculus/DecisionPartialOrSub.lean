import Solidity.Calculus.DecisionPartialOrFloor

/-!
# The partial-OR floor family at any subtraction literal

`Calculus/DecisionPartialOrFloor.lean` decides the guard
`(i ≤ j && i < s - 1) || i ≤ i`. The same argument holds for `s - c` at every
literal `c` whose subtraction from zero halts (`c ≥ 1`, checked by evaluation
at recognition): the guard is `true` exactly when `j < i` or the subtraction
is defined, so the claim `owed[k] == r` under `owed[i] == v` is valid exactly
when `0 < k` and `r = v`, and otherwise refuted at the same symbolic region
(`PartialOrRoots.counterState`: the scalar `0`, the mapping `v` everywhere but
key zero). Discovery reads roots from the declarations and `c`, `v`, `k`, `r`
from the skeleton's uint literals after the constant-work shape check.
-/
namespace Solidity.Decide.ResidueReason
open Semantics (lookupBy)

namespace PartialOrRoots
variable {C : Contract}

/-- `(i ≤ j && i < s - c) || i ≤ i`. -/
def subGuard (sp : PartialOrRoots C) (c : PrimTy.uint.Denote) :
    Tm C [.val .uint, .val .uint] (.val .bool) :=
  .app2 (.binop .or rfl)
    (.app2 (.binop .and rfl)
      (.app2 (.binop .le (p := .uint) rfl) (.pvV (.there .here)) (.pvV .here))
      (.app2 (.binop .lt (p := .uint) rfl) (.pvV (.there .here))
        (.app2 (.binop .sub rfl) sp.scalarRead (.app0 (.lit c)))))
    (.app2 (.binop .le (p := .uint) rfl) (.pvV (.there .here)) (.pvV (.there .here)))

/-- `∀ uint i; ∀ uint j; subGuard == true → m[i] == value`. -/
def subBlock (sp : PartialOrRoots C) (i j : Var) (c value : PrimTy.uint.Denote) : Fml C [] :=
  .all i .uint (.all j .uint
    (.imp (.eq (sp.subGuard c) (.app0 (.lit true)))
      (.eq (sp.mapRead (.pvV (.there .here))) (.app0 (.lit value)))))

/-- The block implies `m[key] == result`. -/
def subClaim (sp : PartialOrRoots C) (i j : Var)
    (c value key result : PrimTy.uint.Denote) : Fml C [] :=
  .imp (sp.subBlock i j c value)
    (.eq (sp.mapRead (.app0 (.lit key))) (.app0 (.lit result)))

/-- A positive first key and zero second key bypass the partial subtraction. -/
theorem subGuard_positive (sp : PartialOrRoots C) (c : PrimTy.uint.Denote) (σ : State C [])
    (key : PrimTy.uint.Denote) (hk : 0 < key.1) :
    holds ((σ.push (t := .val .uint) key).push (t := .val .uint) (uintOfNat 0))
      (.eq (sp.subGuard c) (.app0 (.lit true))) := by
  have hz : decide (key.1 ≤ 0) = false := decide_eq_false (by omega)
  change ((some (decide (key.1 ≤ 0))).bind
    (fun x => binopT (p := .bool) .and rfl x _)).bind
    (fun x => binopT (p := .bool) .or rfl x (some (decide (key.1 ≤ key.1)))) = some true
  rw [hz]
  change some (decide (key.1 ≤ key.1)) = some true
  simp only [Int.le_refl, decide_true]

theorem subClaim_positive_valid (sp : PartialOrRoots C) (first second : Var)
    (c value key : PrimTy.uint.Denote) (hk : 0 < key.1) :
    Fml.Valid (sp.subClaim first second c value key value) := by
  intro σ h
  exact h key (uintOfNat 0) (sp.subGuard_positive c σ key hk)

/-- With a zero scalar and a halting subtraction, the guard is never `true` at index zero. -/
theorem subGuard_zero (sp : PartialOrRoots C) (c : PrimTy.uint.Denote)
    (hc : binopT (p := .uint) .sub rfl (uintOfNat 0) (some c) = none) (σ : State C [])
    (value result : PrimTy.uint.Denote) (hs : σ.storage = sp.counterStorage value result)
    (j : PrimTy.uint.Denote) :
    ¬ holds ((σ.push (t := .val .uint) (uintOfNat 0)).push (t := .val .uint) j)
      (.eq (sp.subGuard c) (.app0 (.lit true))) := by
  intro h
  have hs0 : (sp.scalarRead (Γ := [.val .uint, .val .uint])).denote
      ((σ.push (t := .val .uint) (uintOfNat 0)).push (t := .val .uint) j) = some (uintOfNat 0) :=
    Tm.denote_eval _ _ _ (sp.scalarRead_counter _ value result hs)
  change ((some (decide ((uintOfNat 0).1 ≤ j.1))).bind (fun x => binopT (p := .bool) .and rfl x
      ((some (uintOfNat 0)).bind fun a => binopT (p := .uint) .lt rfl a
        ((sp.scalarRead.denote ((σ.push (t := .val .uint) (uintOfNat 0)).push (t := .val .uint) j)).bind
          fun b => binopT (p := .uint) .sub rfl b (some c))))).bind
    (fun x => binopT (p := .bool) .or rfl x
      (some (decide ((uintOfNat 0).1 ≤ (uintOfNat 0).1)))) = some true at h
  rw [hs0] at h
  have hj : decide ((uintOfNat 0).val ≤ j.val) = true :=
    decide_eq_true (PrimTy.uint_nonneg j)
  simp only [Option.bind_some] at h
  rw [hj, hc] at h
  exact absurd h (by decide)

theorem subBlock_counter (sp : PartialOrRoots C) (first second : Var)
    (c : PrimTy.uint.Denote) (hc : binopT (p := .uint) .sub rfl (uintOfNat 0) (some c) = none)
    (value result : PrimTy.uint.Denote) :
    holds (sp.counterState value result) (sp.subBlock first second c value) := by
  intro i j hg
  by_cases hi : i = uintOfNat 0
  · subst hi
    exact absurd hg (sp.subGuard_zero c hc _ value result rfl j)
  · apply (holds_eq_of_eval (x := value) (y := value) ?_ rfl).mpr rfl
    rw [sp.mapRead_counter _ value result rfl _ i rfl, if_neg hi]

theorem subClaim_counter_refutes (sp : PartialOrRoots C) (first second : Var)
    (c : PrimTy.uint.Denote) (hc : binopT (p := .uint) .sub rfl (uintOfNat 0) (some c) = none)
    (value key result : PrimTy.uint.Denote) (h : ¬ (0 < key.1 ∧ result = value)) :
    ¬ holds (sp.counterState value result) (sp.subClaim first second c value key result) := by
  intro hcl
  have hb := hcl (sp.subBlock_counter first second c hc value result)
  have he := (holds_eq_of_eval (sp.mapRead_counter _ value result rfl _ key rfl) rfl).mp hb
  by_cases hk : key = uintOfNat 0
  · rw [if_pos hk] at he
    exact MemoryWitness.different_ne _ _ he
  · rw [if_neg hk] at he
    apply h
    refine ⟨?_, he.symm⟩
    have hn : 0 ≤ key.1 := PrimTy.uint_nonneg key
    have hne : key.1 ≠ 0 := fun h0 => hk (Subtype.ext h0)
    omega

end PartialOrRoots

variable {C : Contract}

/-- A recognized member: roots, literals, its halting check and its source equation. -/
structure PartialOrSub (φ : Fml C []) where
  sp : PartialOrRoots C
  c : PrimTy.uint.Denote
  value : PrimTy.uint.Denote
  key : PrimTy.uint.Denote
  result : PrimTy.uint.Denote
  halts : binopT (p := .uint) .sub rfl (uintOfNat 0) (some c) = none
  first : Var
  second : Var
  equation : φ = sp.subClaim first second c value key result

/-- Full source recognition at supplied roots and literals. -/
def partialOrSubAt? (sp : PartialOrRoots C) (c value key result : PrimTy.uint.Denote)
    (φ : Fml C []) : Option (PartialOrSub φ) := do
  if hc : binopT (p := .uint) .sub rfl (uintOfNat 0) (some c) = none then
    let outer ← sourceImpView? φ
    let first ← sourceUIntAllView? outer.lhs
    let second ← sourceUIntAllView? first.body
    let inner ← sourceImpView? second.body
    let ⟨hg⟩ ← sourceEquationSame? inner.lhs (.eq (sp.subGuard c) (.app0 (.lit true)))
    let ⟨hb⟩ ← sourceEquationSame? inner.rhs
      (.eq (sp.mapRead (.pvV (.there .here))) (.app0 (.lit value)))
    let ⟨hr⟩ ← sourceEquationSame? outer.rhs
      (.eq (sp.mapRead (.app0 (.lit key))) (.app0 (.lit result)))
    return ⟨sp, c, value, key, result, hc, first.name, second.name, by
      have hi : second.body = .imp (.eq (sp.subGuard c) (.app0 (.lit true)))
          (.eq (sp.mapRead (.pvV (.there .here))) (.app0 (.lit value))) :=
        inner.equation.trans (congr (congrArg Fml.imp hg) hb)
      have hj : first.body = .all second.name .uint
          (.imp (.eq (sp.subGuard c) (.app0 (.lit true)))
            (.eq (sp.mapRead (.pvV (.there .here))) (.app0 (.lit value)))) :=
        second.equation.trans (congrArg (Fml.all second.name .uint) hi)
      have hf : outer.lhs = sp.subBlock first.name second.name c value :=
        first.equation.trans (congrArg (Fml.all first.name .uint) hj)
      exact outer.equation.trans (congr (congrArg Fml.imp hf) hr)⟩
  else none

/-- Search the declared roots and the skeleton's uint literals. -/
def partialOrSub? (φ : Fml C []) : Option (PartialOrSub φ) :=
  if !partialOrShape φ then none else
  let lits := sourceUIntChainLiterals φ
  (partialOrRootsOf C).findSome? fun sp =>
    lits.findSome? fun c => lits.findSome? fun value => lits.findSome? fun key =>
      lits.findSome? fun result => partialOrSubAt? sp c value key result φ

/-- Decidable source classification, independent of target, coverage and verdict. -/
def _root_.Solidity.Fml.partialOrSub (φ : Fml C []) : Bool := (partialOrSub? φ).isSome

/-- The exact semantic verdict of every member. -/
theorem PartialOrSub.valid_iff {φ : Fml C []} (w : PartialOrSub φ) :
    Fml.Valid φ ↔ (0 < w.key.1 ∧ w.result = w.value) := by
  constructor
  · intro hv
    by_cases h : 0 < w.key.1 ∧ w.result = w.value
    · exact h
    · exact absurd (Eq.mp (congrArg (fun ψ => holds (w.sp.counterState w.value w.result) ψ)
        w.equation) (hv _))
        (w.sp.subClaim_counter_refutes w.first w.second w.c w.halts _ _ _ h)
  · intro ⟨hk, hr⟩ σ
    have hv := w.sp.subClaim_positive_valid w.first w.second w.c w.value w.key hk σ
    exact Eq.mpr (congrArg (fun ψ => holds σ ψ) (w.equation.trans (by rw [hr]))) hv

/-- The exact answer: proved on the valid literals, else the symbolic countermodel. -/
def PartialOrSub.answer {φ : Fml C []} (w : PartialOrSub φ) : MemoryWitness.Answer φ :=
  if h : 0 < w.key.1 ∧ w.result = w.value then .proved ((w.valid_iff).mpr h)
  else .refuted (fun _ => w.sp.counterState w.value w.result) (fun _ hh =>
    w.sp.subClaim_counter_refutes w.first w.second w.c w.halts _ _ _ h
      (Eq.mp (congrArg (fun ψ => holds (w.sp.counterState w.value w.result) ψ) w.equation) hh))

def partialOrSubAnswer? (φ : Fml C []) : Option (MemoryWitness.Answer φ) :=
  (partialOrSub? φ).map PartialOrSub.answer

theorem partialOrSubAnswer_isSome {φ : Fml C []} (h : φ.partialOrSub = true) :
    (partialOrSubAnswer? φ).isSome = true := by
  unfold partialOrSubAnswer?
  simpa only [Option.isSome_map] using h

end Solidity.Decide.ResidueReason
