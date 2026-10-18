import Solidity.Calculus.ScalarCode

/-!
# Complete arithmetic over bounded typed variables

A finite primitive context gives every arithmetic variable its exact
Solidity domain. Signed words use the scalar codec's offset. The guarded
arithmetic sentence quantifies over naturals; its domain premise makes
that quantification equivalent to quantifying over typed values. A false
decision decodes to actual typed values rather than truncating a word.
-/

namespace Solidity.Linear

namespace ScalarCode

/-- Heterogeneous primitive values in a finite context. -/
def Values : List PrimTy → Type
  | [] => Unit
  | p :: ps => p.Denote × Values ps

/-- The natural assignment represented by a typed vector. -/
def Values.codes : {ps : List PrimTy} → Values ps → Nat → Nat
  | [], _, _ => 0
  | p :: _, vs, 0 => (encode p vs.1).val
  | _ :: _, vs, k + 1 => vs.2.codes k

/-- Exact bounds for a context, starting at variable `start`. -/
def domainFrom : List PrimTy → Nat → AFml
  | [], _ => .tt
  | p :: ps, start => .and (range p start) (domainFrom ps (start + 1))

def domain (ps : List PrimTy) : AFml := domainFrom ps 0

theorem domainFrom_iff (ps : List PrimTy) (start : Nat) (x : Nat → Nat) :
    (domainFrom ps start).holds x ↔
      ∀ (k : Nat) (p : PrimTy), ps[k]? = some p → x (start + k) < bound p := by
  induction ps generalizing start with
  | nil => simp only [domainFrom, AFml.holds, List.getElem?_nil, reduceCtorEq, false_implies, implies_true, iff_self]
  | cons p ps ih =>
    simp only [domainFrom, AFml.holds, range_holds_iff, ih]
    constructor
    · rintro ⟨h0, ht⟩ k q hk
      cases k with
      | zero => cases hk; exact h0
      | succ k => simpa only [Nat.add_assoc, Nat.add_comm 1] using ht k q hk
    · intro h
      exact ⟨h 0 p rfl, fun k q hk => by
        simpa only [Nat.add_assoc, Nat.add_comm 1] using h (k + 1) q hk⟩

theorem Values.codes_bound {ps : List PrimTy} (vs : Values ps) (k : Nat) (p : PrimTy)
    (h : ps[k]? = some p) : vs.codes k < bound p := by
  induction ps generalizing k p with
  | nil => cases h
  | cons q ps ih =>
    cases k with
    | zero => cases h; exact (encode q vs.1).isLt
    | succ k => exact ih vs.2 k p h

theorem domain_codes {ps : List PrimTy} (vs : Values ps) : (domain ps).holds vs.codes := by
  exact (domainFrom_iff ps 0 vs.codes).2 (fun k p hk => by simpa only [Nat.zero_add] using vs.codes_bound k p hk)

/-- A domain proof is sufficient to decode every component. -/
def Values.decode : (ps : List PrimTy) → (x : Nat → Nat) → (domain ps).holds x → Values ps
  | [], _, _ => ()
  | p :: ps, x, h =>
      (ScalarCode.decode p ⟨x 0, by exact (domainFrom_iff (p :: ps) 0 x).1 h 0 p rfl⟩,
       Values.decode ps (fun k => x (k + 1)) (by
         apply (domainFrom_iff ps 0 _).2
         intro k q hk
         exact (domainFrom_iff (p :: ps) 0 x).1 h (k + 1) q hk))

theorem Values.codes_decode (ps : List PrimTy) (x : Nat → Nat) (h : (domain ps).holds x) :
    ∀ k < ps.length, (Values.decode ps x h).codes k = x k := by
  induction ps generalizing x with
  | nil => intro k hk; cases hk
  | cons p ps ih =>
    intro k hk
    cases k with
    | zero => exact congrArg Fin.val (encode_decode p _)
    | succ k => exact ih (fun j => x (j + 1)) _ k (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hk)

end ScalarCode

/-- A linear formula whose free variables fit its typed context. -/
structure TypedFormula (ps : List PrimTy) where
  formula : AFml
  width : formula.width ≤ ps.length

namespace TypedFormula

open ScalarCode

variable {ps : List PrimTy}

/-- The typed interpretation uses the exact, bijective scalar codes. -/
def holds (F : TypedFormula ps) (vs : Values ps) : Prop := F.formula.holds vs.codes

def Valid (F : TypedFormula ps) : Prop := ∀ vs, F.holds vs

/-- Domain constraints are premises, not extra goals or assumed facts. -/
def guarded (F : TypedFormula ps) : AFml := .imp (domain ps) F.formula

/-- Quantification over natural codes loses no typed inputs. -/
theorem valid_iff (F : TypedFormula ps) : F.Valid ↔ F.guarded.Valid := by
  constructor
  · intro hv x hd
    exact (F.formula.holds_agree _ x (fun k hk =>
      Values.codes_decode ps x hd k (Nat.lt_of_lt_of_le hk F.width))).1
      (hv (Values.decode ps x hd))
  · intro hv vs
    exact hv vs.codes (domain_codes vs)

/-- Reconstruct typed values from an actual false guarded assignment. -/
def countermodelOf (F : TypedFormula ps) (x : Nat → Nat) (h : ¬ F.guarded.holds x) :
    { vs : Values ps // ¬ F.holds vs } := by
  have hd : (domain ps).holds x := by
    apply Classical.byContradiction
    intro hn
    exact h (fun hx => (hn hx).elim)
  refine ⟨Values.decode ps x hd, ?_⟩
  intro hv
  apply h
  intro _
  exact (F.formula.holds_agree _ x (fun k hk =>
    Values.codes_decode ps x hd k (Nat.lt_of_lt_of_le hk F.width))).1 hv

/-- A false guarded assignment has a successful typed decoding. -/
def countermodel (F : TypedFormula ps) (h : F.guarded.decide = false) :
    { vs : Values ps // ¬ F.holds vs } :=
  let cm := F.guarded.countermodel h
  F.countermodelOf cm.val cm.property

/-- A total typed verdict: either all typed vectors satisfy the formula,
or an explicitly decoded vector falsifies it. Uses one graph traversal. -/
def verify (F : TypedFormula ps) : Sum (PLift F.Valid) { vs : Values ps // ¬ F.holds vs } := by
  match F.guarded.verify with
  | .inl h => exact .inl ⟨F.valid_iff.mpr h.down⟩
  | .inr cm => exact .inr (F.countermodelOf cm.val cm.property)

end TypedFormula

end Solidity.Linear
