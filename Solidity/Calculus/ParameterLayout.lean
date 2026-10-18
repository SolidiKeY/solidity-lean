import Solidity.Calculus.ReadLayout
import Solidity.Calculus.DecideLang

/-!
# Finite typed parameters beside storage reads

Parameters retain both their primitive type and their atom position.
The parameter prefix of a scalar vector is followed by the actual storage
layout. Distinct parameter keys can be reconstructed independently, even
when different primitive types use the same numbered position.
-/

namespace Solidity.Decide

open ReadRealization Linear ScalarCode

structure Parameter where
  prim : PrimTy
  index : Nat
  deriving DecidableEq

namespace Parameter

abbrev Value (p : Parameter) := p.prim.Denote

def read (p : Parameter) (ν : AEnv) : p.Value := ν.get p.prim p.index
def set (p : Parameter) (ν : AEnv) (v : p.Value) : AEnv := ν.set p.prim p.index v

theorem read_set (p : Parameter) (ν : AEnv) (v : p.Value) : p.read (p.set ν v) = v :=
  AEnv.get_set_self ν p.prim p.index v

theorem read_set_ne (a b : Parameter) (h : a ≠ b) (ν : AEnv) (v : b.Value) :
    a.read (b.set ν v) = a.read ν := by
  obtain ⟨p, k⟩ := a
  obtain ⟨q, j⟩ := b
  by_cases hk : k = j
  · subst j
    cases p <;> cases q <;> first | rfl | exact (h rfl).elim
  · exact AEnv.get_set_ne ν q p v hk

end Parameter

namespace Parameters

variable {C : Contract}

/-- Instantiate a universal prefix with the chosen valuation's values. -/
def assign : List Parameter → AEnv → AEnv → AEnv
  | [], _, ν => ν
  | p :: ps, chosen, ν => assign ps chosen (p.set ν (p.read chosen))

theorem read_assign (ps : List Parameter) (p : Parameter) (chosen ν : AEnv) :
    p.read (assign ps chosen ν) = if p ∈ ps then p.read chosen else p.read ν := by
  induction ps generalizing ν with
  | nil => simp only [assign, List.not_mem_nil, ↓reduceIte]
  | cons q ps ih =>
    rw [assign, ih]
    by_cases ht : p ∈ ps
    · simp only [ht, List.mem_cons_of_mem q ht, ↓reduceIte]
    · by_cases he : p = q
      · subst p
        simp only [ht, List.mem_cons_self, ↓reduceIte, Parameter.read_set]
      · simp only [List.mem_cons, he, ht, false_or, ↓reduceIte, Parameter.read_set_ne p q he]

def types (ps : List Parameter) (rs : List (Ref C)) : List PrimTy := ps.map Parameter.prim ++ Layout.types rs

def observe : (ps : List Parameter) → (rs : List (Ref C)) → Storage C → AEnv → Values (types ps rs)
  | [], rs, st, _ => Layout.observe rs st
  | p :: ps, rs, st, ν => (p.read ν, observe ps rs st ν)

def index (p : Parameter) : List Parameter → Nat
  | [] => 0
  | q :: ps => if p = q then 0 else index p ps + 1

theorem codes_parameter (ps : List Parameter) (p : Parameter) (rs : List (Ref C))
    (st : Storage C) (ν : AEnv) (h : p ∈ ps) :
    (observe ps rs st ν).codes (index p ps) = (encode p.prim (p.read ν)).val := by
  induction ps with
  | nil => cases h
  | cons q qs ih =>
    by_cases he : p = q
    · subst p
      simp only [index, ↓reduceIte, observe, Values.codes]
    · simp only [index, he, ↓reduceIte, observe, Values.codes]
      exact ih ((List.mem_cons.mp h).resolve_left he)

theorem codes_storage (ps : List Parameter) (rs : List (Ref C)) (st : Storage C) (ν : AEnv) (k : Nat) :
    (observe ps rs st ν).codes (ps.length + k) = (Layout.observe rs st).codes k := by
  induction ps with
  | nil => simp only [observe, List.length_nil, Nat.zero_add]
  | cons p ps ih =>
    simpa only [List.length_cons, Nat.succ_add, observe, Values.codes] using ih

def realize : (ps : List Parameter) → (rs : List (Ref C)) → Values (types ps rs) → Storage C × AEnv
  | [], rs, vs => (Layout.realize rs vs, AEnv.dflt)
  | p :: ps, rs, vs =>
    let tail := realize ps rs vs.2
    (tail.1, p.set tail.2 vs.1)

theorem observe_set_ne (ps : List Parameter) (rs : List (Ref C)) (st : Storage C) (ν : AEnv)
    (p : Parameter) (v : p.Value) (h : p ∉ ps) :
    observe ps rs st (p.set ν v) = observe ps rs st ν := by
  induction ps with
  | nil => rfl
  | cons q ps ih =>
    have hne : q ≠ p := fun he => h (he ▸ List.mem_cons_self)
    have ht : p ∉ ps := fun hm => h (List.mem_cons_of_mem q hm)
    simp only [observe, Parameter.read_set_ne q p hne, ih ht]

theorem observe_assign (ps : List Parameter) (rs : List (Ref C)) (st : Storage C) (chosen ν : AEnv) :
    observe ps rs st (assign ps chosen ν) = observe ps rs st chosen := by
  induction ps generalizing ν with
  | nil => rfl
  | cons p ps ih =>
    change (p.read (assign (p :: ps) chosen ν),
      observe ps rs st (assign ps chosen (p.set ν (p.read chosen)))) =
        (p.read chosen, observe ps rs st chosen)
    rw [read_assign, if_pos List.mem_cons_self, ih]

theorem observe_realize (ps : List Parameter) (rs : List (Ref C)) (hp : ps.Nodup) (hr : rs.Nodup)
    (vs : Values (types ps rs)) :
    observe ps rs (realize ps rs vs).1 (realize ps rs vs).2 = vs := by
  induction ps with
  | nil => exact Layout.observe_realize rs hr vs
  | cons p ps ih =>
    have hp' : p ∉ ps ∧ ps.Nodup := List.nodup_cons.mp hp
    change (p.read (p.set (realize ps rs vs.2).2 vs.1),
      observe ps rs (realize ps rs vs.2).1 (p.set (realize ps rs vs.2).2 vs.1)) = vs
    rw [Parameter.read_set, observe_set_ne ps rs _ _ p vs.1 hp'.1, ih hp'.2 vs.2]
    rfl

end Parameters

end Solidity.Decide
