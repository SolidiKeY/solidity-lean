import Solidity.Calculus.CallFunctionTermPower
import Solidity.Calculus.TermEq

/-! # Checked plans for actual old call-summary terms
A plan carries an exact intrinsic expansion certificate, not a name match.
The producer checks real terms and existing strict/no-push/value-only flags.
-/
namespace Solidity.CallFunctionPlan
open CallFunctionTable CallFunctionLeaf CallFunctionTermPower
variable {C : Contract} {Γ : Ctx}

/-- The actual old result term is the index of every plan and its equations. -/
structure Plan (out : Tm C Γ (.val .uint)) where
  base : Tm C (.val .uint :: Γ) (.val .uint)
  input : Idx Γ (.val .uint)
  level : Nat
  pushFree : base.pushFree = true
  valOnly : base.valOnly = true
  strict : base.strictReads 0 = true
  expansion : expanded? base input (2^level) = some out

/-- Internal expansion stops whenever an intermediate result exceeds the
actual old term's size. A separate step-count guard is checked before entry. -/
def boundedExpansion? (limit : Nat) (base : Tm C (.val .uint :: Γ) (.val .uint))
    (input : Idx Γ (.val .uint)) : Nat → Option (Tm C Γ (.val .uint))
  | 0 => if 1 ≤ limit then some (.pvV input) else none
  | n+1 => do
    let prev ← boundedExpansion? limit base input n
    let next ← inst? .refl base prev
    if next.size ≤ limit then some next else none

/-- Every bounded result carries an exact equation for the actual old-term
expansion, regardless of which intermediate guard refused other candidates. -/
theorem boundedExpansion_eq (limit : Nat)
    (base : Tm C (.val .uint :: Γ) (.val .uint)) (input : Idx Γ (.val .uint))
    (n : Nat) (out : Tm C Γ (.val .uint))
    (he : boundedExpansion? limit base input n = some out) :
    expanded? base input n = some out := by
  induction n generalizing out with
  | zero =>
    unfold boundedExpansion? at he
    split at he
    · cases he; rfl
    · cases he
  | succ n ih =>
    have hh : (boundedExpansion? limit base input n).bind (fun prev =>
        (inst? .refl base prev).bind (fun next =>
          if next.size ≤ limit then some next else none)) = some out := he
    obtain ⟨prev, hp, hr⟩ := Option.bind_eq_some_iff.mp hh
    obtain ⟨next, hi, hn⟩ := Option.bind_eq_some_iff.mp hr
    split at hn
    · cases hn
      simp only [expanded?, ih prev hp, Option.bind_some]
      exact hi
    · cases hn

/-- A retained expansion result never exceeds its checked syntax limit.
This is not a bound on transient substitution allocation or kernel bytes. -/
theorem boundedExpansion_size (limit : Nat)
    (base : Tm C (.val .uint :: Γ) (.val .uint)) (input : Idx Γ (.val .uint))
    (n : Nat) (out : Tm C Γ (.val .uint))
    (he : boundedExpansion? limit base input n = some out) : out.size ≤ limit := by
  cases n with
  | zero =>
    unfold boundedExpansion? at he
    split at he
    · rename_i hb
      cases he
      exact hb
    · cases he
  | succ n =>
    have hh : (boundedExpansion? limit base input n).bind (fun prev =>
        (inst? .refl base prev).bind (fun next =>
          if next.size ≤ limit then some next else none)) = some out := he
    obtain ⟨prev, hp, hr⟩ := Option.bind_eq_some_iff.mp hh
    obtain ⟨next, hi, hn⟩ := Option.bind_eq_some_iff.mp hr
    split at hn
    · rename_i hb
      cases hn
      exact hb
    · cases hn

/-- A proposed concrete base/level is accepted only with actual typed term
comparison. Level/step/intermediate size checks are derived from the actual
old term size; refusal returns ordinary handling to the caller. These are
producer resource guards, not new semantic validity premises. -/
def checked? (base : Tm C (.val .uint :: Γ) (.val .uint)) (level : Nat)
    (input : Idx Γ (.val .uint)) (out : Tm C Γ (.val .uint)) : Option (Plan out) :=
  if hp : base.pushFree = true then
    if hv : base.valOnly = true then
      if hs : base.strictReads 0 = true then
        if base.size ≤ out.size ∧ level ≤ Nat.log2 out.size then
          if 2^level ≤ out.size then
            match he : boundedExpansion? out.size base input (2^level) with
            | none => none
            | some candidate =>
              if hEq : candidate.beqR out = true then
                some ⟨base, input, level, hp, hv, hs, by
                  rw [← Tm.eq_of_beqR hEq]
                  exact boundedExpansion_eq out.size base input (2^level) candidate he⟩
              else none
          else none
        else none
      else none
    else none
  else none

/-- Actual checker acceptance certifies its input-derived expansion limits.
This does not apply to arbitrary manually constructed plans. -/
theorem checked_bounds (base : Tm C (.val .uint :: Γ) (.val .uint)) (level : Nat)
    (input : Idx Γ (.val .uint)) (out : Tm C Γ (.val .uint)) (plan : Plan out)
    (hc : checked? base level input out = some plan) :
    plan.base.size ≤ out.size ∧ plan.level ≤ Nat.log2 out.size ∧ 2^plan.level ≤ out.size := by
  unfold checked? at hc
  split at hc
  · split at hc
    · split at hc
      · split at hc
        · rename_i hrange
          split at hc
          · rename_i hsteps
            split at hc
            · cases hc
            · split at hc
              · cases hc
                exact ⟨hrange.1, hrange.2, hsteps⟩
              · cases hc
          · cases hc
        · cases hc
      · cases hc
    · cases hc
  · cases hc

/-- The complete emitted intrinsic leaf selected by an accepted checked plan. -/
def Plan.leaf {out : Tm C Γ (.val .uint)} (plan : Plan out) (m : Modality)
    (tableName inputName resultName : Var) (target : Idx Γ (.val .uint))
    (φ : Fml C Γ) : Fml C Γ :=
  CallFunctionLeaf.leaf m tableName inputName resultName plan.base plan.level target plan.input φ

/-- Every actual accepted plan gives exact old-assignment semantics at all
states/posts and both modalities. No future theorem or user premise is assumed. -/
theorem Plan.holds {out : Tm C Γ (.val .uint)} (plan : Plan out) (m : Modality)
    (tableName inputName resultName : Var) (target : Idx Γ (.val .uint))
    (φ : Fml C Γ) (σ : State C Γ) :
    holds σ (plan.leaf m tableName inputName resultName target φ) ↔
      holds σ (.upd m (Upd.nil.snoc (.local target (.val out))) φ) :=
  holds_assignment m tableName inputName resultName plan.base plan.pushFree plan.valOnly
    plan.strict plan.level target plan.input out plan.expansion φ σ

/-- Full emitted formula syntax, including every definition and caller post. -/
theorem Plan.size {out : Tm C Γ (.val .uint)} (plan : Plan out) (m : Modality)
    (tableName inputName resultName : Var) (target : Idx Γ (.val .uint))
    (φ : Fml C Γ) :
    (plan.leaf m tableName inputName resultName target φ).tmSize =
      2*plan.base.size + φ.tmSize + 33*plan.level + 44 +
        (haltPost (C := C) (Δ := Γ) m).tmSize :=
  leaf_size m tableName inputName resultName plan.base plan.level target plan.input φ

end Solidity.CallFunctionPlan
