import Solidity.Calculus.CheckedLinear

/-!
# Complete decisions with a typed universal parameter prefix

The prefix chooses actual values for every parameter; it is not sampled.
The body uses the shared checked-expression compiler. A false arithmetic
assignment reconstructs storage and the parameter instance together.
-/

namespace Solidity.Decide

open ReadRealization Linear ScalarCode

variable {C : Contract}

structure UniversalPrefix (φ : LFml C) where
  parameters : List Parameter
  body : LFml C
  close : ∀ (g : State C []) (ν : AEnv), (∀ ν', body.holds g ν') → φ.holds g ν
  instantiate : ∀ (g : State C []) (ν chosen : AEnv), φ.holds g ν →
    body.holds g (Parameters.assign parameters chosen ν)

namespace UniversalPrefix

def base (φ : LFml C) : UniversalPrefix φ :=
  ⟨[], φ, fun _ ν h => h ν, fun _ _ _ h => h⟩

def all (k : Nat) (p : PrimTy) {φ : LFml C} (r : UniversalPrefix φ) :
    UniversalPrefix (.all k p φ) :=
  ⟨⟨p, k⟩ :: r.parameters, r.body,
    fun g ν h v => r.close g (ν.set p k v) h,
    fun g ν chosen h => r.instantiate g (ν.set p k (chosen.get p k)) chosen (h (chosen.get p k))⟩

def ofFormula? : Nat → (φ : LFml C) → Option (UniversalPrefix φ)
  | 0, _ => none
  | fuel + 1, .all k p φ => (ofFormula? fuel φ).map (all k p)
  | _ + 1, φ => some (base φ)

end UniversalPrefix

structure ParameterReduction (φ : Fml C []) where
  parameters : List Parameter
  distinctParameters : parameters.Nodup
  refs : List (Ref C)
  distinctRefs : refs.Nodup
  arithmetic : TypedFormula (Parameters.types parameters refs)
  meaning : ∀ σ : State C [],
    (∀ ν, arithmetic.holds (Parameters.observe parameters refs σ.storage ν)) ↔ holds σ φ

def parameterReduction? (φ : Fml C []) : Option (ParameterReduction φ) := do
  let r ← sourceReduction? φ
  let sentence ← UniversalPrefix.ofFormula? 1024 r.leaf.elim
  let encoded ← StorageEncoding.ofFormula? (ps := sentence.parameters) (es := []) sentence.body
  let rs := Layout.unique encoded.refs
  if hp : sentence.parameters.Nodup then
    if hr : rs.Nodup then
      if hc : ∀ q ∈ encoded.refs, q ∈ rs then
        if hw : (encoded.lower rs).width ≤ (Parameters.types sentence.parameters rs).length then
          return ⟨sentence.parameters, hp, rs, hr, ⟨encoded.lower rs, hw⟩, by
            intro σ
            apply Iff.trans ?_ (r.elim_holds_iff σ)
            constructor
            · intro h
              exact sentence.close σ AEnv.dflt (fun ν => (encoded.correct rs hc σ ν).1 (h ν))
            · intro h ν
              have hb : sentence.body.holds σ (Parameters.assign sentence.parameters ν AEnv.dflt) :=
                sentence.instantiate σ AEnv.dflt ν h
              have ha : (encoded.lower rs).holds
                  (Parameters.observe sentence.parameters rs σ.storage
                    (Parameters.assign sentence.parameters ν AEnv.dflt)).codes :=
                (encoded.correct rs hc σ _).2 hb
              rw [Parameters.observe_assign] at ha
              exact ha⟩
        else none
      else none
    else none
  else none

namespace ParameterReduction

/-- Keep computed layout data explicit, so elaborating a typed witness need
not unfold the source recognizer to discover its parameter and read types. -/
def withLayout {φ : Fml C []} (r : ParameterReduction φ) (ps : List Parameter)
    (rs : List (Ref C)) (hp : r.parameters = ps) (hr : r.refs = rs) : ParameterReduction φ :=
  { parameters := ps
    distinctParameters := hp ▸ r.distinctParameters
    refs := rs
    distinctRefs := hr ▸ r.distinctRefs
    arithmetic := ⟨r.arithmetic.formula, by
      simpa only [← hp, ← hr] using r.arithmetic.width⟩
    meaning := by
      subst ps rs
      exact r.meaning }

structure Countermodel {φ : Fml C []} (r : ParameterReduction φ) where
  state : State C []
  atoms : AEnv
  falseInstance : ¬ r.arithmetic.holds (Parameters.observe r.parameters r.refs state.storage atoms)

theorem Countermodel.refutes {φ : Fml C []} {r : ParameterReduction φ} (cm : r.Countermodel) :
    ¬ holds cm.state φ := fun h => cm.falseInstance ((r.meaning cm.state).2 h cm.atoms)

theorem valid_iff {φ : Fml C []} (r : ParameterReduction φ) : Fml.Valid φ ↔ r.arithmetic.Valid := by
  constructor
  · intro h vs
    let model : Storage C × AEnv := Parameters.realize r.parameters r.refs vs
    let σ : State C [] := { State.init C with storage := model.1 }
    have hv : r.arithmetic.holds (Parameters.observe r.parameters r.refs σ.storage model.2) :=
      (r.meaning σ).2 (h σ) model.2
    change r.arithmetic.holds (Parameters.observe r.parameters r.refs
      (Parameters.realize r.parameters r.refs vs).1 (Parameters.realize r.parameters r.refs vs).2) at hv
    rw [Parameters.observe_realize _ _ r.distinctParameters r.distinctRefs] at hv
    exact hv
  · intro h σ
    exact (r.meaning σ).1 (fun _ => h _)

def countermodelOf {φ : Fml C []} (r : ParameterReduction φ)
    (cm : { vs // ¬ r.arithmetic.holds vs }) : r.Countermodel := by
  let model : Storage C × AEnv := Parameters.realize r.parameters r.refs cm.val
  refine ⟨{ State.init C with storage := model.1 }, model.2, ?_⟩
  change ¬ r.arithmetic.holds (Parameters.observe r.parameters r.refs
    (Parameters.realize r.parameters r.refs cm.val).1 (Parameters.realize r.parameters r.refs cm.val).2)
  rw [Parameters.observe_realize _ _ r.distinctParameters r.distinctRefs]
  exact cm.property

def countermodel {φ : Fml C []} (r : ParameterReduction φ)
    (h : r.arithmetic.guarded.decide = false) : r.Countermodel := r.countermodelOf (r.arithmetic.countermodel h)

def countermodelOfCheck {φ : Fml C []} (r : ParameterReduction φ)
    (vs : Values (Parameters.types r.parameters r.refs))
    (h : r.arithmetic.formula.check vs.codes = false) : r.Countermodel :=
  r.countermodelOf ⟨vs, fun hv => Bool.false_ne_true (h ▸ (AFml.check_iff _ _).2 hv)⟩

def verify {φ : Fml C []} (r : ParameterReduction φ) : Sum (PLift (Fml.Valid φ)) r.Countermodel :=
  match r.arithmetic.verify with
  | .inl h => .inl ⟨fun σ => (r.meaning σ).1 (fun _ => h.down _)⟩
  | .inr cm => .inr (r.countermodelOf cm)

end ParameterReduction

end Solidity.Decide
