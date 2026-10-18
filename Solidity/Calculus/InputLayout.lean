import Solidity.Calculus.ParameterLayout

/-!
# Transaction inputs beside typed parameters and storage

Every observed environment field is a bounded uint. Distinct fields can be
reconstructed independently in an actual initial state, including the
contract's balance. The remaining state components retain their values.
-/

namespace Solidity.Decide.Inputs

open ReadRealization Linear ScalarCode

variable {C : Contract}

def types : List EnvKey → List Parameter → List (Ref C) → List PrimTy
  | [], ps, rs => Parameters.types ps rs
  | _ :: es, ps, rs => .uint :: types es ps rs

def observe : (es : List EnvKey) → (ps : List Parameter) → (rs : List (Ref C)) →
    State C [] → AEnv → Values (types es ps rs)
  | [], ps, rs, g, ν => Parameters.observe ps rs g.storage ν
  | e :: es, ps, rs, g, ν => (g.envVal e, observe es ps rs g ν)

def index (e : EnvKey) : List EnvKey → Nat
  | [] => 0
  | k :: es => if e = k then 0 else index e es + 1

def set (g : State C []) (e : EnvKey) (v : PrimTy.uint.Denote) : State C [] :=
  match e with
  | .msgSender => { g with tx := { g.tx with msgSender := v } }
  | .msgValue => { g with tx := { g.tx with msgValue := v } }
  | .timestamp => { g with tx := { g.tx with timestamp := v } }
  | .selfBalance => { g with selfBalance := v }
  | .selfAddress => { g with tx := { g.tx with selfAddress := v } }

theorem storage_set (g : State C []) (e : EnvKey) (v : PrimTy.uint.Denote) :
    (set g e v).storage = g.storage := by
  cases e <;> rfl

theorem envVal_set (g : State C []) (e : EnvKey) (v : PrimTy.uint.Denote) :
    (set g e v).envVal e = v := by
  cases e <;> rfl

theorem envVal_set_ne (g : State C []) (e k : EnvKey) (v : PrimTy.uint.Denote) (h : e ≠ k) :
    (set g k v).envVal e = g.envVal e := by
  cases e <;> cases k <;> first | exact (h rfl).elim | rfl

theorem codes_tail (es : List EnvKey) (ps : List Parameter) (rs : List (Ref C))
    (g : State C []) (ν : AEnv) (k : Nat) :
    (observe es ps rs g ν).codes (es.length + k) = (Parameters.observe ps rs g.storage ν).codes k := by
  induction es with
  | nil => simp only [observe, List.length_nil, Nat.zero_add]
  | cons e es ih =>
    simpa only [List.length_cons, Nat.succ_add, observe, Values.codes] using ih

theorem codes_env (es : List EnvKey) (ps : List Parameter) (rs : List (Ref C))
    (g : State C []) (ν : AEnv) (e : EnvKey) (h : e ∈ es) :
    (observe es ps rs g ν).codes (index e es) = (encode .uint (g.envVal e)).val := by
  induction es with
  | nil => cases h
  | cons k es ih =>
    by_cases he : e = k
    · subst e
      simp only [index, ↓reduceIte, observe, Values.codes]
    · simpa only [index, he, ↓reduceIte, observe, Values.codes] using
        ih ((List.mem_cons.mp h).resolve_left he)

def realize : (es : List EnvKey) → (ps : List Parameter) → (rs : List (Ref C)) →
    Values (types es ps rs) → State C [] × AEnv
  | [], ps, rs, vs =>
    let model := Parameters.realize ps rs vs
    ({ State.init C with storage := model.1 }, model.2)
  | e :: es, ps, rs, vs =>
    let tail := realize es ps rs vs.2
    (set tail.1 e vs.1, tail.2)

theorem observe_set_ne (es : List EnvKey) (ps : List Parameter) (rs : List (Ref C))
    (g : State C []) (ν : AEnv) (e : EnvKey) (v : PrimTy.uint.Denote) (h : e ∉ es) :
    observe es ps rs (set g e v) ν = observe es ps rs g ν := by
  induction es with
  | nil => simp only [observe, storage_set]
  | cons k es ih =>
    have hk : k ≠ e := fun he => h (he ▸ List.mem_cons_self)
    have ht : e ∉ es := fun hm => h (List.mem_cons_of_mem k hm)
    simp only [observe, envVal_set_ne g k e v hk, ih ht]

theorem observe_realize (es : List EnvKey) (ps : List Parameter) (rs : List (Ref C))
    (he : es.Nodup) (hp : ps.Nodup) (hr : rs.Nodup) (vs : Values (types es ps rs)) :
    observe es ps rs (realize es ps rs vs).1 (realize es ps rs vs).2 = vs := by
  induction es with
  | nil => exact Parameters.observe_realize ps rs hp hr vs
  | cons e es ih =>
    have he' : e ∉ es ∧ es.Nodup := List.nodup_cons.mp he
    simp only [realize, observe, envVal_set, observe_set_ne es ps rs _ _ e _ he'.1, ih he'.2]
    rfl

theorem observe_assign (es : List EnvKey) (ps : List Parameter) (rs : List (Ref C))
    (g : State C []) (chosen ν : AEnv) :
    observe es ps rs g (Parameters.assign ps chosen ν) = observe es ps rs g chosen := by
  induction es with
  | nil => exact Parameters.observe_assign ps rs g.storage chosen ν
  | cons e es ih => exact congrArg (Prod.mk (g.envVal e)) ih

end Solidity.Decide.Inputs
