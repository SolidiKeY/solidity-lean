import Solidity.Calculus.ProgramReduction

/-!
# Complete source decisions with actual transaction inputs

The environment prefix contains only fields read by the normalized leaf.
Its values, universally bound parameters and storage reads have independent
typed representatives. A negative verdict reconstructs them together.
-/

namespace Solidity.Decide

open ReadRealization Linear ScalarCode

variable {C : Contract}

namespace Inputs

def termKeys : {s : Srt} → LTm C s → List EnvKey
  | _, .app0 (.env e) => [e]
  | _, .app1 _ a | _, .obsW a | _, .obsL a | _, .obsH a => termKeys a
  | _, .app2 _ a b | _, .index _ a b | _, .seq a b | _, .orElse a b => termKeys a ++ termKeys b
  | _, .app3 _ a b c => termKeys a ++ termKeys b ++ termKeys c
  | _, .kite a b t e => termKeys a ++ termKeys b ++ termKeys t ++ termKeys e
  | _, .var _ | _, .app0 _ | _, .err => []

def formulaKeys : LFml C → List EnvKey
  | .tt => []
  | .eq a b => termKeys a ++ termKeys b
  | .not φ | .all _ _ φ => formulaKeys φ
  | .and φ ψ | .imp φ ψ => formulaKeys φ ++ formulaKeys ψ

def unique : List EnvKey → List EnvKey
  | [] => []
  | e :: es => let tail := unique es; if e ∈ tail then tail else e :: tail

end Inputs

structure InputReduction (φ : Fml C []) where
  environment : List EnvKey
  distinctEnvironment : environment.Nodup
  parameters : List Parameter
  distinctParameters : parameters.Nodup
  refs : List (Ref C)
  distinctRefs : refs.Nodup
  arithmetic : TypedFormula (Inputs.types environment parameters refs)
  meaning : ∀ σ : State C [],
    (∀ ν, arithmetic.holds (Inputs.observe environment parameters refs σ ν)) ↔ holds σ φ

/-- Normalize source programs, then compile all observed initial inputs. -/
def inputReduction? (φ : Fml C []) : Option (InputReduction φ) := do
  let d ← ProgramNormalization.ofFormula? 2048 φ
  let r ← sourceReduction? d.formula
  let sentence ← UniversalPrefix.ofFormula? 1024 r.leaf.elim
  let es := Inputs.unique (Inputs.formulaKeys sentence.body)
  let encoded ← StorageEncoding.ofFormula? (ps := sentence.parameters) (es := es) sentence.body
  let rs := Layout.unique encoded.refs
  if he : es.Nodup then
    if hp : sentence.parameters.Nodup then
      if hr : rs.Nodup then
        if hc : ∀ q ∈ encoded.refs, q ∈ rs then
          if hw : (encoded.lower rs).width ≤ (Inputs.types es sentence.parameters rs).length then
            return ⟨es, he, sentence.parameters, hp, rs, hr, ⟨encoded.lower rs, hw⟩, by
              intro σ
              apply Iff.trans ?_ ((r.elim_holds_iff σ).trans (d.correct σ))
              constructor
              · intro h
                exact sentence.close σ AEnv.dflt (fun ν => (encoded.correct rs hc σ ν).1 (h ν))
              · intro h ν
                simpa only [Inputs.observe_assign] using
                  (encoded.correct rs hc σ (Parameters.assign sentence.parameters ν AEnv.dflt)).2
                    (sentence.instantiate σ AEnv.dflt ν h)⟩
          else none
        else none
      else none
    else none
  else none

namespace InputReduction

structure Countermodel {φ : Fml C []} (r : InputReduction φ) where
  state : State C []
  atoms : AEnv
  falseInstance : ¬ r.arithmetic.holds (Inputs.observe r.environment r.parameters r.refs state atoms)

theorem Countermodel.refutes {φ : Fml C []} {r : InputReduction φ} (cm : r.Countermodel) :
    ¬ holds cm.state φ := fun h => cm.falseInstance ((r.meaning cm.state).2 h cm.atoms)

theorem valid_iff {φ : Fml C []} (r : InputReduction φ) : Fml.Valid φ ↔ r.arithmetic.Valid := by
  constructor
  · intro h vs
    let model : State C [] × AEnv := Inputs.realize r.environment r.parameters r.refs vs
    have hv : r.arithmetic.holds (Inputs.observe r.environment r.parameters r.refs model.1 model.2) :=
      (r.meaning model.1).2 (h model.1) model.2
    simpa only [model, Inputs.observe_realize r.environment r.parameters r.refs
      r.distinctEnvironment r.distinctParameters r.distinctRefs] using hv
  · intro h σ
    exact (r.meaning σ).1 (fun _ => h _)

/-- A positive arithmetic computation proves the original source claim. -/
theorem valid_of_decide {φ : Fml C []} (r : InputReduction φ)
    (h : r.arithmetic.guarded.decide = true) : Fml.Valid φ :=
  r.valid_iff.mpr (r.arithmetic.valid_iff.mpr ((AFml.decide_iff _).mp h))

def countermodelOf {φ : Fml C []} (r : InputReduction φ)
    (cm : { vs // ¬ r.arithmetic.holds vs }) : r.Countermodel := by
  let model : State C [] × AEnv := Inputs.realize r.environment r.parameters r.refs cm.val
  refine ⟨model.1, model.2, ?_⟩
  simpa only [model, Inputs.observe_realize r.environment r.parameters r.refs
    r.distinctEnvironment r.distinctParameters r.distinctRefs] using cm.property

def countermodelOfCheck {φ : Fml C []} (r : InputReduction φ)
    (vs : Values (Inputs.types r.environment r.parameters r.refs))
    (h : r.arithmetic.formula.check vs.codes = false) : r.Countermodel :=
  r.countermodelOf ⟨vs, fun hv => Bool.false_ne_true (h ▸ (AFml.check_iff _ _).2 hv)⟩

/-- Replay only a finite assignment after compiled graph exploration.
The guarded check establishes both the typed domains and the false claim. -/
def checkCodes {φ : Fml C []} (r : InputReduction φ) (xs : List Nat) : Bool :=
  r.arithmetic.guarded.check (fun k => xs[k]?.getD 0)

/-- Reconstruct the actual typed initial state from checked scalar codes. -/
def countermodelOfCodes {φ : Fml C []} (r : InputReduction φ) (xs : List Nat)
    (h : r.arithmetic.guarded.check (fun k => xs[k]?.getD 0) = false) : r.Countermodel :=
  r.countermodelOf (r.arithmetic.countermodelOf (fun k => xs[k]?.getD 0)
    (fun hv => Bool.false_ne_true (h ▸ (AFml.check_iff _ _).mpr hv)))

/-- A finite checked assignment refutes the original source formula. -/
theorem not_valid_of_codes {φ : Fml C []} (r : InputReduction φ) (xs : List Nat)
    (h : r.arithmetic.guarded.check (fun k => xs[k]?.getD 0) = false) : ¬ Fml.Valid φ :=
  fun hv => (r.countermodelOfCodes xs h).refutes (hv (r.countermodelOfCodes xs h).state)

def verify {φ : Fml C []} (r : InputReduction φ) : Sum (PLift (Fml.Valid φ)) r.Countermodel :=
  match r.arithmetic.verify with
  | .inl h => .inl ⟨fun σ => (r.meaning σ).1 (fun _ => h.down _)⟩
  | .inr cm => .inr (r.countermodelOf cm)

end InputReduction

end Solidity.Decide
