import Solidity.Calculus.InputReduction
import Solidity.Calculus.ActiveReadConstraints

/-!
# Automatic arithmetic for flattened dependent-read leaves

The shared checked compiler receives all typed atoms in the generated leaf,
including fresh read results. Complete arithmetic selects values; the exact
flattening bridge reconstructs actual storage. The interface here concerns
leaf validity over all atom environments; universal-prefix/source transport
is kept separate.
-/

namespace Solidity.Decide

open Semantics ReadRealization Linear ScalarCode

variable {C : Contract}

def LTm.parameters : {s : Srt} → LTm C s → List Parameter
  | _, .var (p := p) k => [⟨p, k⟩]
  | _, .app0 _ | _, .err => []
  | _, .app1 _ a | _, .obsW a | _, .obsL a | _, .obsH a => a.parameters
  | _, .app2 _ a b | _, .index _ a b | _, .seq a b | _, .orElse a b => a.parameters ++ b.parameters
  | _, .app3 _ a b c => a.parameters ++ b.parameters ++ c.parameters
  | _, .kite a b t e => a.parameters ++ b.parameters ++ t.parameters ++ e.parameters

def LFml.parameters : LFml C → List Parameter
  | .tt => []
  | .eq a b => a.parameters ++ b.parameters
  | .not φ => φ.parameters
  | .and φ ψ | .imp φ ψ => φ.parameters ++ ψ.parameters
  | .all _ _ φ => φ.parameters

/-- Pointwise arithmetic encoding of a quantifier-free leaf, with actual
typed representatives for every arithmetic input. -/
structure LeafArithmetic (φ : LFml C) where
  environment : List EnvKey
  distinctEnvironment : environment.Nodup
  parameters : List Parameter
  distinctParameters : parameters.Nodup
  refs : List (Ref C)
  distinctRefs : refs.Nodup
  arithmetic : TypedFormula (Inputs.types environment parameters refs)
  correct : ∀ (g : State C []) (ν : AEnv),
    arithmetic.holds (Inputs.observe environment parameters refs g ν) ↔ φ.holds g ν

def leafArithmetic? (φ : LFml C) : Option (LeafArithmetic φ) := do
  let es := Inputs.unique (Inputs.formulaKeys φ)
  let ps := φ.parameters.eraseDups
  let encoded ← StorageEncoding.ofFormula? (ps := ps) (es := es) φ
  let rs := Layout.unique encoded.refs
  if he : es.Nodup then
    if hp : ps.Nodup then
      if hr : rs.Nodup then
        if hc : ∀ q ∈ encoded.refs, q ∈ rs then
          if hw : (encoded.lower rs).width ≤ (Inputs.types es ps rs).length then
            return ⟨es, he, ps, hp, rs, hr, ⟨encoded.lower rs, hw⟩,
              fun g ν => encoded.correct rs hc g ν⟩
          else none
        else none
      else none
    else none
  else none

namespace LeafArithmetic

theorem valid_iff {φ : LFml C} (r : LeafArithmetic φ) : φ.Valid ↔ r.arithmetic.Valid := by
  constructor
  · intro hv vs
    have h := (r.correct (Inputs.realize r.environment r.parameters r.refs vs).1
      (Inputs.realize r.environment r.parameters r.refs vs).2).mpr (hv _ _)
    simpa only [Inputs.observe_realize _ _ _ r.distinctEnvironment r.distinctParameters r.distinctRefs] using h
  · intro hv g ν
    exact (r.correct g ν).mp (hv _)

structure Countermodel {φ : LFml C} (r : LeafArithmetic φ) where
  state : State C []
  atoms : AEnv
  refutes : ¬ φ.holds state atoms

def countermodelOf {φ : LFml C} (r : LeafArithmetic φ)
    (cm : {vs // ¬ r.arithmetic.holds vs}) : r.Countermodel := by
  let model := Inputs.realize r.environment r.parameters r.refs cm.val
  refine ⟨model.1, model.2, fun hv => cm.property ?_⟩
  simpa only [model, Inputs.observe_realize _ _ _ r.distinctEnvironment r.distinctParameters r.distinctRefs]
    using (r.correct model.1 model.2).mpr hv

end LeafArithmetic

structure FlattenedArithmetic (φ : LFml C) where
  flattening : ReadFlattening φ φ.atomBound
  encoding : LeafArithmetic flattening.formula

/-- Check the quadratic alias-pair budget before constructing its formula. -/
def flattenedArithmetic? (budget : Nat) (φ : LFml C) : Option (FlattenedArithmetic φ) := do
  let r ← readFlatten? budget φ
  if r.flat.reads.length * r.flat.reads.length ≤ budget then
    return ⟨r, ← leafArithmetic? r.formula⟩
  else none

namespace FlattenedArithmetic

theorem valid_iff {φ : LFml C} (r : FlattenedArithmetic φ) : φ.Valid ↔ r.encoding.arithmetic.Valid :=
  r.flattening.formula_valid_iff.symm.trans r.encoding.valid_iff

structure Countermodel {φ : LFml C} (r : FlattenedArithmetic φ) where
  state : State C []
  atoms : AEnv
  refutes : ¬ φ.holds state atoms

def countermodelOf {φ : LFml C} (r : FlattenedArithmetic φ)
    (cm : {vs // ¬ r.encoding.arithmetic.holds vs}) : r.Countermodel := by
  let raw := r.encoding.countermodelOf cm
  have hn : ¬ ((ReadOccurrence.constraints r.flattening.flat.reads).holds raw.state raw.atoms →
      r.flattening.flat.formula.holds raw.state raw.atoms) := raw.refutes
  have hc := Classical.byContradiction (fun h => hn (fun hh => (h hh).elim))
  have hf := fun h => hn (fun _ => h)
  let actual := r.flattening.countermodel raw.state raw.atoms
    ((r.flattening.layout.constraints_iff _ _).mp hc) hf
  exact ⟨actual.val, raw.atoms, actual.property⟩

def verify {φ : LFml C} (r : FlattenedArithmetic φ) : Sum (PLift φ.Valid) r.Countermodel :=
  match r.encoding.arithmetic.verify with
  | .inl h => .inl ⟨r.valid_iff.mpr h.down⟩
  | .inr cm => .inr (r.countermodelOf cm)

theorem valid_of_decide {φ : LFml C} (r : FlattenedArithmetic φ)
    (h : r.encoding.arithmetic.guarded.decide = true) : φ.Valid :=
  r.valid_iff.mpr (r.encoding.arithmetic.valid_iff.mpr ((AFml.decide_iff _).mp h))

def checkCodes {φ : LFml C} (r : FlattenedArithmetic φ) (xs : List Nat) : Bool :=
  r.encoding.arithmetic.guarded.check (fun k => xs[k]?.getD 0)

def countermodelOfCodes {φ : LFml C} (r : FlattenedArithmetic φ) (xs : List Nat)
    (h : r.checkCodes xs = false) : r.Countermodel :=
  r.countermodelOf (r.encoding.arithmetic.countermodelOf (fun k => xs[k]?.getD 0)
    (fun hv => Bool.false_ne_true (h ▸ (AFml.check_iff _ _).mpr hv)))

end FlattenedArithmetic

end Solidity.Decide
