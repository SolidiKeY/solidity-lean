import Solidity.Calculus.QueryReduction
import Solidity.Calculus.ReadLayout
import Solidity.Calculus.LinearForms

/-!
# Exact arithmetic compilation of static primitive reads

This initial source bridge recognizes logical combinations of equalities
between primitive literals/defined closed expressions and declared storage
reads with literal mapping
keys. It computes a distinct layout, so aliases share a scalar variable.
The complete bounded arithmetic verdict is transported to the original
scoped formula. Unsupported terms, binders, programs and updates return
`none`, never a semantic verdict.
-/

namespace Solidity.Decide

open Semantics ReadRealization Linear ScalarCode

variable {C : Contract}

/-- A path independent of the starting state and atom environment. -/
structure StaticPath {T : Ty} (t : LTm C (.path T)) where
  ref : SRef C T
  declared : ref.Declared
  eval : ∀ (g : State C []) (ν : AEnv), t.eval g ν = some ref

namespace StaticPath

private def literal? {p : PrimTy} (t : LTm C (.val p)) :
    Option { v : p.Denote // ∀ (g : State C []) (ν : AEnv), t.eval g ν = some v } :=
  match t with
  | .app0 (.lit v) => some ⟨v, fun _ _ => rfl⟩
  | _ => none

private def ofTermFuel? : Nat → {T : Ty} → (t : LTm C (.path T)) → Option (StaticPath t)
  | 0, _, _ => none
  | _ + 1, _, .app0 (.root r h) => some ⟨SRef.ofRoot r h, .nil, fun _ _ => rfl⟩
  | fuel + 1, _, .app1 (.field h) q => do
    let r ← ofTermFuel? fuel q
    return ⟨r.ref.field h, r.declared.append (.field h .nil), by
      intro g ν
      rw [LTm.eval_app1, Close.Op1.eval_field, r.eval g ν]
      rfl⟩
  | fuel + 1, _, .index .map q key => do
    let r ← ofTermFuel? fuel q
    let kv ← literal? key
    let k := kv.val
    return ⟨r.ref.index .map k, by
      change (r.ref.path.append (Path.index .map k)).Declared
      rw [Path.index_map]
      exact r.declared.append (.key k .nil), by
      intro g ν
      rw [LTm.eval_index, r.eval g ν, kv.property g ν]
      rfl⟩
  | _ + 1, _, _ => none

/-- Bounded path recognition; exhaustion is unsupported, never falsity. -/
def ofTerm? {T : Ty} (t : LTm C (.path T)) : Option (StaticPath t) := ofTermFuel? 1024 t

end StaticPath

/-- A closed primitive expression with its exact optional evaluation.
Failure or recognition exhaustion is unsupported, including checked
arithmetic failure; a failing expression is never made into a literal. -/
private def constantValue? : Nat → {p : PrimTy} → (t : LTm C (.val p)) →
    Option { v : p.Denote // ∀ (g : State C []) (ν : AEnv), t.eval g ν = some v }
  | 0, _, _ => none
  | _ + 1, _, .app0 (.lit v) => some ⟨v, fun _ _ => rfl⟩
  | fuel + 1, _, .app1 (.unop op h) t => do
    let a ← constantValue? fuel t
    match he : op.evalT h a.val with
    | none => none
    | some v => return ⟨v, by
        intro g ν
        rw [LTm.eval_app1, Close.Op1.eval_unop, a.property g ν]
        exact he⟩
  | fuel + 1, _, .app2 (.binop op h) t u => do
    let a ← constantValue? fuel t
    let b ← constantValue? fuel u
    match he : binopT op h a.val (some b.val) with
    | none => none
    | some v => return ⟨v, by
        intro g ν
        rw [LTm.eval_app2, Close.Op2.eval_binop, a.property g ν, b.property g ν]
        exact he⟩
  | _ + 1, _, _ => none

/-- Total primitive atoms, including certified closed computations.
Operations on inputs or storage reads need their own checked translation. -/
inductive StaticValue : {p : PrimTy} → LTm C (.val p) → Type where
  | lit {p : PrimTy} (v : p.Denote) : StaticValue (.app0 (.lit v))
  | constant {p : PrimTy} {t : LTm C (.val p)} (v : p.Denote)
      (eval : ∀ (g : State C []) (ν : AEnv), t.eval g ν = some v) : StaticValue t
  | read {p : PrimTy} {q : LTm C (.path (.prim p))} (r : StaticPath q) : StaticValue (.obsW q)

namespace StaticValue

def ofTerm? : {p : PrimTy} → (t : LTm C (.val p)) → Option (StaticValue t)
  | _, .app0 (.lit v) => some (.lit v)
  | _, .obsW q => (StaticPath.ofTerm? q).map .read
  | _, t => (constantValue? 1024 t).map fun v => .constant v.val v.property

def value (st : Storage C) : {p : PrimTy} → {t : LTm C (.val p)} → StaticValue t → p.Denote
  | _, _, .lit v => v
  | _, _, .constant v _ => v
  | _, _, .read r => (Ref.mk _ r.ref r.declared).read st

theorem eval_value (g : State C []) (ν : AEnv) {p : PrimTy} {t : LTm C (.val p)}
    (v : StaticValue t) : t.eval g ν = some (v.value g.storage) := by
  cases v with
  | lit v => rfl
  | constant v h => exact h g ν
  | read r =>
    rw [LTm.eval_obsW, r.eval g ν]
    exact congrArg some ((Ref.mk _ r.ref r.declared).obs_read g.storage)

def refs : {p : PrimTy} → {t : LTm C (.val p)} → StaticValue t → List (Ref C)
  | _, _, .lit _ => []
  | _, _, .constant _ _ => []
  | _, _, .read r => [⟨_, r.ref, r.declared⟩]

def code (rs : List (Ref C)) : {p : PrimTy} → {t : LTm C (.val p)} → StaticValue t → Affine
  | p, _, .lit v => .literal (encode p v).val
  | p, _, .constant v _ => .literal (encode p v).val
  | _, _, .read r => .variable (Layout.index ⟨_, r.ref, r.declared⟩ rs)

theorem code_value (rs : List (Ref C)) (st : Storage C) {p : PrimTy} {t : LTm C (.val p)}
    (v : StaticValue t) (h : ∀ r ∈ v.refs, r ∈ rs) :
    (v.code rs).eval (Layout.observe rs st).codes = ((encode p (v.value st)).val : Int) := by
  cases v with
  | lit v => exact Affine.eval_literal _ _
  | constant v _ => exact Affine.eval_literal _ _
  | read r =>
    rw [code, Affine.eval_variable, Layout.codes_index rs _ st (h _ List.mem_cons_self)]
    rfl

end StaticValue

/-- The recognized leaf fragment retains the existing formula as index. -/
inductive StaticFormula : LFml C → Type where
  | tt : StaticFormula .tt
  | eq {p : PrimTy} {a b : LTm C (.val p)} (ha : StaticValue a) (hb : StaticValue b) :
      StaticFormula (.eq a b)
  | not {φ : LFml C} (hφ : StaticFormula φ) : StaticFormula (.not φ)
  | and {φ ψ : LFml C} (hφ : StaticFormula φ) (hψ : StaticFormula ψ) : StaticFormula (.and φ ψ)
  | imp {φ ψ : LFml C} (hφ : StaticFormula φ) (hψ : StaticFormula ψ) : StaticFormula (.imp φ ψ)

namespace StaticFormula

def ofFormula? : (φ : LFml C) → Option (StaticFormula φ)
  | .tt => some .tt
  | .eq a b => do return .eq (← StaticValue.ofTerm? a) (← StaticValue.ofTerm? b)
  | .not φ => (ofFormula? φ).map .not
  | .and φ ψ => do return .and (← ofFormula? φ) (← ofFormula? ψ)
  | .imp φ ψ => do return .imp (← ofFormula? φ) (← ofFormula? ψ)
  | .all .. => none

def refs : {φ : LFml C} → StaticFormula φ → List (Ref C)
  | _, .tt => []
  | _, .eq ha hb => ha.refs ++ hb.refs
  | _, .not hφ => hφ.refs
  | _, .and hφ hψ | _, .imp hφ hψ => hφ.refs ++ hψ.refs

def compile (rs : List (Ref C)) : {φ : LFml C} → StaticFormula φ → AFml
  | _, .tt => .tt
  | _, .eq ha hb => (ha.code rs).eq (hb.code rs)
  | _, .not hφ => .not (hφ.compile rs)
  | _, .and hφ hψ => .and (hφ.compile rs) (hψ.compile rs)
  | _, .imp hφ hψ => .imp (hφ.compile rs) (hψ.compile rs)

theorem compile_iff (rs : List (Ref C)) (g : State C []) (ν : AEnv)
    {φ : LFml C} (hf : StaticFormula φ) (h : ∀ r ∈ hf.refs, r ∈ rs) :
    (hf.compile rs).holds (Layout.observe rs g.storage).codes ↔ φ.holds g ν := by
  induction hf with
  | tt => rfl
  | eq ha hb =>
    simp only [compile, Affine.holds_eq,
      ha.code_value rs g.storage (fun r hr => h r (List.mem_append_left _ hr)),
      hb.code_value rs g.storage (fun r hr => h r (List.mem_append_right _ hr)),
      LFml.holds, ha.eval_value g ν, hb.eval_value g ν]
    exact (show ((encode _ (ha.value g.storage)).val : Int) = (encode _ (hb.value g.storage)).val ↔
      (encode _ (ha.value g.storage)).val = (encode _ (hb.value g.storage)).val by omega).trans
      (ScalarCode.encode_val_eq_iff _ _ _)
  | not hφ ih => exact not_congr (ih h)
  | and hφ hψ ihφ ihψ =>
    exact and_congr (ihφ (fun r hr => h r (List.mem_append_left _ hr)))
      (ihψ (fun r hr => h r (List.mem_append_right _ hr)))
  | imp hφ hψ ihφ ihψ =>
    exact imp_congr (ihφ (fun r hr => h r (List.mem_append_left _ hr)))
      (ihψ (fun r hr => h r (List.mem_append_right _ hr)))

end StaticFormula

/-- A source-to-storage arithmetic equivalence. The certificate is about
the original formula in every typed state, including the reverse direction. -/
structure StaticReduction (φ : Fml C []) where
  refs : List (Ref C)
  distinct : refs.Nodup
  arithmetic : Layout.Formula refs
  meaning : ∀ σ : State C [], arithmetic.holds (Layout.observe refs σ.storage) ↔ holds σ φ

/-- Compile only after exact source reduction, source-fragment recognition,
actual-reference coverage, alias deduplication and variable-width checks. -/
def staticReduction? (φ : Fml C []) : Option (StaticReduction φ) := do
  let r ← exactReduction? φ
  let hf ← StaticFormula.ofFormula? r.leaf.elim
  let rs := Layout.unique hf.refs
  if hn : rs.Nodup then
    if hc : ∀ q ∈ hf.refs, q ∈ rs then
      if hw : (hf.compile rs).width ≤ (Layout.types rs).length then
        return ⟨rs, hn, ⟨hf.compile rs, hw⟩, fun σ =>
          (hf.compile_iff rs σ AEnv.dflt hc).trans (r.elim_holds_iff σ)⟩
      else none
    else none
  else none

namespace StaticReduction

/-- A successful complete arithmetic decision proves the source formula. -/
theorem valid_of_decide {φ : Fml C []} (r : StaticReduction φ)
    (h : r.arithmetic.guarded.decide = true) : Fml.Valid φ :=
  fun σ => (r.meaning σ).1
    ((r.arithmetic.valid_iff.2 ((AFml.decide_iff _).1 h)) _)

/-- A negative complete decision reconstructs a guaranteed original-source
counterstate, without requiring a proposed read assignment. -/
def countermodel {φ : Fml C []} (r : StaticReduction φ)
    (h : r.arithmetic.guarded.decide = false) : { σ : State C [] // ¬ holds σ φ } :=
  let cm := r.arithmetic.countermodel h
  let st := Layout.realize r.refs cm.val
  ⟨{ State.init C with storage := st }, fun hv => cm.property (by
    have hf := (r.meaning _).2 hv
    change r.arithmetic.holds (Layout.observe r.refs (Layout.realize r.refs cm.val)) at hf
    rw [Layout.observe_realize _ r.distinct] at hf
    exact hf)⟩

/-- A complete supported-fragment verdict with an original-formula proof
or an actual typed state that falsifies the original formula. -/
def verify {φ : Fml C []} (r : StaticReduction φ) :
    Sum (PLift (Fml.Valid φ)) { σ : State C [] // ¬ holds σ φ } := by
  match Layout.verify r.refs r.distinct r.arithmetic with
  | .inl h => exact .inl ⟨fun σ => (r.meaning σ).1 (h.down σ.storage)⟩
  | .inr cm =>
    let σ : State C [] := { State.init C with storage := cm.val }
    exact .inr ⟨σ, fun h => cm.property ((r.meaning σ).2 h)⟩

end StaticReduction

/-- `none` is unsupported; each returned verdict is exact. No candidate
pool or finite witness bound is used after successful recognition. -/
def staticVerify? (φ : Fml C []) :
    Option (Sum (PLift (Fml.Valid φ)) { σ : State C [] // ¬ holds σ φ }) :=
  (staticReduction? φ).map StaticReduction.verify

end Solidity.Decide
