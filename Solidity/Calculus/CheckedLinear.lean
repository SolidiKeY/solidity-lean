import Solidity.Calculus.CheckedBool
import Solidity.Calculus.StaticLinear
import Solidity.Calculus.ExactUpdates
import Solidity.Calculus.InputLayout

/-!
# Checked arithmetic compilation of typed inputs

Each expression certificate records its finite actual references, affine
scalar code and exact definedness guard. Partial expression evaluation is
preserved before an equality is compiled. Finite typed parameters share
these same proofs, with storage positions shifted beyond their prefix.
The interpreter, closer and symbolic executor retain their semantics.
-/

namespace Solidity.Decide

open Semantics ReadRealization Linear ScalarCode

variable {C : Contract} {ps : List Parameter} {es : List EnvKey}

namespace StaticValue

def codeIn (es : List EnvKey) (ps : List Parameter) (rs : List (Ref C)) :
    {p : PrimTy} → {t : LTm C (.val p)} → StaticValue t → Affine
  | p, _, .lit v | p, _, .constant v _ => .literal (encode p v).val
  | _, _, .read r => .variable (es.length + (ps.length + Layout.index ⟨_, r.ref, r.declared⟩ rs))

theorem codeIn_value (es : List EnvKey) (ps : List Parameter) (rs : List (Ref C)) (g : State C []) (ν : AEnv)
    {p : PrimTy} {t : LTm C (.val p)} (v : StaticValue t) (h : ∀ r ∈ v.refs, r ∈ rs) :
    (v.codeIn es ps rs).eval (Inputs.observe es ps rs g ν).codes = ((encode p (v.value g.storage)).val : Int) := by
  cases v with
  | lit v => exact Affine.eval_literal _ _
  | constant v _ => exact Affine.eval_literal _ _
  | read r =>
    rw [codeIn, Affine.eval_variable, Inputs.codes_tail, Parameters.codes_storage,
      Layout.codes_index rs _ g.storage (h _ List.mem_cons_self)]
    rfl

end StaticValue

/-- A term guard states precisely that its actual evaluation returns. -/
structure DefinedValue {s : Srt} (t : LTm C s) (ps : List Parameter := []) (es : List EnvKey := []) where
  refs : List (Ref C)
  lower : List (Ref C) → AFml
  correct : ∀ (rs : List (Ref C)), (∀ r ∈ refs, r ∈ rs) →
    ∀ (g : State C []) (ν : AEnv),
      (lower rs).holds (Inputs.observe es ps rs g ν).codes ↔ (t.eval g ν).isSome = true

/-- An exact partial-value encoding of an existing typed leaf term. -/
structure CheckedValue {p : PrimTy} (t : LTm C (.val p)) (ps : List Parameter := []) (es : List EnvKey := []) where
  refs : List (Ref C)
  lower : List (Ref C) → CheckedScalar p
  correct : ∀ (rs : List (Ref C)), (∀ r ∈ refs, r ∈ rs) →
    ∀ (g : State C []) (ν : AEnv),
      (lower rs).Correct (Inputs.observe es ps rs g ν).codes (t.eval g ν)

/-- The term is a literal: its value. -/
def LTm.lit? {p : PrimTy} : (t : LTm C (.val p)) → Option {v : p.Denote // t = .app0 (.lit v)}
  | .app0 (.lit v) => some ⟨v, rfl⟩
  | _ => none

namespace CheckedValue

def parameter {p : PrimTy} (k : Nat) (h : Parameter.mk p k ∈ ps) :
    CheckedValue (ps := ps) (es := es) (LTm.var (C := C) (p := p) k) :=
  ⟨[], fun _ => ⟨.variable (es.length + Parameters.index ⟨p, k⟩ ps), .tt⟩, by
    intro rs _ g ν
    refine ⟨trivial, ?_⟩
    rw [Affine.eval_variable, Inputs.codes_tail, Parameters.codes_parameter ps ⟨p, k⟩ rs g.storage ν h]
    rfl⟩

def environment (e : EnvKey) (h : e ∈ es) :
    CheckedValue (ps := ps) (es := es) (LTm.app0 (C := C) (.env e)) :=
  ⟨[], fun _ => ⟨.variable (Inputs.index e es), .tt⟩, by
    intro rs _ g ν
    refine ⟨trivial, ?_⟩
    rw [Affine.eval_variable, Inputs.codes_env es ps rs g ν e h]⟩

def defined {p : PrimTy} {t : LTm C (.val p)} (a : CheckedValue (ps := ps) (es := es) t) : DefinedValue (ps := ps) (es := es) t :=
  ⟨a.refs, fun rs => (a.lower rs).defined, by
    intro rs hr g ν
    have ih : (a.lower rs).Correct (Inputs.observe es ps rs g ν).codes (t.eval g ν) :=
      a.correct rs hr g ν
    cases he : t.eval g ν with
    | none =>
      rw [he] at ih
      exact ⟨fun h => (ih h).elim, fun h => (nomatch h)⟩
    | some _ =>
      rw [he] at ih
      exact ⟨fun _ => rfl, fun _ => ih.1⟩⟩

def ofStatic {p : PrimTy} {t : LTm C (.val p)} (v : StaticValue t) : CheckedValue (ps := ps) (es := es) t :=
  ⟨v.refs, fun rs => ⟨v.codeIn es ps rs, .tt⟩, by
    intro rs hr g ν
    rw [v.eval_value g ν]
    exact ⟨trivial, v.codeIn_value es ps rs g ν hr⟩⟩

def failed {p : PrimTy} : CheckedValue (ps := ps) (es := es) (LTm.err (C := C) (s := .val p)) :=
  ⟨[], fun _ => ⟨.literal 0, .ff⟩, fun _ _ _ _ => id⟩

def add {p : PrimTy} (hp : BinOp.add.accepts p = true) {a b : LTm C (.val p)}
    (ha : CheckedValue (ps := ps) (es := es) a) (hb : CheckedValue (ps := ps) (es := es) b) : CheckedValue (ps := ps) (es := es) (.app2 (.binop .add hp) a b) :=
  ⟨ha.refs ++ hb.refs, fun rs => .arith false (ha.lower rs) (hb.lower rs), by
    intro rs hr g ν
    have hpa : p.isNumeric = true := hp
    have ih : (CheckedScalar.arith false (ha.lower rs) (hb.lower rs)).Correct
        (Inputs.observe es ps rs g ν).codes
        ((a.eval g ν).bind fun v => (b.eval g ν).bind fun w => p.ofInt? (integer p v + integer p w)) :=
      CheckedScalar.arith_correct hpa false (ha.lower rs) (hb.lower rs)
      (Inputs.observe es ps rs g ν).codes (a.eval g ν) (b.eval g ν)
      (ha.correct rs (fun r hm => hr r (List.mem_append_left _ hm)) g ν)
      (hb.correct rs (fun r hm => hr r (List.mem_append_right _ hm)) g ν)
    rw [LTm.eval_app2, Close.Op2.eval_binop]
    cases p with
    | bool => cases hp
    | uint | int => exact ih⟩

def sub {p : PrimTy} (hp : BinOp.sub.accepts p = true) {a b : LTm C (.val p)}
    (ha : CheckedValue (ps := ps) (es := es) a) (hb : CheckedValue (ps := ps) (es := es) b) : CheckedValue (ps := ps) (es := es) (.app2 (.binop .sub hp) a b) :=
  ⟨ha.refs ++ hb.refs, fun rs => .arith true (ha.lower rs) (hb.lower rs), by
    intro rs hr g ν
    have hpa : p.isNumeric = true := hp
    have ih : (CheckedScalar.arith true (ha.lower rs) (hb.lower rs)).Correct
        (Inputs.observe es ps rs g ν).codes
        ((a.eval g ν).bind fun v => (b.eval g ν).bind fun w => p.ofInt? (integer p v - integer p w)) :=
      CheckedScalar.arith_correct hpa true (ha.lower rs) (hb.lower rs)
      (Inputs.observe es ps rs g ν).codes (a.eval g ν) (b.eval g ν)
      (ha.correct rs (fun r hm => hr r (List.mem_append_left _ hm)) g ν)
      (hb.correct rs (fun r hm => hr r (List.mem_append_right _ hm)) g ν)
    rw [LTm.eval_app2, Close.Op2.eval_binop]
    cases p with
    | bool => cases hp
    | uint | int => exact ih⟩

/-- Checked multiplication by the literal `v` on the left. -/
def mulLit {p : PrimTy} (hp : BinOp.mul.accepts p = true) {a b : LTm C (.val p)} (v : p.Denote)
    (ha : a = .app0 (.lit v)) (hb : CheckedValue (ps := ps) (es := es) b) :
    CheckedValue (ps := ps) (es := es) (.app2 (.binop .mul hp) a b) :=
  ⟨hb.refs, fun rs => .scale (integer p v) (hb.lower rs), by
    intro rs hr g ν
    subst ha
    have hpa : p.isNumeric = true := hp
    have ih := CheckedScalar.scale_correct hpa (integer p v) (hb.lower rs)
      (Inputs.observe es ps rs g ν).codes (b.eval g ν) (hb.correct rs hr g ν)
    rw [LTm.eval_app2, Close.Op2.eval_binop]
    cases p with
    | bool => cases hp
    | uint | int => exact ih⟩

/-- Checked multiplication by the literal `v` on the right. -/
def litMul {p : PrimTy} (hp : BinOp.mul.accepts p = true) {a b : LTm C (.val p)} (v : p.Denote)
    (hb : b = .app0 (.lit v)) (ha : CheckedValue (ps := ps) (es := es) a) :
    CheckedValue (ps := ps) (es := es) (.app2 (.binop .mul hp) a b) :=
  ⟨ha.refs, fun rs => .scale (integer p v) (ha.lower rs), by
    intro rs hr g ν
    subst hb
    have hpa : p.isNumeric = true := hp
    have ih := CheckedScalar.scale_correct' hpa (integer p v) (ha.lower rs)
      (Inputs.observe es ps rs g ν).codes (a.eval g ν) (ha.correct rs hr g ν)
    rw [LTm.eval_app2, Close.Op2.eval_binop]
    cases p with
    | bool => cases hp
    | uint | int => exact ih⟩

/-- Checked negation on `int`: `-1 · a`, out of range at `-2^255`. -/
def neg (hp : UnOp.neg.accepts .int = true) {a : LTm C (.val .int)}
    (ha : CheckedValue (ps := ps) (es := es) a) :
    CheckedValue (ps := ps) (es := es) (.app1 (.unop .neg hp) a) :=
  ⟨ha.refs, fun rs => .scale (-1) (ha.lower rs), by
    intro rs hr g ν
    have ih := CheckedScalar.scale_correct (p := .int) rfl (-1) (ha.lower rs)
      (Inputs.observe es ps rs g ν).codes (a.eval g ν) (ha.correct rs hr g ν)
    rw [LTm.eval_app1, Close.Op1.eval_unop]
    simp only [integer, Int.neg_one_mul] at ih
    exact ih⟩

/-- The complement on `uint`: `2^256 - 1 - a`, always in range. -/
def bnot (hp : UnOp.bnot.accepts .uint = true) {a : LTm C (.val .uint)}
    (ha : CheckedValue (ps := ps) (es := es) a) :
    CheckedValue (ps := ps) (es := es) (.app1 (.unop .bnot hp) a) :=
  ⟨ha.refs, fun rs => .compl (ha.lower rs), by
    intro rs hr g ν
    have ih := CheckedScalar.compl_correct (ha.lower rs)
      (Inputs.observe es ps rs g ν).codes (a.eval g ν) (ha.correct rs hr g ν)
    rw [LTm.eval_app1, Close.Op1.eval_unop]
    exact ih⟩

/-- A primitive guard must return before the value does. This is the
definedness sequencing emitted by read-occurrence flattening. -/
def seq {q p : PrimTy} {d : LTm C (.val q)} {t : LTm C (.val p)}
    (hd : CheckedValue (ps := ps) (es := es) d)
    (a : CheckedValue (ps := ps) (es := es) t) : CheckedValue (ps := ps) (es := es) (.seq d t) :=
  ⟨hd.refs ++ a.refs, fun rs => (a.lower rs).guard (hd.lower rs).defined, by
    intro rs hr g ν
    have ihd := hd.correct rs (fun r hm => hr r (List.mem_append_left _ hm)) g ν
    have iha := a.correct rs (fun r hm => hr r (List.mem_append_right _ hm)) g ν
    rw [LTm.eval_seq]
    cases hv : d.eval g ν with
    | none =>
      rw [hv] at ihd
      exact fun h => ihd h.1
    | some v =>
      rw [hv] at ihd
      exact CheckedScalar.guard_correct _ _ _ _ iha ihd.1⟩

/-- Recognition is bounded by term depth. Rejection has no semantic verdict. -/
def ofTermFuel? (ps : List Parameter) : Nat → {p : PrimTy} → (t : LTm C (.val p)) → Option (CheckedValue (ps := ps) (es := es) t)
  | 0, _, _ => none
  | fuel + 1, _, t =>
    match StaticValue.ofTerm? t with
    | some v => some (ofStatic v)
    | none => match t with
      | .var (p := p) k => if h : Parameter.mk p k ∈ ps then some (parameter k h) else none
      | .app0 (.env e) => if h : e ∈ es then some (environment e h) else none
      | .app2 (.binop .add h) a b => do return add h (← ofTermFuel? ps fuel a) (← ofTermFuel? ps fuel b)
      | .app2 (.binop .sub h) a b => do return sub h (← ofTermFuel? ps fuel a) (← ofTermFuel? ps fuel b)
      | .app2 (.binop .mul h) a b =>
        match a.lit? with
        | some ⟨v, hv⟩ => do return mulLit h v hv (← ofTermFuel? ps fuel b)
        | none =>
          match b.lit? with
          | some ⟨v, hv⟩ => do return litMul h v hv (← ofTermFuel? ps fuel a)
          | none => none
      | .app1 (.unop .neg (p := .int) h) a => do return neg h (← ofTermFuel? ps fuel a)
      | .app1 (.unop .bnot (p := .uint) h) a => do return bnot h (← ofTermFuel? ps fuel a)
      | .seq (s' := .val _) d a => do return seq (← ofTermFuel? ps fuel d) (← ofTermFuel? ps fuel a)
      | .err => some failed
      | _ => none

def ofTermIn? (ps : List Parameter) {p : PrimTy} (t : LTm C (.val p)) : Option (CheckedValue (ps := ps) (es := es) t) := ofTermFuel? ps 1024 t

def ofTerm? {p : PrimTy} (t : LTm C (.val p)) : Option (CheckedValue t) := ofTermIn? [] t

end CheckedValue

/-- Source Boolean values use success predicates, retaining the distinction
between false and failed evaluation. -/
structure BooleanValue (t : LTm C (.val .bool)) (ps : List Parameter := []) (es : List EnvKey := []) where
  refs : List (Ref C)
  lower : List (Ref C) → CheckedBool
  correct : ∀ (rs : List (Ref C)), (∀ r ∈ refs, r ∈ rs) →
    ∀ (g : State C []) (ν : AEnv),
      (lower rs).Correct (Inputs.observe es ps rs g ν).codes (t.eval g ν)

namespace BooleanValue

def defined {t : LTm C (.val .bool)} (a : BooleanValue (ps := ps) (es := es) t) : DefinedValue (ps := ps) (es := es) t :=
  ⟨a.refs, fun rs => CheckedBool.disj (a.lower rs).yes (a.lower rs).no, by
    intro rs hr g ν
    have ih : (a.lower rs).Correct (Inputs.observe es ps rs g ν).codes (t.eval g ν) :=
      a.correct rs hr g ν
    simp only [CheckedBool.disj_holds, ih.1, ih.2]
    cases t.eval g ν with
    | none => simp only [reduceCtorEq, false_or, Option.isSome_none, Bool.false_eq_true, iff_self]
    | some b => cases b <;> simp only [Option.some.injEq, or_true, true_or,
        Option.isSome_some, iff_self]⟩

def seq {s : Srt} {d : LTm C s} {t : LTm C (.val .bool)}
    (hd : DefinedValue (ps := ps) (es := es) d) (a : BooleanValue (ps := ps) (es := es) t) : BooleanValue (ps := ps) (es := es) (.seq d t) :=
  ⟨hd.refs ++ a.refs, fun rs =>
    ⟨.and (hd.lower rs) (a.lower rs).yes, .and (hd.lower rs) (a.lower rs).no⟩, by
    intro rs hr g ν
    have ihd : (hd.lower rs).holds (Inputs.observe es ps rs g ν).codes ↔ (d.eval g ν).isSome = true :=
      hd.correct rs (fun r hm => hr r (List.mem_append_left _ hm)) g ν
    have iha : (a.lower rs).Correct (Inputs.observe es ps rs g ν).codes (t.eval g ν) :=
      a.correct rs (fun r hm => hr r (List.mem_append_right _ hm)) g ν
    simp only [CheckedBool.Correct, AFml.holds, ihd, iha.1, iha.2, LTm.eval_seq]
    cases d.eval g ν with
    | none => simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true,
        false_and, reduceCtorEq, iff_self, and_self]
    | some _ => simp only [Option.bind_some, Option.isSome_some, true_and, iff_self, and_self]⟩

def ofScalar {t : LTm C (.val .bool)} (v : CheckedValue (ps := ps) (es := es) t) : BooleanValue (ps := ps) (es := es) t :=
  ⟨v.refs, fun rs => .ofScalar (v.lower rs), fun rs hr g ν =>
    CheckedBool.ofScalar_correct _ _ _ (v.correct rs hr g ν)⟩

def not {t : LTm C (.val .bool)} (v : BooleanValue (ps := ps) (es := es) t) :
    BooleanValue (ps := ps) (es := es) (.app1 (.unop .not rfl) t) :=
  ⟨v.refs, fun rs => (v.lower rs).not, by
    intro rs hr g ν
    have ih : ((v.lower rs).not).Correct (Inputs.observe es ps rs g ν).codes
        ((t.eval g ν).map (! ·)) := CheckedBool.not_correct _ _ _ (v.correct rs hr g ν)
    rw [LTm.eval_app1, Close.Op1.eval_unop]
    cases he : t.eval g ν <;> rw [he] at ih <;> exact ih⟩

/-- The interpreter's comparison, cast only at its proved Boolean result. -/
theorem eval_comparison (op : BinOp) (hc : op.zCmp = true) {p : PrimTy}
    (h : op.accepts p = true) (hr : op.ret p = .bool) (a b : LTm C (.val p))
    (g : State C []) (ν : AEnv) :
    ((hr ▸ LTm.app2 (.binop op h) a b) : LTm C (.val .bool)).eval g ν =
      (a.eval g ν).bind (fun v => (b.eval g ν).map fun w =>
        op.cmpZ (integer p v) (integer p w)) := by
  cases op <;> simp only [BinOp.zCmp, Bool.false_eq_true] at hc
  all_goals cases p with
  | uint | int =>
    cases hr
    rw [LTm.eval_app2, Close.Op2.eval_binop]
    cases a.eval g ν <;> cases b.eval g ν <;> rfl
  | bool =>
    simp only [BinOp.accepts, PrimTy.isNumeric, Bool.false_eq_true] at h
    all_goals
      cases hr
      rw [LTm.eval_app2, Close.Op2.eval_binop]
      cases a.eval g ν with
      | none => rfl
      | some v =>
        cases b.eval g ν with
        | none => rfl
        | some w => cases v <;> cases w <;> rfl

def comparison {p : PrimTy} (op : BinOp) (hc : op.zCmp = true) (h : op.accepts p = true)
    (hr : op.ret p = .bool) {a b : LTm C (.val p)} (ha : CheckedValue (ps := ps) (es := es) a) (hb : CheckedValue (ps := ps) (es := es) b) :
    BooleanValue (ps := ps) (es := es) (hr ▸ LTm.app2 (.binop op h) a b) :=
  ⟨ha.refs ++ hb.refs, fun rs => .comparison op (ha.lower rs) (hb.lower rs), by
    intro rs hs g ν
    rw [eval_comparison op hc h hr a b g ν]
    exact CheckedBool.comparison_correct _ _ _ _ _ _
      (ha.correct rs (fun r hm => hs r (List.mem_append_left _ hm)) g ν)
      (hb.correct rs (fun r hm => hs r (List.mem_append_right _ hm)) g ν)⟩

def binary (f : CheckedBool → CheckedBool → CheckedBool) (result : Option Bool → Option Bool → Option Bool)
    (sound : ∀ a b x va vb, a.Correct x va → b.Correct x vb → (f a b).Correct x (result va vb))
    {a b t : LTm C (.val .bool)} (ha : BooleanValue (ps := ps) (es := es) a) (hb : BooleanValue (ps := ps) (es := es) b)
    (he : ∀ g ν, t.eval g ν = result (a.eval g ν) (b.eval g ν)) : BooleanValue (ps := ps) (es := es) t :=
  ⟨ha.refs ++ hb.refs, fun rs => f (ha.lower rs) (hb.lower rs), by
    intro rs hs g ν
    rw [he g ν]
    exact sound _ _ _ _ _
      (ha.correct rs (fun r hm => hs r (List.mem_append_left _ hm)) g ν)
      (hb.correct rs (fun r hm => hs r (List.mem_append_right _ hm)) g ν)⟩

def and {a b : LTm C (.val .bool)} (ha : BooleanValue (ps := ps) (es := es) a) (hb : BooleanValue (ps := ps) (es := es) b) :
    BooleanValue (ps := ps) (es := es) (.app2 (.binop .and rfl) a b) :=
  binary CheckedBool.and CheckedBool.andResult CheckedBool.and_correct ha hb (by
    intro g ν
    rw [LTm.eval_app2, Close.Op2.eval_binop]
    cases a.eval g ν with
    | none => rfl
    | some v =>
      cases b.eval g ν with
      | none => cases v <;> rfl
      | some w => cases v <;> cases w <;> rfl)

def or {a b : LTm C (.val .bool)} (ha : BooleanValue (ps := ps) (es := es) a) (hb : BooleanValue (ps := ps) (es := es) b) :
    BooleanValue (ps := ps) (es := es) (.app2 (.binop .or rfl) a b) :=
  binary CheckedBool.or CheckedBool.orResult CheckedBool.or_correct ha hb (by
    intro g ν
    rw [LTm.eval_app2, Close.Op2.eval_binop]
    cases a.eval g ν with
    | none => rfl
    | some v =>
      cases b.eval g ν with
      | none => cases v <;> rfl
      | some w => cases v <;> cases w <;> rfl)

def eq {a b : LTm C (.val .bool)} (ha : BooleanValue (ps := ps) (es := es) a) (hb : BooleanValue (ps := ps) (es := es) b) :
    BooleanValue (ps := ps) (es := es) (.app2 (.binop .eqB rfl) a b) :=
  binary CheckedBool.eq (fun va vb => va.bind fun v => vb.map fun w => decide (v = w))
    CheckedBool.eq_correct ha hb (by
      intro g ν
      rw [LTm.eval_app2, Close.Op2.eval_binop]
      cases a.eval g ν <;> cases b.eval g ν <;> rfl)

def ne {a b : LTm C (.val .bool)} (ha : BooleanValue (ps := ps) (es := es) a) (hb : BooleanValue (ps := ps) (es := es) b) :
    BooleanValue (ps := ps) (es := es) (.app2 (.binop .neB rfl) a b) :=
  ⟨ha.refs ++ hb.refs, fun rs => ((ha.lower rs).eq (hb.lower rs)).not, by
    intro rs hs g ν
    have heq : ((ha.lower rs).eq (hb.lower rs)).Correct (Inputs.observe es ps rs g ν).codes
        ((a.eval g ν).bind fun v => (b.eval g ν).map fun w => decide (v = w)) :=
      CheckedBool.eq_correct _ _ _ _ _
        (ha.correct rs (fun r hm => hs r (List.mem_append_left _ hm)) g ν)
        (hb.correct rs (fun r hm => hs r (List.mem_append_right _ hm)) g ν)
    have hn : (((ha.lower rs).eq (hb.lower rs)).not).Correct (Inputs.observe es ps rs g ν).codes
        (((a.eval g ν).bind fun v => (b.eval g ν).map fun w => decide (v = w)).map (! ·)) :=
      CheckedBool.not_correct _ _ _ heq
    rw [LTm.eval_app2, Close.Op2.eval_binop]
    cases hv : a.eval g ν <;> cases hw : b.eval g ν <;> rw [hv, hw] at hn <;> exact hn⟩

def Result (ps : List Parameter) : {s : Srt} → LTm C s → Type
  | .val .bool, t => BooleanValue (ps := ps) (es := es) t
  | _, _ => Empty

def scalar? : {s : Srt} → (t : LTm C s) → Option (Result (es := es) ps t)
  | .val .bool, t => (CheckedValue.ofTermIn? ps t).map ofScalar
  | _, _ => none

def ofTermFuel? (ps : List Parameter) : Nat → {s : Srt} → (t : LTm C s) → Option (Result (es := es) ps t)
  | 0, _, _ => none
  | fuel + 1, s, .seq (s' := s') d a =>
    match s with
    | .val .bool => match s' with
      | .val .bool => do return seq (← ofTermFuel? ps fuel d).defined (← ofTermFuel? ps fuel a)
      | .val .uint | .val .int => do return seq (← CheckedValue.ofTermIn? ps d).defined (← ofTermFuel? ps fuel a)
      | _ => none
    | _ => none
  | fuel + 1, _, .app1 (.unop op (p := p) _) a =>
    match op, p with
    | .not, .bool => (ofTermFuel? ps fuel a).map not
    | _, _ => none
  | fuel + 1, _, .app2 (.binop op (p := p) h) a b =>
    match op with
    | .and => match p with
      | .bool => do return and (← ofTermFuel? ps fuel a) (← ofTermFuel? ps fuel b)
      | _ => none
    | .or => match p with
      | .bool => do return or (← ofTermFuel? ps fuel a) (← ofTermFuel? ps fuel b)
      | _ => none
    | .eqB => match p with
      | .bool => do return eq (← ofTermFuel? ps fuel a) (← ofTermFuel? ps fuel b)
      | .uint | .int => do return comparison .eqB rfl h rfl (← CheckedValue.ofTermIn? ps a) (← CheckedValue.ofTermIn? ps b)
    | .neB => match p with
      | .bool => do return ne (← ofTermFuel? ps fuel a) (← ofTermFuel? ps fuel b)
      | .uint | .int => do return comparison .neB rfl h rfl (← CheckedValue.ofTermIn? ps a) (← CheckedValue.ofTermIn? ps b)
    | .lt => do return comparison .lt rfl h rfl (← CheckedValue.ofTermIn? ps a) (← CheckedValue.ofTermIn? ps b)
    | .gt => do return comparison .gt rfl h rfl (← CheckedValue.ofTermIn? ps a) (← CheckedValue.ofTermIn? ps b)
    | .le => do return comparison .le rfl h rfl (← CheckedValue.ofTermIn? ps a) (← CheckedValue.ofTermIn? ps b)
    | .ge => do return comparison .ge rfl h rfl (← CheckedValue.ofTermIn? ps a) (← CheckedValue.ofTermIn? ps b)
    | _ => none
  | _ + 1, _, t => scalar? t

def ofTermIn? (ps : List Parameter) (t : LTm C (.val .bool)) : Option (BooleanValue (ps := ps) (es := es) t) := ofTermFuel? ps 1024 t

def ofTerm? (t : LTm C (.val .bool)) : Option (BooleanValue t) := ofTermIn? [] t

end BooleanValue

/-- A compositional arithmetic encoding of the existing leaf formula. -/
structure StorageEncoding (φ : LFml C) (ps : List Parameter := []) (es : List EnvKey := []) where
  refs : List (Ref C)
  lower : List (Ref C) → AFml
  correct : ∀ (rs : List (Ref C)), (∀ r ∈ refs, r ∈ rs) →
    ∀ (g : State C []) (ν : AEnv),
      (lower rs).holds (Inputs.observe es ps rs g ν).codes ↔ φ.holds g ν

namespace StorageEncoding

def tt : StorageEncoding (ps := ps) (es := es) (LFml.tt (C := C)) := ⟨[], fun _ => .tt, fun _ _ _ _ => Iff.rfl⟩

def eq {p : PrimTy} {a b : LTm C (.val p)} (ha : CheckedValue (ps := ps) (es := es) a) (hb : CheckedValue (ps := ps) (es := es) b) :
    StorageEncoding (ps := ps) (es := es) (.eq a b) :=
  ⟨ha.refs ++ hb.refs, fun rs => (ha.lower rs).eq (hb.lower rs), by
    intro rs hr g ν
    rw [CheckedScalar.eq_correct _ _ _ (a.eval g ν) (b.eval g ν)
      (ha.correct rs (fun r hm => hr r (List.mem_append_left _ hm)) g ν)
      (hb.correct rs (fun r hm => hr r (List.mem_append_right _ hm)) g ν)]
    simp only [LFml.holds]
    cases a.eval g ν <;> cases b.eval g ν <;>
      simp only [ReadFormula.equal, Bool.false_eq_true, decide_eq_true_eq]⟩

def boolEq {a b : LTm C (.val .bool)} (ha : BooleanValue (ps := ps) (es := es) a) (hb : BooleanValue (ps := ps) (es := es) b) :
    StorageEncoding (ps := ps) (es := es) (.eq a b) :=
  ⟨ha.refs ++ hb.refs, fun rs => ((ha.lower rs).eq (hb.lower rs)).yes, by
    intro rs hs g ν
    have hq : ((ha.lower rs).eq (hb.lower rs)).Correct (Inputs.observe es ps rs g ν).codes
        ((a.eval g ν).bind fun v => (b.eval g ν).map fun w => decide (v = w)) :=
      CheckedBool.eq_correct _ _ _ _ _
        (ha.correct rs (fun r hm => hs r (List.mem_append_left _ hm)) g ν)
        (hb.correct rs (fun r hm => hs r (List.mem_append_right _ hm)) g ν)
    apply hq.1.trans
    simp only [LFml.holds]
    cases a.eval g ν <;> cases b.eval g ν <;>
      simp only [Option.bind_none, Option.bind_some, Option.map_none, Option.map_some,
        Option.some.injEq, decide_eq_true_eq, reduceCtorEq]⟩

def not {φ : LFml C} (a : StorageEncoding (ps := ps) (es := es) φ) : StorageEncoding (ps := ps) (es := es) (.not φ) :=
  ⟨a.refs, fun rs => .not (a.lower rs), fun rs hr g ν => not_congr (a.correct rs hr g ν)⟩

def and {φ ψ : LFml C} (a : StorageEncoding (ps := ps) (es := es) φ) (b : StorageEncoding (ps := ps) (es := es) ψ) : StorageEncoding (ps := ps) (es := es) (.and φ ψ) :=
  ⟨a.refs ++ b.refs, fun rs => .and (a.lower rs) (b.lower rs), fun rs hr g ν =>
    and_congr (a.correct rs (fun r hm => hr r (List.mem_append_left _ hm)) g ν)
      (b.correct rs (fun r hm => hr r (List.mem_append_right _ hm)) g ν)⟩

def imp {φ ψ : LFml C} (a : StorageEncoding (ps := ps) (es := es) φ) (b : StorageEncoding (ps := ps) (es := es) ψ) : StorageEncoding (ps := ps) (es := es) (.imp φ ψ) :=
  ⟨a.refs ++ b.refs, fun rs => .imp (a.lower rs) (b.lower rs), fun rs hr g ν =>
    imp_congr (a.correct rs (fun r hm => hr r (List.mem_append_left _ hm)) g ν)
      (b.correct rs (fun r hm => hr r (List.mem_append_right _ hm)) g ν)⟩

def equality? : {p : PrimTy} → (a b : LTm C (.val p)) → Option (StorageEncoding (ps := ps) (es := es) (.eq a b))
  | .bool, a, b => do return boolEq (← BooleanValue.ofTermIn? ps a) (← BooleanValue.ofTermIn? ps b)
  | .uint, a, b | .int, a, b => do return eq (← CheckedValue.ofTermIn? ps a) (← CheckedValue.ofTermIn? ps b)

def ofFormula? : (φ : LFml C) → Option (StorageEncoding (ps := ps) (es := es) φ)
  | .tt => some tt
  | .eq a b => equality? a b
  | .not φ => (ofFormula? φ).map not
  | .and φ ψ => do return and (← ofFormula? φ) (← ofFormula? ψ)
  | .imp φ ψ => do return imp (← ofFormula? φ) (← ofFormula? ψ)
  | .all .. => none

end StorageEncoding

/-- Exact source reduction followed by checked storage arithmetic. The
same source certificate transports both verdicts and materializes models. -/
def checkedReduction? (φ : Fml C []) : Option (StaticReduction φ) := do
  let r ← sourceReduction? φ
  let hf ← StorageEncoding.ofFormula? (ps := []) (es := []) r.leaf.elim
  let rs := Layout.unique hf.refs
  if hn : rs.Nodup then
    if hc : ∀ q ∈ hf.refs, q ∈ rs then
      if hw : (hf.lower rs).width ≤ (Layout.types rs).length then
        return ⟨rs, hn, ⟨hf.lower rs, hw⟩, fun σ =>
          (hf.correct rs hc σ AEnv.dflt).trans (r.elim_holds_iff σ)⟩
      else none
    else none
  else none

end Solidity.Decide
