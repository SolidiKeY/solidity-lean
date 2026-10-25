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

/-! ## Values at their ranges -/

theorem uint_val_nonneg (v : PrimTy.uint.Denote) : 0 ≤ v.val := by
  have h := v.property
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  exact h.1

theorem uint_val_lt (v : PrimTy.uint.Denote) : v.val < ((2 ^ 256 : Nat) : Int) := by
  have h := v.property
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  exact h.2

theorem ofInt?_isSome' {p : PrimTy} (hp : p.isNumeric = true) {n : Int} (h : p.inRange n = true) :
    (p.ofInt? n).isSome = true := by
  cases p with
  | bool => cases hp
  | uint | int => simp only [PrimTy.ofInt?, dif_pos h, Option.isSome_some]

theorem uint_inRange {n : Int} (h0 : 0 ≤ n) (h1 : n < ((2 ^ 256 : Nat) : Int)) :
    PrimTy.uint.inRange n = true := decide_eq_true ⟨h0, h1⟩

theorem int_inRange {n : Int} (h0 : -((2 ^ 255 : Nat) : Int) ≤ n) (h1 : n < ((2 ^ 255 : Nat) : Int)) :
    PrimTy.int.inRange n = true := decide_eq_true ⟨h0, h1⟩

theorem uintBound_eq : ((2 ^ 256 : Nat) : Int) =
    115792089237316195423570985008687907853269984665640564039457584007913129639936 := by decide

theorem intBound_eq : ((2 ^ 255 : Nat) : Int) =
    57896044618658097711785492504343953926634992332820282019728792003956564819968 := by decide

theorem int_val_bounds (v : PrimTy.int.Denote) :
    -((2 ^ 255 : Nat) : Int) ≤ v.val ∧ v.val < ((2 ^ 255 : Nat) : Int) := by
  have h := v.property
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  exact h

theorem LTm.eval_binop_of {op : BinOp} {p : PrimTy} (h : op.accepts p = true)
    (hs : ∀ x : p.Denote, op.shortT x = none) (a b : LTm C (.val p)) (σ : State C []) (ν : AEnv) :
    (LTm.app2 (.binop op h) a b).eval σ ν = (a.eval σ ν).bind fun x => (b.eval σ ν).bind (op.evalT h x) := by
  rw [LTm.eval_app2, Close.Op2.eval_binop]
  cases a.eval σ ν with
  | none => rfl
  | some x => simp only [Option.bind_some, binopT, hs]

/-- Every cut binary operator but `&&`/`||` evaluates both operands. -/
theorem shortT_none {op : BinOp} (hop : op ≠ .and ∧ op ≠ .or) {p : PrimTy} (x : p.Denote) :
    op.shortT x = none := by
  cases op <;> cases p <;> first | rfl | exact absurd rfl hop.1 | exact absurd rfl hop.2

theorem uint_ofInt?_eq {n : Int} (h0 : 0 ≤ n) (h1 : n < ((2 ^ 256 : Nat) : Int)) :
    PrimTy.uint.ofInt? n = some ⟨n, uint_inRange h0 h1⟩ := by
  simp only [PrimTy.ofInt?, dif_pos (uint_inRange h0 h1)]

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

/-- **An exact encoding of a KeY `int` term** (`Srt.kint`): an affine form
over the codes, unbounded, and its definedness guard. -/
structure KIntValue (t : LTm C .kint) (ps : List Parameter := []) (es : List EnvKey := []) where
  refs : List (Ref C)
  lower : List (Ref C) → CheckedInt
  correct : ∀ (rs : List (Ref C)), (∀ r ∈ refs, r ∈ rs) →
    ∀ (g : State C []) (ν : AEnv),
      (lower rs).Correct (Inputs.observe es ps rs g ν).codes (t.eval g ν)

/-- The term is a KeY `int` literal: its value. -/
def LTm.zlit? : (t : LTm C .kint) → Option {n : Int // t = .app0 (.zlit n)}
  | .app0 (.zlit n) => some ⟨n, rfl⟩
  | _ => none

namespace KIntValue

def zlit (n : Int) : KIntValue (ps := ps) (es := es) (LTm.app0 (C := C) (.zlit n)) :=
  ⟨[], fun _ => .lit n, fun _ _ _ _ => CheckedInt.lit_correct n _⟩

/-- `toInt(a)`: a `uint` read as a KeY `int`. -/
def toInt {a : LTm C (.val .uint)} (ha : CheckedValue (ps := ps) (es := es) a) :
    KIntValue (ps := ps) (es := es) (.app1 .toInt a) :=
  ⟨ha.refs, fun rs => .ofUint (ha.lower rs), fun rs hr g ν =>
    CheckedInt.ofUint_correct _ _ _ (ha.correct rs hr g ν)⟩

theorem eval_zbin (g : State C []) (ν : AEnv) (op : BinOp) (h : op.zArith = true)
    (a b : LTm C .kint) :
    ((LTm.app2 (.zbin op h) a b).eval g ν : Option Int) =
      ((a.eval g ν : Option Int).bind fun v => (b.eval g ν : Option Int).map fun w => op.evalZ v w) := by
  rw [LTm.eval_app2]
  cases (a.eval g ν : Option Int) <;> cases (b.eval g ν : Option Int) <;> rfl

/-- `a + b` (`subtract = false`) or `a - b` on KeY's `int`. -/
def arith (subtract : Bool) (op : BinOp) (h : op.zArith = true)
    (hop : op = if subtract then .sub else .add) {a b : LTm C .kint}
    (ha : KIntValue (ps := ps) (es := es) a) (hb : KIntValue (ps := ps) (es := es) b) :
    KIntValue (ps := ps) (es := es) (.app2 (.zbin op h) a b) :=
  ⟨ha.refs ++ hb.refs, fun rs => .arith subtract (ha.lower rs) (hb.lower rs), by
    intro rs hr g ν
    have ih := CheckedInt.arith_correct subtract (ha.lower rs) (hb.lower rs)
      (Inputs.observe es ps rs g ν).codes (a.eval g ν) (b.eval g ν)
      (ha.correct rs (fun r hm => hr r (List.mem_append_left _ hm)) g ν)
      (hb.correct rs (fun r hm => hr r (List.mem_append_right _ hm)) g ν)
    rw [eval_zbin]
    subst hop
    cases subtract <;> exact ih⟩

/-- `n · b` on KeY's `int`, `n` a literal. -/
def mulLit (h : BinOp.mul.zArith = true) {a b : LTm C .kint} (n : Int)
    (ha : a = .app0 (.zlit n)) (hb : KIntValue (ps := ps) (es := es) b) :
    KIntValue (ps := ps) (es := es) (.app2 (.zbin .mul h) a b) :=
  ⟨hb.refs, fun rs => .scale n (hb.lower rs), by
    intro rs hr g ν
    subst ha
    have ih := CheckedInt.scale_correct n (hb.lower rs)
      (Inputs.observe es ps rs g ν).codes (b.eval g ν) (hb.correct rs hr g ν)
    rw [eval_zbin]
    exact ih⟩

/-- `a · n` on KeY's `int`, `n` a literal. -/
def litMul (h : BinOp.mul.zArith = true) {a b : LTm C .kint} (n : Int)
    (hb : b = .app0 (.zlit n)) (ha : KIntValue (ps := ps) (es := es) a) :
    KIntValue (ps := ps) (es := es) (.app2 (.zbin .mul h) a b) :=
  ⟨ha.refs, fun rs => .scale n (ha.lower rs), by
    intro rs hr g ν
    subst hb
    have ih := CheckedInt.scale_correct n (ha.lower rs)
      (Inputs.observe es ps rs g ν).codes (a.eval g ν) (ha.correct rs hr g ν)
    rw [eval_zbin]
    cases ha' : (a.eval g ν : Option Int) with
    | none => rw [ha'] at ih; exact ih
    | some v =>
      rw [ha'] at ih
      show (CheckedInt.scale n (ha.lower rs)).Correct _ (some (v * n))
      rw [Int.mul_comm]
      exact ih⟩

/-- Recognition is bounded by term depth; a product of two non-literals is
refused (decision c). -/
def ofTermFuel? (ps : List Parameter) : Nat → (t : LTm C .kint) →
    Option (KIntValue (ps := ps) (es := es) t)
  | 0, _ => none
  | _ + 1, .app0 (.zlit n) => some (zlit n)
  | _ + 1, .app1 .toInt a => (CheckedValue.ofTermIn? ps a).map toInt
  | fuel + 1, .app2 (.zbin .add h) a b => do
    return arith false .add h rfl (← ofTermFuel? ps fuel a) (← ofTermFuel? ps fuel b)
  | fuel + 1, .app2 (.zbin .sub h) a b => do
    return arith true .sub h rfl (← ofTermFuel? ps fuel a) (← ofTermFuel? ps fuel b)
  | fuel + 1, .app2 (.zbin .mul h) a b =>
    match a.zlit? with
    | some ⟨n, hn⟩ => do return mulLit h n hn (← ofTermFuel? ps fuel b)
    | none =>
      match b.zlit? with
      | some ⟨n, hn⟩ => do return litMul h n hn (← ofTermFuel? ps fuel a)
      | none => none
  | _ + 1, _ => none

def ofTermIn? (ps : List Parameter) (t : LTm C .kint) : Option (KIntValue (ps := ps) (es := es) t) :=
  ofTermFuel? ps 1024 t

end KIntValue

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

theorem eval_zcmp (g : State C []) (ν : AEnv) (op : BinOp) (h : op.zCmp = true)
    (a b : LTm C .kint) :
    ((LTm.app2 (.zcmp op h) a b).eval g ν : Option Bool) =
      ((a.eval g ν : Option Int).bind fun v => (b.eval g ν : Option Int).map fun w => op.cmpZ v w) := by
  rw [LTm.eval_app2]
  cases (a.eval g ν : Option Int) <;> cases (b.eval g ν : Option Int) <;> rfl

/-- `a ⊲ b` on KeY's `int`. -/
def zcmp (op : BinOp) (h : op.zCmp = true) {a b : LTm C .kint}
    (ha : KIntValue (ps := ps) (es := es) a) (hb : KIntValue (ps := ps) (es := es) b) :
    BooleanValue (ps := ps) (es := es) (.app2 (.zcmp op h) a b) :=
  ⟨ha.refs ++ hb.refs, fun rs => CheckedInt.comparison op (ha.lower rs) (hb.lower rs), by
    intro rs hs g ν
    rw [eval_zcmp]
    exact CheckedInt.comparison_correct _ _ _ _ _ _
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
  | _ + 1, _, .app2 (.zcmp op h) a b => do
    return zcmp op h (← KIntValue.ofTermIn? ps a) (← KIntValue.ofTermIn? ps b)
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

def equalityPlain? : {p : PrimTy} → (a b : LTm C (.val p)) → Option (StorageEncoding (ps := ps) (es := es) (.eq a b))
  | .bool, a, b => do return boolEq (← BooleanValue.ofTermIn? ps a) (← BooleanValue.ofTermIn? ps b)
  | .uint, a, b | .int, a, b => do return eq (← CheckedValue.ofTermIn? ps a) (← CheckedValue.ofTermIn? ps b)

/-! ### The defining equations of cut atoms

`Calculus/QuotientCut.lean` replaces an operator that is not affine in its
operand's code by a fresh atom `k` and defines it by `e == k`, `e` the
operator's node.  Each such equation is encoded exactly by a relation
between the operands' codes and `k`'s, linear because the divisor, the shift
and the wrap are literals: `d·q ≤ x < d·q + d` for a quotient,
`y = x₁ + x₂` or `y + 2^256 = x₁ + x₂` for a wrapped sum, `y = x + 2^255` or
`y + 2^255 = x` for a conversion. -/

/-- The parameter `k`'s code, as `CheckedValue.parameter` lays it out. -/
theorem param_code {r : PrimTy} (k : Nat) (hk : Parameter.mk r k ∈ ps) (rs : List (Ref C))
    (g : State C []) (ν : AEnv) :
    (Affine.variable (es.length + Parameters.index ⟨r, k⟩ ps)).eval (Inputs.observe es ps rs g ν).codes =
      ((encode r (ν.get r k)).val : Int) :=
  ((CheckedValue.parameter (C := C) (ps := ps) (es := es) k hk).correct rs (fun _ h => nomatch h) g ν).2

/-- A unary node `e` of `a` defining the atom `k`, by the relation `rel`
between their codes. -/
def rel1 {p r : PrimTy} {a : LTm C (.val p)} {e : LTm C (.val r)} (k : Nat)
    (hk : Parameter.mk r k ∈ ps) (f : p.Denote → Option r.Denote)
    (he : ∀ g ν, e.eval g ν = (a.eval g ν).bind f) (rel : Affine → Affine → AFml)
    (hrel : ∀ (x : Nat → Nat) (v : p.Denote) (w : r.Denote) (A B : Affine),
      A.eval x = ((encode p v).val : Int) → B.eval x = ((encode r w).val : Int) →
        ((rel A B).holds x ↔ f v = some w))
    (ha : CheckedValue (ps := ps) (es := es) a) : StorageEncoding (ps := ps) (es := es) (.eq e (.var k)) :=
  ⟨ha.refs, fun rs => .and (ha.lower rs).defined
      (rel (ha.lower rs).code (.variable (es.length + Parameters.index ⟨r, k⟩ ps))), by
    intro rs hr g ν
    have ih := ha.correct rs hr g ν
    have hq := param_code (C := C) (es := es) k hk rs g ν
    simp only [LFml.holds, he, LTm.eval_var]
    cases hv : a.eval g ν with
    | none =>
      rw [hv] at ih
      simp only [AFml.holds, Option.bind_none]
      exact ⟨(fun h => (ih h.1).elim), (fun h => h.elim)⟩
    | some v =>
      rw [hv] at ih
      simp only [AFml.holds, Option.bind_some, ih.1, true_and, hrel _ v (ν.get r k) _ _ ih.2 hq]
      cases f v with
      | none => exact ⟨(fun h => nomatch h), (fun h => h.elim)⟩
      | some w => exact ⟨(fun h => Option.some.inj h), (fun h => congrArg some h)⟩⟩

/-- A binary node `e` of `a` and `b` defining the atom `k`. -/
def rel2 {p r : PrimTy} {a b : LTm C (.val p)} {e : LTm C (.val r)} (k : Nat)
    (hk : Parameter.mk r k ∈ ps) (f : p.Denote → p.Denote → Option r.Denote)
    (he : ∀ g ν, e.eval g ν = (a.eval g ν).bind fun x => (b.eval g ν).bind (f x))
    (rel : Affine → Affine → Affine → AFml)
    (hrel : ∀ (x : Nat → Nat) (v u : p.Denote) (w : r.Denote) (A B Y : Affine),
      A.eval x = ((encode p v).val : Int) → B.eval x = ((encode p u).val : Int) →
        Y.eval x = ((encode r w).val : Int) → ((rel A B Y).holds x ↔ f v u = some w))
    (ha : CheckedValue (ps := ps) (es := es) a) (hb : CheckedValue (ps := ps) (es := es) b) :
    StorageEncoding (ps := ps) (es := es) (.eq e (.var k)) :=
  ⟨ha.refs ++ hb.refs, fun rs => .and (ha.lower rs).defined (.and (hb.lower rs).defined
      (rel (ha.lower rs).code (hb.lower rs).code (.variable (es.length + Parameters.index ⟨r, k⟩ ps)))), by
    intro rs hr g ν
    have iha := ha.correct rs (fun r hm => hr r (List.mem_append_left _ hm)) g ν
    have ihb := hb.correct rs (fun r hm => hr r (List.mem_append_right _ hm)) g ν
    have hq := param_code (C := C) (es := es) k hk rs g ν
    simp only [LFml.holds, he, LTm.eval_var]
    cases hv : a.eval g ν with
    | none =>
      rw [hv] at iha
      simp only [AFml.holds, Option.bind_none]
      exact ⟨(fun h => (iha h.1).elim), (fun h => h.elim)⟩
    | some v =>
      rw [hv] at iha
      cases hu : b.eval g ν with
      | none =>
        rw [hu] at ihb
        simp only [AFml.holds, Option.bind_none, Option.bind_some]
        exact ⟨(fun h => (ihb h.2.1).elim), (fun h => h.elim)⟩
      | some u =>
        rw [hu] at ihb
        simp only [AFml.holds, Option.bind_some, iha.1, ihb.1, true_and,
          hrel _ v u (ν.get r k) _ _ _ iha.2 ihb.2 hq]
        cases f v u with
        | none => exact ⟨(fun h => nomatch h), (fun h => h.elim)⟩
        | some w => exact ⟨(fun h => Option.some.inj h), (fun h => congrArg some h)⟩⟩

end StorageEncoding

/-- `d · (y - off) ≤ x - off ≤ d · (y - off) + d - 1`: `y` is `x` divided by
`d`, rounding down, on codes offset by `off`. -/
def floorRel (off d M : Int) (A B : Affine) : AFml :=
  .and (.and (((B.offset (-off)).scale d).le (A.offset (-off)))
    ((A.offset (-off)).le (((B.offset (-off)).scale d).offset (d - 1))))
    ((B.offset (-off)).le (.literal (M / d)))

theorem floorRel_holds (off d M : Int) (A B : Affine) (x : Nat → Nat) :
    (floorRel off d M A B).holds x ↔
      (d * (B.eval x - off) ≤ A.eval x - off ∧ A.eval x - off ≤ d * (B.eval x - off) + (d - 1)) ∧
        B.eval x - off ≤ M / d := by
  simp only [floorRel, AFml.holds, Affine.holds_le, Affine.eval_offset, Affine.eval_scale,
    Affine.eval_literal, ← Int.sub_eq_add_neg]

/-- `y = x₁ + x₂` or `y + 2^256 = x₁ + x₂`, and for a difference `y = x₁ - x₂`
or `y = x₁ - x₂ + 2^256`. -/
def wrapRel (sub : Bool) (A B Y : Affine) : AFml :=
  if sub then .imp (.not (Y.eq (A.sub B))) (Y.eq ((A.sub B).offset ((2 ^ 256 : Nat) : Int)))
  else .imp (.not (Y.eq (A.add B))) ((Y.offset ((2 ^ 256 : Nat) : Int)).eq (A.add B))

/-- `y = x + 2^255` or `y + 2^255 = x`: a conversion between the codes of
`uint` and `int`. -/
def convRel (A Y : Affine) : AFml :=
  .imp (.not (Y.eq (A.offset ((2 ^ 255 : Nat) : Int)))) ((Y.offset ((2 ^ 255 : Nat) : Int)).eq A)

theorem convRel_holds (A Y : Affine) (x : Nat → Nat) :
    (convRel A Y).holds x ↔ Y.eval x = A.eval x + ((2 ^ 255 : Nat) : Int) ∨
      Y.eval x + ((2 ^ 255 : Nat) : Int) = A.eval x := by
  simp only [convRel, AFml.holds, Affine.holds_eq, Affine.eval_offset]
  omega

theorem PrimTy.ofInt?_eq_some_iff {p : PrimTy} (hp : p.isNumeric = true) (n : Int) (w : p.Denote) :
    p.ofInt? n = some w ↔ integer p w = n := by
  cases p with
  | bool => cases hp
  | uint | int =>
    simp only [PrimTy.ofInt?, integer]
    split
    · exact ⟨(fun h => by cases h; rfl), (fun h => by subst h; rfl)⟩
    · rename_i hn
      exact ⟨(fun h => nomatch h), (fun h => absurd (h ▸ w.property) hn)⟩

theorem encode_uint (v : PrimTy.uint.Denote) : ((encode .uint v).val : Int) = v.val := by
  rw [encode_integer]; simp only [integer, offset, Int.add_zero]

theorem encode_int (v : PrimTy.int.Denote) :
    ((encode .int v).val : Int) = v.val + ((2 ^ 255 : Nat) : Int) := by
  rw [encode_integer]; rfl

theorem eq_ediv_iff {d : Int} (hd : 0 < d) (v w : Int) :
    w = v / d ↔ d * w ≤ v ∧ v ≤ d * w + (d - 1) := by
  constructor
  · rintro rfl
    have h1 := Int.ediv_mul_le v (Int.ne_of_gt hd)
    have h2 := Int.lt_ediv_add_one_mul_self v hd
    rw [Int.add_mul, Int.one_mul] at h2
    rw [Int.mul_comm]
    omega
  · rintro ⟨h1, h2⟩
    have hle : w ≤ v / d := (Int.le_ediv_iff_mul_le hd).mpr (by rw [Int.mul_comm]; exact h1)
    have hlt : v / d < w + 1 := (Int.ediv_lt_iff_lt_mul hd).mpr (by rw [Int.add_mul, Int.one_mul, Int.mul_comm]; omega)
    omega

/-- A quotient below the largest value `M` its dividend may take: the bound
the relation states, so that the decision need not discover it. -/
theorem eq_ediv_iff_bounded {d : Int} (hd : 0 < d) (v w M : Int) (hv : v ≤ M) :
    w = v / d ↔ (d * w ≤ v ∧ v ≤ d * w + (d - 1)) ∧ w ≤ M / d := by
  rw [eq_ediv_iff hd]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2⟩, (Int.le_ediv_iff_mul_le hd).mpr (by rw [Int.mul_comm]; omega)⟩
  · rintro ⟨h, -⟩
    exact h

/-- The largest value of a type. -/
def maxInt : PrimTy → Int
  | .uint => ((2 ^ 256 : Nat) : Int) - 1
  | .int => ((2 ^ 255 : Nat) : Int) - 1
  | .bool => 1

namespace StorageEncoding

/-- `a / c == k` at `uint`, `c ≠ 0`. -/
def defDiv (h : BinOp.div.accepts .uint = true) {a : LTm C (.val .uint)} (c : PrimTy.uint.Denote)
    (hc : c.val ≠ 0) (k : Nat) (hk : Parameter.mk .uint k ∈ ps)
    (ha : CheckedValue (ps := ps) (es := es) a) :
    StorageEncoding (ps := ps) (es := es) (.eq (.app2 (.binop .div h) a (.app0 (.lit c))) (.var k)) :=
  rel1 k hk (fun x => BinOp.evalT .div h x c)
    (fun g ν => by rw [LTm.eval_binop_of h (shortT_none ⟨by decide, by decide⟩)]; rfl)
    (floorRel 0 c.val (maxInt .uint)) (by
      intro x v w A B hA hB
      change PrimTy.uint.Denote at w
      change B.eval x = ((encode .uint w).val : Int) at hB
      rw [floorRel_holds, hA, hB, encode_uint, encode_uint]
      show _ ↔ (if c.val = 0 then none else some (Int.tdiv v.val c.val)).bind PrimTy.uint.ofInt? = some w
      rw [if_neg hc, Option.bind_some, PrimTy.ofInt?_eq_some_iff rfl,
        Int.tdiv_eq_ediv_of_nonneg (uint_val_nonneg v)]
      have hc0 : 0 < c.val := by have := uint_val_nonneg c; omega
      have := eq_ediv_iff_bounded hc0 v.val w.val (maxInt .uint)
        (by have := uint_val_lt v; simp only [maxInt]; omega)
      simp only [integer, Int.sub_zero]
      omega) ha

/-- The divisor of `a >> v`: `2^v`, every shift past the word one of `2^256`. -/
def shrDiv {p : PrimTy} (v : p.Denote) : Int :=
  2 ^ (if integer p v < 256 then (integer p v).toNat else 256)

/-- `a >> v == k`, at `uint` (logical) and `int` (arithmetic). -/
def defShr {p : PrimTy} (h : BinOp.shr.accepts p = true) {a : LTm C (.val p)} (v : p.Denote)
    (k : Nat) (hk : Parameter.mk p k ∈ ps) (ha : CheckedValue (ps := ps) (es := es) a) :
    StorageEncoding (ps := ps) (es := es) (.eq (.app2 (.binop .shr h) a (.app0 (.lit v))) (.var k)) :=
  rel1 k hk (fun x => BinOp.evalT .shr h x v)
    (fun g ν => by rw [LTm.eval_binop_of h (shortT_none ⟨by decide, by decide⟩)]; rfl)
    (floorRel (offset p) (shrDiv v) (maxInt p)) (by
      intro x u w A B hA hB
      have hM := uintBound_eq
      have hp : (2 : Int) ^ 256 = ((2 ^ 256 : Nat) : Int) := by rw [Int.natCast_pow]; rfl
      rw [floorRel_holds, hA]
      cases p with
      | bool => cases h
      | uint =>
        change PrimTy.uint.Denote at w
        change B.eval x = ((encode .uint w).val : Int) at hB
        rw [hB, encode_uint, encode_uint]
        have hu0 := uint_val_nonneg u
        have hu1 := uint_val_lt u
        have hw0 := uint_val_nonneg w
        have hw1 := uint_val_lt w
        show _ ↔ (some (if v.val < 256 then u.val / 2 ^ v.val.toNat
          else if u.val < 0 then -1 else 0)).bind PrimTy.uint.ofInt? = some w
        rw [Option.bind_some, PrimTy.ofInt?_eq_some_iff rfl]
        simp only [shrDiv, integer, offset, Int.sub_zero]
        by_cases hk : v.val < 256
        · simp only [hk, if_true]
          exact (eq_ediv_iff_bounded (Int.pow_pos (by decide)) _ _ _
            (by simp only [maxInt]; omega)).symm
        · simp only [hk, if_false, if_neg (show ¬ u.val < 0 by omega), hp, maxInt]
          rw [hM] at *
          omega
      | int =>
        change PrimTy.int.Denote at w
        change B.eval x = ((encode .int w).val : Int) at hB
        rw [hB, encode_int, encode_int]
        have hu := int_val_bounds u
        have hw := int_val_bounds w
        have hB' := intBound_eq
        show _ ↔ (some (if v.val < 256 then u.val / 2 ^ v.val.toNat
          else if u.val < 0 then -1 else 0)).bind PrimTy.int.ofInt? = some w
        rw [Option.bind_some, PrimTy.ofInt?_eq_some_iff rfl]
        simp only [shrDiv, integer, offset, Int.add_sub_cancel]
        by_cases hk : v.val < 256
        · simp only [hk, if_true]
          exact (eq_ediv_iff_bounded (Int.pow_pos (by decide)) _ _ _
            (by simp only [maxInt]; omega)).symm
        · simp only [hk, if_false, hp, maxInt]
          rw [hM, hB'] at *
          split <;> omega) ha

/-- `a +% b == k` at `uint`. -/
def defAddW (h : BinOp.addW.accepts .uint = true) {a b : LTm C (.val .uint)} (k : Nat)
    (hk : Parameter.mk .uint k ∈ ps)
    (ha : CheckedValue (ps := ps) (es := es) a) (hb : CheckedValue (ps := ps) (es := es) b) :
    StorageEncoding (ps := ps) (es := es) (.eq (.app2 (.binop .addW h) a b) (.var k)) :=
  rel2 k hk (fun x y => BinOp.evalT .addW h x y)
    (fun g ν => by rw [LTm.eval_binop_of h (shortT_none ⟨by decide, by decide⟩)])
    (wrapRel false) (by
      intro x v u w A B Y hA hB hY
      change PrimTy.uint.Denote at w
      change Y.eval x = ((encode .uint w).val : Int) at hY
      have hM := uintBound_eq
      have hv0 := uint_val_nonneg v
      have hv1 := uint_val_lt v
      have hu0 := uint_val_nonneg u
      have hu1 := uint_val_lt u
      have hw0 := uint_val_nonneg w
      have hw1 := uint_val_lt w
      simp only [wrapRel, Bool.false_eq_true, if_false, AFml.holds, Affine.holds_eq,
        Affine.eval_offset, Affine.eval_add, hA, hB, hY, encode_uint]
      show _ ↔ (some ((v.val + u.val) % Semantics.uintBound)).bind PrimTy.uint.ofInt? = some w
      rw [Option.bind_some, PrimTy.ofInt?_eq_some_iff rfl]
      simp only [integer, Semantics.uintBound]
      rw [hM] at *
      omega) ha hb

/-- `a -% b == k` at `uint`. -/
def defSubW (h : BinOp.subW.accepts .uint = true) {a b : LTm C (.val .uint)} (k : Nat)
    (hk : Parameter.mk .uint k ∈ ps)
    (ha : CheckedValue (ps := ps) (es := es) a) (hb : CheckedValue (ps := ps) (es := es) b) :
    StorageEncoding (ps := ps) (es := es) (.eq (.app2 (.binop .subW h) a b) (.var k)) :=
  rel2 k hk (fun x y => BinOp.evalT .subW h x y)
    (fun g ν => by rw [LTm.eval_binop_of h (shortT_none ⟨by decide, by decide⟩)])
    (wrapRel true) (by
      intro x v u w A B Y hA hB hY
      change PrimTy.uint.Denote at w
      change Y.eval x = ((encode .uint w).val : Int) at hY
      have hM := uintBound_eq
      have hv0 := uint_val_nonneg v
      have hv1 := uint_val_lt v
      have hu0 := uint_val_nonneg u
      have hu1 := uint_val_lt u
      have hw0 := uint_val_nonneg w
      have hw1 := uint_val_lt w
      simp only [wrapRel, if_true, AFml.holds, Affine.holds_eq, Affine.eval_offset,
        Affine.eval_sub, hA, hB, hY, encode_uint]
      show _ ↔ (some ((v.val - u.val) % Semantics.uintBound)).bind PrimTy.uint.ofInt? = some w
      rw [Option.bind_some, PrimTy.ofInt?_eq_some_iff rfl]
      simp only [integer, Semantics.uintBound]
      rw [hM] at *
      omega) ha hb

/-- `int(a) == k`. -/
def defToInt (h : UnOp.toInt.accepts .uint = true) {a : LTm C (.val .uint)} (k : Nat)
    (hk : Parameter.mk .int k ∈ ps) (ha : CheckedValue (ps := ps) (es := es) a) :
    StorageEncoding (ps := ps) (es := es) (.eq (.app1 (.unop .toInt h) a) (.var k)) :=
  rel1 k hk (fun x => UnOp.evalT .toInt h x)
    (fun g ν => by rw [LTm.eval_app1, Close.Op1.eval_unop]) convRel (by
      intro x v w A B hA hB
      change PrimTy.int.Denote at w
      change B.eval x = ((encode .int w).val : Int) at hB
      rw [convRel_holds, hA, hB, encode_uint, encode_int]
      have hM := uintBound_eq
      have hB' := intBound_eq
      have hv0 := uint_val_nonneg v
      have hv1 := uint_val_lt v
      have hw := int_val_bounds w
      show _ ↔ PrimTy.int.ofInt? (if v.val < Semantics.intBound then v.val
        else v.val - Semantics.uintBound) = some w
      rw [PrimTy.ofInt?_eq_some_iff rfl]
      simp only [integer, Semantics.uintBound, Semantics.intBound]
      rw [hM, hB'] at *
      split <;> omega) ha

/-- `uint(a) == k`. -/
def defToUint (h : UnOp.toUint.accepts .int = true) {a : LTm C (.val .int)} (k : Nat)
    (hk : Parameter.mk .uint k ∈ ps) (ha : CheckedValue (ps := ps) (es := es) a) :
    StorageEncoding (ps := ps) (es := es) (.eq (.app1 (.unop .toUint h) a) (.var k)) :=
  rel1 k hk (fun x => UnOp.evalT .toUint h x)
    (fun g ν => by rw [LTm.eval_app1, Close.Op1.eval_unop]) (fun A Y => convRel Y A) (by
      intro x v w A B hA hB
      change PrimTy.uint.Denote at w
      change B.eval x = ((encode .uint w).val : Int) at hB
      rw [convRel_holds, hA, hB, encode_int, encode_uint]
      have hM := uintBound_eq
      have hB' := intBound_eq
      have hv := int_val_bounds v
      have hw0 := uint_val_nonneg w
      have hw1 := uint_val_lt w
      show _ ↔ PrimTy.uint.ofInt? (v.val % Semantics.uintBound) = some w
      rw [PrimTy.ofInt?_eq_some_iff rfl]
      simp only [integer, Semantics.uintBound]
      rw [hM, hB'] at *
      omega) ha

/-- The defining equation `op x y == k` of a cut atom, by the operator. -/
def specialBin? (op : BinOp) {q : PrimTy} (h : op.accepts q = true) (x y : LTm C (.val q)) (k : Nat)
    (hk : Parameter.mk (op.ret q) k ∈ ps) :
    Option (StorageEncoding (ps := ps) (es := es) (.eq (.app2 (.binop op h) x y) (.var k))) :=
  match op, h, hk with
  | .div, h, hk =>
    match q, h, y, hk with
    | .uint, h, .app0 (.lit c), hk =>
      if hc : c.val = 0 then none else (CheckedValue.ofTermIn? ps x).map (defDiv h c hc k hk)
    | _, _, _, _ => none
  | .shr, h, hk =>
    match y with
    | .app0 (.lit v) => (CheckedValue.ofTermIn? ps x).map (defShr h v k hk)
    | _ => none
  | .addW, h, hk =>
    match q, h, x, y, hk with
    | .uint, h, x, y, hk => do
      return defAddW h k hk (← CheckedValue.ofTermIn? ps x) (← CheckedValue.ofTermIn? ps y)
    | _, _, _, _, _ => none
  | .subW, h, hk =>
    match q, h, x, y, hk with
    | .uint, h, x, y, hk => do
      return defSubW h k hk (← CheckedValue.ofTermIn? ps x) (← CheckedValue.ofTermIn? ps y)
    | _, _, _, _, _ => none
  | _, _, _ => none

/-- The defining equation `op x == k` of a cut atom, by the operator. -/
def specialUn? (op : UnOp) {q : PrimTy} (h : op.accepts q = true) (x : LTm C (.val q)) (k : Nat)
    (hk : Parameter.mk (op.ret q) k ∈ ps) :
    Option (StorageEncoding (ps := ps) (es := es) (.eq (.app1 (.unop op h) x) (.var k))) :=
  match op, h, hk with
  | .toInt, h, hk =>
    match q, h, x, hk with
    | .uint, h, x, hk => (CheckedValue.ofTermIn? ps x).map (defToInt h k hk)
    | _, _, _, _ => none
  | .toUint, h, hk =>
    match q, h, x, hk with
    | .int, h, x, hk => (CheckedValue.ofTermIn? ps x).map (defToUint h k hk)
    | _, _, _, _ => none
  | _, _, _ => none

/-- The defining equation `e == k` of a cut atom, recognized by `e`'s operator. -/
def specialVar? : {p : PrimTy} → (a : LTm C (.val p)) → (k : Nat) → Parameter.mk p k ∈ ps →
    Option (StorageEncoding (ps := ps) (es := es) (.eq a (.var k)))
  | _, .app2 (.binop op h) x y, k, hk => specialBin? op h x y k hk
  | _, .app1 (.unop op h) x, k, hk => specialUn? op h x k hk
  | _, _, _, _ => none

def special? {p : PrimTy} (a : LTm C (.val p)) : (b : LTm C (.val p)) →
    Option (StorageEncoding (ps := ps) (es := es) (.eq a b))
  | .var k => if hk : Parameter.mk p k ∈ ps then specialVar? a k hk else none
  | _ => none

def equality? {p : PrimTy} (a b : LTm C (.val p)) : Option (StorageEncoding (ps := ps) (es := es) (.eq a b)) :=
  match special? a b with
  | some e => some e
  | none => equalityPlain? a b

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
