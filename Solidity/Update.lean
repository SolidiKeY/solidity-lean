import Solidity.Semantics.Agree
import Solidity.Semantics.WellFormed
import Solidity.TermSimp
import Solidity.Theory.Abs

/-!
# Modalities, and what the terms' signature leaves to the interpreter

The terms of the calculus are typed (`Signature.lean`: KeY's sorts indexed
by Solidity types, the symbols over the contract; `Calculus/Fml.lean`: the
terms, updates and formulas in a context).  The untyped signature that was
here (`Srt`, `Op0` … `Op3`, read on `Semantics.State`) went at W9.8.3
(`docs/intrinsic.md`).  What stays: the two modalities and how a halt
reads under each (`Modality.after`), the interpreter's memory read
(`readAddr`), the Theory's reading of a result (`StValue.toRes`,
`Res.toSt`), the ledger's arithmetic (`IntOp`), and the states a callee or
a loop iteration may leave (`State.havoc`, `State.anon`).

Unlike KeY's, the terms can halt: they are read by the interpreter's own
operations, so `a + b` reverts on overflow and `values[i]` on an index out
of range, exactly as the statement they came from.  An update therefore
carries the modality of the goal it was produced in, and `{U} φ` with a
halting `U` is judged as the halting statement would be.
-/

namespace Solidity

open Semantics

/-- The two modalities: the diamond `⟨ P ⟩ φ` and the box `[ P ] φ`. -/
inductive Modality where
  | diamond
  | box
  deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

/-- What a modality says of a run that reverts (or is `undef`): every box
formula holds of it, no diamond formula does. -/
def Modality.onHalt : Modality → Prop
  | .diamond => False
  | .box => True

/-- `p` after a run under `m`: `p` of the state it ends in, or `m.onHalt`.
An update reads so: a term never panics (`Upd.applyV_noPanic`). -/
def Modality.after (m : Modality) (p : State → Prop) : Res State → Prop
  | .ok τ => p τ
  | .error _ => m.onHalt

/-! ## Memory reads

The slot a memory address names, as the interpreter reads it. -/

variable {C : Contract}

/-- The slot at a memory address. -/
def readAddr (σ : State) : Addr → Res MVal
  | .memoryField id f => do
    match ← σ.getObj id with
    | .struct fields =>
      match lookupBy f fields with
      | some v => pure v
      | none => .error .undef
    | .array _ _ => .error .undef
  | .memoryIndex id i => do
    match ← σ.getObj id with
    | .array elems _ =>
      if h : 0 ≤ i ∧ i.toNat < elems.length then pure (elems.get ⟨i.toNat, h.2⟩)
      else .error .revert
    | .struct _ => .error .undef

/-! ## The Theory's readings of results -/

section Denote

open Theory Theory.StValue

/-- A Theory value as an interpreter result: a primitive, or a halt. -/
def Theory.StValue.toRes : StValue → Res Value
  | .prim p => .ok p
  | .st _ => .error .undef

/-- An interpreter result as a Theory value: a halt reads as nothing. -/
def Semantics.Res.toSt : Res Value → StValue
  | .ok v => .prim v
  | .error _ => .st .mtSt


/-- A binop that returns on a halting right operand short-circuited, so it
returns the same on any.  `denote` hands `evalBinop` the right operand's
`toRes`, which is not `eval`'s halt where `eval` halts. -/
theorem Denote.evalBinop_of_error {op : BinOp} {p : PrimTy} {lv x : Value} {e : Halt}
    (rb : Res Value) (h : evalBinop op p lv (.error e) = .ok x) :
    evalBinop op p lv rb = .ok x := by
  unfold evalBinop at h ⊢
  split <;> simp_all only [bind, Except.bind, reduceCtorEq]

/-- A stored word read as a value abstracts to that value. -/
theorem _root_.Solidity.Semantics.SVal.abs_of_asValue {w : SVal} {x : Value}
    (h : w.asValue = .ok x) : w.abs = .prim x := by
  match w, h with
  | .prim (.int _), h => cases h; rfl
  | .prim (.bool _), h => cases h; rfl
  | .struct _, h | .array .., h | .map .., h => cases h

/-- The Theory's `int` cast agrees with the interpreter's where it returns:
an index and `newArr`'s size are read with the Theory's total cast. -/
theorem Denote.asInt_prim_of_asInt {v : Value} {i : Int} (h : v.asInt = .ok i) :
    asInt (.prim v) = i := by
  cases v <;> cases h; rfl

end Denote

/-! ## Updates -/

/-- `+` or `-` of KeY's `int`, which has no range to check: the arithmetic
of the ledger updates, where a `Term.binop` would be range-checked. -/
inductive IntOp where
  | add | sub
  deriving DecidableEq, Repr

def IntOp.apply : IntOp → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b

/-- The operator as a Lean term, for the quoter (`Calculus/Quote.lean`). -/
def IntOp.quote : IntOp → Lean.Expr
  | .add => Lean.mkConst ``IntOp.add
  | .sub => Lean.mkConst ``IntOp.sub

/-! ## States a callee may leave -/

/-- The state after a callback: storage and ledger replaced by what the
callee left (KeY's `{storage := storageSk ‖ net := netSk}`, fresh skolem
constants), the locals, memory and funds of the caller kept: the funds are
not a transfer's to change. -/
def Semantics.State.havoc (σ : State) (st : List (Name × SVal)) (nt : List (Int × Int)) :
    State :=
  { σ with storage := st, net := nt }

/-- A callee that changes nothing. -/
@[simp] theorem Semantics.State.havoc_self (σ : State) :
    σ.havoc σ.storage σ.net = σ := by
  cases σ; rfl

theorem Semantics.EnvAgreeExcept.havoc {ns : List Var} {σ τ : State} (h : EnvAgreeExcept ns σ τ)
    (st : List (Name × SVal)) (nt : List (Int × Int)) :
    EnvAgreeExcept ns (σ.havoc st nt) (τ.havoc st nt) :=
  ⟨rfl, h.heap, h.nextId, rfl, h.env, h.selfBalance, h.tx⟩

/-! ## States a loop iteration may leave

solkey's `#loopAnon` gives every local a loop body assigns or declares a
fresh constant (`LoopFrame`).  Here the locals `xs` are bound as `b` says,
or unbound: an untyped state may hold anything there, and a local the body
declares is unbound before the first iteration. -/

/-- The environment `e` with each local of `xs` bound as `b` says. -/
def anonEnv (b : Var → Option Binding) : List Var → List (Var × Binding) → List (Var × Binding)
  | [], e => e
  | x :: xs, e =>
    match b x with
    | some v => setBy x v (anonEnv b xs e)
    | none => (anonEnv b xs e).filter (·.1 != x)

/-- The state after an anonymising update of the locals `xs`. -/
def Semantics.State.anon (σ : State) (xs : List Var) (b : Var → Option Binding) : State :=
  { σ with env := anonEnv b xs σ.env }

theorem lookupBy_filter_self {α : Type} (x : Var) :
    (l : List (Var × α)) → lookupBy x (l.filter (·.1 != x)) = none
  | [] => rfl
  | (y, v) :: l => by
    by_cases h : y = x
    · subst h; simp only [List.filter, bne_self_eq_false]; exact lookupBy_filter_self y l
    · have h' : (y != x) = true := bne_iff_ne.2 h
      simp only [List.filter, h', lookupBy, Ne.symm h, if_false]
      exact lookupBy_filter_self x l

theorem lookupBy_filter_ne {α : Type} {x y : Var} (hne : y ≠ x) :
    (l : List (Var × α)) → lookupBy y (l.filter (·.1 != x)) = lookupBy y l
  | [] => rfl
  | (z, v) :: l => by
    by_cases h : z = x
    · subst h
      simp only [List.filter, bne_self_eq_false, lookupBy, hne, if_false]
      exact lookupBy_filter_ne hne l
    · have h' : (z != x) = true := bne_iff_ne.2 h
      simp only [List.filter, h', lookupBy]
      split
      · rfl
      · exact lookupBy_filter_ne hne l

/-- A local of `xs` reads as `b` says, any other as before. -/
theorem lookupBy_anonEnv (b : Var → Option Binding) (y : Var) :
    (xs : List Var) → (e : List (Var × Binding)) →
      lookupBy y (anonEnv b xs e) = if y ∈ xs then b y else lookupBy y e
  | [], e => by simp only [anonEnv, List.not_mem_nil, if_false]
  | x :: xs, e => by
    have ih := lookupBy_anonEnv b y xs e
    by_cases h : y = x
    · subst h
      simp only [anonEnv, List.mem_cons, true_or, if_true]
      cases hb : b y with
      | some v => exact SemanticsProperties.lookupBy_setBy_self _ _ _
      | none => exact lookupBy_filter_self _ _
    · simp only [anonEnv, List.mem_cons, h, false_or]
      cases b x with
      | some v => rw [SemanticsProperties.lookupBy_setBy_ne h, ih]
      | none => rw [lookupBy_filter_ne h, ih]

theorem Semantics.EnvAgreeExcept.anon {ns : List Var} {σ τ : State} (h : EnvAgreeExcept ns σ τ)
    (xs : List Var) (b : Var → Option Binding) :
    EnvAgreeExcept ns (σ.anon xs b) (τ.anon xs b) :=
  ⟨h.storage, h.heap, h.nextId, h.net, fun n hn => by
    simp only [State.anon, lookupBy_anonEnv, h.env n hn], h.selfBalance, h.tx⟩

/-- The values of the primitive type `p`, which a quantifier ranges over. -/
def PrimTy.admits : PrimTy → Value → Prop
  | .bool, .bool _ => True
  | .uint, .int n => 0 ≤ n ∧ n < uintBound
  | .int, .int n => -intBound ≤ n ∧ n < intBound
  | _, _ => False

end Solidity
