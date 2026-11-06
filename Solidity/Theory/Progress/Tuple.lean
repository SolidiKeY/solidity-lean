import Solidity.Source.StmtProgress
import Solidity.Source.Progress.BuiltinAdmission

/-!
# Progress of tuple declarations (S4.2)

`(, T x, , U y) = e;` (lane FU2-B, `RStmt.declTuple`) evaluates `e`, takes
its components (`RVal.untuple`) and pushes each declared one converted to
its slot's type (`pushVals`). Three places can be `stuck`:

* `untuple` on a value that is not a tuple — impossible: no plain `Val` has
  a tuple type (`Val.not_tuple`), so every `RVal` of a tuple type is a
  `.tuple` (`RVal.untuple_ok`);
* `pushVals` on slots and components of different lengths — excluded by
  the typing rule's `slotsFit` (`pushVals_ns`);
* the conversion of a component and its read as a plain value — never
  `stuck` for a slot of a value type converted from a value type or a
  constant (`SlotsOK`, the conditions `declInit` has in the fragment).

The initializer is either an expression of the call fragment (a call
returning several values) or a tuple literal whose components are in the
builtins' argument fragment (`TupleInit`, `ArgsFragment`). `declTuple_ns`
is the node step the fragment closure of `Theory/Progress/Fragment.lean`
uses; it asks expression progress only at horizons up to the statement's.

A tuple **assignment** `(a, b) = (b, a);` has no source typing rule
(`LVal` has no tuple form), so it is a typing gap, not a progress gap; in
the core semantics it is a `Prog` and progresses by construction
(`Theory/Progress/Outcome.lean`).
-/

namespace Solidity.Theory.Progress

open Solidity.Source Solidity.Source.Progress EM

variable {E : Env}

/-- **No plain value has a tuple type**: a tuple is only ever an `RVal.tuple`. -/
theorem Val.not_tuple {D : Layout} {σs : List STy} (v : Val D (.tuple σs)) : False := by
  cases v <;> rename_i h <;> simp only [STy.loc?, reduceCtorEq] at h

/-- **Taking a tuple's components is never `stuck`.** -/
theorem RVal.untuple_ok {D : Layout} {σs : List STy} (v : RVal D (.tuple σs)) : NotStuckR v.untuple := by
  cases v with
  | val x => exact (Val.not_tuple x).elim
  | tuple vs => exact NotStuckR.pure _

/-- **Slots the fragment pushes**: a slot for every component (the typing
rule's `slotsFit` already says so), each declared one at a value type,
its component of a value type or a constant. -/
def SlotsOK : List (Option STy) → List STy → Prop
  | [], [] => True
  | Option.none :: ss, _ :: σs => SlotsOK ss σs
  | Option.some τ :: ss, σ :: σs => τ.isValue = true ∧ σ.FragSrc ∧ SlotsOK ss σs
  | _, _ => False

/-- **Pushing a tuple declaration's components is never `stuck`.** -/
theorem pushVals_ns {Γ' : RCtx} (F : Fr) (n : Nat) : (slots : List (Option STy)) → {σs : List STy} →
    (vs : RVals E.layout σs) → {Γ : RCtx} → (l : Locals E.layout Γ) → slotsFit E.isBase E.mapFree slots σs = true →
    SlotsOK slots σs → NS (pushVals (Γ' := Γ') F n slots vs l)
  | [], _, .nil, _, _, _, _ => by simp only [pushVals]; exact NS.pure' _
  | Option.none :: ss, _ :: _, .cons _ vs, _, l, hf, ho => by
    simp only [slotsFit, Bool.and_eq_true] at hf
    simp only [pushVals]
    exact pushVals_ns F n ss vs l hf.2 ho
  | Option.some _ :: ss, _ :: _, .cons v vs, _, l, hf, ho => by
    simp only [slotsFit, Bool.and_eq_true] at hf
    simp only [pushVals]
    exact NS.bind (convRV_ns F n (.inl hf.1) ho.2.1 v) fun w =>
      NS.bind (getV_ns ho.1 w) fun x => pushVals_ns F n ss vs (.cons x l) hf.2 ho.2.2
  | [], _ :: _, .cons _ _, _, _, _, ho => ho.elim
  | Option.none :: _, [], .nil, _, _, _, ho => ho.elim
  | Option.some _ :: _, [], .nil, _, _, _, ho => ho.elim

/-- **A tuple declaration's initializer in the fragment**: an expression of
the call fragment (a call returning several values), or a tuple literal
whose components are of the builtins' argument fragment. -/
inductive TupleInit (A : Decl → Prop) {Γ : RCtx} : {σs : List STy} → RExpr E Γ (.tuple σs) → Prop where
  | checked {σs : List STy} (e : RExpr E Γ (.tuple σs)) : e.ValFragC A → e.OpsOK → TupleInit A e
  | lit {σs : List STy} (es : RArgs E Γ σs) : ArgsFragment A es → TupleInit A (.tuple es)

/-- Arguments of the builtins' fragment, given expression progress at every
horizon up to `n`. -/
theorem argsFragment_le {A : Decl → Prop} (G : Glob E) (F : Fr) {Γ : RCtx} :
    ∀ (n : Nat), (∀ m, m ≤ n → ExprNSAt A G F m) → {ts : List STy} → (es : RArgs E Γ ts) →
      ArgsFragment A es → NS (evalArgs G F n es)
  | 0, _, _, _, _ => by rw [evalArgs.eq_1]; exact NS.halt' fun _ h => by cases h
  | n + 1, hE, _, _, hf => by
    cases hf with
    | nil => simp only [evalArgs]; exact NS.pure' _
    | @cons t ts e es h hs =>
      simp only [evalArgs]
      have harg : NS (evalE G F n e) := by
        cases h with
        | checked e hf ho => exact (hE n (Nat.le_succ n)).val e hf ho
        | literal bs =>
          cases n
          · exact NS.halt' fun _ h => by cases h
          · exact NS.pure' _
      exact NS.bind harg fun _ =>
        NS.bind (argsFragment_le G F n (fun m hm => hE m (Nat.le_succ_of_le hm)) es hs) fun _ => NS.pure' _

/-- **A tuple declaration's initializer is never `stuck`.** -/
theorem tupleInit_ns {A : Decl → Prop} (G : Glob E) (F : Fr) (n : Nat) (hE : ∀ m, m ≤ n → ExprNSAt A G F m)
    {Γ : RCtx} {σs : List STy} (e : RExpr E Γ (.tuple σs)) (hi : TupleInit A e) : NS (evalE G F n e) := by
  cases hi with
  | checked e hf ho => exact (hE n (Nat.le_refl n)).val e hf ho
  | lit es hs =>
    cases n with
    | zero => rw [evalE.eq_1]; exact NS.halt' fun _ h => by cases h
    | succ n =>
      simp only [evalE]
      exact NS.bind (argsFragment_le G F n (fun m hm => hE m (Nat.le_succ_of_le hm)) es hs) fun _ => NS.pure' _

/-- **The tuple declaration step**: at horizon `n + 1`, a tuple declaration
whose initializer and slots are in the fragment is never `stuck`, and it
completes normally (so no `break` or `continue` escapes it). -/
theorem declTuple_ns {A : Decl → Prop} (G : Glob E) (F : Fr) (n : Nat) (hE : ∀ m, m ≤ n → ExprNSAt A G F m)
    (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ : RCtx} {σs : List STy}
    (slots : List (Option STy)) (e : RExpr E Γ (.tuple σs)) (h : slotsFit E.isBase E.mapFree slots σs = true)
    (l : Locals E.layout Γ) (hi : TupleInit A e) (hs : SlotsOK slots σs) :
    NSP (execS G F (n + 1) nps ph (RStmt.declTuple (R := R) (M := M) (k := k) slots e h) l)
      (fun o => ∃ l', o = .normal l') := by
  simp only [execS]
  refine NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken (NSP.of_ns (NS.bind (tupleInit_ns G F n hE e hi)
    fun v => NS.lift' (RVal.untuple_ok v))) fun _ _ _ => trivial)) fun p _ => ?_
  exact NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken (NSP.of_ns (pushVals_ns F n slots p.1 p.2 h hs))
    fun _ _ _ => trivial)) fun _ _ => NSP.pure' ⟨_, rfl⟩

end Solidity.Theory.Progress
