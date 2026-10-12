import Solidity.Calculus.Fml

/-!
# Reading a term

`Tm.eval` reads a term (`Calculus/Fml.lean`) on the typed state, a local by
`TEnv.get`, a symbol by `OpN.eval` on the global part (`State.glob`); no
value is erased, and a revert is `none` (`docs/intrinsic.md`, W9.8.1 and
W9.8.3).

The laws on terms are `Storage`'s (`Signature.lean`) read through
`Tm.eval`: `Tm.findOnSave`, `Tm.findOnSaveFrameRoot`, `Tm.findOnSaveIn`
(under a `select`); the frame below one root (`Storage.findOnSaveFrame`,
over `Path.Diverges`) waits for a term-level divergence test.
-/

namespace Solidity

open Semantics (lookupBy)

variable {C : Contract}

namespace Tm

variable {Γ : Ctx}

/-- `x[a]` on a ledger: an `int`, where the entry is one. -/
def netOfT (l : List (Int × Int)) (n : PrimTy.uint.Denote) : Option PrimTy.int.Denote :=
  PrimTy.int.ofInt? ((lookupBy n.1 l).getD 0)

/-- `eval` by `match`, its compiled form. -/
def evalM (σ : State C Γ) : {s : Srt} → Tm C Γ s → Option (s.Den C σ.H)
  | _, .pvV i => some (TEnv.get i σ.env)
  | _, .pvP i => TEnv.get i σ.env
  | _, .pvS i => some (TEnv.get i σ.env)
  | _, .pvI i => (TEnv.get i σ.env).map (·.id)
  | _, .netOf i a => (a.evalM σ).bind (netOfT (TEnv.get i σ.env))
  | _, .app0 o => o.eval σ.glob
  | _, .app1 o x => o.eval σ.glob (x.evalM σ)
  | _, .app2 o x y => o.eval σ.glob (x.evalM σ) (y.evalM σ)
  | _, .app3 o x y z => o.eval σ.glob (x.evalM σ) (y.evalM σ) (z.evalM σ)

/-- A term read on the typed state: a local by its position, a symbol on the
global part; `none` where it reverts. -/
@[implemented_by evalM]
def eval (σ : State C Γ) {s : Srt} (t : Tm C Γ s) : Option (s.Den C σ.H) :=
  @Tm.rec C Γ (fun s _ => Option (s.Den C σ.H))
    (fun {_} i => some (TEnv.get i σ.env))
    (fun {_} i => TEnv.get i σ.env)
    (fun i => some (TEnv.get i σ.env))
    (fun {_} i => (TEnv.get i σ.env).map (·.id))
    (fun i _ ia => ia.bind (netOfT (TEnv.get i σ.env)))
    (fun {_} o => o.eval σ.glob)
    (fun {_} {_} o _ ix => o.eval σ.glob ix)
    (fun {_} {_} {_} o _ _ ix iy => o.eval σ.glob ix iy)
    (fun {_} {_} {_} {_} o _ _ _ ix iy iz => o.eval σ.glob ix iy iz) s t

theorem eval_eq_evalM (σ : State C Γ) : {s : Srt} → (t : Tm C Γ s) → t.eval σ = t.evalM σ
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .app0 _ => rfl
  | _, .netOf i a => by
    show (a.eval σ).bind _ = (a.evalM σ).bind _
    rw [eval_eq_evalM σ a]
  | _, .app1 o x => by
    show o.eval σ.glob (x.eval σ) = o.eval σ.glob (x.evalM σ)
    rw [eval_eq_evalM σ x]
  | _, .app2 o x y => by
    show o.eval σ.glob (x.eval σ) (y.eval σ) = o.eval σ.glob (x.evalM σ) (y.evalM σ)
    rw [eval_eq_evalM σ x, eval_eq_evalM σ y]
  | _, .app3 o x y z => by
    show o.eval σ.glob (x.eval σ) (y.eval σ) (z.eval σ) =
      o.eval σ.glob (x.evalM σ) (y.evalM σ) (z.evalM σ)
    rw [eval_eq_evalM σ x, eval_eq_evalM σ y, eval_eq_evalM σ z]

theorem eval_app0 (σ : State C Γ) {s : Srt} (o : Op0 C s) :
    (Tm.app0 (Γ := Γ) o).eval σ = o.eval σ.glob := rfl
theorem eval_app1 (σ : State C Γ) {a s : Srt} (o : Op1 C a s) (x : Tm C Γ a) :
    (Tm.app1 o x).eval σ = o.eval σ.glob (x.eval σ) := rfl
theorem eval_app2 (σ : State C Γ) {a b s : Srt} (o : Op2 C a b s) (x : Tm C Γ a)
    (y : Tm C Γ b) : (Tm.app2 o x y).eval σ = o.eval σ.glob (x.eval σ) (y.eval σ) := rfl
theorem eval_app3 (σ : State C Γ) {a b c s : Srt} (o : Op3 C a b c s) (x : Tm C Γ a)
    (y : Tm C Γ b) (z : Tm C Γ c) :
    (Tm.app3 o x y z).eval σ = o.eval σ.glob (x.eval σ) (y.eval σ) (z.eval σ) := rfl

end Tm

/-! ## The laws on terms -/

namespace Tm

/-- **`findOnSave`** on terms: `find(save(s, p, sval(v)), p) = v` where the
write lands (solkey's `findOnSave`; `Storage.findOnSave`). -/
theorem findOnSave (σ : State C Γ) {p : PrimTy} (s : Tm C Γ .st)
    (q : Tm C Γ (.path (.prim p))) (v : Tm C Γ (.val p))
    (hd : (Tm.app3 .save s q (.app1 .sval v)).eval σ ≠ none) :
    (Tm.app2 .find (.app3 .save s q (.app1 .sval v)) q).eval σ = v.eval σ := by
  simp only [eval_app1, eval_app2, eval_app3, Op1.eval_eq_evalM, Op2.eval_eq_evalM,
    Op3.eval_eq_evalM, Op1.evalM, Op2.evalM, Op3.evalM, Option.bind_eq_bind] at hd ⊢
  cases hs : s.eval σ <;> cases hq : q.eval σ <;> cases hv : v.eval σ <;>
    simp only [hs, hq, hv, Option.bind_none, Option.bind_some, Option.map_some, Option.map_none,
      ne_eq, not_true_eq_false] at hd ⊢
  rename_i st r w
  cases hw : st.write r (.prim w) with
  | none => simp only [hw, not_true_eq_false] at hd
  | some st' =>
    simp only [Option.bind_some, Storage.findOnSave st r w hw]
    rfl

/-- **`findOnSaveFrame`** across roots on terms: a write leaves a read at
another state variable (solkey's `findOnSaveDifferent`;
`Storage.findOnSaveFrameRoot`). -/
theorem findOnSaveFrameRoot (σ : State C Γ) {T U : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path T))
    (v : Tm C Γ (.sv T)) (q' : Tm C Γ (.path U))
    (hne : ∀ r r', q.eval σ = some r → q'.eval σ = some r' → r.root ≠ r'.root)
    (hd : (Tm.app3 .save s q v).eval σ ≠ none) :
    (Tm.app2 .sfind (.app3 .save s q v) q').eval σ = (Tm.app2 .sfind s q').eval σ := by
  simp only [eval_app2, eval_app3, Op2.eval_eq_evalM, Op3.eval_eq_evalM, Op2.evalM,
    Op3.evalM, Option.bind_eq_bind] at hd ⊢
  cases hs : s.eval σ <;> cases hq : q.eval σ <;> cases hv : v.eval σ <;>
    simp only [hs, hq, hv, Option.bind_none, Option.bind_some, ne_eq, not_true_eq_false] at hd ⊢
  rename_i st r w
  cases hw : st.write r w with
  | none => simp only [hw, not_true_eq_false] at hd
  | some st' =>
    cases hq' : q'.eval σ with
    | none => simp only [Option.bind_some, Option.bind_none]
    | some r' =>
      simp only [Option.bind_some,
        Storage.findOnSaveFrameRoot st r r' (hne r r' hq hq') w hw]

/-- **`findOnSave`** under a `select`: `find(save(select(s, r), p, sval(v)), p) = v`
where the write lands (`Storage.findOnSave` over `Contract.ofStruct`). -/
theorem findOnSaveIn (σ : State C Γ) {sn : Name} {p : PrimTy} (s : Tm C Γ (.sts sn))
    (q : Tm C Γ (.spath sn (.prim p))) (v : Tm C Γ (.val p))
    (hd : (Tm.app3 .saveIn s q (.app1 .sval v)).eval σ ≠ none) :
    (Tm.app2 .findIn (.app3 .saveIn s q (.app1 .sval v)) q).eval σ = v.eval σ := by
  simp only [eval_app1, eval_app2, eval_app3, Op1.eval_eq_evalM, Op2.eval_eq_evalM,
    Op3.eval_eq_evalM, Op1.evalM, Op2.evalM, Op3.evalM, Option.bind_eq_bind] at hd ⊢
  cases hs : s.eval σ <;> cases hq : q.eval σ <;> cases hv : v.eval σ <;>
    simp only [hs, hq, hv, Option.bind_none, Option.bind_some, Option.map_some, Option.map_none,
      ne_eq, not_true_eq_false] at hd ⊢
  rename_i st r w
  cases hw : st.write r (.prim w) with
  | none => simp only [hw, not_true_eq_false] at hd
  | some st' =>
    simp only [Option.bind_some, Storage.findOnSave st r w hw]
    rfl

end Tm

/-! ## A literal

`find(save(storage, alice.age, sval(1)), alice.age)` over `StandardExample`,
written by hand. -/

/-- `alice.age`. -/
def Tm.aliceAge : Tm StandardExample [] (.path (.prim .uint)) :=
  .app1 (.field (s := "Person") (f := "age") rfl) (.app0 (.root "alice" rfl))

/-- `find(save(storage, alice.age, sval(1)), alice.age)`. -/
def Tm.aliceAgeRead : Tm StandardExample [] (.val .uint) :=
  .app2 .find (.app3 .save (.app0 .storage) Tm.aliceAge (.app1 .sval (.app0 (.lit ⟨1, rfl⟩))))
    Tm.aliceAge

/-- It reads `1` in the initial state, by the kernel. -/
example : (Tm.aliceAgeRead.eval (State.init StandardExample)).map (·.1) = some 1 := by
  decide +kernel

/-- `find(select(save(storage, alice.age, sval(1)), alice), age)`, the chain
line `selectOnSaveMember` rewrites, at its typed sorts (`sts`, `spath`). -/
def Tm.aliceSelectRead : Tm StandardExample [] (.val .uint) :=
  .app2 .findIn
    (.app1 (.select (s := "Person") "alice" rfl)
      (.app3 .save (.app0 .storage) Tm.aliceAge (.app1 .sval (.app0 (.lit ⟨1, rfl⟩)))))
    (.app0 (.member "Person" "age" rfl))

/-- It reads `1` too, by the kernel. -/
example : (Tm.aliceSelectRead.eval (State.init StandardExample)).map (·.1) = some 1 := by
  decide +kernel

end Solidity
