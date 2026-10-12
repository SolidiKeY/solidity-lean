import Solidity.Calculus.Lands
import Solidity.Signature

/-!
# Terms over the typed signature

`TmT C Γ s`: the scoped terms of `Calculus/Fml.lean` at the typed sorts of
`Signature.lean`, a local at its position, a symbol applied to terms of its
argument sorts (`docs/intrinsic.md`, W9.8.1).  `RhsT`, `UpdElemT` and `UpdT`
are `Rhs`, `UpdElem` and `Upd` over them.  Nothing reads them yet: they sit
beside the untyped terms, and `TmT.erase` (`RhsT.erase`, `UpdT.erase`) is the
bridge the later waves switch over (W9.8.2: the lowering and `Lands` on
`TmT`).

`TmT.eval` reads a term on the typed state, a local by `TEnv.get`, a symbol
by `OpTn.eval` on the global part (`State.glob`); no value is erased.
`TmT.eval_agree` is the bridge: the erased term's `Tm.eval` agrees with it
(`SrtT.Agree`) where the term is exact (`TmT.Exact`: each symbol's
`OpTn.Exact`, and `x[a]`'s entry an `int`).

The laws on terms are `Storage`'s (`Signature.lean`) read through `TmT.eval`:
`TmT.findOnSave`, `TmT.findOnSaveFrameRoot`, `TmT.findOnSaveIn` (under a
`select`); the frame below one root
(`Storage.findOnSaveFrame`, over `Path.Diverges`) waits for a term-level
divergence test (W9.8.4).
-/

namespace Solidity

open Semantics (lookupBy)

variable {C : Contract}

/-- No typed symbol is a named one (`Op1.netOf`): a term applies it bare. -/
theorem OpT1.erase_named {a s : SrtT} (o : OpT1 C a s) : o.erase.named = false := by
  cases o <;> rfl

/-- Terms at the typed sorts. -/
inductive TmT (C : Contract) (Γ : Ctx) : SrtT → Type where
  /-- A stack local. -/
  | pvV {p : PrimTy} (i : Idx Γ (.val p)) : TmT C Γ (.val p)
  /-- A storage alias. -/
  | pvP {R : RefTy} (i : Idx Γ (.alias R)) : TmT C Γ (.path (.ref R))
  /-- A storage variable, KeY's `old`. -/
  | pvS (i : Idx Γ .old) : TmT C Γ .st
  /-- A memory local. -/
  | pvI {R : RefTy} (i : Idx Γ (.mem R)) : TmT C Γ (.ident R)
  /-- `x[a]`: what the ledger bound at `x` holds for `a`, an `int`. -/
  | netOf (i : Idx Γ .oldNet) (a : TmT C Γ (.val .uint)) : TmT C Γ (.val .int)
  | app0 {s : SrtT} (o : OpT0 C s) : TmT C Γ s
  | app1 {a s : SrtT} (o : OpT1 C a s) (x : TmT C Γ a) : TmT C Γ s
  | app2 {a b s : SrtT} (o : OpT2 C a b s) (x : TmT C Γ a) (y : TmT C Γ b) : TmT C Γ s
  | app3 {a b c s : SrtT} (o : OpT3 C a b c s) (x : TmT C Γ a) (y : TmT C Γ b)
      (z : TmT C Γ c) : TmT C Γ s

namespace TmT

variable {Γ : Ctx}

/-- The untyped term. -/
def erase : {s : SrtT} → TmT C Γ s → Tm C Γ s.erase
  | _, .pvV i => .pvV i
  | _, .pvP i => .pvP i
  | _, .pvS i => .pvS i
  | _, .pvI i => .pvI i
  | _, .netOf i a => .netOf i a.erase
  | _, .app0 o => .app0 o.erase
  | _, .app1 o x => .app1 o.erase (OpT1.erase_named o) x.erase
  | _, .app2 o x y => .app2 o.erase x.erase y.erase
  | _, .app3 o x y z => .app3 o.erase x.erase y.erase z.erase

/-- `x[a]` on a ledger: an `int`, where the entry is one. -/
def netOfT (l : List (Int × Int)) (n : PrimTy.uint.Denote) : Option PrimTy.int.Denote :=
  PrimTy.int.ofInt? ((lookupBy n.1 l).getD 0)

/-- `eval` by `match`, its compiled form. -/
def evalM (σ : State C Γ) : {s : SrtT} → TmT C Γ s → Option (s.Den C σ.H)
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
def eval (σ : State C Γ) {s : SrtT} (t : TmT C Γ s) : Option (s.Den C σ.H) :=
  @TmT.rec C Γ (fun s _ => Option (s.Den C σ.H))
    (fun {_} i => some (TEnv.get i σ.env))
    (fun {_} i => TEnv.get i σ.env)
    (fun i => some (TEnv.get i σ.env))
    (fun {_} i => (TEnv.get i σ.env).map (·.id))
    (fun i _ ia => ia.bind (netOfT (TEnv.get i σ.env)))
    (fun {_} o => o.eval σ.glob)
    (fun {_} {_} o _ ix => o.eval σ.glob ix)
    (fun {_} {_} {_} o _ _ ix iy => o.eval σ.glob ix iy)
    (fun {_} {_} {_} {_} o _ _ _ ix iy iz => o.eval σ.glob ix iy iz) s t

theorem eval_eq_evalM (σ : State C Γ) : {s : SrtT} → (t : TmT C Γ s) → t.eval σ = t.evalM σ
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

theorem eval_app0 (σ : State C Γ) {s : SrtT} (o : OpT0 C s) :
    (TmT.app0 (Γ := Γ) o).eval σ = o.eval σ.glob := rfl
theorem eval_app1 (σ : State C Γ) {a s : SrtT} (o : OpT1 C a s) (x : TmT C Γ a) :
    (TmT.app1 o x).eval σ = o.eval σ.glob (x.eval σ) := rfl
theorem eval_app2 (σ : State C Γ) {a b s : SrtT} (o : OpT2 C a b s) (x : TmT C Γ a)
    (y : TmT C Γ b) : (TmT.app2 o x y).eval σ = o.eval σ.glob (x.eval σ) (y.eval σ) := rfl
theorem eval_app3 (σ : State C Γ) {a b c s : SrtT} (o : OpT3 C a b c s) (x : TmT C Γ a)
    (y : TmT C Γ b) (z : TmT C Γ c) :
    (TmT.app3 o x y z).eval σ = o.eval σ.glob (x.eval σ) (y.eval σ) (z.eval σ) := rfl

/-- Where the term is exact: every symbol where its `OpTn.Exact` holds, every
`x[a]` an `int`. -/
def Exact (σ : State C Γ) : {s : SrtT} → TmT C Γ s → Prop
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .app0 _ => True
  | _, .netOf i a => a.Exact σ ∧
      ∀ n, a.eval σ = some n →
        PrimTy.int.inRange ((lookupBy n.1 (TEnv.get i σ.env : List (Int × Int))).getD 0) = true
  | _, .app1 o x => x.Exact σ ∧ ∀ u, x.eval σ = some u → o.Exact σ.glob u
  | _, .app2 o x y => x.Exact σ ∧ y.Exact σ ∧
      ∀ u v, x.eval σ = some u → y.eval σ = some v → o.Exact σ.glob u v
  | _, .app3 o x y z => x.Exact σ ∧ y.Exact σ ∧ z.Exact σ ∧
      ∀ u v w, x.eval σ = some u → y.eval σ = some v → z.eval σ = some w →
        o.Exact σ.glob u v w

/-- **The term bridge**: the erased term's `Tm.eval` agrees with `TmT.eval`
where the term is exact. -/
theorem eval_agree (σ : State C Γ) : {s : SrtT} → (t : TmT C Γ s) → t.Exact σ →
    SrtT.Agree σ.glob s (t.eval σ) (t.erase.eval σ)
  | _, .pvV _, _ => rfl
  | _, .pvP i, _ => by
    show SrtT.Agree σ.glob (.path (.ref _)) (TEnv.get i σ.env) (σ.aliasPathT i)
    unfold State.aliasPathT
    cases TEnv.get i σ.env
    · exact ⟨.revert, rfl⟩
    · rfl
  | _, .pvS _, _ => rfl
  | _, .pvI i, _ => by
    show SrtT.Agree σ.glob (.ident _) ((TEnv.get i σ.env).map (·.id)) (σ.memRefT i)
    unfold State.memRefT
    cases TEnv.get i σ.env
    · exact ⟨.revert, rfl⟩
    · rfl
  | _, .netOf i a, h => by
    simp only [Exact] at h
    obtain ⟨ha, he⟩ := h
    have ih := eval_agree σ a ha
    show SrtT.Agree σ.glob (.val .int) ((a.eval σ).bind _) (Tm.eval σ (.netOf i a.erase))
    simp only [Tm.eval]
    revert he ih
    cases a.eval σ with
    | none =>
      intro _ ih
      obtain ⟨h, hr⟩ := ih
      simp only [hr, bind, Except.bind]
      exact ⟨h, rfl⟩
    | some n =>
      intro he ih
      have hn := he n rfl
      change a.erase.eval σ = Except.ok (PrimTy.erase n) at ih
      simp only [ih, bind, Except.bind, Option.bind_some, netOfT, PrimTy.ofInt?,
        PrimTy.ofValue?, dif_pos hn]
      rfl
  | _, .app0 o, _ => OpT0.eval_agree σ.glob o
  | _, .app1 o x, h => by
    simp only [Exact] at h
    exact OpT1.eval_agree σ.glob o (eval_agree σ x h.1) fun u hu => h.2 u hu
  | _, .app2 o x y, h => by
    simp only [Exact] at h
    exact OpT2.eval_agree σ.glob o (eval_agree σ x h.1) (eval_agree σ y h.2.1)
      fun u v hu hv => h.2.2 u v hu hv
  | _, .app3 o x y z, h => by
    simp only [Exact] at h
    exact OpT3.eval_agree σ.glob o (eval_agree σ x h.1) (eval_agree σ y h.2.1)
      (eval_agree σ z h.2.2.1) fun u v w hu hv hw => h.2.2.2 u v w hu hv hw

end TmT

/-! ## Updates over typed terms -/

/-- What a local of type `t` is set to (`Rhs`), its terms typed. -/
inductive RhsT (C : Contract) (Γ : Ctx) : LTy → Type where
  | val {p : PrimTy} (t : TmT C Γ (.val p)) : RhsT C Γ (.val p)
  | path {R : RefTy} (p : TmT C Γ (.path (.ref R))) : RhsT C Γ (.alias R)
  | unset {R : RefTy} : RhsT C Γ (.alias R)
  | mref {R : RefTy} (i : TmT C Γ (.ident R)) : RhsT C Γ (.mem R)
  | store (s : TmT C Γ .st) : RhsT C Γ .old
  | saveNet : RhsT C Γ .oldNet
  | saveNetMt : RhsT C Γ .oldNet

/-- One assigning element (`UpdElem`), its terms typed: an amount and an
address a `uint`. -/
inductive UpdElemT (C : Contract) (Γ Δ : Ctx) where
  | local {t : LTy} (i : Idx Δ t) (r : RhsT C Γ t)
  | storage (s : TmT C Γ .st)
  | memory (m : TmT C Γ .mem)
  | selfBalance (op : IntOp) (a : TmT C Γ (.val .uint))
  | net (r : TmT C Γ (.val .uint)) (op : IntOp) (a : TmT C Γ (.val .uint))
  | pay (r a : TmT C Γ (.val .uint))
  | netMt (r a : TmT C Γ (.val .uint))
  | setBalance (a : TmT C Γ (.val .uint))

/-- A parallel update (`Upd`), its terms typed. -/
inductive UpdT (C : Contract) (Γ : Ctx) : Ctx → Type where
  | nil : UpdT C Γ Γ
  | snoc {Δ : Ctx} (U : UpdT C Γ Δ) (e : UpdElemT C Γ Δ) : UpdT C Γ Δ
  | decl {Δ : Ctx} {t : LTy} (U : UpdT C Γ Δ) (x : Var) (r : RhsT C Γ t) : UpdT C Γ (t :: Δ)
  | pop {Δ Δ' : Ctx} (U : UpdT C Γ Δ) (h : Ext Δ' Δ) : UpdT C Γ Δ'
  | drop {Δ Δ' : Ctx} (U : UpdT C Γ Δ) (h : Thin Δ' Δ) : UpdT C Γ Δ'

variable {Γ : Ctx}

/-- The untyped right-hand side. -/
def RhsT.erase : {t : LTy} → RhsT C Γ t → Rhs C Γ t
  | _, .val t => .val t.erase
  | _, .path p => .path p.erase
  | _, .unset => .unset
  | _, .mref i => .mref i.erase
  | _, .store s => .store s.erase
  | _, .saveNet => .saveNet
  | _, .saveNetMt => .saveNetMt

/-- The untyped element. -/
def UpdElemT.erase {Δ : Ctx} : UpdElemT C Γ Δ → UpdElem C Γ Δ
  | .local i r => .local i r.erase
  | .storage s => .storage s.erase
  | .memory m => .memory m.erase
  | .selfBalance op a => .selfBalance op a.erase
  | .net r op a => .net r.erase op a.erase
  | .pay r a => .pay r.erase a.erase
  | .netMt r a => .netMt r.erase a.erase
  | .setBalance a => .setBalance a.erase

/-- The untyped update. -/
def UpdT.erase : {Δ : Ctx} → UpdT C Γ Δ → Upd C Γ Δ
  | _, .nil => .nil
  | _, .snoc U e => .snoc U.erase e.erase
  | _, .decl U x r => .decl U.erase x r.erase
  | _, .pop U h => .pop U.erase h
  | _, .drop U h => .drop U.erase h

/-! ## The laws on terms -/

namespace TmT

/-- **`findOnSave`** on terms: `find(save(s, p, sval(v)), p) = v` where the
write lands (solkey's `findOnSave`; `Storage.findOnSave`). -/
theorem findOnSave (σ : State C Γ) {p : PrimTy} (s : TmT C Γ .st)
    (q : TmT C Γ (.path (.prim p))) (v : TmT C Γ (.val p))
    (hd : (TmT.app3 .save s q (.app1 .sval v)).eval σ ≠ none) :
    (TmT.app2 .find (.app3 .save s q (.app1 .sval v)) q).eval σ = v.eval σ := by
  simp only [eval_app1, eval_app2, eval_app3, OpT1.eval_eq_evalM, OpT2.eval_eq_evalM,
    OpT3.eval_eq_evalM, OpT1.evalM, OpT2.evalM, OpT3.evalM, Option.bind_eq_bind] at hd ⊢
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
theorem findOnSaveFrameRoot (σ : State C Γ) {T U : Ty} (s : TmT C Γ .st) (q : TmT C Γ (.path T))
    (v : TmT C Γ (.sv T)) (q' : TmT C Γ (.path U))
    (hne : ∀ r r', q.eval σ = some r → q'.eval σ = some r' → r.root ≠ r'.root)
    (hd : (TmT.app3 .save s q v).eval σ ≠ none) :
    (TmT.app2 .sfind (.app3 .save s q v) q').eval σ = (TmT.app2 .sfind s q').eval σ := by
  simp only [eval_app2, eval_app3, OpT2.eval_eq_evalM, OpT3.eval_eq_evalM, OpT2.evalM,
    OpT3.evalM, Option.bind_eq_bind] at hd ⊢
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
theorem findOnSaveIn (σ : State C Γ) {sn : Name} {p : PrimTy} (s : TmT C Γ (.sts sn))
    (q : TmT C Γ (.spath sn (.prim p))) (v : TmT C Γ (.val p))
    (hd : (TmT.app3 .saveIn s q (.app1 .sval v)).eval σ ≠ none) :
    (TmT.app2 .findIn (.app3 .saveIn s q (.app1 .sval v)) q).eval σ = v.eval σ := by
  simp only [eval_app1, eval_app2, eval_app3, OpT1.eval_eq_evalM, OpT2.eval_eq_evalM,
    OpT3.eval_eq_evalM, OpT1.evalM, OpT2.evalM, OpT3.evalM, Option.bind_eq_bind] at hd ⊢
  cases hs : s.eval σ <;> cases hq : q.eval σ <;> cases hv : v.eval σ <;>
    simp only [hs, hq, hv, Option.bind_none, Option.bind_some, Option.map_some, Option.map_none,
      ne_eq, not_true_eq_false] at hd ⊢
  rename_i st r w
  cases hw : st.write r (.prim w) with
  | none => simp only [hw, not_true_eq_false] at hd
  | some st' =>
    simp only [Option.bind_some, Storage.findOnSave st r w hw]
    rfl

end TmT

/-! ## A literal

`find(save(storage, alice.age, sval(1)), alice.age)` over `StandardExample`,
written by hand (no notation reads to `TmT` yet). -/

/-- `alice.age`. -/
def TmT.aliceAge : TmT StandardExample [] (.path (.prim .uint)) :=
  .app1 (.field (s := "Person") (f := "age") rfl) (.app0 (.root "alice" rfl))

/-- `find(save(storage, alice.age, sval(1)), alice.age)`. -/
def TmT.aliceAgeRead : TmT StandardExample [] (.val .uint) :=
  .app2 .find (.app3 .save (.app0 .storage) TmT.aliceAge (.app1 .sval (.app0 (.lit ⟨1, rfl⟩))))
    TmT.aliceAge

/-- It reads `1` in the initial state, by the kernel. -/
example : (TmT.aliceAgeRead.eval (State.init StandardExample)).map (·.1) = some 1 := by
  decide +kernel

/-- `find(select(save(storage, alice.age, sval(1)), alice), age)`, the chain
line `selectOnSaveMember` rewrites, at its typed sorts (`sts`, `spath`). -/
def TmT.aliceSelectRead : TmT StandardExample [] (.val .uint) :=
  .app2 .findIn
    (.app1 (.select (s := "Person") "alice" rfl)
      (.app3 .save (.app0 .storage) TmT.aliceAge (.app1 .sval (.app0 (.lit ⟨1, rfl⟩)))))
    (.app0 (.member "Person" "age" rfl))

/-- It reads `1` too, by the kernel. -/
example : (TmT.aliceSelectRead.eval (State.init StandardExample)).map (·.1) = some 1 := by
  decide +kernel

end Solidity
