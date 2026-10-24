import Solidity.Evm.MemoryStatements

/-!
# Compound writes and bumps through memory references

Compound operands and address reads are pure and can only revert. Their
failure order therefore agrees with an ordinary memory write of the checked
binary result. This supplies a source equality for reusing the existing value
and write compiler certificates, without adding an unchecked target operation. Standalone prefix/postfix bumps
reuse the same certificates after discarding their expression result.
-/

namespace Solidity.Evm.Memory

variable {C : Contract} {Γ : Ctx}

private theorem compound_accepts {op : BinOp} (hop : op.hasCompoundAssign = true)
    {p : PrimTy} (hp : p.isNumeric = true) : op.accepts p = true := by
  cases op <;> first | exact absurd hop (by decide) | exact hp

private theorem compound_ret {op : BinOp} (hop : op.hasCompoundAssign = true)
    (p : PrimTy) : op.ret p = p := by
  cases op <;> first | exact absurd hop (by decide) | rfl

/-- A numeric compound operator in the existing value language. -/
def compoundValue {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (x y : Val C Γ p) : Val C Γ p :=
  .binop op (compound_accepts hop hp) (compound_ret hop p) x y

theorem compoundValue_eval {p : PrimTy} (σ : State C Γ) (op : BinOp)
    (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true) (x y : Val C Γ p) :
    (compoundValue op hop hp x y).evalT σ = (do
      let a ← x.evalT σ
      let b ← y.evalT σ
      TRes.ofOpt (compoundT op p (PrimTy.key a) (PrimTy.key b))) := by
  simp only [compoundValue, Val.evalT]
  cases op <;> simp only [BinOp.hasCompoundAssign, Bool.false_eq_true] at hop <;>
    cases p <;> simp only [PrimTy.isNumeric, Bool.false_eq_true] at hp <;>
    cases x.evalT σ <;> cases y.evalT σ <;> rfl

/-- Reordering pure reads preserves every success and the sole evaluator failure. -/
theorem compoundMemT_eq_assign {p : PrimTy} (σ : State C Γ) (op : BinOp)
    (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
    (l : MLoc C Γ (.prim p)) (r : Val C Γ p) :
    (do
      let v ← r.evalT σ
      let a ← l.addrT σ
      opMemT σ op a v) =
    TRun.assignMem l (.val (compoundValue op hop hp (.readMem l) r)) σ := by
  simp only [TRun.assignMem, MSrc.mvalT, compoundValue_eval, Val.evalT]
  cases ha : l.addrT σ with
  | error e =>
    obtain rfl := (MLoc.addrT_revertOnly σ l).error ha
    cases hr : r.evalT σ with
    | error e =>
      obtain rfl := (Val.evalT_revertOnly σ r).error hr
      rfl
    | ok v => rfl
  | ok a =>
    cases ho : σ.heap.readAddr a with
    | none =>
      cases hr : r.evalT σ with
      | error e =>
        obtain rfl := (Val.evalT_revertOnly σ r).error hr
        simp only [ho, TRes.ofOpt, bind, Except.bind]
      | ok v => simp only [ho, opMemT, TRes.ofOpt, bind, Except.bind]
    | some old =>
      cases hr : r.evalT σ with
      | error e => simp only [ho, TRes.ofOpt, bind, Except.bind]
      | ok v =>
        cases hc : compoundT op p (PrimTy.key old) (PrimTy.key v) <;>
          simp only [ho, hc, opMemT, TRes.ofOpt, bind, Except.bind]

/-- A scoped memory compound assignment is the corresponding checked binary write. -/
theorem compoundAssign_eq_write {p : PrimTy} {R : RefTy} (σ : State C Γ) (op : BinOp)
    (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
    (a : ArrTy R (.prim p)) (src : MPath C Γ (.ref R)) (i : Simple C Γ .uint)
    (r : Val C Γ p) :
    TRun.opAssign op (.mindex a src i) r σ =
      TRun.assignMem (.index a src (.simple i))
        (.val (compoundValue op hop hp (.readMem (.index a src (.simple i))) r)) σ :=
  compoundMemT_eq_assign σ op hop hp (.index a src (.simple i)) r

/-- A scoped field compound assignment uses the corresponding checked binary write. -/
theorem compoundField_eq_write {p : PrimTy} {s f : Name} (σ : State C Γ) (op : BinOp)
    (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
    (src : MPath C Γ (.struct s)) (hf : C.fieldType s f = some (.prim p)) (r : Val C Γ p) :
    TRun.opAssign op (.mfield src f hf) r σ =
      TRun.assignMem (.field src f hf)
        (.val (compoundValue op hop hp (.readMem (.field src f hf)) r)) σ :=
  compoundMemT_eq_assign σ op hop hp (.field src f hf) r

/-- A primitive local can also consume a compound RHS containing memory reads. -/
theorem compoundLocal_eq_assign {p : PrimTy} (σ : State C Γ) (op : BinOp)
    (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
    (dst : Idx Γ (.val p)) (r : Val C Γ p) :
    TRun.opAssign op (.local dst) r σ =
      TRun.assignLocal dst (compoundValue op hop hp (.simple (.local dst)) r) σ := by
  simp only [TRun.assignLocal, compoundValue_eval, Val.evalT, Simple.evalT,
    TRun.opAssign, OpLoc.storeT]
  cases r.evalT σ <;> rfl

/-- The typed unit used by checked increments and decrements. -/
def incrementOne {p : PrimTy} (hp : p.isNumeric = true) : Val C Γ p :=
  .simple (.lit 1 (by cases p <;> first | rfl | cases hp))

/-- Both bump directions have an existing compound-assignment certificate. -/
theorem increment_compound (op : IncDec) : op.binOp.hasCompoundAssign = true := by
  cases op <;> rfl

/-- Range checking is identical to checked addition or subtraction by one. -/
theorem bumpT_compound (op : IncDec) (p : PrimTy) (v : Int) :
    bumpT op p v = compoundT op.binOp p v 1 := by
  cases op <;> rfl

/-- A standalone memory bump discards its expression result and keeps the checked write. -/
theorem incrementMemory_eq_compound {p : PrimTy} {R : RefTy} (σ : State C Γ)
    (op : IncDec) (hp : p.isNumeric = true) (a : ArrTy R (.prim p))
    (src : MPath C Γ (.ref R)) (i : Simple C Γ .uint) :
    TRun.incDec op (.mindex a src i) σ =
      TRun.opAssign op.binOp (.mindex a src i) (incrementOne hp) σ := by
  simp only [TRun.incDec, TRun.opAssign, OpLoc.bumpT, OpLoc.storeT, incrementOne,
    Val.evalT, Simple.evalT]
  cases ha : MLoc.addrT σ (MLoc.index a src (.simple i)) with
  | error _ => rfl
  | ok addr =>
    simp only [bind, Except.bind, bumpMemT, opMemT, bumpT_compound]
    have oneKey (h : p.inRange 1 = true) : PrimTy.key (p.ofLit 1 h) = 1 := by
      cases p <;> first | rfl | cases hp
    rw [oneKey]
    cases σ.heap.readAddr addr with
    | none => rfl
    | some old =>
      simp only [TRes.ofOpt]
      cases hc : compoundT op.binOp p (PrimTy.key old) 1 with
      | none => rfl
      | some new =>
        simp only
        cases σ.heap.writeAddr addr new <;> rfl

/-- A field bump uses the same checked operation as its compound write. -/
theorem incrementField_eq_compound {p : PrimTy} {s f : Name} (σ : State C Γ)
    (op : IncDec) (hp : p.isNumeric = true) (src : MPath C Γ (.struct s))
    (hf : C.fieldType s f = some (.prim p)) :
    TRun.incDec op (.mfield src f hf) σ =
      TRun.opAssign op.binOp (.mfield src f hf) (incrementOne hp) σ := by
  simp only [TRun.incDec, TRun.opAssign, OpLoc.bumpT, OpLoc.storeT, incrementOne,
    Val.evalT, Simple.evalT]
  cases ha : MLoc.addrT σ (MLoc.field src f hf) with
  | error _ => rfl
  | ok addr =>
    simp only [bind, Except.bind, bumpMemT, opMemT, bumpT_compound]
    have oneKey (h : p.inRange 1 = true) : PrimTy.key (p.ofLit 1 h) = 1 := by
      cases p <;> first | rfl | cases hp
    rw [oneKey]
    cases σ.heap.readAddr addr with
    | none => rfl
    | some old =>
      simp only [TRes.ofOpt]
      cases hc : compoundT op.binOp p (PrimTy.key old) 1 with
      | none => rfl
      | some new =>
        simp only
        cases σ.heap.writeAddr addr new <;> rfl

/-- A standalone local bump has the same complete result as its compound update. -/
theorem incrementLocal_eq_compound {p : PrimTy} (σ : State C Γ) (op : IncDec)
    (hp : p.isNumeric = true) (dst : Idx Γ (.val p)) :
    TRun.incDec op (.local dst) σ =
      TRun.opAssign op.binOp (.local dst) (incrementOne hp) σ := by
  simp only [TRun.incDec, TRun.opAssign, OpLoc.bumpT, OpLoc.storeT, incrementOne,
    Val.evalT, Simple.evalT, bumpT_compound, bind, Except.bind]
  have oneKey (h : p.inRange 1 = true) : PrimTy.key (p.ofLit 1 h) = 1 := by
    cases p <;> first | rfl | cases hp
  rw [oneKey]
  cases compoundT op.binOp p (PrimTy.key (TEnv.get dst σ.env)) 1 <;> rfl

end Solidity.Evm.Memory
