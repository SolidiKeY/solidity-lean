import Solidity.Calculus.Rules

/-!
# The soundness kit

What the per-taclet soundness proofs are made of (`SoundUpdate.lean`,
`SoundUnfold.lean`, `RuleSoundness.lean`): `SameOk`, the agreement an
unfolding rule owes (two runs end alike off the fresh names, or both halt);
`Premise.Correct`, what a premise means for the statement it replaces; and
the lemmas and tactics that put an update and a statement, or a premise's
statements and the original, into the same shape.  Most of them name a read
both sides share (`envVal`, `envRef`) or move a fresh binding outward, so
that `res_split` can split both runs on the same atoms.
-/

namespace Solidity

open Semantics SemanticsProperties

variable {C : Contract}

/-! ## Two runs that end alike -/

/-- The fresh names a rule may declare at index `k`: `se`, `sp`, `ie`, `mv`. -/
def freshVars (k : Nat) : List Var :=
  [.fresh "se" k, .fresh "sp" k, .fresh "ie" k, .fresh "mv" k]

def SameOk (ns : List Var) : Res State → Res State → Prop
  | .ok a, .ok b => EnvAgreeExcept ns a b
  | .error _, .error _ => True
  | _, _ => False

theorem SameOk.of_agree {ns : List Var} {x y : Res State} (h : ResultsAgree ns x y) :
    SameOk ns x y := by
  cases x <;> cases y <;> simp_all [SameOk, ResultsAgree]

theorem Semantics.EnvAgreeExcept.setEnv_left {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) {n : Var} (hn : n ∈ ns) (b : Binding) :
    EnvAgreeExcept ns (s₁.setEnv n b) s₂ :=
  ⟨h.storage, h.heap, h.nextId, h.net, fun m hm => by
    have hne : m ≠ n := fun heq => hm (heq ▸ hn)
    simpa [State.setEnv, lookupBy_setBy_ne hne] using h.env m hm,
    h.selfBalance, h.tx⟩

theorem agree_setEnv (σ : State) (x : Var) (b : Binding) :
    EnvAgreeExcept [x] (σ.setEnv x b) σ :=
  (EnvAgreeExcept.refl [x] σ).setEnv_left (by simp) b

theorem avoids_single {x : Var} {vs : List Var} (h : x ∉ vs) : Avoids vs [x] :=
  fun y hy hm => h (by simp at hm; exact hm ▸ hy)

section
variable {σ : State} {x : Var} {b : Binding}

@[simp] theorem Simple.eval_setEnv {p : PrimTy} {s : Simple C p} (h : x ∉ s.vars) :
    s.eval (σ.setEnv x b) = s.eval σ := s.eval_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem Val.eval_setEnv {p : PrimTy} {v : Val C p} (h : x ∉ v.vars) :
    v.eval (σ.setEnv x b) = v.eval σ := v.eval_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem SPath.resolve_setEnv {T : Ty} {p : SPath C T} (h : x ∉ p.vars) :
    p.resolve (σ.setEnv x b) = p.resolve σ := p.resolve_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem Loc.resolve_setEnv {T : Ty} {l : Loc C T} (h : x ∉ l.vars) :
    l.resolve (σ.setEnv x b) = l.resolve σ := l.resolve_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem MPath.mval_setEnv {T : Ty} {p : MPath C T} (h : x ∉ p.vars) :
    p.mval (σ.setEnv x b) = p.mval σ := p.mval_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem MLoc.read_setEnv {T : Ty} {l : MLoc C T} (h : x ∉ l.vars) :
    l.read (σ.setEnv x b) = l.read σ := l.read_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem Src.value_setEnv {T : Ty} {r : Src C T} (h : x ∉ r.vars) :
    r.value (σ.setEnv x b) = r.value σ := r.value_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem MSrc.mval_setEnv {T : Ty} {r : MSrc C T} (h : x ∉ r.vars) :
    r.mval (σ.setEnv x b) = r.mval σ := r.mval_frame (agree_setEnv σ x b) (avoids_single h)
@[simp] theorem State.findStorage_setEnv (r : Name) (segs : List Seg) :
    (σ.setEnv x b).findStorage r segs = σ.findStorage r segs := rfl
@[simp] theorem State.checkIndex_setEnv (r : Name) (segs : List Seg) (i : Int) :
    (σ.setEnv x b).checkIndex r segs i = σ.checkIndex r segs i := rfl
@[simp] theorem State.getObj_setEnv (id : Nat) : (σ.setEnv x b).getObj id = σ.getObj id := rfl
@[simp] theorem arrayLen_setEnv (r : Name) (segs : List Seg) :
    arrayLen (σ.setEnv x b) r segs = arrayLen σ r segs := rfl
@[simp] theorem memArrayLen_setEnv (id : Nat) : memArrayLen (σ.setEnv x b) id = memArrayLen σ id := rfl
@[simp] theorem MLoc.addr_setEnv {T : Ty} {l : MLoc C T} (h : x ∉ l.vars) :
    l.addr (σ.setEnv x b) = l.addr σ := l.addr_frame (agree_setEnv σ x b) (avoids_single h)
end

/-- What a premise means for the statement it replaces. -/
def Premise.Correct (k : Nat) (m : Modality) (s : Stmt C) : Premise C → Prop
  | .update U => ∀ σ, SameOk [] (U.apply σ) (s.run σ)
  | .unfold P => ∀ σ, SameOk (freshVars k) (Prog.run σ P) (s.run σ)
  | .split c c' P Q => ∀ σ,
      (holds σ c → SameOk (freshVars k) (Prog.run σ P) (s.run σ)) ∧
      (holds σ c' → SameOk (freshVars k) (Prog.run σ Q) (s.run σ)) ∧
      (¬ holds σ c → ¬ holds σ c' → ∃ e, s.run σ = .error e)
  | .done b => b = true → m = .box ∧ ∀ σ, ∃ e, s.run σ = .error e
  | .branches bs => ∀ σ, (m = .box ∧ ∃ e, s.run σ = .error e) ∨
      ∃ b ∈ bs, ∃ σ', Binds b.1 σ σ' ∧ Prog.run σ' b.2 = s.run σ

/-! ### Writes as a new storage or heap, the rest of the state kept -/

/-- The storage a successful `writeStorage` leaves: a word saved, or a copy
over what is there. -/
def Semantics.State.writeRes (σ : State) (r : Name) (segs : List Seg) (x : SVal) :
    Res (List (Name × SVal)) :=
  match x with
  | .prim p => σ.storeRes r segs (.prim p)
  | .struct _ | .array .. | .map .. => do
    let cur ← σ.findStorage r segs
    σ.storeRes r segs (cur.overlay x)

@[simp] theorem State.writeRes_toSVal (σ : State) (r segs) (v : Value) :
    σ.writeRes r segs v.toSVal = σ.storeRes r segs v.toSVal := by
  cases v <;> rfl

theorem State.writeStorage_eq (σ : State) (r segs x) :
    σ.writeStorage r segs x = (do let s ← σ.writeRes r segs x; pure { σ with storage := s }) := by
  unfold State.writeStorage State.writeRes
  cases x <;> simp only [State.saveStorage_eq, bind_assoc]

/-- The heap a successful `writeAddr` leaves. -/
def heapRes (σ : State) (mv : MVal) : Addr → Res (List (Nat × MObj))
  | .memoryField id f => do
    match ← σ.getObj id with
    | .struct fields => pure (setBy id (.struct (setBy f mv fields)) σ.heap)
    | .array _ _ => .error .stuck
  | .memoryIndex id i => do
    match ← σ.getObj id with
    | .array elems fx =>
      if 0 ≤ i ∧ i.toNat < elems.length then pure (setBy id (.array (elems.set i.toNat mv) fx) σ.heap)
      else .error .revert
    | .struct _ => .error .stuck

theorem writeAddr_eq (σ : State) (mv : MVal) (a : Addr) :
    writeAddr σ mv a = (do let h ← heapRes σ mv a; pure { σ with heap := h }) := by
  cases a with
  | memoryField id f =>
    simp only [writeAddr, heapRes, memWriteField, bind, Except.bind]
    cases σ.getObj id with
    | error _ => rfl
    | ok o => cases o <;> rfl
  | memoryIndex id i =>
    simp only [writeAddr, heapRes, memWriteIndex, bind, Except.bind]
    cases σ.getObj id with
    | error _ => rfl
    | ok o =>
      cases o with
      | struct _ => rfl
      | array elems => by_cases hh : 0 ≤ i ∧ i.toNat < elems.length <;> simp [hh] <;> rfl

theorem State.saveStorage_with (σ : State) (r segs v) :
    (σ.saveStorage r segs v >>= fun τ => pure { σ with storage := τ.storage }) =
      σ.saveStorage r segs v := by
  rw [State.saveStorage_eq]; cases σ.storeRes r segs v <;> rfl

theorem State.writeStorage_with (σ : State) (r segs v) :
    (σ.writeStorage r segs v >>= fun τ => pure { σ with storage := τ.storage }) =
      σ.writeStorage r segs v := by
  rw [State.writeStorage_eq]; cases σ.writeRes r segs v <;> rfl

theorem writeAddr_with (σ : State) (mv : MVal) (a : Addr) :
    (writeAddr σ mv a >>= fun μ => pure { σ with heap := μ.heap, nextId := μ.nextId }) =
      writeAddr σ mv a := by
  rw [writeAddr_eq]; cases heapRes σ mv a <;> rfl

@[simp] theorem Upd.apply_single (e : UpdElem C) (σ : State) :
    Upd.apply [e] σ = e.write σ σ := by
  simp [Upd.apply]

theorem evalBinop_compound {op : BinOp} (hop : op.hasCompoundAssign = true) (p : PrimTy) (lv : Value)
    (b : Res Value) : evalBinop op p lv b = (do checkArith (.prim p) (← applyBinOp op lv (← b))) := by
  cases op <;> simp [BinOp.hasCompoundAssign] at hop <;> rfl

@[simp] theorem SameOk.self (ns : List Var) (x : Res State) : SameOk ns x x := by
  cases x <;> simp [SameOk, EnvAgreeExcept.refl]
@[simp] theorem SameOk.error_error (ns : List Var) (a b : Halt) :
    SameOk ns (.error a : Res State) (.error b) := trivial
@[simp] theorem SameOk.ok_ok (ns : List Var) (a b : State) :
    SameOk ns (.ok a) (.ok b) ↔ EnvAgreeExcept ns a b := Iff.rfl
@[simp] theorem SameOk.ok_error (ns : List Var) (a : State) (b : Halt) :
    ¬ SameOk ns (.ok a) (.error b) := id
@[simp] theorem SameOk.error_ok (ns : List Var) (a : Halt) (b : State) :
    ¬ SameOk ns (.error a) (.ok b) := id

/-- Close `SameOk ns x y` between two runs made of the same pure reads and one
write: split every `Except` match, and compare. -/
macro "res_split" : tactic => `(tactic| (
  simp only [bind, Except.bind, pure, Except.pure]
  repeat' split
  all_goals (try simp_all [EnvAgreeExcept.refl])))

theorem evalBinop_bump (op : IncDec) (p : PrimTy) (lv : Value) (b : Res Value) :
    evalBinop op.binOp p lv b = (do
      checkArith (.prim p) (← applyBinOp op.binOp lv (← b))) := by
  cases op <;> rfl

theorem applyBinOp_bump (op : IncDec) (lv : Value) :
    applyBinOp op.binOp lv (.int 1) =
      (do let n ← lv.asInt; pure (.int (if op.isIncrement then n + 1 else n - 1))) := by
  cases op <;> cases lv <;> rfl

/-! ### Shared reads

The update and the statement read the same things through differently shaped
code; these name the reads, so both sides split on the same atoms. -/

namespace Close

/-- The value a local holds: `x` after `uint x = 10;` is `10`; an alias or
a memory local has none. -/
def bindingVal : Binding → Res Value
  | .val v => .ok v
  | .spath .. | .mref _ | .store _ | .ledger _ => .error .stuck

/-- The path an alias holds: `p` after `Person storage p = alice;` is
`alice`. -/
def bindingPath : Binding → Res (Name × List Seg)
  | .spath r segs => .ok (r, segs)
  | .val _ | .mref _ | .store _ | .ledger _ => .error .stuck

/-- The object a memory local holds: `m` after `Person memory m;`. -/
def bindingRef : Binding → Res Nat
  | .mref id => .ok id
  | .val _ | .spath .. | .store _ | .ledger _ => .error .stuck

/-- The storage a storage variable holds: `old` after `{old := storage}`. -/
def bindingStore : Binding → Res (List (Name × SVal))
  | .store st => .ok st
  | .val _ | .spath .. | .mref _ | .ledger _ => .error .stuck

/-- The ledger a ledger variable holds: `oldNet` after `{oldNet := net}`. -/
def bindingLedger : Binding → Res (List (Int × Int))
  | .ledger l => .ok l
  | .val _ | .spath .. | .mref _ | .store _ => .error .stuck

end Close

/-- A stack local's value. -/
def envVal (σ : State) (x : Var) : Res Value := σ.getEnv x >>= Close.bindingVal

/-- A memory local's identity. -/
def envRef (σ : State) (x : Var) : Res Nat := σ.getEnv x >>= Close.bindingRef

@[simp] theorem Term.eval_pv (σ : State) (x : Var) : (Term.pv x : Term C).eval σ = envVal σ x := rfl
@[simp] theorem Simple.eval_local (σ : State) {p : PrimTy} (x : Var) :
    (Simple.local x : Simple C p).eval σ = envVal σ x := rfl
@[simp] theorem ITerm.eval_pv (σ : State) (x : Var) : (ITerm.pv x : ITerm C).eval σ = envRef σ x := rfl
@[simp] theorem MPath.mval_var (σ : State) {R : RefTy} (x : Var) :
    (MPath.var x : MPath C (.ref R)).mval σ = (do pure (MVal.ref (← envRef σ x))) := by
  simp only [MPath.mval, envRef, Close.bindingRef, bind, Except.bind]
  cases σ.getEnv x with
  | error _ => rfl
  | ok b => cases b <;> rfl
@[simp] theorem MVal.asRef_ref (id : Nat) : (MVal.ref id).asRef = pure id := rfl

@[simp] theorem bumpLocal_eq (σ : State) (op : IncDec) (p : PrimTy) (x : Var) :
    bumpLocal σ op p x = (do
      let old ← envVal σ x
      let oldInt ← old.asInt
      let new ← checkArith (.prim p) (.int (if op.isIncrement then oldInt + 1 else oldInt - 1))
      pure (σ.setEnv x (.val new), if op.isPre then new else old)) := by
  simp only [bumpLocal, envVal, Close.bindingVal, bind, Except.bind, pure, Except.pure]
  repeat' split
  all_goals simp_all

@[simp] theorem opLocal_eq (σ : State) (op : BinOp) (p : PrimTy) (x : Var) (v : Value) :
    opLocal σ op p x v = (do
      let old ← envVal σ x
      let new ← applyBinOp op old v
      let new ← checkArith (.prim p) new
      pure (σ.setEnv x (.val new))) := by
  simp only [opLocal, envVal, Close.bindingVal, bind, Except.bind, pure, Except.pure]
  repeat' split
  all_goals simp_all

@[simp] theorem readLoc_eq (σ : State) (a : Addr) : readLoc σ a = (do (← readAddr σ a).asValue) := by
  cases a with
  | memoryField id f =>
    simp only [readLoc, readAddr, bind, Except.bind, pure, Except.pure]
    repeat' split
    all_goals simp_all
  | memoryIndex id i =>
    simp only [readLoc, readAddr, bind, Except.bind, pure, Except.pure]
    cases σ.getObj id with
    | error _ => rfl
    | ok o =>
      cases o with
      | struct _ => rfl
      | array elems => by_cases hh : 0 ≤ i ∧ i.toNat < elems.length <;> simp [hh]

@[simp] theorem writeLoc_eq (σ : State) (a : Addr) (v : Value) :
    writeLoc σ a v = writeAddr σ v.toMVal a := by
  cases a <;> rfl

@[simp] theorem MLoc.read_field (σ : State) {s f : Name} {T : Ty} (b : MPath C (.struct s))
    (h : C.fieldType s f = some T) :
    (MLoc.field b f h).read σ = (do readAddr σ (.memoryField (← (← b.mval σ).asRef) f)) := by
  simp only [MLoc.read, readAddr]; rfl

@[simp] theorem MLoc.read_index (σ : State) {R : RefTy} {E : Ty} (a : ArrTy R E)
    (b : MPath C (.ref R)) (i : Val C .uint) :
    (MLoc.index a b i).read σ =
      (do let id ← (← b.mval σ).asRef; readAddr σ (.memoryIndex id (← (← i.eval σ).asInt))) := by
  simp only [MLoc.read, readAddr]; rfl

theorem MPath.mval_loc (σ : State) {T : Ty} (l : MLoc C T) : (MPath.loc l).mval σ = l.read σ := rfl

@[simp] theorem Src.pushVal_none (σ : State) {T : Ty} :
    Src.pushVal (C := C) (T := T) σ none = fun slot => pure slot := rfl

section
variable (σ : State)
/-! A term's reading, one step, but for a value or memory local, which stays
`envVal`/`envRef` (`Term.eval_pv`, `ITerm.eval_pv`). -/
theorem Tm.eval_pvP (x : Var) : (Tm.pvP x : PTerm C).eval σ = aliasPath σ x := rfl
theorem Tm.eval_pvS (x : Var) : (Tm.pvS x : STerm C).eval σ = (do
    match ← σ.getEnv x with
    | .store st => pure { σ with storage := st }
    | .val _ | .spath .. | .mref _ | .ledger _ => .error .stuck) := rfl
theorem Tm.eval_app0 {s : Srt} (o : Op0 s) : (Tm.app0 o : Tm C s).eval σ = o.eval σ := rfl
theorem Tm.eval_app1 {a s : Srt} (o : Op1 a s) (x : Tm C a) :
    (Tm.app1 o x).eval σ = o.eval σ (x.eval σ) := rfl
theorem Tm.eval_app2 {a b s : Srt} (o : Op2 a b s) (x : Tm C a) (y : Tm C b) :
    (Tm.app2 o x y).eval σ = o.eval σ (x.eval σ) (y.eval σ) := rfl
theorem Tm.eval_app3 {a b c s : Srt} (o : Op3 a b c s) (x : Tm C a) (y : Tm C b) (z : Tm C c) :
    (Tm.app3 o x y z).eval σ = o.eval σ (x.eval σ) (y.eval σ) (z.eval σ) := rfl
end

open Lean Parser.Tactic in
/-- The simp set that unfolds an update and a statement to their reads and
writes; `extra` says how terms are evaluated and writes are named. -/
macro "upd_unfold_with" "[" extra:simpArg,* "]" : tactic => do
  let extra : Array (TSyntax [``simpStar, ``simpErase, ``simpLemma]) := extra.getElems.map (⟨·.raw⟩)
  `(tactic| simp only [Upd.apply, List.foldlM, UpdElem.write, Tm.eval_app0, Tm.eval_app1,
    Tm.eval_app2, Tm.eval_app3, Tm.eval_pvP, Tm.eval_pvS, Op0.eval, Op1.eval, Op2.eval, Op3.eval,
    Term.eval_pv, ITerm.eval_pv,
    SPath.lower_eval, Loc.lower_eval, Val.lower_eval, Simple.lower_eval, Stmt.run, Src.value,
    Val.eval, Simple.eval_local, bind_assoc, pure_bind, bind_pure, State.writeStorage_toSVal,
    OpLoc.store, OpLoc.bump, opStore, bumpStore, opLocal_eq, bumpLocal_eq, opMem, bumpMem,
    readLoc_eq, writeLoc_eq, ARhs.bind, MRhs.bind, MSrc.mval, MLoc.write, MPath.mval_var,
    MVal.asRef_ref, MLoc.read_field, MLoc.read_index, Loc.resolve, SPath.resolve, Src.pushVal,
    evalBinop_bump, applyBinOp_bump, $extra,*])

/-- `upd_unfold_with`, evaluating terms whole and keeping the rest of the state
through each write. -/
macro "upd_unfold" : tactic => `(tactic| upd_unfold_with [State.saveStorage_with,
    State.writeStorage_with, writeAddr_with, Term.bumped])

end Solidity
