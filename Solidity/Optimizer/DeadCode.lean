import Solidity.Optimizer.StmtFold
import Solidity.Optimizer.CSE
import Solidity.Optimizer.UnusedVar

/-!
# O02 dead-code elimination after a halting statement

Inside a scope (a block, an `if` branch or a loop body), the statements after
one that always halts — `revert;`, `revert` with data, `assume(false);`,
`require(false);`, `assert(false);` (conditions already literal, e.g. after `Prog.cfold`) — never
run, so they are removed (`Prog.cut`). The scope pops whatever the removed tail
would have declared, so its run is unchanged: `cut_scope` states that the run
of a cut sequence, its scope ended, is the run of the original, its scope
ended. The halt itself (revert or Panic) is kept.

`Prog.dce` cuts every block, `if` branch and loop body of a program (call,
`try`/`catch` and receiver-call bodies are left as written); `Prog.dce_runC` is equality of the
typed run. A top-level sequence is not cut (its output context is the
program's type).

Dead local stores: `x = e₁; x = e₂;` becomes `x = e₂;` when `e₁` is a simple
value (it cannot fail, so dropping it hides no halt) and `e₂` does not read `x`
and has no storage/memory read (both checked by `Val.indep`), in every sequence
reached through blocks, `if` branches and loop bodies (`Prog.dse`, `Prog.dse_runC`). Storage and
memory stores are not touched (they wait for X06's aliasing facts).
-/
namespace Solidity.Optimizer.ConstFold
open Solidity

variable {C : Contract}

/-- A statement that halts in every state. -/
def alwaysHalts {Γ Γ₁ : Ctx} : Stmt C Γ Γ₁ → Bool
  | .revert => true
  | .assumeFalse => true
  | .require c => litIs false c
  | .assert c => litIs false c
  | .revertData _ => true
  | .assign .. | .rebind .. | .assignLocal .. | .declLocal .. | .declStorage .. | .opAssign ..
  | .incDec .. | .assignIncDec .. | .assignLocalPush .. | .push .. | .pop .. | .transfer ..
  | .send .. | .declMem .. | .rebindMem .. | .assignFromMem .. | .assignMem .. | .delete ..
  | .deleteMem .. | .assignNew .. | .ite .. | .call .. | .tryCall .. | .loop .. | .block ..
  | .pushOpAssign .. | .pushIncDec .. | .callReceiver .. | .callReceiverPush .. | .callRec ..
  | .catchData .. => false

theorem alwaysHalts_runC {Γ Γ₁ : Ctx} (s : Stmt C Γ Γ₁) (h : alwaysHalts s = true)
    (σ : State C Γ) : ∃ e, Stmt.runC s σ = .error e := by
  cases s with
  | revert => exact ⟨_, rfl⟩
  | assumeFalse => exact ⟨_, rfl⟩
  | require c =>
    refine ⟨.revert, ?_⟩
    simp only [Stmt.runC, TRun.require, litIs_evalT h σ, bind, Except.bind]
    rfl
  | assert c =>
    refine ⟨.panic, ?_⟩
    simp only [Stmt.runC, TRun.assert, litIs_evalT h σ, bind, Except.bind]
    rfl
  | revertData d =>
    simp only [Stmt.runC, TRun.revertData, bind, Except.bind]
    cases d.mapM (·.evalT σ) with
    | error e => exact ⟨e, rfl⟩
    | ok bs => exact ⟨_, rfl⟩
  | assign | rebind | assignLocal | declLocal | declStorage | opAssign | incDec | assignIncDec
  | assignLocalPush | push | pop | transfer | send | declMem | rebindMem | assignFromMem
  | assignMem | delete | deleteMem | assignNew | ite | call | tryCall | loop | block
  | pushOpAssign | pushIncDec | callReceiver | callReceiverPush | callRec
  | catchData => simp only [alwaysHalts, Bool.false_eq_true] at h

/-- A sequence cut after its first halting statement. -/
def Prog.cut {Γ : Ctx} : {Δ : Ctx} → Prog C Γ Δ → (Δ' : Ctx) × Prog C Γ Δ'
  | _, .nil => ⟨_, .nil⟩
  | _, .cons s P =>
    if alwaysHalts s then ⟨_, .cons s .nil⟩ else ⟨_, .cons s (Prog.cut P).2⟩

/-- A run with its scope ended. -/
abbrev scopeRun {Γ Δ : Ctx} (P : Prog C Γ Δ) (σ : State C Γ) : TRes (Out C σ.H Γ) :=
  (Prog.runC P σ).map fun o => ⟨o.st.drop P.ext, o.ext⟩

private theorem drop_trans {H : HTy} {Γ Δ : Ctx} (a : Ext Γ Δ) : {Ε : Ctx} → (b : Ext Δ Ε) →
    (e : TEnv C H Ε) → TEnv.drop (a.trans b) e = TEnv.drop a (TEnv.drop b e)
  | _, .refl, _ => rfl
  | _, .push b, e => drop_trans a b e.2

theorem scopeRun_cons {Γ Γ₁ Δ : Ctx} (s : Stmt C Γ Γ₁) (P : Prog C Γ₁ Δ) (σ : State C Γ) :
    scopeRun (.cons s P) σ =
      match Stmt.runC s σ with
      | .ok o => (scopeRun P o.st).map fun o' =>
          ⟨o'.st.drop s.ext, o.ext.trans o'.ext⟩
      | .error e => .error e := by
  simp only [scopeRun, Prog.runC, TRun.seq]
  cases Stmt.runC s σ with
  | error e => rfl
  | ok o =>
    show Except.map _ (Except.map _ _) = Except.map _ (Except.map _ _)
    cases Prog.runC P o.st with
    | error e => rfl
    | ok o' =>
      show Except.ok _ = Except.ok _
      dsimp only
      simp only [Except.ok.injEq, Out.mk.injEq]
      show o'.st.drop ((Stmt.ext s).trans P.ext) = (o'.st.drop P.ext).drop s.ext
      simp only [State.drop, State.withEnv, drop_trans]

/-- **A cut sequence, its scope ended, runs as the original.** -/
theorem cut_scope {Γ : Ctx} : {Δ : Ctx} → (P : Prog C Γ Δ) → (σ : State C Γ) →
    scopeRun (Prog.cut P).2 σ = scopeRun P σ
  | _, .nil, _ => rfl
  | _, .cons s P, σ => by
    simp only [Prog.cut]
    by_cases h : alwaysHalts s = true
    · rw [if_pos h]
      obtain ⟨e, he⟩ := alwaysHalts_runC s h σ
      rw [scopeRun_cons, scopeRun_cons, he]
    · rw [if_neg h, scopeRun_cons, scopeRun_cons]
      cases Stmt.runC s σ with
      | error e => rfl
      | ok o => simp only [cut_scope P o.st]

/-! ## The pass -/

theorem scopeRun_congr {Γ Δ : Ctx} {P Q : Prog C Γ Δ} (h : Prog.runC P = Prog.runC Q) :
    scopeRun P = scopeRun Q := by
  funext σ
  simp only [scopeRun, h, Subsingleton.elim P.ext Q.ext]

theorem block_scope {Γ Δ Δ' : Ctx} (P : Prog C Γ Δ) (Q : Prog C Γ Δ')
    (h : scopeRun P = scopeRun Q) : Stmt.runC (.block P) = Stmt.runC (.block Q) := h

theorem ite_scope {Γ Δ₁ Δ₂ Δ₁' Δ₂' : Ctx} (c : Val C Γ .bool) (P : Prog C Γ Δ₁) (Q : Prog C Γ Δ₂)
    (P' : Prog C Γ Δ₁') (Q' : Prog C Γ Δ₂') (hP : scopeRun P = scopeRun P')
    (hQ : scopeRun Q = scopeRun Q') : Stmt.runC (.ite c P Q) = Stmt.runC (.ite c P' Q') := by
  funext σ
  show (do let v ← c.evalT σ; if boolT v then scopeRun P σ else scopeRun Q σ) =
    (do let v ← c.evalT σ; if boolT v then scopeRun P' σ else scopeRun Q' σ)
  rw [hP, hQ]

theorem loop_scope {Γ Δ Δ' : Ctx} (a : LoopAnn C Γ) (c : Val C Γ .bool) (P : Prog C Γ Δ)
    (Q : Prog C Γ Δ') (h : scopeRun P = scopeRun Q) :
    Stmt.runC (.loop a c P) = Stmt.runC (.loop a c Q) := by
  funext σ
  simp only [Stmt.runC, TRun.loop]
  congr 1
  funext o
  have e := congrArg (Except.map fun o' : Out C o.st.H Γ =>
    (⟨o'.st, o.ext.trans o'.ext⟩ : Out C σ.H Γ)) (congrFun h o.st)
  simp only [scopeRun] at e
  revert e
  cases Prog.runC P o.st <;> cases Prog.runC Q o.st <;> exact id

mutual
/-- Cut every scope of a statement after its first halting statement. -/
def Stmt.dce : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Stmt C Γ Γ'
  | _, _, .ite c thn els => .ite c (Prog.cut (Prog.dce thn)).2 (Prog.cut (Prog.dce els)).2
  | _, _, .block body => .block (Prog.cut (Prog.dce body)).2
  | _, _, .loop a c body => .loop a c (Prog.cut (Prog.dce body)).2
  | _, _, s@(.assign ..) => s
  | _, _, s@(.rebind ..) => s
  | _, _, s@(.assignLocal ..) => s
  | _, _, s@(.declLocal ..) => s
  | _, _, s@(.declStorage ..) => s
  | _, _, s@(.opAssign ..) => s
  | _, _, s@(.incDec ..) => s
  | _, _, s@(.assignIncDec ..) => s
  | _, _, s@(.assignLocalPush ..) => s
  | _, _, s@(.push ..) => s
  | _, _, s@(.pop ..) => s
  | _, _, s@(.transfer ..) => s
  | _, _, s@(.send ..) => s
  | _, _, s@(.declMem ..) => s
  | _, _, s@(.rebindMem ..) => s
  | _, _, s@(.assignFromMem ..) => s
  | _, _, s@(.assignMem ..) => s
  | _, _, s@(.delete ..) => s
  | _, _, s@(.deleteMem ..) => s
  | _, _, s@(.assignNew ..) => s
  | _, _, s@(.require ..) => s
  | _, _, s@(.assert ..) => s
  | _, _, s@(.revert) => s
  | _, _, s@(.assumeFalse) => s
  | _, _, s@(.call ..) => s
  | _, _, s@(.tryCall ..) => s
  | _, _, s@(.pushOpAssign ..) => s
  | _, _, s@(.pushIncDec ..) => s
  | _, _, s@(.callReceiver ..) => s
  | _, _, s@(.callReceiverPush ..) => s
  | _, _, s@(.callRec ..) => s
  | _, _, s@(.revertData ..) => s
  | _, _, s@(.catchData ..) => s

/-- Cut every scope of a sequence. -/
def Prog.dce : {Γ Γ' : Ctx} → Prog C Γ Γ' → Prog C Γ Γ'
  | _, _, .nil => .nil
  | _, _, .cons s P => .cons (Stmt.dce s) (Prog.dce P)
end

mutual
theorem Stmt.dce_runC : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → Stmt.runC (Stmt.dce s) = Stmt.runC s
  | _, _, .ite c thn els => by
    simp only [Stmt.dce]
    refine ite_scope c _ _ _ _ ?_ ?_
    · rw [funext (cut_scope (Prog.dce thn)), scopeRun_congr (Prog.dce_runC thn)]
    · rw [funext (cut_scope (Prog.dce els)), scopeRun_congr (Prog.dce_runC els)]
  | _, _, .block body => by
    simp only [Stmt.dce]
    refine block_scope _ _ ?_
    rw [funext (cut_scope (Prog.dce body)), scopeRun_congr (Prog.dce_runC body)]
  | _, _, .loop a c body => by
    simp only [Stmt.dce]
    refine loop_scope a c _ _ ?_
    rw [funext (cut_scope (Prog.dce body)), scopeRun_congr (Prog.dce_runC body)]
  | _, _, .assign ..
  | _, _, .rebind ..
  | _, _, .assignLocal ..
  | _, _, .declLocal ..
  | _, _, .declStorage ..
  | _, _, .opAssign ..
  | _, _, .incDec ..
  | _, _, .assignIncDec ..
  | _, _, .assignLocalPush ..
  | _, _, .push ..
  | _, _, .pop ..
  | _, _, .transfer ..
  | _, _, .send ..
  | _, _, .declMem ..
  | _, _, .rebindMem ..
  | _, _, .assignFromMem ..
  | _, _, .assignMem ..
  | _, _, .delete ..
  | _, _, .deleteMem ..
  | _, _, .assignNew ..
  | _, _, .require ..
  | _, _, .assert ..
  | _, _, .revert
  | _, _, .assumeFalse
  | _, _, .call ..
  | _, _, .tryCall ..
  | _, _, .pushOpAssign ..
  | _, _, .pushIncDec ..
  | _, _, .callReceiver ..
  | _, _, .callReceiverPush ..
  | _, _, .callRec ..
  | _, _, .revertData ..
  | _, _, .catchData .. => rfl

theorem Prog.dce_runC : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → Prog.runC (Prog.dce P) = Prog.runC P
  | _, _, .nil => rfl
  | _, _, .cons s P => by
    simp only [Prog.dce, Prog.runC]
    rw [Stmt.dce_runC s, Prog.dce_runC P]
end

theorem dce_preserves (Γ Γ' : Ctx) :
    Preserves (SameRun (C := C) (Γ := Γ) (Γ' := Γ')) (Prog.dce : Lowering.Pass C Γ Γ') :=
  fun P => (Prog.dce_runC P).symm

/-! ## Dead local stores -/

theorem tenv_set_set {H : HTy} : {Γ : Ctx} → {t : LTy} → (i : Idx Γ t) → (v w : t.TDenote C H) →
    (e : TEnv C H Γ) → TEnv.set i w (TEnv.set i v e) = TEnv.set i w e
  | _, _, .here, _, _, _ => rfl
  | _, _, .there i, v, w, e => congrArg (Prod.mk e.1) (tenv_set_set i v w e.2)

/-- A local assignment's target and value. -/
def stmtAssign? {Γ Γ₁ : Ctx} : Stmt C Γ Γ₁ → Option ((q : PrimTy) × Idx Γ (.val q) × Val C Γ q)
  | .assignLocal j e => some ⟨_, j, e⟩
  | .assign .. | .rebind .. | .declLocal .. | .declStorage .. | .opAssign .. | .incDec ..
  | .assignIncDec .. | .assignLocalPush .. | .push .. | .pop .. | .transfer .. | .send ..
  | .declMem .. | .rebindMem .. | .assignFromMem .. | .assignMem .. | .delete .. | .deleteMem ..
  | .assignNew .. | .ite .. | .require .. | .assert .. | .revert | .assumeFalse | .call ..
  | .tryCall .. | .loop .. | .block .. | .pushOpAssign .. | .pushIncDec .. | .callReceiver ..
  | .callReceiverPush .. | .callRec .. | .revertData .. | .catchData .. => none

/-- The first local assignment of a sequence. -/
def headAssign? {Γ : Ctx} : {Δ : Ctx} → Prog C Γ Δ →
    Option ((q : PrimTy) × Idx Γ (.val q) × Val C Γ q)
  | _, .nil => none
  | _, .cons s _ => stmtAssign? s

/-- `x = e₁;` before a sequence: dropped when the sequence starts with `x = e₂;`,
`e₁` cannot fail and `e₂` does not read `x`. -/
def dseCons : {Γ Γ₁ Δ : Ctx} → Stmt C Γ Γ₁ → Prog C Γ₁ Δ → Prog C Γ Δ
  | _, _, _, .assignLocal (p := p) i e₁, P =>
    match headAssign? P with
    | some ⟨q, j, e₂⟩ =>
      if Val.isSimple e₁ && j.toNat == i.toNat && Val.indep i.toNat e₂ then P
      else .cons (.assignLocal i e₁) P
    | none => .cons (.assignLocal i e₁) P
  | _, _, _, s@(.assign ..), P => .cons s P
  | _, _, _, s@(.rebind ..), P => .cons s P
  | _, _, _, s@(.declLocal ..), P => .cons s P
  | _, _, _, s@(.declStorage ..), P => .cons s P
  | _, _, _, s@(.opAssign ..), P => .cons s P
  | _, _, _, s@(.incDec ..), P => .cons s P
  | _, _, _, s@(.assignIncDec ..), P => .cons s P
  | _, _, _, s@(.assignLocalPush ..), P => .cons s P
  | _, _, _, s@(.push ..), P => .cons s P
  | _, _, _, s@(.pop ..), P => .cons s P
  | _, _, _, s@(.transfer ..), P => .cons s P
  | _, _, _, s@(.send ..), P => .cons s P
  | _, _, _, s@(.declMem ..), P => .cons s P
  | _, _, _, s@(.rebindMem ..), P => .cons s P
  | _, _, _, s@(.assignFromMem ..), P => .cons s P
  | _, _, _, s@(.assignMem ..), P => .cons s P
  | _, _, _, s@(.delete ..), P => .cons s P
  | _, _, _, s@(.deleteMem ..), P => .cons s P
  | _, _, _, s@(.assignNew ..), P => .cons s P
  | _, _, _, s@(.ite ..), P => .cons s P
  | _, _, _, s@(.require ..), P => .cons s P
  | _, _, _, s@(.assert ..), P => .cons s P
  | _, _, _, s@(.revert), P => .cons s P
  | _, _, _, s@(.assumeFalse), P => .cons s P
  | _, _, _, s@(.call ..), P => .cons s P
  | _, _, _, s@(.tryCall ..), P => .cons s P
  | _, _, _, s@(.loop ..), P => .cons s P
  | _, _, _, s@(.block ..), P => .cons s P
  | _, _, _, s@(.pushOpAssign ..), P => .cons s P
  | _, _, _, s@(.pushIncDec ..), P => .cons s P
  | _, _, _, s@(.callReceiver ..), P => .cons s P
  | _, _, _, s@(.callReceiverPush ..), P => .cons s P
  | _, _, _, s@(.callRec ..), P => .cons s P
  | _, _, _, s@(.revertData ..), P => .cons s P
  | _, _, _, s@(.catchData ..), P => .cons s P

theorem headAssign?_eq {Γ Δ : Ctx} {P : Prog C Γ Δ} {q : PrimTy} {j : Idx Γ (.val q)}
    {e : Val C Γ q} (h : headAssign? P = some ⟨q, j, e⟩) :
    ∃ Q : Prog C Γ Δ, P = .cons (.assignLocal j e) Q := by
  cases P with
  | nil => simp only [headAssign?, reduceCtorEq] at h
  | cons s Q =>
    cases s with
    | assignLocal j' e' =>
      simp only [headAssign?, stmtAssign?, Option.some.injEq, Sigma.mk.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      simp only [heq_eq_eq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact ⟨Q, rfl⟩
    | assign | rebind | declLocal | declStorage | opAssign | incDec | assignIncDec
    | assignLocalPush | push | pop | transfer | send | declMem | rebindMem | assignFromMem
    | assignMem | delete | deleteMem | assignNew | ite | require | assert | revert
    | assumeFalse | call | tryCall | loop | block | pushOpAssign | pushIncDec | callReceiver
    | callReceiverPush | callRec | revertData | catchData =>
      simp only [headAssign?, stmtAssign?, reduceCtorEq] at h

theorem dseCons_runC : {Γ Γ₁ Δ : Ctx} → (s : Stmt C Γ Γ₁) → (P : Prog C Γ₁ Δ) →
    Prog.runC (dseCons s P) = Prog.runC (.cons s P)
  | _, _, _, .assignLocal (p := p) i e₁, P => by
    simp only [dseCons]
    split
    · next q j e₂ hh =>
      split
      · next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨hs, hji⟩, hind⟩ := hc
        obtain ⟨eq, hj⟩ := Idx.eq_of_toNat i j hji
        cases eq
        subst j
        obtain ⟨Q, rfl⟩ := headAssign?_eq hh
        funext σ
        cases e₁ with
        | simple t =>
          simp only [Prog.runC, TRun.seq, Stmt.runC, TRun.assignLocal, Val.evalT, bind,
            Except.bind, pure, Except.pure]
          rw [Val.evalT_setLocal_indep σ i _ e₂ hind]
          cases e₂.evalT σ with
          | error err => rfl
          | ok w =>
            show Except.map _ (Prog.runC Q ((σ.setLocal i w))) =
              Except.map _ (Except.map _ (Prog.runC Q ((σ.setLocal i (t.evalT σ)).setLocal i w)))
            show Except.map _ (Prog.runC Q (σ.withEnv (TEnv.set i w σ.env))) =
              Except.map _ (Except.map _
                (Prog.runC Q (σ.withEnv (TEnv.set i w (TEnv.set i (t.evalT σ) σ.env)))))
            rw [tenv_set_set]
            cases Prog.runC Q (σ.withEnv (TEnv.set i w σ.env)) <;> rfl
        | read | binop | unop | ternary | readMem | len | mlen | modular | hash =>
          simp only [Val.isSimple, Bool.false_eq_true] at hs
      · rfl
    · rfl
  | _, _, _, .assign .., _
  | _, _, _, .rebind .., _
  | _, _, _, .declLocal .., _
  | _, _, _, .declStorage .., _
  | _, _, _, .opAssign .., _
  | _, _, _, .incDec .., _
  | _, _, _, .assignIncDec .., _
  | _, _, _, .assignLocalPush .., _
  | _, _, _, .push .., _
  | _, _, _, .pop .., _
  | _, _, _, .transfer .., _
  | _, _, _, .send .., _
  | _, _, _, .declMem .., _
  | _, _, _, .rebindMem .., _
  | _, _, _, .assignFromMem .., _
  | _, _, _, .assignMem .., _
  | _, _, _, .delete .., _
  | _, _, _, .deleteMem .., _
  | _, _, _, .assignNew .., _
  | _, _, _, .ite .., _
  | _, _, _, .require .., _
  | _, _, _, .assert .., _
  | _, _, _, .revert, _
  | _, _, _, .assumeFalse, _
  | _, _, _, .call .., _
  | _, _, _, .tryCall .., _
  | _, _, _, .loop .., _
  | _, _, _, .block .., _
  | _, _, _, .pushOpAssign .., _
  | _, _, _, .pushIncDec .., _
  | _, _, _, .callReceiver .., _
  | _, _, _, .callReceiverPush .., _
  | _, _, _, .callRec .., _
  | _, _, _, .revertData .., _
  | _, _, _, .catchData .., _ => rfl

mutual
/-- Dead local stores removed in every sequence of a statement. -/
def Stmt.dse : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Stmt C Γ Γ'
  | _, _, .ite c thn els => .ite c (Prog.dse thn) (Prog.dse els)
  | _, _, .block body => .block (Prog.dse body)
  | _, _, .loop a c body => .loop a c (Prog.dse body)
  | _, _, s@(.assign ..) => s
  | _, _, s@(.rebind ..) => s
  | _, _, s@(.assignLocal ..) => s
  | _, _, s@(.declLocal ..) => s
  | _, _, s@(.declStorage ..) => s
  | _, _, s@(.opAssign ..) => s
  | _, _, s@(.incDec ..) => s
  | _, _, s@(.assignIncDec ..) => s
  | _, _, s@(.assignLocalPush ..) => s
  | _, _, s@(.push ..) => s
  | _, _, s@(.pop ..) => s
  | _, _, s@(.transfer ..) => s
  | _, _, s@(.send ..) => s
  | _, _, s@(.declMem ..) => s
  | _, _, s@(.rebindMem ..) => s
  | _, _, s@(.assignFromMem ..) => s
  | _, _, s@(.assignMem ..) => s
  | _, _, s@(.delete ..) => s
  | _, _, s@(.deleteMem ..) => s
  | _, _, s@(.assignNew ..) => s
  | _, _, s@(.require ..) => s
  | _, _, s@(.assert ..) => s
  | _, _, s@(.revert) => s
  | _, _, s@(.assumeFalse) => s
  | _, _, s@(.call ..) => s
  | _, _, s@(.tryCall ..) => s
  | _, _, s@(.pushOpAssign ..) => s
  | _, _, s@(.pushIncDec ..) => s
  | _, _, s@(.callReceiver ..) => s
  | _, _, s@(.callReceiverPush ..) => s
  | _, _, s@(.callRec ..) => s
  | _, _, s@(.revertData ..) => s
  | _, _, s@(.catchData ..) => s

/-- Dead local stores removed in a sequence. -/
def Prog.dse : {Γ Γ' : Ctx} → Prog C Γ Γ' → Prog C Γ Γ'
  | _, _, .nil => .nil
  | _, _, .cons s P => dseCons (Stmt.dse s) (Prog.dse P)
end

mutual
theorem Stmt.dse_runC : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → Stmt.runC (Stmt.dse s) = Stmt.runC s
  | _, _, .ite c thn els => by
    simp only [Stmt.dse, Stmt.runC]
    rw [Prog.dse_runC thn, Prog.dse_runC els]
    exact TRun.ite_congr (fun _ => rfl) _ _ _ _ _ _
  | _, _, .block body => by
    simp only [Stmt.dse, Stmt.runC]
    rw [Prog.dse_runC body]
    exact TRun.block_congr _ _ _
  | _, _, .loop a c body => by
    simp only [Stmt.dse, Stmt.runC]
    rw [Prog.dse_runC body]
    exact TRun.loop_congr (fun _ => rfl) _ _ _
  | _, _, .assign ..
  | _, _, .rebind ..
  | _, _, .assignLocal ..
  | _, _, .declLocal ..
  | _, _, .declStorage ..
  | _, _, .opAssign ..
  | _, _, .incDec ..
  | _, _, .assignIncDec ..
  | _, _, .assignLocalPush ..
  | _, _, .push ..
  | _, _, .pop ..
  | _, _, .transfer ..
  | _, _, .send ..
  | _, _, .declMem ..
  | _, _, .rebindMem ..
  | _, _, .assignFromMem ..
  | _, _, .assignMem ..
  | _, _, .delete ..
  | _, _, .deleteMem ..
  | _, _, .assignNew ..
  | _, _, .require ..
  | _, _, .assert ..
  | _, _, .revert
  | _, _, .assumeFalse
  | _, _, .call ..
  | _, _, .tryCall ..
  | _, _, .pushOpAssign ..
  | _, _, .pushIncDec ..
  | _, _, .callReceiver ..
  | _, _, .callReceiverPush ..
  | _, _, .callRec ..
  | _, _, .revertData ..
  | _, _, .catchData .. => rfl

theorem Prog.dse_runC : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → Prog.runC (Prog.dse P) = Prog.runC P
  | _, _, .nil => rfl
  | _, _, .cons s P => by
    simp only [Prog.dse]
    rw [dseCons_runC]
    simp only [Prog.runC]
    rw [Stmt.dse_runC s, Prog.dse_runC P]
end

theorem dse_preserves (Γ Γ' : Ctx) :
    Preserves (SameRun (C := C) (Γ := Γ) (Γ' := Γ')) (Prog.dse : Lowering.Pass C Γ Γ') :=
  fun P => (Prog.dse_runC P).symm

end Solidity.Optimizer.ConstFold
