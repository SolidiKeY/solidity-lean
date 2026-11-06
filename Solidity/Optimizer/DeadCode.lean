import Solidity.Optimizer.StmtFold

/-!
# O02 dead-code elimination after a halting statement

Inside a scope (a block, an `if` branch or a loop body), the statements after
one that always halts — `revert;`, `assume(false);`, `require(false);`,
`assert(false);` (conditions already literal, e.g. after `Prog.cfold`) — never
run, so they are removed (`Prog.cut`). The scope pops whatever the removed tail
would have declared, so its run is unchanged: `cut_scope` states that the run
of a cut sequence, its scope ended, is the run of the original, its scope
ended. The halt itself (revert or Panic) is kept.

`Prog.dce` cuts every scope of a program; `Prog.dce_runC` is equality of the
typed run. A top-level sequence is not cut (its output context is the
program's type).
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
  | .assign .. | .rebind .. | .assignLocal .. | .declLocal .. | .declStorage .. | .opAssign ..
  | .incDec .. | .assignIncDec .. | .assignLocalPush .. | .push .. | .pop .. | .transfer ..
  | .send .. | .declMem .. | .rebindMem .. | .assignFromMem .. | .assignMem .. | .delete ..
  | .deleteMem .. | .assignNew .. | .ite .. | .call .. | .tryCall .. | .loop .. | .block ..
  | .pushOpAssign .. | .pushIncDec .. | .callReceiver .. | .callReceiverPush .. | .callRec ..
  | .revertData .. | .catchData .. => false

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
  | assign | rebind | assignLocal | declLocal | declStorage | opAssign | incDec | assignIncDec
  | assignLocalPush | push | pop | transfer | send | declMem | rebindMem | assignFromMem
  | assignMem | delete | deleteMem | assignNew | ite | call | tryCall | loop | block
  | pushOpAssign | pushIncDec | callReceiver | callReceiverPush | callRec | revertData
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

end Solidity.Optimizer.ConstFold
