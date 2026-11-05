import Solidity.Optimizer.ConstFold
import Solidity.Optimizer.Pass

/-!
# O02 constant folding and dead-branch elimination over lowering programs

`Prog.cfold` folds the value expressions of local assignments, local
declarations, `require`/`assert` conditions, `transfer`/`send` operands and
`if`/`while` conditions (`Val.cfold`), and recurses into `if` branches, blocks
and loop bodies. On the folded program it removes dead code whose removal the
run cannot observe:

* `if (true) A else B` becomes the block `{ A }` (and `false` gives `{ B }`):
  the branch is a scope in both forms;
* `require(true);`, `assert(true);` and `while (false) …` are dropped from the
  sequence.

A failing condition (`require(false)`, `assert(false)` — its Panic) is never
dropped. Every other statement is left as written. The preservation theorem
is equality of the typed run, as a function of the typed state
(`Prog.cfold_runC`): result, halt kind, final state and heap growth are all
unchanged, so every observation of the program is.
-/
namespace Solidity.Optimizer.ConstFold
open Solidity

variable {C : Contract}

/-! ## Run congruences -/

section Congr
variable {Γ : Ctx}

/-- Two expressions with the same results in every state. -/
def SameVal {p : PrimTy} (a b : Val C Γ p) : Prop := ∀ σ : State C Γ, a.evalT σ = b.evalT σ

theorem TRun.ite_congr {Γ₁ Γ₂ : Ctx} {c c' : Val C Γ .bool} (hc : SameVal c' c)
    (h₁ h₁' : Ext Γ Γ₁) (f₁ : TStep C Γ Γ₁) (h₂ h₂' : Ext Γ Γ₂) (f₂ : TStep C Γ Γ₂) :
    TRun.ite c' h₁' f₁ h₂' f₂ = TRun.ite c h₁ f₁ h₂ f₂ := by
  cases Subsingleton.elim h₁' h₁
  cases Subsingleton.elim h₂' h₂
  funext σ
  simp only [TRun.ite, hc σ]

theorem TRun.block_congr {Γ₁ : Ctx} (h h' : Ext Γ Γ₁) (f : TStep C Γ Γ₁) :
    TRun.block h' f = TRun.block h f := by
  cases Subsingleton.elim h' h
  rfl

theorem TRun.loop_congr {Γ₁ : Ctx} {c c' : Val C Γ .bool} (hc : SameVal c' c)
    (h h' : Ext Γ Γ₁) (f : TStep C Γ Γ₁) :
    TRun.loop c' h' f = TRun.loop c h f := by
  cases Subsingleton.elim h' h
  funext σ
  simp only [TRun.loop, hc _]

theorem TRun.require_congr {c c' : Val C Γ .bool} (hc : SameVal c' c) :
    TRun.require c' = TRun.require c := by
  funext σ
  simp only [TRun.require, hc σ]

theorem TRun.assert_congr {c c' : Val C Γ .bool} (hc : SameVal c' c) :
    TRun.assert c' = TRun.assert c := by
  funext σ
  simp only [TRun.assert, hc σ]

theorem TRun.assignLocal_congr {p : PrimTy} (i : Idx Γ (.val p)) {r r' : Val C Γ p}
    (hr : SameVal r' r) : TRun.assignLocal i r' = TRun.assignLocal i r := by
  funext σ
  simp only [TRun.assignLocal, hr σ]

theorem TRun.declLocal_congr (p : PrimTy) {init init' : Option (Val C Γ p)}
    (hi : ∀ σ : State C Γ, init'.map (·.evalT σ) = init.map (·.evalT σ)) :
    TRun.declLocal p init' = TRun.declLocal p init := by
  funext σ
  have := hi σ
  cases init <;> cases init' <;> simp_all only [TRun.declLocal, Option.map, Option.some.injEq,
    reduceCtorEq]

theorem TRun.transfer_congr {r r' a a' : Val C Γ .uint} (hr : SameVal r' r) (ha : SameVal a' a) :
    TRun.transfer r' a' = TRun.transfer r a := by
  funext σ
  simp only [TRun.transfer, hr σ, ha σ]

theorem TRun.send_congr (pv : Idx Γ (.val .bool)) {r r' a a' : Val C Γ .uint}
    (hr : SameVal r' r) (ha : SameVal a' a) :
    TRun.send pv r' a' = TRun.send pv r a := by
  funext σ
  simp only [TRun.send, hr σ, ha σ]

/-- A sequence after a step that leaves the state as it is. -/
theorem TRun.seq_stay {Γ₂ : Ctx} (s : TStep C Γ Γ) (P : TStep C Γ Γ₂)
    (hs : ∀ σ, s σ = .ok ⟨σ, List.prefix_refl _⟩) : TRun.seq s P = P := by
  funext σ
  simp only [TRun.seq, hs σ]
  cases P σ <;> rfl

end Congr

/-! ## The pass -/

/-- `if` on a literal: the branch it takes, as a block (the branch is a scope). -/
def foldIte {Γ Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (thn : Prog C Γ Γ₁) (els : Prog C Γ Γ₂) :
    Stmt C Γ Γ :=
  match c.const? with
  | some v => if boolT v then .block thn else .block els
  | none => .ite c thn els

/-- Is this condition the literal `true` (resp. `false`)? -/
def litIs {Γ : Ctx} (b : Bool) (c : Val C Γ .bool) : Bool :=
  match c.const? with
  | some v => boolT v == b
  | none => false

/-- Sequence a folded statement, dropping one the run cannot observe. -/
def consDrop : {Γ Γ₁ Γ₂ : Ctx} → Stmt C Γ Γ₁ → Prog C Γ₁ Γ₂ → Prog C Γ Γ₂
  | _, _, _, .require c, P => if litIs true c then P else .cons (.require c) P
  | _, _, _, .assert c, P => if litIs true c then P else .cons (.assert c) P
  | _, _, _, .loop a c body, P => if litIs false c then P else .cons (.loop a c body) P
  | _, _, _, s@(.assign ..), P => .cons s P
  | _, _, _, s@(.rebind ..), P => .cons s P
  | _, _, _, s@(.assignLocal ..), P => .cons s P
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
  | _, _, _, s@(.revert), P => .cons s P
  | _, _, _, s@(.assumeFalse), P => .cons s P
  | _, _, _, s@(.call ..), P => .cons s P
  | _, _, _, s@(.tryCall ..), P => .cons s P
  | _, _, _, s@(.block ..), P => .cons s P
  | _, _, _, s@(.pushOpAssign ..), P => .cons s P
  | _, _, _, s@(.pushIncDec ..), P => .cons s P
  | _, _, _, s@(.callReceiver ..), P => .cons s P
  | _, _, _, s@(.callReceiverPush ..), P => .cons s P
  | _, _, _, s@(.callRec ..), P => .cons s P
  | _, _, _, s@(.revertData ..), P => .cons s P
  | _, _, _, s@(.catchData ..), P => .cons s P

mutual
/-- Constant folding and dead-branch elimination of a statement. -/
def _root_.Solidity.Stmt.cfold : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Stmt C Γ Γ'
  | _, _, .assignLocal i r => .assignLocal i r.cfold
  | _, _, .declLocal p x init => .declLocal p x (init.map Val.cfold)
  | _, _, .require c => .require c.cfold
  | _, _, .assert c => .assert c.cfold
  | _, _, .transfer r a => .transfer r.cfold a.cfold
  | _, _, .send pv r a full => .send pv r.cfold a.cfold full
  | _, _, .ite c thn els => foldIte c.cfold (Prog.cfold thn) (Prog.cfold els)
  | _, _, .block body => .block (Prog.cfold body)
  | _, _, .loop a c body => .loop a c.cfold (Prog.cfold body)
  | _, _, s@(.assign ..) => s
  | _, _, s@(.rebind ..) => s
  | _, _, s@(.declStorage ..) => s
  | _, _, s@(.opAssign ..) => s
  | _, _, s@(.incDec ..) => s
  | _, _, s@(.assignIncDec ..) => s
  | _, _, s@(.assignLocalPush ..) => s
  | _, _, s@(.push ..) => s
  | _, _, s@(.pop ..) => s
  | _, _, s@(.declMem ..) => s
  | _, _, s@(.rebindMem ..) => s
  | _, _, s@(.assignFromMem ..) => s
  | _, _, s@(.assignMem ..) => s
  | _, _, s@(.delete ..) => s
  | _, _, s@(.deleteMem ..) => s
  | _, _, s@(.assignNew ..) => s
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

/-- Constant folding and dead-code elimination of a sequence. -/
def _root_.Solidity.Prog.cfold : {Γ Γ' : Ctx} → Prog C Γ Γ' → Prog C Γ Γ'
  | _, _, .nil => .nil
  | _, _, .cons s P => consDrop (Stmt.cfold s) (Prog.cfold P)
end

/-! ## Preservation -/

theorem foldIte_runC {Γ Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (thn : Prog C Γ Γ₁)
    (els : Prog C Γ Γ₂) :
    Stmt.runC (foldIte c thn els) = Stmt.runC (.ite c thn els) := by
  unfold foldIte
  cases hc : c.const? with
  | none => rfl
  | some v =>
    funext σ
    simp only [Stmt.runC, TRun.ite, const?_evalT σ hc, bind, Except.bind]
    cases boolT v <;> rfl

theorem litIs_evalT {Γ : Ctx} {b : Bool} {c : Val C Γ .bool} (h : litIs b c = true)
    (σ : State C Γ) : c.evalT σ = .ok b := by
  unfold litIs at h
  cases hc : c.const? with
  | none => simp only [hc, Bool.false_eq_true] at h
  | some v =>
    simp only [hc, beq_iff_eq] at h
    rw [const?_evalT σ hc]
    exact congrArg Except.ok h

theorem consDrop_runC : {Γ Γ₁ Γ₂ : Ctx} → (s : Stmt C Γ Γ₁) → (P : Prog C Γ₁ Γ₂) →
    Prog.runC (consDrop s P) = TRun.seq (Stmt.runC s) (Prog.runC P)
  | _, _, _, .require c, P => by
    simp only [consDrop]
    split
    · next h =>
      refine (TRun.seq_stay _ _ fun σ => ?_).symm
      simp only [Stmt.runC, TRun.require, litIs_evalT h σ, bind, Except.bind]
      rfl
    · rfl
  | _, _, _, .assert c, P => by
    simp only [consDrop]
    split
    · next h =>
      refine (TRun.seq_stay _ _ fun σ => ?_).symm
      simp only [Stmt.runC, TRun.assert, litIs_evalT h σ, bind, Except.bind]
      rfl
    · rfl
  | _, _, _, .loop a c body, P => by
    simp only [consDrop]
    split
    · next h =>
      refine (TRun.seq_stay _ _ fun σ => ?_).symm
      simp only [Stmt.runC, TRun.loop]
      exact TLoop.run_of_iterN (n := 1) (by
        simp only [TLoop.iterN, TLoop.step, litIs_evalT h σ])
    · rfl
  | _, _, _, .assign .., _ | _, _, _, .rebind .., _ | _, _, _, .assignLocal .., _
  | _, _, _, .declLocal .., _ | _, _, _, .declStorage .., _ | _, _, _, .opAssign .., _
  | _, _, _, .incDec .., _ | _, _, _, .assignIncDec .., _ | _, _, _, .assignLocalPush .., _
  | _, _, _, .push .., _ | _, _, _, .pop .., _ | _, _, _, .transfer .., _
  | _, _, _, .send .., _ | _, _, _, .declMem .., _ | _, _, _, .rebindMem .., _
  | _, _, _, .assignFromMem .., _ | _, _, _, .assignMem .., _ | _, _, _, .delete .., _
  | _, _, _, .deleteMem .., _ | _, _, _, .assignNew .., _ | _, _, _, .ite .., _
  | _, _, _, .revert, _ | _, _, _, .assumeFalse, _ | _, _, _, .call .., _
  | _, _, _, .tryCall .., _ | _, _, _, .block .., _ | _, _, _, .pushOpAssign .., _
  | _, _, _, .pushIncDec .., _ | _, _, _, .callReceiver .., _
  | _, _, _, .callReceiverPush .., _ | _, _, _, .callRec .., _
  | _, _, _, .revertData .., _ | _, _, _, .catchData .., _ => rfl

mutual
/-- **Statement folding preserves the typed run.** -/
theorem _root_.Solidity.Stmt.cfold_runC : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') →
    Stmt.runC (Stmt.cfold s) = Stmt.runC s
  | _, _, .assignLocal i r => by
    simp only [Stmt.cfold, Stmt.runC]
    exact TRun.assignLocal_congr i (Val.cfold_evalT · r)
  | _, _, .declLocal p x init => by
    simp only [Stmt.cfold, Stmt.runC]
    exact TRun.declLocal_congr p fun σ => by
      cases init <;> simp only [Option.map, Val.cfold_evalT]
  | _, _, .require c => by
    simp only [Stmt.cfold, Stmt.runC]
    exact TRun.require_congr (Val.cfold_evalT · c)
  | _, _, .assert c => by
    simp only [Stmt.cfold, Stmt.runC]
    exact TRun.assert_congr (Val.cfold_evalT · c)
  | _, _, .transfer r a => by
    simp only [Stmt.cfold, Stmt.runC]
    exact TRun.transfer_congr (Val.cfold_evalT · r) (Val.cfold_evalT · a)
  | _, _, .send pv r a full => by
    simp only [Stmt.cfold, Stmt.runC]
    exact TRun.send_congr pv (Val.cfold_evalT · r) (Val.cfold_evalT · a)
  | _, _, .ite c thn els => by
    rw [Stmt.cfold, foldIte_runC]
    simp only [Stmt.runC, Prog.cfold_runC thn, Prog.cfold_runC els]
    exact TRun.ite_congr (Val.cfold_evalT · c) _ _ _ _ _ _
  | _, _, .block body => by
    simp only [Stmt.cfold, Stmt.runC]
    rw [Prog.cfold_runC body]
    exact TRun.block_congr _ _ _
  | _, _, .loop a c body => by
    simp only [Stmt.cfold, Stmt.runC]
    rw [Prog.cfold_runC body]
    exact TRun.loop_congr (Val.cfold_evalT · c) _ _ _
  | _, _, .assign .. | _, _, .rebind .. | _, _, .declStorage .. | _, _, .opAssign ..
  | _, _, .incDec .. | _, _, .assignIncDec .. | _, _, .assignLocalPush .. | _, _, .push ..
  | _, _, .pop .. | _, _, .declMem .. | _, _, .rebindMem .. | _, _, .assignFromMem ..
  | _, _, .assignMem .. | _, _, .delete .. | _, _, .deleteMem .. | _, _, .assignNew ..
  | _, _, .revert | _, _, .assumeFalse | _, _, .call .. | _, _, .tryCall ..
  | _, _, .pushOpAssign .. | _, _, .pushIncDec .. | _, _, .callReceiver ..
  | _, _, .callReceiverPush .. | _, _, .callRec .. | _, _, .revertData ..
  | _, _, .catchData .. => rfl

/-- **Program folding preserves the typed run.** -/
theorem _root_.Solidity.Prog.cfold_runC : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') →
    Prog.runC (Prog.cfold P) = Prog.runC P
  | _, _, .nil => rfl
  | _, _, .cons s P => by
    rw [Prog.cfold, consDrop_runC, Stmt.cfold_runC s, Prog.cfold_runC P]
    rfl
end

/-- The pass in the O01 interface: preservation of the exact typed run. -/
def SameRun {Γ Γ' : Ctx} (P Q : Prog C Γ Γ') : Prop := Prog.runC P = Prog.runC Q

theorem cfold_preserves (Γ Γ' : Ctx) :
    Preserves (SameRun (C := C) (Γ := Γ) (Γ' := Γ'))
      (Prog.cfold : Lowering.Pass C Γ Γ') :=
  fun P => (Prog.cfold_runC P).symm

end Solidity.Optimizer.ConstFold
