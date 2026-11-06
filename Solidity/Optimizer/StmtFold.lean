import Solidity.Optimizer.ConstFold
import Solidity.Optimizer.Pass

/-!
# O02 constant folding and dead-branch elimination over lowering programs

`Prog.vopt V` applies a proved expression pass `V` (`Prog.cfold` uses
`Val.cfold`) to the value expressions of local assignments, local declarations,
storage writes of a value and their locations' index expressions (`assign`,
`push`, `delete`, `pop`, via `Src.vopt`, `Loc.vmap`, `SPath.vmap`),
compound-assignment right sides (`opAssign`, `pushOpAssign`; their receivers are
left as written, as is `pushIncDec`), `require`/`assert` conditions,
`transfer`/`send` operands and `if`/`while` conditions, and recurses into `if`
branches, blocks and loop bodies. On the folded program it removes dead code whose removal the
run cannot observe:

* `if (true) A else B` becomes the block `{ A }` (and `false` gives `{ B }`):
  the branch is a scope in both forms;
* `require(true);`, `assert(true);` and `while (false) …` are dropped from the
  sequence.

No pass recurses into call, `try`/`catch` or receiver-call bodies.
Dropping `while (false)` also drops its `LoopAnn` (which the run does not read).

A failing condition (`require(false)`, `assert(false)` — its Panic) is never
dropped. Every other statement and position is left as written. The preservation theorem
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

/-- An expression pass with its proof: equal results in every typed state. -/
structure ValPass (C : Contract) where
  run : {Γ : Ctx} → {p : PrimTy} → Val C Γ p → Val C Γ p
  sound : ∀ {Γ : Ctx} {p : PrimTy} (σ : State C Γ) (v : Val C Γ p), (run v).evalT σ = v.evalT σ

/-- An expression pass on a storage source's value. -/
def _root_.Solidity.Src.vopt {Γ : Ctx} (V : ValPass C) : {T : Ty} → Src C Γ T → Src C Γ T
  | _, .val v => .val (V.run v)
  | _, s@(.copy ..) | _, s@(.fixedCopy ..) | _, s@(.copyMem ..) | _, s@(.fixedCopyMem ..) => s

theorem _root_.Solidity.Src.vopt_valueT {Γ : Ctx} (V : ValPass C) (σ : State C Γ) :
    {T : Ty} → (r : Src C Γ T) → (r.vopt V).valueT σ = r.valueT σ
  | _, .val v => by simp only [Src.vopt, Src.valueT, V.sound]
  | _, .copy .. | _, .fixedCopy .. | _, .copyMem .. | _, .fixedCopyMem .. => rfl

mutual
/-- An expression pass on the index expressions of a storage path. -/
def _root_.Solidity.SPath.vmap {Γ : Ctx} (V : ValPass C) : {T : Ty} → SPath C Γ T → SPath C Γ T
  | _, .alias i => .alias i
  | _, .loc l => .loc (l.vmap V)

/-- An expression pass on the index expressions of a storage location. -/
def _root_.Solidity.Loc.vmap {Γ : Ctx} (V : ValPass C) : {T : Ty} → Loc C Γ T → Loc C Γ T
  | _, .root r h => .root r h
  | _, .field b f h => .field (b.vmap V) f h
  | _, .index it b i => .index it (b.vmap V) (V.run i)
end

mutual
theorem _root_.Solidity.SPath.vmap_resolveT {Γ : Ctx} (V : ValPass C) (σ : State C Γ) :
    {T : Ty} → (b : SPath C Γ T) → (b.vmap V).resolveT σ = b.resolveT σ
  | _, .alias _ => rfl
  | _, .loc l => by simp only [SPath.vmap, SPath.resolveT, Loc.vmap_resolveT V σ l]

theorem _root_.Solidity.Loc.vmap_resolveT {Γ : Ctx} (V : ValPass C) (σ : State C Γ) :
    {T : Ty} → (l : Loc C Γ T) → (l.vmap V).resolveT σ = l.resolveT σ
  | _, .root .. => rfl
  | _, .field b f h => by simp only [Loc.vmap, Loc.resolveT, SPath.vmap_resolveT V σ b]
  | _, .index it b i => by
    simp only [Loc.vmap, Loc.resolveT, SPath.vmap_resolveT V σ b, V.sound]
end

/-- Constant folding as an expression pass. -/
def cfoldPass : ValPass C := ⟨Val.cfold, fun σ v => Val.cfold_evalT σ v⟩

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
/-- An expression pass on every handled position, and dead-branch elimination. -/
def _root_.Solidity.Stmt.vopt (V : ValPass C) : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Stmt C Γ Γ'
  | _, _, .assignLocal i r => .assignLocal i (V.run r)
  | _, _, .declLocal p x init => .declLocal p x (init.map V.run)
  | _, _, .require c => .require (V.run c)
  | _, _, .assert c => .assert (V.run c)
  | _, _, .transfer r a => .transfer (V.run r) (V.run a)
  | _, _, .send pv r a full => .send pv (V.run r) (V.run a) full
  | _, _, .ite c thn els => foldIte (V.run c) (Prog.vopt V thn) (Prog.vopt V els)
  | _, _, .block body => .block (Prog.vopt V body)
  | _, _, .loop a c body => .loop a (V.run c) (Prog.vopt V body)
  | _, _, .assign l r => .assign (l.vmap V) (r.vopt V)
  | _, _, .delete l => .delete (l.vmap V)
  | _, _, .pop b => .pop (b.vmap V)
  | _, _, s@(.rebind ..) => s
  | _, _, s@(.declStorage ..) => s
  | _, _, .opAssign op hop hp l r => .opAssign op hop hp l (V.run r)
  | _, _, s@(.incDec ..) => s
  | _, _, s@(.assignIncDec ..) => s
  | _, _, s@(.assignLocalPush ..) => s
  | _, _, .push b v hd =>
    .push (b.vmap V) (v.map (Src.vopt V)) (by rw [Option.isSome_map]; exact hd)
  | _, _, s@(.declMem ..) => s
  | _, _, s@(.rebindMem ..) => s
  | _, _, s@(.assignFromMem ..) => s
  | _, _, s@(.assignMem ..) => s
  | _, _, s@(.deleteMem ..) => s
  | _, _, s@(.assignNew ..) => s
  | _, _, s@(.revert) => s
  | _, _, s@(.assumeFalse) => s
  | _, _, s@(.call ..) => s
  | _, _, s@(.tryCall ..) => s
  | _, _, .pushOpAssign op hop hp b r => .pushOpAssign op hop hp b (V.run r)
  | _, _, s@(.pushIncDec ..) => s
  | _, _, s@(.callReceiver ..) => s
  | _, _, s@(.callReceiverPush ..) => s
  | _, _, s@(.callRec ..) => s
  | _, _, s@(.revertData ..) => s
  | _, _, s@(.catchData ..) => s

/-- An expression pass and dead-code elimination of a sequence. -/
def _root_.Solidity.Prog.vopt (V : ValPass C) : {Γ Γ' : Ctx} → Prog C Γ Γ' → Prog C Γ Γ'
  | _, _, .nil => .nil
  | _, _, .cons s P => consDrop (Stmt.vopt V s) (Prog.vopt V P)
end

/-- Constant folding and dead-code elimination. -/
abbrev _root_.Solidity.Prog.cfold {Γ Γ' : Ctx} (P : Prog C Γ Γ') : Prog C Γ Γ' :=
  Prog.vopt cfoldPass P

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
/-- **An expression pass lifted to a statement preserves the typed run.** -/
theorem _root_.Solidity.Stmt.vopt_runC (V : ValPass C) : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') →
    Stmt.runC (Stmt.vopt V s) = Stmt.runC s
  | _, _, .assignLocal i r => by
    simp only [Stmt.vopt, Stmt.runC]
    exact TRun.assignLocal_congr i (V.sound · r)
  | _, _, .declLocal p x init => by
    simp only [Stmt.vopt, Stmt.runC]
    exact TRun.declLocal_congr p fun σ => by
      cases init <;> simp only [Option.map, V.sound]
  | _, _, .require c => by
    simp only [Stmt.vopt, Stmt.runC]
    exact TRun.require_congr (V.sound · c)
  | _, _, .assert c => by
    simp only [Stmt.vopt, Stmt.runC]
    exact TRun.assert_congr (V.sound · c)
  | _, _, .transfer r a => by
    simp only [Stmt.vopt, Stmt.runC]
    exact TRun.transfer_congr (V.sound · r) (V.sound · a)
  | _, _, .send pv r a full => by
    simp only [Stmt.vopt, Stmt.runC]
    exact TRun.send_congr pv (V.sound · r) (V.sound · a)
  | _, _, .ite c thn els => by
    rw [Stmt.vopt, foldIte_runC]
    simp only [Stmt.runC, Prog.vopt_runC V thn, Prog.vopt_runC V els]
    exact TRun.ite_congr (V.sound · c) _ _ _ _ _ _
  | _, _, .block body => by
    simp only [Stmt.vopt, Stmt.runC]
    rw [Prog.vopt_runC V body]
    exact TRun.block_congr _ _ _
  | _, _, .loop a c body => by
    simp only [Stmt.vopt, Stmt.runC]
    rw [Prog.vopt_runC V body]
    exact TRun.loop_congr (V.sound · c) _ _ _
  | _, _, .assign l r => by
    simp only [Stmt.vopt, Stmt.runC]
    funext σ
    simp only [TRun.assign, Src.vopt_valueT, Loc.vmap_resolveT]
  | _, _, .opAssign op hop hp l r => by
    simp only [Stmt.vopt, Stmt.runC]
    funext σ
    simp only [TRun.opAssign, V.sound]
  | _, _, .pushOpAssign op hop hp b r => by
    simp only [Stmt.vopt, Stmt.runC]
    funext σ
    simp only [TRun.pushOpAssign, V.sound]
  | _, _, .push b v hd => by
    simp only [Stmt.vopt, Stmt.runC]
    funext σ
    cases v <;> simp only [TRun.push, Option.map, Src.vopt_valueT, SPath.vmap_resolveT]
  | _, _, .delete l => by
    simp only [Stmt.vopt, Stmt.runC]
    funext σ
    simp only [TRun.delete, Loc.vmap_resolveT]
  | _, _, .pop b => by
    simp only [Stmt.vopt, Stmt.runC]
    funext σ
    simp only [TRun.pop, SPath.vmap_resolveT]
  | _, _, .rebind .. | _, _, .declStorage ..
  | _, _, .incDec .. | _, _, .assignIncDec .. | _, _, .assignLocalPush ..
  | _, _, .declMem .. | _, _, .rebindMem .. | _, _, .assignFromMem ..
  | _, _, .assignMem .. | _, _, .deleteMem .. | _, _, .assignNew ..
  | _, _, .revert | _, _, .assumeFalse | _, _, .call .. | _, _, .tryCall ..
  | _, _, .pushIncDec .. | _, _, .callReceiver ..
  | _, _, .callReceiverPush .. | _, _, .callRec .. | _, _, .revertData ..
  | _, _, .catchData .. => rfl

/-- **An expression pass lifted to a program preserves the typed run.** -/
theorem _root_.Solidity.Prog.vopt_runC (V : ValPass C) : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') →
    Prog.runC (Prog.vopt V P) = Prog.runC P
  | _, _, .nil => rfl
  | _, _, .cons s P => by
    rw [Prog.vopt, consDrop_runC, Stmt.vopt_runC V s, Prog.vopt_runC V P]
    rfl
end

/-- **Constant folding and dead-code elimination preserve the typed run.** -/
theorem _root_.Solidity.Prog.cfold_runC {Γ Γ' : Ctx} (P : Prog C Γ Γ') :
    Prog.runC (Prog.cfold P) = Prog.runC P :=
  Prog.vopt_runC cfoldPass P

/-- The pass in the O01 interface: preservation of the exact typed run. -/
def SameRun {Γ Γ' : Ctx} (P Q : Prog C Γ Γ') : Prop := Prog.runC P = Prog.runC Q

theorem vopt_preserves (V : ValPass C) (Γ Γ' : Ctx) :
    Preserves (SameRun (C := C) (Γ := Γ) (Γ' := Γ'))
      (Prog.vopt V : Lowering.Pass C Γ Γ') :=
  fun P => (Prog.vopt_runC V P).symm

theorem cfold_preserves (Γ Γ' : Ctx) :
    Preserves (SameRun (C := C) (Γ := Γ) (Γ' := Γ'))
      (Prog.cfold : Lowering.Pass C Γ Γ') :=
  fun P => (Prog.cfold_runC P).symm

end Solidity.Optimizer.ConstFold
