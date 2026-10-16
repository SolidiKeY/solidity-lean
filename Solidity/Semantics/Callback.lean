import Solidity.Semantics.RunFrame

/-!
# The callback semantics of `transfer`, typed

The relational layer of the callbacks over the typed run
(`docs/intrinsic.md`, W1 lane `runlemmas`; the untyped one was deleted at W4
`sem-del`): `ExecS J σ s o` runs
`s : Stmt C Γ Γ'` from `σ : State C Γ` exactly as `Stmt.run` does,
except where control leaves the contract (a `transfer`, a `send`, a `try`),
where the run either leaves it with the invariant `J` broken (`violated`)
or resumes in any state the callee may leave (`State.havoc`: the typed
storage and the ledger replaced) that satisfies `J`.  A loop or a block
whose body pays runs iteration by iteration, statement by statement; a
loop that pays may diverge.

What the types settle:

* **The invariant is closed by its type**: it reads a state of the empty
  context (`StateInv`), on the state's global part (`StateInv.at`), so the
  callee has none of the contract's locals.  A formula's reading
  (`Fml C []`) is one such invariant once the formulas are read on typed
  states.
* **No `undef` arms, no failed entries**: a condition is a `Bool`
  (`Val.evalT`), a call's frame is always entered (`CallRet.enterT`), and a
  `try`'s call is always made (`ExtCall.keyT`).
* **The heap only grows**: an outcome carries the extension of the heap
  typing from the state it ran from (`COut C H Γ` over `Out`), so a call
  gives its caller's locals back weakened (`TRun.callLeave`).
* **A scope's end is the run's**: a branch, a block, a loop body or a
  callee's frame pops its locals on every outcome (`COut.map`).

Proved: the deterministic run is one of the callback runs, unless the
invariant breaks (`Prog.exec_run`, `Frames.exec_run`); with no payment in a
program, its only callback run is the deterministic one (`ExecP.eq_run`),
so a property of every callback run is one of the deterministic run
(`ExecP.forall_iff`, `ExecF.forall_iff`).  The modalities read over these
runs are `holdsC` (`Calculus/CallbackHolds.lean`).
-/

namespace Solidity

open Semantics (Word lookupBy)
open Solidity (Modality)

variable {C : Contract}

/-! ## Outcomes -/

/-- How a run with callbacks ends: in a state of the context `Γ` over a heap
grown from `H`, halted, or leaving the contract with its invariant broken. -/
inductive COut (C : Contract) (H : HTy) (Γ : Ctx) where
  | ok (o : Out C H Γ)
  | halt (e : THalt)
  | violated

namespace COut

variable {H H' : HTy} {Γ Δ : Ctx}

/-- The outcome of a deterministic run. -/
def ofRes : TRes (Out C H Γ) → COut C H Γ
  | .ok o => .ok o
  | .error e => .halt e

def isOk : COut C H Γ → Bool
  | .ok _ => true
  | _ => false

/-- How an outcome halts, if it does. -/
def halt? : COut C H Γ → Option THalt
  | .halt e => some e
  | _ => none

/-- The state an outcome ends in, mapped (a scope's locals popped, the
heap's growth carried). -/
def map (f : Out C H Γ → Out C H' Δ) : COut C H Γ → COut C H' Δ
  | .ok o => .ok (f o)
  | .halt e => .halt e
  | .violated => .violated

/-- `p` after a run under `m`: of the state it ends in, `m.onTHalt` of a halt
that is not a panic, and never of a panic or of a broken invariant. -/
def after (m : Modality) (p : State C Γ → Prop) : COut C H Γ → Prop
  | .ok o => p o.st
  | .halt e => m.onTHalt e ∧ e ≠ .panic
  | .violated => False

theorem map_ofRes (f : Out C H Γ → Out C H' Δ) (r : TRes (Out C H Γ)) :
    (ofRes r).map f = ofRes (r.map f) := by
  cases r <;> rfl

theorem isOk_map (f : Out C H Γ → Out C H' Δ) (o : COut C H Γ) : (o.map f).isOk = o.isOk := by
  cases o <;> rfl

theorem after_ofRes_ok (m : Modality) (p : State C Γ → Prop) (o : Out C H Γ) :
    (ofRes (.ok o)).after m p ↔ p o.st := Iff.rfl

theorem after_ofRes_error (m : Modality) (p : State C Γ → Prop) (e : THalt) :
    (ofRes (.error e : TRes (Out C H Γ))).after m p ↔ m.onTHalt e ∧ e ≠ .panic := Iff.rfl

end COut

/-- A run continued: the second outcome over the first's heap, the
extensions composed (`TRun.seq`). -/
def Out.cat {H : HTy} {Γ₁ Γ₂ : Ctx} (o₁ : Out C H Γ₁) (o : Out C o₁.st.H Γ₂) : Out C H Γ₂ :=
  ⟨o.st, o₁.ext.trans o.ext⟩

/-- After `f()` returns an array alias, run its push/pop and remove the alias.
Halts and broken callback invariants propagate before the operation. -/
def COut.receiverOp {H : HTy} {Γ : Ctx} {E : Ty} (op : ReceiverOp C Γ E) :
    COut C H (.alias (.array E) :: Γ) → COut C H Γ
  | .ok a => .ofRes ((TRun.receiverOp (op.wk (.drop .refl)) (.alias .here) a.st).map
      fun o => Out.cat a (Out.drop (.push .refl) o))
  | .halt e => .halt e
  | .violated => .violated

/-- Finish `f().push(e)` after the operand prefix, snapshotting its final source. -/
def COut.pushPrefix {H : HTy} {Γ Γv : Ctx} {E : Ty} (he : Ext Γ Γv)
    (value : Src C Γv E) (ref : SRef C (.array E)) : COut C H Γv → COut C H Γ
  | .ok a => .ofRes (do
      let v ← value.valueT a.st
      if a.st.storage.full ref then throw .exhausted else do
        let st ← TRes.ofOpt (a.st.storage.push ref (fun _ => some v.strip))
        pure ⟨(a.st.withStorage st).drop he, a.ext⟩)
  | .halt e => .halt e
  | .violated => .violated

/-- With no callback, the operand prefix of `f().push(e)` has its ordinary result. -/
theorem COut.pushPrefix_ofRes {Γ Γv : Ctx} {E : Ty} (he : Ext Γ Γv)
    (code : TStep C Γ Γv) (value : Src C Γv E) (ref : SRef C (.array E))
    (σ : State C Γ) :
    (COut.ofRes (code σ)).pushPrefix he value ref =
      COut.ofRes (TRun.pushAfterPrefix he code value ref σ) := by
  cases h : code σ <;> simp only [pushPrefix, TRun.pushAfterPrefix, h, ofRes,
    bind, Except.bind] <;> rfl

/-- The callback continuation of `f().push(e)` agrees with its deterministic run. -/
theorem COut.receiverOp_of_call {Γ ps Γf : Ctx} {E : Ty} (args : Args C Γ ps) (r : Var)
    (hb : Ext ([.alias (.array E)] ++ ps) Γf)
    (body : TStep C ([.alias (.array E)] ++ ps) Γf) (op : ReceiverOp C Γ E) (σ : State C Γ) :
    (COut.ofRes (TRun.call args (.storage _ r) hb body σ)).receiverOp op =
      COut.ofRes (TRun.callReceiver args r hb body op σ) := by
  rw [TRun.callReceiver_eq_seq]
  unfold TRun.seq
  cases TRun.call args (.storage _ r) hb body σ with
  | error => rfl
  | ok a =>
    dsimp only [COut.ofRes, COut.receiverOp]
    cases TRun.receiverOp (op.wk (.drop .refl)) (.alias .here) a.st <;> rfl

/-! ## The invariant, the callee -/

/-- A contract invariant, read on a state with no locals (solkey's
`CInv(storage, net)`). -/
structure StateInv (C : Contract) where
  holds : State C [] → Prop

/-- The invariant holds of the global part of `σ`. -/
def StateInv.at {Γ : Ctx} (J : StateInv C) (σ : State C Γ) : Prop :=
  J.holds (σ.withEnv (Δ := []) ())

/-- What a call leaves its caller once its body ran to `o` from the frame
`o₁`: the caller's locals weakened along the heap the call grew, with the
call's result (`TRun.call`). -/
def TRun.callLeave {Γ Γ' ps rs Γf : Ctx} (ret : CallRet Γ rs Γ') (hb : Ext (rs ++ ps) Γf)
    (σ : State C Γ) (o₁ : Out C σ.H (rs ++ ps)) (o : Out C o₁.st.H Γf) : Out C σ.H Γ' :=
  ⟨o.st.withEnv (ret.leaveT (TEnv.wk (o₁.ext.trans o.ext) Γ σ.env)
    (TEnv.take rs (TEnv.drop hb o.st.env))), o₁.ext.trans o.ext⟩

theorem TRun.callFrom_eq {Γ Γ' ps rs Γf : Ctx} (ret : CallRet Γ rs Γ') (hb : Ext (rs ++ ps) Γf)
    (body : TStep C (rs ++ ps) Γf) (σ : State C Γ) (o₁ : Out C σ.H (rs ++ ps)) :
    TRun.callFrom ret hb body σ o₁ = (body o₁.st).map (TRun.callLeave ret hb σ o₁) := by
  unfold TRun.callFrom
  cases body o₁.st <;> rfl

/-! ## Which statements the callback reading sees -/

mutual

/-- Whether a `transfer`, a `send` or a `try` occurs in the statement, in a
branch, a block, a loop or a callee included. -/
def Stmt.hasTransfer : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Bool
  | _, _, s => Stmt.casesOn (motive_1 := fun _ _ _ => Bool) s
    (assign := fun _ _ => false) (rebind := fun _ _ => false) (assignLocal := fun _ _ => false)
    (declLocal := fun _ _ _ => false) (declStorage := fun _ _ _ => false)
    (opAssign := fun _ _ _ _ _ => false) (incDec := fun _ _ _ => false)
    (assignIncDec := fun _ _ _ _ _ => false) (assignLocalPush := fun _ _ => false)
    (pushOpAssign := fun _ _ _ _ _ => false) (pushIncDec := fun _ _ _ => false)
    (push := fun _ _ _ => false) (pop := fun _ => false)
    (transfer := fun _ _ => true) (send := fun _ _ _ => true)
    (declMem := fun _ _ _ _ _ => false) (rebindMem := fun _ _ => false)
    (assignFromMem := fun _ _ => false) (assignMem := fun _ _ => false)
    (delete := fun _ => false) (deleteMem := fun _ _ => false) (assignNew := fun _ _ _ => false)
    (ite := fun _ thn els => Prog.hasTransfer thn || Prog.hasTransfer els)
    (require := fun _ => false) (assert := fun _ => false) (revert := false)
    (call := fun _ _ _ body => Prog.hasTransfer body)
    (callReceiver := fun _ _ _ body _ => Prog.hasTransfer body)
    (callReceiverPush := fun _ _ _ body code _ => Prog.hasTransfer body || Prog.hasTransfer code)
    (tryCall := fun _ _ _ _ _ _ _ => true)
    (loop := fun _ _ body => Prog.hasTransfer body) (block := fun body => Prog.hasTransfer body)
  termination_by structural _ _ s => s

def Prog.hasTransfer : {Γ Γ' : Ctx} → Prog C Γ Γ' → Bool
  | _, _, P => Prog.casesOn (motive_2 := fun _ _ _ => Bool) P false
      (fun s P => Stmt.hasTransfer s || Prog.hasTransfer P)
  termination_by structural _ _ P => P

end

/-- The statements the relation does not take from `Stmt.run`: a
`transfer`, a `send`, a `try`, the two that run others by a choice (`if`, a
call), and a loop or a block whose body pays. -/
def Stmt.forks {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Bool :=
  Stmt.casesOn (motive_1 := fun _ _ _ => Bool) s
    (assign := fun _ _ => false) (rebind := fun _ _ => false) (assignLocal := fun _ _ => false)
    (declLocal := fun _ _ _ => false) (declStorage := fun _ _ _ => false)
    (opAssign := fun _ _ _ _ _ => false) (incDec := fun _ _ _ => false)
    (assignIncDec := fun _ _ _ _ _ => false) (assignLocalPush := fun _ _ => false)
    (pushOpAssign := fun _ _ _ _ _ => false) (pushIncDec := fun _ _ _ => false)
    (push := fun _ _ _ => false) (pop := fun _ => false)
    (transfer := fun _ _ => true) (send := fun _ _ _ => true)
    (declMem := fun _ _ _ _ _ => false) (rebindMem := fun _ _ => false)
    (assignFromMem := fun _ _ => false) (assignMem := fun _ _ => false)
    (delete := fun _ => false) (deleteMem := fun _ _ => false) (assignNew := fun _ _ _ => false)
    (ite := fun _ _ _ => true)
    (require := fun _ => false) (assert := fun _ => false) (revert := false)
    (call := fun _ _ _ _ => true)
    (callReceiver := fun _ _ _ _ _ => true)
    (callReceiverPush := fun _ _ _ _ _ _ => true)
    (tryCall := fun _ _ _ _ _ _ _ => true)
    (loop := fun _ _ body => Prog.hasTransfer body) (block := fun body => Prog.hasTransfer body)

/-- Whether a `transfer` occurs in a program of the frames. -/
def Frames.hasTransfer : {Γ Γ₀ : Ctx} → Frames C Γ Γ₀ → Bool
  | _, _, κ => Frames.casesOn (motive := fun _ _ _ => Bool) κ false
      (fun ω κ => Prog.hasTransfer ω || Frames.hasTransfer κ) (fun _ _ κ => Frames.hasTransfer κ)
      (fun _ κ => Frames.hasTransfer κ)
  termination_by structural _ _ κ => κ

/-- Whether a `transfer` occurs in a program of the formula. -/
def Fml.hasTransfer : {Γ : Ctx} → Fml C Γ → Bool
  | _, φ => Fml.casesOn (motive := fun _ _ => Bool) φ
    (tt := false) (eq := fun _ _ => false) (defined := fun _ => false)
    (not := fun φ => Fml.hasTransfer φ)
    (and := fun φ ψ => Fml.hasTransfer φ || Fml.hasTransfer ψ)
    (imp := fun φ ψ => Fml.hasTransfer φ || Fml.hasTransfer ψ)
    (upd := fun _ _ φ => Fml.hasTransfer φ)
    (modal := fun _ P κ φ => Prog.hasTransfer P || κ.hasTransfer || Fml.hasTransfer φ)
    (havoc := fun φ => Fml.hasTransfer φ) (all := fun _ _ φ => Fml.hasTransfer φ)
    (bind := fun _ _ _ φ => Fml.hasTransfer φ) (anon := fun _ φ => Fml.hasTransfer φ)
  termination_by structural _ φ => φ

theorem Prog.hasTransfer_cons {Γ Γ₁ Γ' : Ctx} (s : Stmt C Γ Γ₁) (P : Prog C Γ₁ Γ') :
    Prog.hasTransfer (.cons s P) = (Stmt.hasTransfer s || Prog.hasTransfer P) := rfl

theorem Frames.hasTransfer_seq {Γ Γ₁ Γ₀ : Ctx} (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) :
    Frames.hasTransfer (.seq ω κ) = (Prog.hasTransfer ω || κ.hasTransfer) := rfl

theorem Fml.hasTransfer_and {Γ : Ctx} (φ ψ : Fml C Γ) :
    Fml.hasTransfer (.and φ ψ) = (φ.hasTransfer || ψ.hasTransfer) := rfl

theorem Fml.hasTransfer_imp {Γ : Ctx} (φ ψ : Fml C Γ) :
    Fml.hasTransfer (.imp φ ψ) = (φ.hasTransfer || ψ.hasTransfer) := rfl

theorem Fml.hasTransfer_modal {Γ Γ' Γ₀ : Ctx} (m : Modality) (P : Prog C Γ Γ') (κ : Frames C Γ' Γ₀)
    (φ : Fml C Γ₀) :
    Fml.hasTransfer (.modal m P κ φ) = (Prog.hasTransfer P || κ.hasTransfer || φ.hasTransfer) :=
  rfl

/-! ## Runs with callbacks -/

mutual

/-- `ExecS J σ s o`: run from `σ`, `s` may end in `o` when every payment
may call back into a contract with invariant `J`. -/
inductive ExecS (J : StateInv C) : {Γ Γ' : Ctx} → (σ : State C Γ) → Stmt C Γ Γ' →
    COut C σ.H Γ' → Prop where
  /-- A statement that runs no other by a choice and pays nothing runs as
  `Stmt.run`. -/
  | det {Γ Γ' : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ'} :
      s.forks = false → ExecS J σ s (.ofRes (s.run σ))
  /-- A transfer whose operands halt. -/
  | transferHalt {Γ : Ctx} {σ : State C Γ} {r a : Val C Γ .uint} {e : THalt} :
      TRun.transfer r a σ = .error e → ExecS J σ (.transfer r a) (.halt e)
  /-- KeY's "invariant on exit": control leaves with `J` broken. -/
  | transferViolated {Γ : Ctx} {σ : State C Γ} {r a : Val C Γ .uint} {o₁ : Out C σ.H Γ} :
      TRun.transfer r a σ = .ok o₁ → ¬ J.at o₁.st → ExecS J σ (.transfer r a) .violated
  /-- KeY's "resume after callback": control leaves with `J` kept and comes
  back to any state the callee may leave in which `J` holds. -/
  | transferResume {Γ : Ctx} {σ : State C Γ} {r a : Val C Γ .uint} {o₁ : Out C σ.H Γ}
      {st : Storage C} {nt : Ledger} :
      TRun.transfer r a σ = .ok o₁ → J.at o₁.st → J.at (o₁.st.havoc st nt) →
        ExecS J σ (.transfer r a) (.ok ⟨o₁.st.havoc st nt, o₁.ext⟩)
  /-- A send that halts, where its transfer would. -/
  | sendHalt {Γ : Ctx} {σ : State C Γ} {pv : Idx Γ (.val .bool)} {r a : Val C Γ .uint}
      {e : THalt} :
      TRun.transfer r a σ = .error e → ExecS J σ (.send pv r a) (.halt e)
  /-- KeY's "send failed": the callee reverts, nothing is booked and `pv`
  is `false`, whatever the transaction's oracle says. -/
  | sendFailed {Γ : Ctx} {σ : State C Γ} {pv : Idx Γ (.val .bool)} {r a : Val C Γ .uint}
      {o₁ : Out C σ.H Γ} :
      TRun.transfer r a σ = .ok o₁ →
        ExecS J σ (.send pv r a) (.ok ⟨σ.setLocal pv (false : Bool), List.prefix_refl _⟩)
  /-- KeY's "invariant on exit", the payment booked. -/
  | sendViolated {Γ : Ctx} {σ : State C Γ} {pv : Idx Γ (.val .bool)} {r a : Val C Γ .uint}
      {o₁ : Out C σ.H Γ} :
      TRun.transfer r a σ = .ok o₁ → ¬ J.at o₁.st → ExecS J σ (.send pv r a) .violated
  /-- KeY's "send succeeded": the payment booked, `J` kept, any state the
  callee may leave in which `J` holds, `pv` then `true`. -/
  | sendResume {Γ : Ctx} {σ : State C Γ} {pv : Idx Γ (.val .bool)} {r a : Val C Γ .uint}
      {o₁ : Out C σ.H Γ} {st : Storage C} {nt : Ledger} :
      TRun.transfer r a σ = .ok o₁ → J.at o₁.st → J.at (o₁.st.havoc st nt) →
        ExecS J σ (.send pv r a)
          (.ok ⟨(o₁.st.havoc st nt).setLocal pv (true : Bool), o₁.ext⟩)
  | iteHalt {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {c : Val C Γ .bool} {thn : Prog C Γ Γ₁}
      {els : Prog C Γ Γ₂} {e : THalt} :
      c.evalT σ = .error e → ExecS J σ (.ite c thn els) (.halt e)
  /-- The branch the condition picks, its locals popped. -/
  | iteThen {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {c : Val C Γ .bool} {thn : Prog C Γ Γ₁}
      {els : Prog C Γ Γ₂} {o : COut C σ.H Γ₁} :
      c.evalT σ = .ok true → ExecP J σ thn o →
        ExecS J σ (.ite c thn els) (o.map (Out.drop thn.ext))
  | iteElse {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {c : Val C Γ .bool} {thn : Prog C Γ Γ₁}
      {els : Prog C Γ Γ₂} {o : COut C σ.H Γ₂} :
      c.evalT σ = .ok false → ExecP J σ els o →
        ExecS J σ (.ite c thn els) (o.map (Out.drop els.ext))
  /-- A call whose arguments halt. -/
  | callArgs {Γ Γ' ps rs Γf : Ctx} {σ : State C Γ} {f : Name} {args : Args C Γ ps}
      {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf} {e : THalt} :
      args.evalT σ = .error e → ExecS J σ (.call f args ret body) (.halt e)
  /-- The body run in the callee's frame, and what the call leaves the
  caller (`TRun.call`). -/
  | callBody {Γ Γ' ps rs Γf : Ctx} {σ : State C Γ} {f : Name} {args : Args C Γ ps}
      {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf} {a : TEnv C σ.H ps}
      {o : COut C (ret.enterT (σ.withEnv a)).st.H Γf} :
      args.evalT σ = .ok a → ExecP J (ret.enterT (σ.withEnv a)).st body o →
        ExecS J σ (.call f args ret body)
          (o.map (TRun.callLeave ret body.ext σ (ret.enterT (σ.withEnv a))))
  /-- `f().push(e)` and `f().pop()` continue the getter's callback run once. -/
  | callReceiver {Γ ps Γf : Ctx} {E : Ty} {σ : State C Γ} {f : Name}
      {args : Args C Γ ps} {r : Var} {body : Prog C ([.alias (.array E)] ++ ps) Γf}
      {op : ReceiverOp C Γ E} {o : COut C σ.H (.alias (.array E) :: Γ)} :
      ExecS J σ (.call f args (.storage _ r) body) o →
        ExecS J σ (.callReceiver f args r body op) (o.receiverOp op)
  /-- A successful getter precedes every callback in the deferred operand. -/
  | callReceiverPush {Γ ps Γf Γv : Ctx} {E : Ty} {σ : State C Γ} {f : Name}
      {args : Args C Γ ps} {r : Var} {body : Prog C ([.alias (.array E)] ++ ps) Γf}
      {code : Prog C Γ Γv} {value : Src C Γv E}
      {a : Out C σ.H (.alias (.array E) :: Γ)} {ref : SRef C (.array E)}
      {u : COut C a.st.H Γv} :
      ExecS J σ (.call f args (.storage _ r) body) (.ok a) →
      a.st.env.1 = some ref → ExecP J (a.st.drop (.push .refl)) code u →
      ExecS J σ (.callReceiverPush f args r body code value)
        ((u.pushPrefix code.ext value ref).map (fun b => ⟨b.st, a.ext.trans b.ext⟩))
  /-- An unset getter result reverts before the operand's first effect. -/
  | callReceiverPushUnset {Γ ps Γf Γv : Ctx} {E : Ty} {σ : State C Γ} {f : Name}
      {args : Args C Γ ps} {r : Var} {body : Prog C ([.alias (.array E)] ++ ps) Γf}
      {code : Prog C Γ Γv} {value : Src C Γv E}
      {a : Out C σ.H (.alias (.array E) :: Γ)} :
      ExecS J σ (.call f args (.storage _ r) body) (.ok a) → a.st.env.1 = none →
      ExecS J σ (.callReceiverPush f args r body code value) (.halt .revert)
  /-- Getter failure stops `f().push(e)` before its operand. -/
  | callReceiverPushHalt {Γ ps Γf Γv : Ctx} {E : Ty} {σ : State C Γ} {f : Name}
      {args : Args C Γ ps} {r : Var} {body : Prog C ([.alias (.array E)] ++ ps) Γf}
      {code : Prog C Γ Γv} {value : Src C Γv E} {err : THalt} :
      ExecS J σ (.call f args (.storage _ r) body) (.halt err) →
      ExecS J σ (.callReceiverPush f args r body code value) (.halt err)
  /-- A getter's invariant violation stops `f().push(e)` before its operand. -/
  | callReceiverPushViolated {Γ ps Γf Γv : Ctx} {E : Ty} {σ : State C Γ} {f : Name}
      {args : Args C Γ ps} {r : Var} {body : Prog C ([.alias (.array E)] ++ ps) Γf}
      {code : Prog C Γ Γv} {value : Src C Γv E} :
      ExecS J σ (.call f args (.storage _ r) body) .violated →
      ExecS J σ (.callReceiverPush f args r body code value) .violated
  /-- The call reverts in the caller: no code at the address, or the callee
  reverts. -/
  | tryRevert {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄} :
      ExecS J σ (.tryCall call rets ok err code pnc other) (.halt .revert)
  /-- Data that the return variables do not decode. -/
  | tryDecode {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄} {vs : List Word} {e : THalt} :
      rets.decodeT (C := C) (H := σ.H) vs = .error e →
        ExecS J σ (.tryCall call rets ok err code pnc other) (.halt e)
  /-- KeY's "invariant on exit": control leaves with `J` broken. -/
  | tryViolated {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄} :
      ¬ J.at σ → ExecS J σ (.tryCall call rets ok err code pnc other) .violated
  /-- KeY's "call succeeded": `J` kept, any state the callee may leave in
  which `J` holds, the return data bound, the clause run, its locals popped. -/
  | tryOk {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄} {st : Storage C} {nt : Ledger}
      {vs rest : List Word} {r : TEnv C σ.H ρ} {o : COut C σ.H Γ₁} :
      J.at σ → J.at (σ.havoc st nt) → rets.decodeT vs = .ok (r, rest) →
        ExecP J ((σ.havoc st nt).withEnv (TEnv.append ρ r σ.env)) ok o →
          ExecS J σ (.tryCall call rets ok err code pnc other)
            (o.map (Out.drop ((Ext.append Γ ρ).trans ok.ext)))
  /-- "Error caught": the call reverted, and its effects with it. -/
  | tryError {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄} {o : COut C σ.H Γ₂} :
      ExecP J σ err o →
        ExecS J σ (.tryCall call rets ok err code pnc other) (o.map (Out.drop err.ext))
  /-- "Panic caught", with the code bound. -/
  | tryPanic {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄} {v : Word} {o : COut C σ.H Γ₃} :
      ExecP J (σ.withEnv (TEnv.append κ (code.decodeT v) σ.env)) pnc o →
        ExecS J σ (.tryCall call rets ok err code pnc other)
          (o.map (Out.drop ((Ext.append Γ κ).trans pnc.ext)))
  /-- "Other failure caught". -/
  | tryOther {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄} {o : COut C σ.H Γ₄} :
      ExecP J σ other o →
        ExecS J σ (.tryCall call rets ok err code pnc other) (o.map (Out.drop other.ext))
  /-- A loop that pays, whose condition halts. -/
  | loopHalt {Γ Γ₁ : Ctx} {σ : State C Γ} {a : LoopAnn C Γ} {c : Val C Γ .bool}
      {body : Prog C Γ Γ₁} {e : THalt} :
      Prog.hasTransfer body = true → c.evalT σ = .error e → ExecS J σ (.loop a c body) (.halt e)
  /-- The condition is false: the loop ends where it is. -/
  | loopExit {Γ Γ₁ : Ctx} {σ : State C Γ} {a : LoopAnn C Γ} {c : Val C Γ .bool}
      {body : Prog C Γ Γ₁} :
      Prog.hasTransfer body = true → c.evalT σ = .ok false →
        ExecS J σ (.loop a c body) (.ok ⟨σ, List.prefix_refl _⟩)
  /-- One iteration, its locals popped, and the loop again. -/
  | loopIter {Γ Γ₁ : Ctx} {σ : State C Γ} {a : LoopAnn C Γ} {c : Val C Γ .bool}
      {body : Prog C Γ Γ₁} {υ : Out C σ.H Γ₁} {o : COut C (υ.st.drop body.ext).H Γ} :
      Prog.hasTransfer body = true → c.evalT σ = .ok true → ExecP J σ body (.ok υ) →
        ExecS J (υ.st.drop body.ext) (.loop a c body) o →
          ExecS J σ (.loop a c body) (o.map (Out.cat (Out.drop body.ext υ)))
  /-- An iteration whose body halts or breaks the invariant. -/
  | loopStop {Γ Γ₁ : Ctx} {σ : State C Γ} {a : LoopAnn C Γ} {c : Val C Γ .bool}
      {body : Prog C Γ Γ₁} {o : COut C σ.H Γ₁} :
      Prog.hasTransfer body = true → c.evalT σ = .ok true → ExecP J σ body o → o.isOk = false →
        ExecS J σ (.loop a c body) (o.map (Out.drop body.ext))
  /-- A loop that pays may diverge: an over-approximation, which a box
  accepts and a diamond does not. -/
  | loopDiverge {Γ Γ₁ : Ctx} {σ : State C Γ} {a : LoopAnn C Γ} {c : Val C Γ .bool}
      {body : Prog C Γ Γ₁} :
      Prog.hasTransfer body = true → ExecS J σ (.loop a c body) (.halt .diverge)
  /-- A block that pays, statement by statement, its locals popped. -/
  | block {Γ Γ₁ : Ctx} {σ : State C Γ} {body : Prog C Γ Γ₁} {o : COut C σ.H Γ₁} :
      Prog.hasTransfer body = true → ExecP J σ body o →
        ExecS J σ (.block body) (o.map (Out.drop body.ext))

/-- `ExecP J σ P o`: the same, for a sequence. -/
inductive ExecP (J : StateInv C) : {Γ Γ' : Ctx} → (σ : State C Γ) → Prog C Γ Γ' →
    COut C σ.H Γ' → Prop where
  | nil {Γ : Ctx} {σ : State C Γ} : ExecP J σ .nil (.ok ⟨σ, List.prefix_refl _⟩)
  | cons {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ₁} {P : Prog C Γ₁ Γ₂}
      {o₁ : Out C σ.H Γ₁} {o : COut C o₁.st.H Γ₂} :
      ExecS J σ s (.ok o₁) → ExecP J o₁.st P o → ExecP J σ (.cons s P) (o.map (Out.cat o₁))
  | halt {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ₁} {P : Prog C Γ₁ Γ₂} {e : THalt} :
      ExecS J σ s (.halt e) → ExecP J σ (.cons s P) (.halt e)
  | violated {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ₁} {P : Prog C Γ₁ Γ₂} :
      ExecS J σ s .violated → ExecP J σ (.cons s P) .violated

end

/-- `ExecF J σ κ o`: the frames after a program (`Frames.run`), with
callbacks: the rest of the program run so, a scope's locals popped. -/
inductive ExecF (J : StateInv C) {Γ₀ : Ctx} : {Γ : Ctx} → (σ : State C Γ) → Frames C Γ Γ₀ →
    COut C σ.H Γ₀ → Prop where
  | nil {σ : State C Γ₀} : ExecF J σ .nil (.ok ⟨σ, List.prefix_refl _⟩)
  | seq {Γ Γ₁ : Ctx} {σ : State C Γ} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} {o₁ : Out C σ.H Γ₁}
      {o : COut C o₁.st.H Γ₀} :
      ExecP J σ ω (.ok o₁) → ExecF J o₁.st κ o → ExecF J σ (.seq ω κ) (o.map (Out.cat o₁))
  | seqHalt {Γ Γ₁ : Ctx} {σ : State C Γ} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} {e : THalt} :
      ExecP J σ ω (.halt e) → ExecF J σ (.seq ω κ) (.halt e)
  | seqViolated {Γ Γ₁ : Ctx} {σ : State C Γ} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} :
      ExecP J σ ω .violated → ExecF J σ (.seq ω κ) .violated
  | pop {Γ Γ' : Ctx} {σ : State C Γ'} {b : BlockKind} {h : Ext Γ Γ'} {κ : Frames C Γ Γ₀}
      {o : COut C σ.H Γ₀} :
      ExecF J (σ.drop h) κ o → ExecF J σ (.pop b h κ) o
  | drop {Γ Γ' : Ctx} {σ : State C Γ'} {h : Thin Γ Γ'} {κ : Frames C Γ Γ₀} {o : COut C σ.H Γ₀} :
      ExecF J (σ.thin h) κ o → ExecF J σ (.drop h κ) o

end Solidity

namespace Solidity

open Semantics (Word lookupBy)

variable {C : Contract}

/-! ## The deterministic run is a run with callbacks -/

section Det

variable {Γ : Ctx}

/-- **A send runs as its transfer**: it halts where the transfer does, and
otherwise ends in the booking with `pv` true, or with nothing booked and `pv`
false (`sendT`, as the transaction's oracle says). -/
theorem TRun.send_cases (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) (σ : State C Γ) :
    (∃ e, TRun.transfer r a σ = .error e ∧ TRun.send pv r a σ = .error e) ∨
    ∃ o₁ : Out C σ.H Γ, TRun.transfer r a σ = .ok o₁ ∧
      (TRun.send pv r a σ = .ok ⟨o₁.st.setLocal pv (true : Bool), o₁.ext⟩ ∨
        TRun.send pv r a σ = .ok ⟨σ.setLocal pv (false : Bool), List.prefix_refl _⟩) := by
  simp only [TRun.transfer, TRun.send, bind, Except.bind]
  cases r.evalT σ with
  | error e => exact .inl ⟨e, rfl, rfl⟩
  | ok addr =>
    cases a.evalT σ with
    | error e => exact .inl ⟨e, rfl, rfl⟩
    | ok amt =>
      refine .inr ⟨_, rfl, ?_⟩
      simp only [pure, Except.pure, sendT]
      rcases lookupBy (sendKey addr amt) σ.tx.ext with _ | (_ | _ | _ | _)
      · exact .inl rfl
      · exact .inl rfl
      · exact .inr rfl
      · exact .inr rfl
      · exact .inr rfl

/-- `if` by its condition. -/
theorem TRun.ite_eval {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (h₁ : Ext Γ Γ₁) (thn : TStep C Γ Γ₁)
    (h₂ : Ext Γ Γ₂) (els : TStep C Γ Γ₂) (σ : State C Γ) :
    TRun.ite c h₁ thn h₂ els σ = match c.evalT σ with
      | .ok true => (thn σ).map (Out.drop h₁)
      | .ok false => (els σ).map (Out.drop h₂)
      | .error e => .error e := by
  unfold TRun.ite
  cases c.evalT σ with
  | error e => rfl
  | ok v => cases v <;> rfl

/-- A loop's turn, from a head over the heap `H`. -/
def TRun.loopBody {Γ₁ : Ctx} (h : Ext Γ Γ₁) (body : TStep C Γ Γ₁) (H : HTy) :
    Out C H Γ → TRes (Out C H Γ) :=
  fun o => (body o.st).map fun o' => ⟨o'.st.drop h, o.ext.trans o'.ext⟩

theorem TRun.loop_eq {Γ₁ : Ctx} (c : Val C Γ .bool) (h : Ext Γ Γ₁) (body : TStep C Γ Γ₁)
    (σ : State C Γ) :
    TRun.loop c h body σ =
      TLoop.run (TRun.loopBody h body σ.H) (fun o => c.evalT o.st) ⟨σ, List.prefix_refl _⟩ := rfl

/-- A loop from a head reached over a grown heap runs as the loop from that
head, the growth carried (`TLoop.iterN_map`). -/
theorem TRun.loop_iterN_cat {Γ₁ : Ctx} (c : Val C Γ .bool) (h : Ext Γ Γ₁) (body : TStep C Γ Γ₁)
    {H : HTy} (o₀ : Out C H Γ) (n : Nat) :
    TLoop.iterN (TRun.loopBody h body H) (fun o => c.evalT o.st) n o₀ =
      Sum.map (Out.cat o₀) (Except.map (Out.cat o₀))
        (TLoop.iterN (TRun.loopBody h body o₀.st.H) (fun o => c.evalT o.st) n
          ⟨o₀.st, List.prefix_refl _⟩) :=
  TLoop.iterN_map (body := TRun.loopBody h body o₀.st.H) (c := fun o => c.evalT o.st)
    (body' := TRun.loopBody h body H) (c' := fun o => c.evalT o.st) (Out.cat o₀) (fun _ => rfl)
    (fun o => by
      dsimp only [TRun.loopBody, Out.cat]
      cases body o.st <;> rfl) n ⟨o₀.st, List.prefix_refl _⟩

mutual

/-- **The run `Stmt.run` makes is a callback run**, the callee changing
nothing, unless it leaves `J` broken on the way. -/
theorem Stmt.exec_run (J : StateInv C) : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → ∀ σ : State C Γ,
    ExecS J σ s (.ofRes (s.run σ)) ∨ ExecS J σ s .violated
  | _, _, .transfer r a, σ => by
    show ExecS J σ _ (.ofRes (TRun.transfer r a σ)) ∨ _
    cases h : TRun.transfer r a σ with
    | error e => exact .inl (.transferHalt h)
    | ok o₁ =>
      by_cases hI : J.at o₁.st
      · exact .inl (ExecS.transferResume (st := o₁.st.storage) (nt := o₁.st.net) h hI hI)
      · exact .inr (.transferViolated h hI)
  | _, _, .send pv r a, σ => by
    show ExecS J σ _ (.ofRes (TRun.send pv r a σ)) ∨ _
    rcases TRun.send_cases pv r a σ with ⟨e, ht, hs⟩ | ⟨o₁, ht, hs | hs⟩
    · rw [hs]; exact .inl (.sendHalt ht)
    · rw [hs]
      by_cases hI : J.at o₁.st
      · exact .inl (ExecS.sendResume (st := o₁.st.storage) (nt := o₁.st.net) ht hI hI)
      · exact .inr (.sendViolated ht hI)
    · rw [hs]; exact .inl (.sendFailed ht)
  | _, _, .ite c thn els, σ => by
    show ExecS J σ _ (.ofRes (TRun.ite c thn.ext thn.runR els.ext els.runR σ)) ∨ _
    rw [TRun.ite_eval]
    cases hc : c.evalT σ with
    | error e => exact .inl (.iteHalt hc)
    | ok b =>
      cases b with
      | true =>
        dsimp only
        rw [← COut.map_ofRes]
        rcases Prog.exec_run J thn σ with h | h
        · exact .inl (.iteThen hc h)
        · exact .inr (.iteThen (o := .violated) hc h)
      | false =>
        dsimp only
        rw [← COut.map_ofRes]
        rcases Prog.exec_run J els σ with h | h
        · exact .inl (.iteElse hc h)
        · exact .inr (.iteElse (o := .violated) hc h)
  | _, _, .call f args ret body, σ => by
    show ExecS J σ _ (.ofRes (TRun.call args ret body.ext body.runR σ)) ∨ _
    rw [TRun.call_eq]
    cases ha : args.evalT σ with
    | error e => exact .inl (.callArgs ha)
    | ok a =>
      show ExecS J σ _
        (.ofRes (TRun.callFrom ret body.ext body.runR σ (ret.enterT (σ.withEnv a)))) ∨ _
      rw [TRun.callFrom_eq, ← COut.map_ofRes]
      rcases Prog.exec_run J body (ret.enterT (σ.withEnv a)).st with h | h
      · exact .inl (ExecS.callBody (f := f) ha h)
      · exact .inr (ExecS.callBody (f := f) (o := .violated) ha h)
  | _, _, .callReceiver f args r body op, σ => by
    have hc : ExecS J σ (.call f args (.storage _ r) body)
        (.ofRes (TRun.call args (.storage _ r) body.ext body.runR σ)) ∨
        ExecS J σ (.call f args (.storage _ r) body) .violated := by
      rw [TRun.call_eq]
      cases ha : args.evalT σ with
      | error e => exact .inl (.callArgs ha)
      | ok a =>
        change ExecS J σ _ (.ofRes (TRun.callFrom (.storage _ r) body.ext body.runR σ
          ⟨σ.withEnv (none, a), List.prefix_refl _⟩)) ∨ _
        rw [TRun.callFrom_eq, ← COut.map_ofRes]
        rcases Prog.exec_run J body (σ.withEnv (none, a)) with h | h
        · exact .inl (ExecS.callBody (f := f) ha h)
        · exact .inr (ExecS.callBody (f := f) (o := .violated) ha h)
    rcases hc with h | h
    · exact .inl (by
        simpa only [COut.receiverOp_of_call] using (ExecS.callReceiver (op := op) h))
    · exact .inr (ExecS.callReceiver (op := op) h)
  | _, _, .callReceiverPush f args r body code value, σ => by
    change ExecS J σ _ (.ofRes (TRun.callReceiverPush args r body.ext body.runR
      code.ext code.runR value σ)) ∨ _
    have hc : ExecS J σ (.call f args (.storage _ r) body)
        (.ofRes (TRun.call args (.storage _ r) body.ext body.runR σ)) ∨
        ExecS J σ (.call f args (.storage _ r) body) .violated := by
      rw [TRun.call_eq]
      cases ha : args.evalT σ with
      | error e => exact .inl (.callArgs ha)
      | ok a =>
        change ExecS J σ _ (.ofRes (TRun.callFrom (.storage _ r) body.ext body.runR σ
          ⟨σ.withEnv (none, a), List.prefix_refl _⟩)) ∨ _
        rw [TRun.callFrom_eq, ← COut.map_ofRes]
        rcases Prog.exec_run J body (σ.withEnv (none, a)) with h | h
        · exact .inl (ExecS.callBody (f := f) ha h)
        · exact .inr (ExecS.callBody (f := f) (o := .violated) ha h)
    rcases hc with h | h
    · cases hg : TRun.call args (.storage _ r) body.ext body.runR σ with
      | error err =>
        rw [hg] at h
        exact .inl (by
          simpa only [TRun.callReceiverPush, hg, bind, Except.bind,
            COut.ofRes] using (ExecS.callReceiverPushHalt (code := code) (value := value) h))
      | ok a =>
        rw [hg] at h
        cases hp : a.st.env.1 with
        | none =>
          exact .inl (by
            simpa only [TRun.callReceiverPush, hg,
              TRun.afterReceiverPrefix, SPath.resolveT, TEnv.get, hp, bind, Except.bind,
              Except.map, COut.ofRes] using
              (ExecS.callReceiverPushUnset (code := code) (value := value) h hp))
        | some ref =>
          rcases Prog.exec_run J code (a.st.drop (.push .refl)) with hu | hu
          · exact .inl (by
              simpa only [TRun.callReceiverPush, hg,
                TRun.afterReceiverPrefix, SPath.resolveT, TEnv.get, hp, bind, Except.bind,
                COut.pushPrefix_ofRes, Prog.run, COut.map_ofRes] using
                (ExecS.callReceiverPush (value := value) h hp hu))
          · exact .inr (ExecS.callReceiverPush (value := value) h hp hu)
    · exact .inr (ExecS.callReceiverPushViolated (code := code) (value := value) h)
  | _, _, .tryCall call rets ok err code pnc other, σ => by
    show ExecS J σ _ (.ofRes (TRun.tryCall call rets ok.ext ok.runR err.ext err.runR code
      pnc.ext pnc.runR other.ext other.runR σ)) ∨ _
    unfold TRun.tryCall
    rcases lookupBy (call.keyT σ) σ.tx.ext with _ | (vs | _ | v | _)
    · exact .inl .tryRevert
    · dsimp only
      cases hd : rets.decodeT (C := C) (H := σ.H) vs with
      | error e => exact .inl (.tryDecode hd)
      | ok p =>
        obtain ⟨r, rest⟩ := p
        simp only [bind, Except.bind]
        by_cases hI : J.at σ
        · rw [← COut.map_ofRes]
          rcases Prog.exec_run J ok (σ.withEnv (TEnv.append _ r σ.env)) with h | h
          · exact .inl (ExecS.tryOk (st := σ.storage) (nt := σ.net) hI hI hd h)
          · exact .inr (ExecS.tryOk (st := σ.storage) (nt := σ.net) (o := .violated) hI hI hd h)
        · exact .inr (.tryViolated hI)
    · rw [← COut.map_ofRes]
      rcases Prog.exec_run J err σ with h | h
      · exact .inl (.tryError h)
      · exact .inr (.tryError (o := .violated) h)
    · dsimp only
      rw [← COut.map_ofRes]
      rcases Prog.exec_run J pnc (σ.withEnv (TEnv.append _ (code.decodeT v) σ.env)) with h | h
      · exact .inl (.tryPanic h)
      · exact .inr (.tryPanic (o := .violated) h)
    · rw [← COut.map_ofRes]
      rcases Prog.exec_run J other σ with h | h
      · exact .inl (.tryOther h)
      · exact .inr (.tryOther (o := .violated) h)
  | Γ, _, .loop a c body, σ => by
    cases ht : Prog.hasTransfer body with
    | false => exact .inl (.det (by simp only [Stmt.forks, ht]))
    | true =>
      show ExecS J σ _ (.ofRes (TRun.loop c body.ext body.runR σ)) ∨ _
      rw [TRun.loop_eq]
      have key : ∀ (n : Nat) (τ : State C Γ) (r : TRes (Out C τ.H Γ)),
          TLoop.iterN (TRun.loopBody body.ext body.runR τ.H) (fun o => c.evalT o.st) n
              ⟨τ, List.prefix_refl _⟩ = .inr r →
            ExecS J τ (.loop a c body) (.ofRes r) ∨ ExecS J τ (.loop a c body) .violated := by
        intro n
        induction n with
        | zero => intro τ r hn; simp only [TLoop.iterN, reduceCtorEq] at hn
        | succ n ih =>
          intro τ r hn
          simp only [TLoop.iterN, TLoop.step] at hn
          cases hc : c.evalT τ with
          | error e =>
            rw [hc] at hn; cases hn
            exact .inl (.loopHalt ht hc)
          | ok b =>
            cases b with
            | false =>
              rw [hc] at hn; cases hn
              exact .inl (.loopExit ht hc)
            | true =>
              rw [hc] at hn
              simp only [TRun.loopBody] at hn
              rcases Prog.exec_run J body τ with h | h
              · change ExecP J τ body (.ofRes (body.runR τ)) at h
                cases hr : body.runR τ with
                | error e =>
                  rw [hr] at hn h
                  cases hn
                  exact .inl (.loopStop (o := .halt e) ht hc h rfl)
                | ok o' =>
                  rw [hr] at hn h
                  have hn' : TLoop.iterN (TRun.loopBody body.ext body.runR τ.H)
                      (fun o => c.evalT o.st) n (Out.drop body.ext o') = .inr r := hn
                  rw [TRun.loop_iterN_cat c body.ext body.runR (Out.drop body.ext o') n] at hn'
                  cases hi : TLoop.iterN
                      (TRun.loopBody body.ext body.runR (Out.drop body.ext o').st.H)
                      (fun o => c.evalT o.st) n ⟨(Out.drop body.ext o').st, List.prefix_refl _⟩ with
                  | inl => rw [hi] at hn'; cases hn'
                  | inr r'' =>
                    rw [hi] at hn'
                    cases hn'
                    rw [← COut.map_ofRes]
                    rcases ih _ r'' hi with h' | h'
                    · exact .inl (.loopIter ht hc h h')
                    · exact .inr (.loopIter (o := .violated) ht hc h h')
              · exact .inr (.loopStop (o := .violated) ht hc h rfl)
      by_cases hex : ∃ r n, TLoop.iterN (TRun.loopBody body.ext body.runR σ.H)
          (fun o => c.evalT o.st) n ⟨σ, List.prefix_refl _⟩ = .inr r
      · obtain ⟨r, n, hn⟩ := hex
        rw [TLoop.run_of_iterN hn]
        exact key n σ r hn
      · have : TLoop.run (TRun.loopBody body.ext body.runR σ.H) (fun o => c.evalT o.st)
            ⟨σ, List.prefix_refl _⟩ = .error .diverge := by
          simp only [TLoop.run, hex, dite_false]
        rw [this]
        exact .inl (.loopDiverge ht)
  | _, _, .block body, σ => by
    cases ht : Prog.hasTransfer body with
    | false => exact .inl (.det (by simp only [Stmt.forks, ht]))
    | true =>
      show ExecS J σ _ (.ofRes ((body.runR σ).map (Out.drop body.ext))) ∨ _
      rw [← COut.map_ofRes]
      rcases Prog.exec_run J body σ with h | h
      · exact .inl (.block ht h)
      · exact .inr (.block (o := .violated) ht h)
  | _, _, .assign .., _ | _, _, .rebind .., _ | _, _, .assignLocal .., _ | _, _, .declLocal .., _
  | _, _, .declStorage .., _ | _, _, .opAssign .., _ | _, _, .incDec .., _
  | _, _, .assignIncDec .., _ | _, _, .assignLocalPush .., _ | _, _, .push .., _
  | _, _, .pushOpAssign .., _ | _, _, .pushIncDec .., _
  | _, _, .pop .., _ | _, _, .declMem .., _
  | _, _, .rebindMem .., _ | _, _, .assignFromMem .., _ | _, _, .assignMem .., _
  | _, _, .delete .., _ | _, _, .deleteMem .., _ | _, _, .assignNew .., _ | _, _, .require .., _
  | _, _, .assert .., _ | _, _, .revert, _ => .inl (.det rfl)

/-- The same, for a sequence. -/
theorem Prog.exec_run (J : StateInv C) : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → ∀ σ : State C Γ,
    ExecP J σ P (.ofRes (Prog.run σ P)) ∨ ExecP J σ P .violated
  | _, _, .nil, _ => .inl .nil
  | _, _, .cons s P, σ => by
    rcases Stmt.exec_run J s σ with h | h
    · cases hs : Stmt.run σ s with
      | error e =>
        rw [hs] at h
        show ExecP J σ _ (.ofRes (TRun.seq s.runR P.runR σ)) ∨ _
        unfold TRun.seq
        rw [show s.runR σ = .error e from hs]
        exact .inl (.halt h)
      | ok o₁ =>
        rw [hs] at h
        rw [Prog.run_cons_ok hs, ← COut.map_ofRes]
        rcases Prog.exec_run J P o₁.st with h' | h'
        · exact .inl (.cons h h')
        · exact .inr (.cons (o := .violated) h h')
    · exact .inr (.violated h)

end

/-- The same, for the frames after a program. -/
theorem Frames.exec_run (J : StateInv C) {Γ₀ : Ctx} : {Γ : Ctx} → (κ : Frames C Γ Γ₀) →
    ∀ σ : State C Γ, ExecF J σ κ (.ofRes (κ.run σ)) ∨ ExecF J σ κ .violated
  | _, .nil, _ => .inl .nil
  | _, .seq ω κ, σ => by
    show ExecF J σ _ (.ofRes (TRun.seq (fun τ => Prog.run τ ω) (fun τ => Frames.run τ κ) σ)) ∨ _
    unfold TRun.seq
    dsimp only
    rcases Prog.exec_run J ω σ with h | h
    · cases hs : Prog.run σ ω with
      | error e => rw [hs] at h; exact .inl (.seqHalt h)
      | ok o₁ =>
        rw [hs] at h
        dsimp only
        rw [← COut.map_ofRes]
        rcases Frames.exec_run J κ o₁.st with h' | h'
        · exact .inl (.seq h h')
        · exact .inr (.seq (o := .violated) h h')
    · exact .inr (.seqViolated h)
  | _, .pop _ h κ, σ => (Frames.exec_run J κ (σ.drop h)).imp .pop .pop
  | _, .drop h κ, σ => (Frames.exec_run J κ (σ.thin h)).imp .drop .drop

end Det

/-! ## With no payment, the run is the deterministic one -/

section NoPay

mutual

/-- **A statement that pays nothing has one callback run**, the
deterministic one. -/
theorem Stmt.eq_run (J : StateInv C) : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') →
    Stmt.hasTransfer s = false → ∀ {σ : State C Γ} {o : COut C σ.H Γ'}, ExecS J σ s o →
      o = .ofRes (s.run σ)
  | _, _, .transfer .., ht, _, _, _ | _, _, .send .., ht, _, _, _
  | _, _, .tryCall .., ht, _, _, _ => by simp only [Stmt.hasTransfer, Bool.true_eq_false] at ht
  | _, _, .ite c thn els, ht, σ, _, h => by
    simp only [Stmt.hasTransfer, Bool.or_eq_false_iff] at ht
    cases h with
    | det _ => rfl
    | iteHalt hc =>
      show _ = COut.ofRes (TRun.ite _ _ _ _ _ _)
      rw [TRun.ite_eval, hc]
      rfl
    | iteThen hc h =>
      rw [Prog.eq_run J thn ht.1 h]
      show _ = COut.ofRes (TRun.ite _ _ _ _ _ _)
      rw [TRun.ite_eval, hc]
      exact COut.map_ofRes _ _
    | iteElse hc h =>
      rw [Prog.eq_run J els ht.2 h]
      show _ = COut.ofRes (TRun.ite _ _ _ _ _ _)
      rw [TRun.ite_eval, hc]
      exact COut.map_ofRes _ _
  | _, _, .call f args ret body, ht, σ, _, h => by
    simp only [Stmt.hasTransfer] at ht
    cases h with
    | det _ => rfl
    | callArgs ha =>
      show _ = COut.ofRes (TRun.call _ _ _ _ _)
      rw [TRun.call_eq, ha]
      rfl
    | @callBody _ _ _ _ _ _ _ _ _ _ a _ ha h =>
      rw [Prog.eq_run J body ht h]
      show _ = COut.ofRes (TRun.call _ _ _ _ _)
      rw [TRun.call_eq, ha]
      show _ = COut.ofRes (TRun.callFrom ret body.ext body.runR σ (ret.enterT (σ.withEnv a)))
      rw [TRun.callFrom_eq, COut.map_ofRes]
  | _, _, .callReceiver f args r body op, ht, σ, _, h => by
    cases h with
    | det _ => rfl
    | callReceiver hc =>
      have he : ∀ {o}, ExecS J σ (.call f args (.storage _ r) body) o →
          o = COut.ofRes (TRun.call args (.storage _ r) body.ext body.runR σ) := by
        intro o h
        cases h with
        | det _ => rfl
        | callArgs ha =>
          rw [TRun.call_eq, ha]
          rfl
        | @callBody _ _ _ _ _ _ _ _ _ _ a _ ha hp =>
          rw [Prog.eq_run J body ht hp]
          rw [TRun.call_eq, ha]
          simp only [bind, Except.bind, TRun.callFrom_eq, COut.map_ofRes]
      rw [he hc]
      exact COut.receiverOp_of_call args r body.ext body.runR op σ
  | _, _, .callReceiverPush f args r body code value, ht, σ, _, h => by
    obtain ⟨hb, hp⟩ := Bool.or_eq_false_iff.mp ht
    have he : ∀ {o}, ExecS J σ (.call f args (.storage _ r) body) o →
        o = COut.ofRes (TRun.call args (.storage _ r) body.ext body.runR σ) := by
      intro o hc
      cases hc with
      | det _ => rfl
      | callArgs ha => rw [TRun.call_eq, ha]; rfl
      | @callBody _ _ _ _ _ _ _ _ _ _ a _ ha hc =>
        rw [Prog.eq_run J body hb hc, TRun.call_eq, ha]
        simp only [bind, Except.bind, TRun.callFrom_eq, COut.map_ofRes]
    change _ = COut.ofRes (TRun.callReceiverPush args r body.ext body.runR
      code.ext code.runR value σ)
    cases h with
    | det _ => rfl
    | @callReceiverPush _ _ _ _ _ _ _ _ _ _ _ _ a ref u hc hr hu =>
      have hg := he hc
      cases ht : TRun.call args (.storage _ r) body.ext body.runR σ with
      | error err => rw [ht] at hg; cases hg
      | ok a' =>
        rw [ht] at hg
        have ha : a = a' := COut.ok.inj hg
        subst a'
        rw [Prog.eq_run J code hp hu, COut.pushPrefix_ofRes, COut.map_ofRes]
        simp only [TRun.callReceiverPush, ht, TRun.afterReceiverPrefix,
          SPath.resolveT, TEnv.get, hr, bind, Except.bind]
    | @callReceiverPushUnset _ _ _ _ _ _ _ _ _ _ _ _ a hc hr =>
      have hg := he hc
      cases ht : TRun.call args (.storage _ r) body.ext body.runR σ with
      | error err => rw [ht] at hg; cases hg
      | ok a' =>
        rw [ht] at hg
        have ha : a = a' := COut.ok.inj hg
        subst a'
        simp only [TRun.callReceiverPush, ht, TRun.afterReceiverPrefix,
          SPath.resolveT, TEnv.get, hr, bind, Except.bind, Except.map, COut.ofRes]
    | callReceiverPushHalt hc =>
      have hg := he hc
      cases ht : TRun.call args (.storage _ r) body.ext body.runR σ <;>
        simp only [ht, COut.ofRes] at hg
      · cases hg
        simp only [TRun.callReceiverPush, ht, bind, Except.bind, COut.ofRes]
      · cases hg
    | callReceiverPushViolated hc =>
      have hg := he hc
      cases ht : TRun.call args (.storage _ r) body.ext body.runR σ <;>
        simp only [ht, COut.ofRes] at hg <;> cases hg
  | _, _, .loop _ _ body, ht, _, _, h => by
    simp only [Stmt.hasTransfer] at ht
    cases h with
    | det _ => rfl
    | loopHalt hb _ | loopExit hb _ | loopIter hb _ _ _ | loopStop hb _ _ _ | loopDiverge hb =>
      rw [hb] at ht; cases ht
  | _, _, .block body, ht, _, _, h => by
    simp only [Stmt.hasTransfer] at ht
    cases h with
    | det _ => rfl
    | block hb _ => rw [hb] at ht; cases ht
  | _, _, .assign .., _, _, _, h | _, _, .rebind .., _, _, _, h
  | _, _, .assignLocal .., _, _, _, h | _, _, .declLocal .., _, _, _, h
  | _, _, .declStorage .., _, _, _, h | _, _, .opAssign .., _, _, _, h
  | _, _, .incDec .., _, _, _, h | _, _, .assignIncDec .., _, _, _, h
  | _, _, .assignLocalPush .., _, _, _, h
  | _, _, .pushOpAssign .., _, _, _, h | _, _, .pushIncDec .., _, _, _, h
  | _, _, .push .., _, _, _, h | _, _, .pop .., _, _, _, h | _, _, .declMem .., _, _, _, h
  | _, _, .rebindMem .., _, _, _, h | _, _, .assignFromMem .., _, _, _, h
  | _, _, .assignMem .., _, _, _, h | _, _, .delete .., _, _, _, h
  | _, _, .deleteMem .., _, _, _, h | _, _, .assignNew .., _, _, _, h
  | _, _, .require .., _, _, _, h | _, _, .assert .., _, _, _, h
  | _, _, .revert, _, _, _, h => by cases h; rfl

/-- The same, for a sequence. -/
theorem Prog.eq_run (J : StateInv C) : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') →
    Prog.hasTransfer P = false → ∀ {σ : State C Γ} {o : COut C σ.H Γ'}, ExecP J σ P o →
      o = .ofRes (Prog.run σ P)
  | _, _, .nil, _, _, _, h => by cases h; rfl
  | _, _, .cons s P, ht, σ, _, h => by
    simp only [Prog.hasTransfer_cons, Bool.or_eq_false_iff] at ht
    cases h with
    | @cons _ _ _ _ _ _ o₁ _ hs hP =>
      have e₁ := Stmt.eq_run J s ht.1 hs
      have hs' : Stmt.run σ s = .ok o₁ := by
        revert e₁
        cases Stmt.run σ s with
        | error _ => exact fun e₁ => nomatch e₁
        | ok _ => intro e₁; cases e₁; rfl
      rw [Prog.run_cons_ok hs', Prog.eq_run J P ht.2 hP, COut.map_ofRes]
      rfl
    | @halt _ _ _ _ _ _ e hs =>
      have e₁ : (COut.halt e : COut C σ.H _) = COut.ofRes (s.runR σ) := Stmt.eq_run J s ht.1 hs
      show _ = COut.ofRes (TRun.seq s.runR P.runR σ)
      unfold TRun.seq
      revert e₁
      cases s.runR σ with
      | error _ => intro e₁; cases e₁; rfl
      | ok _ => exact fun e₁ => nomatch e₁
    | violated hs =>
      have e₁ := Stmt.eq_run J s ht.1 hs
      revert e₁
      cases Stmt.run σ s <;> exact fun e₁ => nomatch e₁

end

/-- **A statement that pays nothing has one callback run** (`Stmt.eq_run`). -/
theorem ExecS.eq_run {J : StateInv C} {Γ Γ' : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ'}
    {o : COut C σ.H Γ'} (h : ExecS J σ s o) (ht : Stmt.hasTransfer s = false) :
    o = .ofRes (s.run σ) :=
  Stmt.eq_run J s ht h

/-- The same, for a sequence. -/
theorem ExecP.eq_run {J : StateInv C} {Γ Γ' : Ctx} {σ : State C Γ} {P : Prog C Γ Γ'}
    {o : COut C σ.H Γ'} (h : ExecP J σ P o) (ht : Prog.hasTransfer P = false) :
    o = .ofRes (Prog.run σ P) :=
  Prog.eq_run J P ht h

/-- The same, for frames. -/
theorem ExecF.eq_run {J : StateInv C} {Γ₀ : Ctx} {Γ : Ctx} {σ : State C Γ} {κ : Frames C Γ Γ₀}
    {o : COut C σ.H Γ₀} (h : ExecF J σ κ o) (ht : κ.hasTransfer = false) :
    o = .ofRes (κ.run σ) := by
  induction h with
  | nil => rfl
  | @seq _ _ σ ω κ o₁ _ hω _ ih =>
    simp only [Frames.hasTransfer_seq, Bool.or_eq_false_iff] at ht
    have e₁ := ExecP.eq_run hω ht.1
    have hs : Prog.run σ ω = .ok o₁ := by
      revert e₁
      cases Prog.run σ ω with
      | error _ => exact fun e₁ => nomatch e₁
      | ok _ => intro e₁; cases e₁; rfl
    show _ = COut.ofRes (TRun.seq (fun τ => Prog.run τ ω) (fun τ => Frames.run τ κ) σ)
    unfold TRun.seq
    dsimp only
    rw [hs, ih ht.2, COut.map_ofRes]
    rfl
  | @seqHalt _ _ σ ω κ _ hω =>
    simp only [Frames.hasTransfer_seq, Bool.or_eq_false_iff] at ht
    have e₁ := ExecP.eq_run hω ht.1
    show _ = COut.ofRes (TRun.seq (fun τ => Prog.run τ ω) (fun τ => Frames.run τ κ) σ)
    unfold TRun.seq
    dsimp only
    revert e₁
    cases Prog.run σ ω with
    | error _ => intro e₁; cases e₁; rfl
    | ok _ => exact fun e₁ => nomatch e₁
  | @seqViolated _ _ σ ω κ hω =>
    simp only [Frames.hasTransfer_seq, Bool.or_eq_false_iff] at ht
    have e₁ := ExecP.eq_run hω ht.1
    revert e₁
    cases Prog.run σ ω <;> exact fun e₁ => nomatch e₁
  | pop _ ih => exact ih ht
  | drop _ ih => exact ih ht

/-- **With no payment, a property of every callback run of a sequence is one
of its deterministic run.** -/
theorem ExecP.forall_iff {J : StateInv C} {Γ Γ' : Ctx} {σ : State C Γ} {P : Prog C Γ Γ'}
    (hP : Prog.hasTransfer P = false) (Q : COut C σ.H Γ' → Prop) :
    (∀ o, ExecP J σ P o → Q o) ↔ Q (.ofRes (Prog.run σ P)) := by
  refine ⟨fun H => ?_, fun H o h => ExecP.eq_run h hP ▸ H⟩
  rcases Prog.exec_run J P σ with h | h
  · exact H _ h
  · have e := ExecP.eq_run h hP
    revert e
    cases Prog.run σ P <;> exact fun e => nomatch e

/-- The same, for frames. -/
theorem ExecF.forall_iff {J : StateInv C} {Γ₀ Γ : Ctx} {σ : State C Γ} {κ : Frames C Γ Γ₀}
    (hκ : κ.hasTransfer = false) (Q : COut C σ.H Γ₀ → Prop) :
    (∀ o, ExecF J σ κ o → Q o) ↔ Q (.ofRes (κ.run σ)) := by
  refine ⟨fun H => ?_, fun H o h => ExecF.eq_run h hκ ▸ H⟩
  rcases Frames.exec_run J κ σ with h | h
  · exact H _ h
  · have e := ExecF.eq_run h hκ
    revert e
    cases κ.run σ <;> exact fun e => nomatch e

end NoPay

end Solidity
