import Solidity.Calculus.Core.Logic

/-!
# The callback semantics of `transfer`, scoped

`Semantics/Callback.lean`'s relational layer over the scoped run
(`docs/intrinsic.md`, M6b): `ExecS I σ s o` runs `s : Stmt C Γ Γ'` from
`σ : State C Γ` exactly as `Stmt.run` does, except where control leaves the
contract (a `transfer`, a `send`, a `try`), where the run either leaves it
with the invariant `I` broken (`violated`) or resumes in any state the callee
may leave (`State.havoc`: storage and ledger replaced) that satisfies `I`.
A loop or a block whose body pays runs iteration by iteration, statement by
statement; a loop that pays may diverge.  `holdsC I` reads the modalities
over it, a modality's frames (`Frames`) included.

What the scoped types settle, which today's layer had to state:

* **The invariant is closed by its type**: `Invariant.fml : Fml C []`, read
  on the state's global part (`Invariant.at`), so no `I.vars = []`
  hypothesis, and no frame lemma for it: the callee has none of the
  contract's locals, and the formula cannot name one.
* **No stuck arms**: a condition is read as a Boolean (`Val.evalB`), whose
  failure, a halt or a word where a Boolean stands, is one halt
  (`iteHalt`, `loopHalt`), so there is no `iteStuck`/`loopStuck`.  When
  values are typed (M4) the word case goes from `evalB` alone.
* **A scope's end is the run's**: a branch, a block, a loop body or a
  callee's frame pops its locals on every outcome (`COut.map`), as
  `Run.ite`/`Run.block`/`Run.call` do.

Proved: the deterministic run is one of the callback runs, unless the
invariant breaks (`Prog.exec_run`), so a modal formula valid with callbacks
is valid without (`holds_of_holdsC_modal`, `valid_of_validC`); with no
payment in a program, its only callback run is the deterministic one
(`ExecP.eq_run`), so the two readings agree on a formula with none
(`holdsC_iff_holds`).
-/

namespace Solidity.Core

open Semantics (Value SVal Halt Res lookupBy)
open Solidity (Modality)

variable {C : Contract}

/-! ## Outcomes -/

/-- How a run with callbacks ends: in a state of the context `Γ`, halted,
or leaving the contract with its invariant broken. -/
inductive COut (C : Contract) (Γ : Ctx) where
  | ok (σ : State C Γ)
  | halt (e : Halt)
  | violated

namespace COut

variable {Γ Δ : Ctx}

/-- The outcome of a deterministic run. -/
def ofRes : Res (State C Γ) → COut C Γ
  | .ok σ => .ok σ
  | .error e => .halt e

def isOk : COut C Γ → Bool
  | .ok _ => true
  | _ => false

/-- The state an outcome ends in, mapped (a scope's locals popped). -/
def map (f : State C Γ → State C Δ) : COut C Γ → COut C Δ
  | .ok σ => .ok (f σ)
  | .halt e => .halt e
  | .violated => .violated

/-- `p` after a run under `m`: of the state it ends in, `m.onHalt` of a halt
that is not a panic, and never of a panic or of a broken invariant. -/
def after (m : Modality) (p : State C Γ → Prop) : COut C Γ → Prop
  | .ok τ => p τ
  | .halt e => m.onHalt ∧ e ≠ .panic
  | .violated => False

theorem after_ofRes (m : Modality) (p : State C Γ → Prop) (r : Res (State C Γ)) :
    (ofRes r).after m p ↔ m.afterRunC p r := by
  cases r with
  | ok τ => exact ⟨fun h => ⟨h, nofun⟩, fun h => h.1⟩
  | error e =>
    exact ⟨fun h => ⟨h.1, fun h' => h.2 (Except.error.inj h')⟩,
      fun h => ⟨h.1, fun h' => h.2 (h' ▸ rfl)⟩⟩

theorem map_ofRes (f : State C Γ → State C Δ) (r : Res (State C Γ)) :
    (ofRes r).map f = ofRes (r.map f) := by
  cases r <;> rfl

theorem isOk_map (f : State C Γ → State C Δ) (o : COut C Γ) : (o.map f).isOk = o.isOk := by
  cases o <;> rfl

end COut

/-! ## The invariant, the callee, a condition -/

/-- A contract invariant: a formula over the contract's state, with no local
by its type (solkey's `CInv(storage, net)`). -/
structure Invariant (C : Contract) where
  fml : Fml C []

/-- The invariant holds of the global part of `σ`. -/
def Invariant.at {Γ : Ctx} (I : Invariant C) (σ : State C Γ) : Prop :=
  holds (σ.withEnv (Γ := Γ) (Δ := []) ()) I.fml

/-- The state after a callback: storage and ledger replaced by what the
callee left, the locals, memory and funds kept (`Semantics.State.havoc`). -/
def State.havoc {Γ : Ctx} (σ : State C Γ) (st : List (Name × SVal)) (nt : List (Int × Int)) :
    State C Γ :=
  σ.withGlob (σ.glob.havoc st nt)

/-- A callee that changes nothing. -/
theorem State.havoc_self {Γ : Ctx} (σ : State C Γ) : σ.havoc σ.storage σ.net = σ := by
  cases σ; rfl

/-- A condition read as a Boolean: a halt, or a word where a Boolean stands,
is a halt (`stuck`). -/
def Val.evalB {Γ : Ctx} (σ : State C Γ) (c : Val C Γ .bool) : Res Bool :=
  match c.eval σ with
  | .ok (.bool b) => .ok b
  | .ok (.int _) => .error .stuck
  | .error e => .error e

/-! ## Which statements the callback reading sees -/

mutual

/-- Whether a `transfer`, a `send` or a `try` occurs in the statement, in a
branch, a block, a loop or a callee included. -/
def Stmt.hasTransfer : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Bool
  | _, _, s => Stmt.casesOn (motive_1 := fun _ _ _ => Bool) s
    (assign := fun _ _ => false) (rebind := fun _ _ => false) (assignLocal := fun _ _ => false)
    (declLocal := fun _ _ _ => false) (declStorage := fun _ _ _ => false)
    (opAssign := fun _ _ _ _ _ => false) (incDec := fun _ _ _ => false)
    (assignIncDec := fun _ _ _ _ _ => false) (push := fun _ _ _ => false) (pop := fun _ => false)
    (transfer := fun _ _ => true) (send := fun _ _ _ => true)
    (declMem := fun _ _ _ _ _ => false) (rebindMem := fun _ _ => false)
    (assignFromMem := fun _ _ => false) (assignMem := fun _ _ => false)
    (delete := fun _ => false) (deleteMem := fun _ _ => false) (assignNew := fun _ _ _ => false)
    (ite := fun _ thn els => Prog.hasTransfer thn || Prog.hasTransfer els)
    (require := fun _ => false) (assert := fun _ => false) (revert := false)
    (call := fun _ _ _ body => Prog.hasTransfer body)
    (tryCall := fun _ _ _ _ _ _ _ => true)
    (loop := fun _ _ body => Prog.hasTransfer body) (block := fun body => Prog.hasTransfer body)
  termination_by structural _ _ s => s

def Prog.hasTransfer : {Γ Γ' : Ctx} → Prog C Γ Γ' → Bool
  | _, _, P => Prog.casesOn (motive_2 := fun _ _ _ => Bool) P false
      (fun s P => Stmt.hasTransfer s || Prog.hasTransfer P)
  termination_by structural _ _ P => P

end

/-- The statements the relation does not take from `Stmt.run`: a `transfer`,
a `send`, a `try`, the two that run others by a choice (`if`, a call), and
a loop or a block whose body pays. -/
def Stmt.forks {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Bool :=
  Stmt.casesOn (motive_1 := fun _ _ _ => Bool) s
    (assign := fun _ _ => false) (rebind := fun _ _ => false) (assignLocal := fun _ _ => false)
    (declLocal := fun _ _ _ => false) (declStorage := fun _ _ _ => false)
    (opAssign := fun _ _ _ _ _ => false) (incDec := fun _ _ _ => false)
    (assignIncDec := fun _ _ _ _ _ => false) (push := fun _ _ _ => false) (pop := fun _ => false)
    (transfer := fun _ _ => true) (send := fun _ _ _ => true)
    (declMem := fun _ _ _ _ _ => false) (rebindMem := fun _ _ => false)
    (assignFromMem := fun _ _ => false) (assignMem := fun _ _ => false)
    (delete := fun _ => false) (deleteMem := fun _ _ => false) (assignNew := fun _ _ _ => false)
    (ite := fun _ _ _ => true)
    (require := fun _ => false) (assert := fun _ => false) (revert := false)
    (call := fun _ _ _ _ => true)
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
    (bind := fun _ _ φ => Fml.hasTransfer φ) (anon := fun _ φ => Fml.hasTransfer φ)
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

/-- `ExecS I σ s o`: run from `σ`, `s` may end in `o` when every payment
may call back into a contract with invariant `I`. -/
inductive ExecS (I : Invariant C) : {Γ Γ' : Ctx} → State C Γ → Stmt C Γ Γ' → COut C Γ' → Prop where
  /-- A statement that runs no other by a choice and pays nothing runs as
  `Stmt.run`. -/
  | det {Γ Γ' : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ'} :
      s.forks = false → ExecS I σ s (.ofRes (s.run σ))
  /-- A transfer that halts (an amount that is not a word). -/
  | transferHalt {Γ : Ctx} {σ : State C Γ} {r a : Val C Γ .uint} {e : Halt} :
      Run.transfer r a σ = .error e → ExecS I σ (.transfer r a) (.halt e)
  /-- KeY's "invariant on exit": control leaves with `I` broken. -/
  | transferViolated {Γ : Ctx} {σ σ₁ : State C Γ} {r a : Val C Γ .uint} :
      Run.transfer r a σ = .ok σ₁ → ¬ I.at σ₁ → ExecS I σ (.transfer r a) .violated
  /-- KeY's "resume after callback": control leaves with `I` kept and comes
  back to any state the callee may leave in which `I` holds. -/
  | transferResume {Γ : Ctx} {σ σ₁ : State C Γ} {r a : Val C Γ .uint}
      {st : List (Name × SVal)} {nt : List (Int × Int)} :
      Run.transfer r a σ = .ok σ₁ → I.at σ₁ → I.at (σ₁.havoc st nt) →
        ExecS I σ (.transfer r a) (.ok (σ₁.havoc st nt))
  /-- A send that halts, where its transfer would. -/
  | sendHalt {Γ : Ctx} {σ : State C Γ} {pv : Idx Γ (.val .bool)} {r a : Val C Γ .uint} {e : Halt} :
      Run.transfer r a σ = .error e → ExecS I σ (.send pv r a) (.halt e)
  /-- KeY's "send failed": the callee reverts, nothing is booked and `pv`
  is `false`, whatever the transaction's oracle says. -/
  | sendFailed {Γ : Ctx} {σ σ₁ : State C Γ} {pv : Idx Γ (.val .bool)} {r a : Val C Γ .uint} :
      Run.transfer r a σ = .ok σ₁ → ExecS I σ (.send pv r a) (.ok (σ.setLocal pv (.bool false)))
  /-- KeY's "invariant on exit", the payment booked. -/
  | sendViolated {Γ : Ctx} {σ σ₁ : State C Γ} {pv : Idx Γ (.val .bool)} {r a : Val C Γ .uint} :
      Run.transfer r a σ = .ok σ₁ → ¬ I.at σ₁ → ExecS I σ (.send pv r a) .violated
  /-- KeY's "send succeeded": the payment booked, `I` kept, any state the
  callee may leave in which `I` holds, `pv` then `true`. -/
  | sendResume {Γ : Ctx} {σ σ₁ : State C Γ} {pv : Idx Γ (.val .bool)} {r a : Val C Γ .uint}
      {st : List (Name × SVal)} {nt : List (Int × Int)} :
      Run.transfer r a σ = .ok σ₁ → I.at σ₁ → I.at (σ₁.havoc st nt) →
        ExecS I σ (.send pv r a) (.ok ((σ₁.havoc st nt).setLocal pv (.bool true)))
  | iteHalt {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {c : Val C Γ .bool} {thn : Prog C Γ Γ₁}
      {els : Prog C Γ Γ₂} {e : Halt} :
      c.evalB σ = .error e → ExecS I σ (.ite c thn els) (.halt e)
  /-- The branch the condition picks, its locals popped. -/
  | iteThen {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {c : Val C Γ .bool} {thn : Prog C Γ Γ₁}
      {els : Prog C Γ Γ₂} {o : COut C Γ₁} :
      c.evalB σ = .ok true → ExecP I σ thn o → ExecS I σ (.ite c thn els) (o.map (State.drop thn.ext))
  | iteElse {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {c : Val C Γ .bool} {thn : Prog C Γ Γ₁}
      {els : Prog C Γ Γ₂} {o : COut C Γ₂} :
      c.evalB σ = .ok false → ExecP I σ els o → ExecS I σ (.ite c thn els) (o.map (State.drop els.ext))
  /-- A call whose arguments halt. -/
  | callArgs {Γ Γ' ps rs Γf : Ctx} {σ : State C Γ} {f : Name} {args : Args C Γ ps}
      {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf} {e : Halt} :
      args.eval σ = .error e → ExecS I σ (.call f args ret body) (.halt e)
  /-- A call whose return variables cannot be made. -/
  | callEnter {Γ Γ' ps rs Γf : Ctx} {σ : State C Γ} {f : Name} {args : Args C Γ ps}
      {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf} {a : Env C ps} {e : Halt} :
      args.eval σ = .ok a → ret.enter (C := C) σ.glob = .error e →
        ExecS I σ (.call f args ret body) (.halt e)
  /-- The body run in the callee's frame, and what the call leaves the
  caller (`Run.call`). -/
  | callBody {Γ Γ' ps rs Γf : Ctx} {σ : State C Γ} {f : Name} {args : Args C Γ ps}
      {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf} {a : Env C ps}
      {τ : Semantics.State} {r : Env C rs} {o : COut C Γf} :
      args.eval σ = .ok a → ret.enter σ.glob = .ok (τ, r) →
        ExecP I (State.ofGlob τ (Env.append rs r a)) body o →
          ExecS I σ (.call f args ret body)
            (o.map fun υ => υ.withEnv (ret.leave σ.env (Env.take rs (Env.drop body.ext υ.env))))
  /-- A `try` whose call cannot be made halts. -/
  | tryHalt {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄} {e : Halt} :
      call.key σ = .error e → ExecS I σ (.tryCall call rets ok err code pnc other) (.halt e)
  /-- The call reverts in the caller: no code at the address, or data that
  does not decode. -/
  | tryRevert {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄} {k : Semantics.ExtKey} :
      call.key σ = .ok k → ExecS I σ (.tryCall call rets ok err code pnc other) (.halt .revert)
  /-- Data that the return variables do not decode. -/
  | tryDecode {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄} {k : Semantics.ExtKey} {vs : List Value}
      {e : Halt} :
      call.key σ = .ok k → rets.decode (C := C) vs = .error e →
        ExecS I σ (.tryCall call rets ok err code pnc other) (.halt e)
  /-- KeY's "invariant on exit": control leaves with `I` broken. -/
  | tryViolated {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄} {k : Semantics.ExtKey} :
      call.key σ = .ok k → ¬ I.at σ → ExecS I σ (.tryCall call rets ok err code pnc other) .violated
  /-- KeY's "call succeeded": `I` kept, any state the callee may leave in
  which `I` holds, the return data bound, the clause run, its locals popped. -/
  | tryOk {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄} {k : Semantics.ExtKey}
      {st : List (Name × SVal)} {nt : List (Int × Int)} {vs rest : List Value} {r : Env C ρ}
      {o : COut C Γ₁} :
      call.key σ = .ok k → I.at σ → I.at (σ.havoc st nt) → rets.decode vs = .ok (r, rest) →
        ExecP I ((σ.havoc st nt).withEnv (Env.append ρ r σ.env)) ok o →
          ExecS I σ (.tryCall call rets ok err code pnc other)
            (o.map (State.drop ((Ext.append Γ ρ).trans ok.ext)))
  /-- "Error caught": the call reverted, and its effects with it. -/
  | tryError {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄} {k : Semantics.ExtKey} {o : COut C Γ₂} :
      call.key σ = .ok k → ExecP I σ err o →
        ExecS I σ (.tryCall call rets ok err code pnc other) (o.map (State.drop err.ext))
  /-- "Panic caught", with the code bound. -/
  | tryPanic {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄} {k : Semantics.ExtKey} {v : Value}
      {r : Env C κ} {o : COut C Γ₃} :
      call.key σ = .ok k → code.decode v = .ok r → ExecP I (σ.withEnv (Env.append κ r σ.env)) pnc o →
        ExecS I σ (.tryCall call rets ok err code pnc other)
          (o.map (State.drop ((Ext.append Γ κ).trans pnc.ext)))
  /-- A panic code that does not decode. -/
  | tryCode {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄} {k : Semantics.ExtKey} {v : Value}
      {e : Halt} :
      call.key σ = .ok k → code.decode (C := C) v = .error e →
        ExecS I σ (.tryCall call rets ok err code pnc other) (.halt e)
  /-- "Other failure caught". -/
  | tryOther {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄} {k : Semantics.ExtKey} {o : COut C Γ₄} :
      call.key σ = .ok k → ExecP I σ other o →
        ExecS I σ (.tryCall call rets ok err code pnc other) (o.map (State.drop other.ext))
  /-- A loop that pays, whose condition halts. -/
  | loopHalt {Γ Γ₁ : Ctx} {σ : State C Γ} {a : LoopAnn C Γ} {c : Val C Γ .bool}
      {body : Prog C Γ Γ₁} {e : Halt} :
      Prog.hasTransfer body = true → c.evalB σ = .error e → ExecS I σ (.loop a c body) (.halt e)
  /-- The condition is false: the loop ends where it is. -/
  | loopExit {Γ Γ₁ : Ctx} {σ : State C Γ} {a : LoopAnn C Γ} {c : Val C Γ .bool}
      {body : Prog C Γ Γ₁} :
      Prog.hasTransfer body = true → c.evalB σ = .ok false → ExecS I σ (.loop a c body) (.ok σ)
  /-- One iteration, its locals popped, and the loop again. -/
  | loopIter {Γ Γ₁ : Ctx} {σ : State C Γ} {υ : State C Γ₁} {a : LoopAnn C Γ} {c : Val C Γ .bool}
      {body : Prog C Γ Γ₁} {o : COut C Γ} :
      Prog.hasTransfer body = true → c.evalB σ = .ok true → ExecP I σ body (.ok υ) →
        ExecS I (υ.drop body.ext) (.loop a c body) o → ExecS I σ (.loop a c body) o
  /-- An iteration whose body halts or breaks the invariant. -/
  | loopStop {Γ Γ₁ : Ctx} {σ : State C Γ} {a : LoopAnn C Γ} {c : Val C Γ .bool}
      {body : Prog C Γ Γ₁} {o : COut C Γ₁} :
      Prog.hasTransfer body = true → c.evalB σ = .ok true → ExecP I σ body o → o.isOk = false →
        ExecS I σ (.loop a c body) (o.map (State.drop body.ext))
  /-- A loop that pays may diverge: an over-approximation, which a box
  accepts and a diamond does not. -/
  | loopDiverge {Γ Γ₁ : Ctx} {σ : State C Γ} {a : LoopAnn C Γ} {c : Val C Γ .bool}
      {body : Prog C Γ Γ₁} :
      Prog.hasTransfer body = true → ExecS I σ (.loop a c body) (.halt .diverge)
  /-- A block that pays, statement by statement, its locals popped. -/
  | block {Γ Γ₁ : Ctx} {σ : State C Γ} {body : Prog C Γ Γ₁} {o : COut C Γ₁} :
      Prog.hasTransfer body = true → ExecP I σ body o →
        ExecS I σ (.block body) (o.map (State.drop body.ext))

/-- `ExecP I σ P o`: the same, for a sequence. -/
inductive ExecP (I : Invariant C) : {Γ Γ' : Ctx} → State C Γ → Prog C Γ Γ' → COut C Γ' → Prop where
  | nil {Γ : Ctx} {σ : State C Γ} : ExecP I σ .nil (.ok σ)
  | cons {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {σ₁ : State C Γ₁} {s : Stmt C Γ Γ₁} {P : Prog C Γ₁ Γ₂}
      {o : COut C Γ₂} :
      ExecS I σ s (.ok σ₁) → ExecP I σ₁ P o → ExecP I σ (.cons s P) o
  | halt {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ₁} {P : Prog C Γ₁ Γ₂} {e : Halt} :
      ExecS I σ s (.halt e) → ExecP I σ (.cons s P) (.halt e)
  | violated {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ₁} {P : Prog C Γ₁ Γ₂} :
      ExecS I σ s .violated → ExecP I σ (.cons s P) .violated

end

/-- `ExecF I σ κ o`: the frames after a program (`Frames.run`), with
callbacks: the rest of the program run so, a scope's locals popped. -/
inductive ExecF (I : Invariant C) {Γ₀ : Ctx} : {Γ : Ctx} → State C Γ → Frames C Γ Γ₀ → COut C Γ₀ → Prop where
  | nil {σ : State C Γ₀} : ExecF I σ .nil (.ok σ)
  | seq {Γ Γ₁ : Ctx} {σ : State C Γ} {σ₁ : State C Γ₁} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀}
      {o : COut C Γ₀} :
      ExecP I σ ω (.ok σ₁) → ExecF I σ₁ κ o → ExecF I σ (.seq ω κ) o
  | seqHalt {Γ Γ₁ : Ctx} {σ : State C Γ} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} {e : Halt} :
      ExecP I σ ω (.halt e) → ExecF I σ (.seq ω κ) (.halt e)
  | seqViolated {Γ Γ₁ : Ctx} {σ : State C Γ} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} :
      ExecP I σ ω .violated → ExecF I σ (.seq ω κ) .violated
  | pop {Γ Γ' : Ctx} {σ : State C Γ'} {b : BlockKind} {h : Ext Γ Γ'} {κ : Frames C Γ Γ₀}
      {o : COut C Γ₀} :
      ExecF I (σ.drop h) κ o → ExecF I σ (.pop b h κ) o
  | drop {Γ Γ' : Ctx} {σ : State C Γ'} {h : Thin Γ Γ'} {κ : Frames C Γ Γ₀} {o : COut C Γ₀} :
      ExecF I (σ.thin h) κ o → ExecF I σ (.drop h κ) o

/-! ## Formulas read with callbacks -/

/-- Whether `φ` holds in `σ` when every payment may call back into a
contract with invariant `I`: `holds`, but a modality ranges over every run
with callbacks of its program and then its frames, and none of them may
break `I`. -/
def holdsC (I : Invariant C) : {Γ : Ctx} → State C Γ → Fml C Γ → Prop
  | _, _, .tt => True
  | _, σ, .eq a b => holds σ (.eq a b)
  | _, σ, .defined t => holds σ (.defined t)
  | _, σ, .not φ => ¬ holdsC I σ φ
  | _, σ, .and φ ψ => holdsC I σ φ ∧ holdsC I σ ψ
  | _, σ, .imp φ ψ => holdsC I σ φ → holdsC I σ ψ
  | _, σ, .upd m U φ => m.afterC (holdsC I · φ) (U.apply σ)
  | _, σ, .modal m P κ φ => ∀ o, ExecP I σ P o →
      o.after m fun σ₁ => ∀ o', ExecF I σ₁ κ o' → o'.after m (holdsC I · φ)
  | _, σ, .havoc φ => ∀ st nt, holdsC I (σ.havoc st nt) φ
  | _, σ, .all _ p φ => ∀ v, p.admits v → holdsC I (σ.push (t := .val p) v) φ
  | _, σ, .bind _ _ φ => ∀ v, holdsC I (σ.push v) φ
  | _, σ, .anon xs φ => ∀ b, holdsC I (σ.anon xs b) φ

/-- Valid with callbacks: true in every state of the empty context. -/
def ValidC (I : Invariant C) (φ : Fml C []) : Prop := ∀ σ, holdsC I σ φ

/-- The two semantics of `transfer` (KeY's `transferSemantics` option). -/
inductive TransferSem (C : Contract) where
  | noCallback
  | withCallback (I : Invariant C)

/-- The judgement under a transfer semantics. -/
def holdsT {Γ : Ctx} : TransferSem C → State C Γ → Fml C Γ → Prop
  | .noCallback => holds
  | .withCallback I => holdsC I

/-- Valid under a transfer semantics. -/
def ValidT (ts : TransferSem C) (φ : Fml C []) : Prop := ∀ σ, holdsT ts σ φ

theorem validT_noCallback {φ : Fml C []} : ValidT .noCallback φ ↔ Valid φ := Iff.rfl

theorem validT_withCallback {I : Invariant C} {φ : Fml C []} :
    ValidT (.withCallback I) φ ↔ ValidC I φ := Iff.rfl

/-! ## The deterministic run is a run with callbacks -/

section Det

variable {Γ : Ctx}

/-- **A send runs as its transfer**: it halts where the transfer does, and
otherwise ends in the booking with `pv` true, or with nothing booked and `pv`
false (`sendAt`, as the transaction's oracle says). -/
theorem Run.send_cases (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) (σ : State C Γ) :
    (∃ e, Run.transfer r a σ = .error e ∧ Run.send pv r a σ = .error e) ∨
    ∃ σ₁, Run.transfer r a σ = .ok σ₁ ∧
      (Run.send pv r a σ = .ok (σ₁.setLocal pv (.bool true)) ∨
        Run.send pv r a σ = .ok (σ.setLocal pv (.bool false))) := by
  simp only [Run.transfer, Run.send, sendAt, transferAt, bind, Except.bind,
    Semantics.Value.asInt]
  cases r.eval σ with
  | error e => exact .inl ⟨e, rfl, rfl⟩
  | ok v =>
    cases v with
    | bool _ => exact .inl ⟨_, rfl, rfl⟩
    | int addr =>
      cases a.eval σ with
      | error e => exact .inl ⟨e, rfl, rfl⟩
      | ok w =>
        cases w with
        | bool _ => exact .inl ⟨_, rfl, rfl⟩
        | int amt =>
          by_cases hn : amt < 0
          · simp only [hn, if_true]
            exact .inl ⟨_, rfl, rfl⟩
          · simp only [hn, if_false]
            refine .inr ⟨_, rfl, ?_⟩
            cases lookupBy (sendKey addr amt) σ.tx.ext with
            | none => exact .inl rfl
            | some o =>
              cases o with
              | ok _ => exact .inl rfl
              | _ => exact .inr rfl

/-- `if` by its condition read as a Boolean. -/
theorem Run.ite_evalB {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (h₁ : Ext Γ Γ₁)
    (thn : State C Γ → Res (State C Γ₁)) (h₂ : Ext Γ Γ₂) (els : State C Γ → Res (State C Γ₂))
    (σ : State C Γ) :
    Run.ite c h₁ thn h₂ els σ = match c.evalB σ with
      | .ok true => (thn σ).map (State.drop h₁)
      | .ok false => (els σ).map (State.drop h₂)
      | .error e => .error e := by
  simp only [Run.ite, Val.evalB, bind, Except.bind]
  cases c.eval σ with
  | error e => rfl
  | ok v =>
    cases v with
    | int _ => rfl
    | bool b => cases b <;> rfl

/-- A call whose arguments halt. -/
theorem Run.call_args {Γ' ps rs Γf : Ctx} {args : Args C Γ ps} {ret : CallRet Γ rs Γ'}
    {hb : Ext (rs ++ ps) Γf} {body : State C (rs ++ ps) → Res (State C Γf)} {σ : State C Γ}
    {e : Halt} (ha : args.eval σ = .error e) : Run.call args ret hb body σ = .error e := by
  simp only [Run.call, bind, Except.bind, ha]

/-- A call whose return variables cannot be made. -/
theorem Run.call_enter {Γ' ps rs Γf : Ctx} {args : Args C Γ ps} {ret : CallRet Γ rs Γ'}
    {hb : Ext (rs ++ ps) Γf} {body : State C (rs ++ ps) → Res (State C Γf)} {σ : State C Γ}
    {a : Env C ps} {e : Halt} (ha : args.eval σ = .ok a) (he : ret.enter (C := C) σ.glob = .error e) :
    Run.call args ret hb body σ = .error e := by
  simp only [Run.call, bind, Except.bind, ha, he]

/-- A call's body run in its frame, and what it leaves the caller. -/
theorem Run.call_body {Γ' ps rs Γf : Ctx} {args : Args C Γ ps} {ret : CallRet Γ rs Γ'}
    {hb : Ext (rs ++ ps) Γf} {body : State C (rs ++ ps) → Res (State C Γf)} {σ : State C Γ}
    {a : Env C ps} {τ : Semantics.State} {r : Env C rs} (ha : args.eval σ = .ok a)
    (he : ret.enter σ.glob = .ok (τ, r)) :
    Run.call args ret hb body σ = (body (State.ofGlob τ (Env.append rs r a))).map
      fun υ => υ.withEnv (ret.leave σ.env (Env.take rs (Env.drop hb υ.env))) := by
  simp only [Run.call, bind, Except.bind, ha, he]
  cases body (State.ofGlob τ (Env.append rs r a)) <;> rfl

mutual

/-- **The run `Stmt.run` makes is a callback run**, the callee changing
nothing, unless it leaves `I` broken on the way. -/
theorem Stmt.exec_run (I : Invariant C) : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → ∀ σ : State C Γ,
    ExecS I σ s (.ofRes (s.run σ)) ∨ ExecS I σ s .violated
  | _, _, .transfer r a, σ => by
    show ExecS I σ _ (.ofRes (Run.transfer r a σ)) ∨ _
    cases h : Run.transfer r a σ with
    | error e => exact .inl (.transferHalt h)
    | ok σ₁ =>
      by_cases hI : I.at σ₁
      · left
        have := ExecS.transferResume (I := I) (st := σ₁.storage) (nt := σ₁.net) h hI
          (by rw [State.havoc_self]; exact hI)
        rwa [State.havoc_self] at this
      · exact .inr (.transferViolated h hI)
  | _, _, .send pv r a, σ => by
    show ExecS I σ _ (.ofRes (Run.send pv r a σ)) ∨ _
    rcases Run.send_cases pv r a σ with ⟨e, ht, hs⟩ | ⟨σ₁, ht, hs | hs⟩
    · rw [hs]; exact .inl (.sendHalt ht)
    · rw [hs]
      by_cases hI : I.at σ₁
      · left
        have := ExecS.sendResume (I := I) (pv := pv) (st := σ₁.storage) (nt := σ₁.net) ht hI
          (by rw [State.havoc_self]; exact hI)
        rwa [State.havoc_self] at this
      · exact .inr (.sendViolated ht hI)
    · rw [hs]; exact .inl (.sendFailed ht)
  | _, _, .ite c thn els, σ => by
    show ExecS I σ _ (.ofRes (Run.ite c thn.ext thn.runR els.ext els.runR σ)) ∨ _
    rw [Run.ite_evalB]
    cases hc : c.evalB σ with
    | error e => exact .inl (.iteHalt hc)
    | ok b =>
      cases b with
      | true =>
        simp only []
        rw [← COut.map_ofRes]
        rcases Prog.exec_run I thn σ with h | h
        · exact .inl (.iteThen hc h)
        · exact .inr (.iteThen (o := .violated) hc h)
      | false =>
        simp only []
        rw [← COut.map_ofRes]
        rcases Prog.exec_run I els σ with h | h
        · exact .inl (.iteElse hc h)
        · exact .inr (.iteElse (o := .violated) hc h)
  | _, _, .call f args ret body, σ => by
    show ExecS I σ _ (.ofRes (Run.call args ret body.ext body.runR σ)) ∨ _
    simp only [Run.call, bind, Except.bind]
    cases ha : args.eval σ with
    | error e => exact .inl (.callArgs ha)
    | ok a =>
      cases he : ret.enter σ.glob with
      | error e => exact .inl (.callEnter ha he)
      | ok p =>
        obtain ⟨τ, r⟩ := p
        simp only []
        rcases Prog.exec_run I body (State.ofGlob τ (Env.append _ r a)) with h | h
        · left
          have h' : ExecP I _ body (.ofRes (body.runR (State.ofGlob τ (Env.append _ r a)))) := h
          revert h'
          cases body.runR (State.ofGlob τ (Env.append _ r a)) with
          | error e => exact fun h' => ExecS.callBody (f := f) ha he h'
          | ok υ => exact fun h' => ExecS.callBody (f := f) ha he h'
        · exact .inr (.callBody (o := .violated) ha he h)
  | _, _, .tryCall call rets ok err code pnc other, σ => by
    show ExecS I σ _ (.ofRes (Run.tryCall call rets ok.ext ok.runR err.ext err.runR code pnc.ext
      pnc.runR other.ext other.runR σ)) ∨ _
    simp only [Run.tryCall, bind, Except.bind]
    cases hk : call.key σ with
    | error e => exact .inl (.tryHalt hk)
    | ok k =>
      simp only []
      rcases lookupBy k σ.tx.ext with _ | (vs | _ | v | _) <;> dsimp only
      · exact .inl (.tryRevert hk)
      · cases hd : rets.decode (C := C) vs with
        | error e => exact .inl (.tryDecode hk hd)
        | ok p =>
          obtain ⟨r, rest⟩ := p
          simp only []
          by_cases hI : I.at σ
          · have hI' : I.at (σ.havoc σ.storage σ.net) := by rw [State.havoc_self]; exact hI
            rw [← COut.map_ofRes]
            rcases Prog.exec_run I ok (σ.withEnv (Env.append _ r σ.env)) with h | h
            · exact .inl (.tryOk hk hI hI' hd (by rw [State.havoc_self]; exact h))
            · exact .inr (.tryOk (o := .violated) hk hI hI' hd (by rw [State.havoc_self]; exact h))
          · exact .inr (.tryViolated hk hI)
      · rw [← COut.map_ofRes]
        rcases Prog.exec_run I err σ with h | h
        · exact .inl (.tryError hk h)
        · exact .inr (.tryError (o := .violated) hk h)
      · cases hd : code.decode (C := C) v with
        | error e => exact .inl (.tryCode hk hd)
        | ok r =>
          simp only []
          rw [← COut.map_ofRes]
          rcases Prog.exec_run I pnc (σ.withEnv (Env.append _ r σ.env)) with h | h
          · exact .inl (.tryPanic hk hd h)
          · exact .inr (.tryPanic (o := .violated) hk hd h)
      · rw [← COut.map_ofRes]
        rcases Prog.exec_run I other σ with h | h
        · exact .inl (.tryOther hk h)
        · exact .inr (.tryOther (o := .violated) hk h)
  | _, _, .loop a c body, σ => by
    cases ht : Prog.hasTransfer body with
    | false => exact .inl (.det (by simp only [Stmt.forks, ht]))
    | true =>
      have hb : ∀ τ, ExecP I τ body (.ofRes (Prog.run τ body)) ∨ ExecP I τ body .violated :=
        fun τ => Prog.exec_run I body τ
      show ExecS I σ _ (.ofRes (Loop.run (fun τ => (Prog.run τ body).map (State.drop body.ext))
        (fun τ => c.eval τ) σ)) ∨ _
      have key : ∀ n (σ : State C _) r,
          Loop.iterN (fun τ => (Prog.run τ body).map (State.drop body.ext)) (fun τ => c.eval τ)
            n σ = .inr r → ExecS I σ (.loop a c body) (.ofRes r) ∨ ExecS I σ (.loop a c body) .violated := by
        intro n
        induction n with
        | zero => intro σ r hn; simp only [Loop.iterN, reduceCtorEq] at hn
        | succ n ih =>
          intro σ r hn
          simp only [Loop.iterN, Loop.step] at hn
          have hcB : ∀ e, c.eval σ = .error e → c.evalB σ = .error e := by
            intro e h; simp only [Val.evalB, h]
          rcases hc : c.eval σ with e | (m | b)
          · rw [hc] at hn; cases hn
            exact .inl (.loopHalt ht (hcB e hc))
          · rw [hc] at hn; cases hn
            exact .inl (.loopHalt ht (by simp only [Val.evalB, hc]))
          · cases b with
            | false =>
              rw [hc] at hn; cases hn
              exact .inl (.loopExit ht (by simp only [Val.evalB, hc]))
            | true =>
              rw [hc] at hn
              have hT : c.evalB σ = .ok true := by simp only [Val.evalB, hc]
              rcases hb σ with h | h
              · cases hr : Prog.run σ body with
                | error e =>
                  rw [hr] at h hn
                  cases hn
                  exact .inl (.loopStop (o := .halt e) ht hT h rfl)
                | ok υ =>
                  rw [hr] at h hn
                  rcases ih (υ.drop body.ext) r hn with h' | h'
                  · exact .inl (.loopIter ht hT h h')
                  · exact .inr (.loopIter ht hT h h')
              · exact .inr (.loopStop (o := .violated) ht hT h rfl)
      by_cases hex : ∃ r n, Loop.iterN (fun τ => (Prog.run τ body).map (State.drop body.ext))
          (fun τ => c.eval τ) n σ = .inr r
      · obtain ⟨r, n, hn⟩ := hex
        rw [Loop.run_of_iterN hn]
        exact key n σ r hn
      · have : Loop.run (fun τ => (Prog.run τ body).map (State.drop body.ext))
            (fun τ => c.eval τ) σ = .error .diverge := by
          simp only [Loop.run, hex, dite_false]
        rw [this]
        exact .inl (.loopDiverge ht)
  | _, _, .block body, σ => by
    cases ht : Prog.hasTransfer body with
    | false => exact .inl (.det (by simp only [Stmt.forks, ht]))
    | true =>
      show ExecS I σ _ (.ofRes ((Prog.run σ body).map (State.drop body.ext))) ∨ _
      rw [← COut.map_ofRes]
      rcases Prog.exec_run I body σ with h | h
      · exact .inl (.block ht h)
      · exact .inr (.block (o := .violated) ht h)
  | _, _, .assign .., _ | _, _, .rebind .., _ | _, _, .assignLocal .., _ | _, _, .declLocal .., _
  | _, _, .declStorage .., _ | _, _, .opAssign .., _ | _, _, .incDec .., _
  | _, _, .assignIncDec .., _ | _, _, .push .., _ | _, _, .pop .., _ | _, _, .declMem .., _
  | _, _, .rebindMem .., _ | _, _, .assignFromMem .., _ | _, _, .assignMem .., _
  | _, _, .delete .., _ | _, _, .deleteMem .., _ | _, _, .assignNew .., _ | _, _, .require .., _
  | _, _, .assert .., _ | _, _, .revert, _ => .inl (.det rfl)

/-- The same, for a sequence. -/
theorem Prog.exec_run (I : Invariant C) : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → ∀ σ : State C Γ,
    ExecP I σ P (.ofRes (Prog.run σ P)) ∨ ExecP I σ P .violated
  | _, _, .nil, _ => .inl .nil
  | _, _, .cons s P, σ => by
    rw [Prog.run_cons]
    rcases Stmt.exec_run I s σ with h | h
    · cases hs : s.run σ with
      | error e => rw [hs] at h; exact .inl (.halt h)
      | ok σ₁ =>
        rw [hs] at h
        rcases Prog.exec_run I P σ₁ with h' | h'
        · exact .inl (.cons h h')
        · exact .inr (.cons h h')
    · exact .inr (.violated h)

end

/-- The same, for the frames after a program. -/
theorem Frames.exec_run (I : Invariant C) {Γ₀ : Ctx} : {Γ : Ctx} → (κ : Frames C Γ Γ₀) →
    ∀ σ : State C Γ, ExecF I σ κ (.ofRes (κ.run σ)) ∨ ExecF I σ κ .violated
  | _, .nil, _ => .inl .nil
  | _, .seq ω κ, σ => by
    show ExecF I σ _ (.ofRes ((Prog.run σ ω).bind (Frames.run · κ))) ∨ _
    rcases Prog.exec_run I ω σ with h | h
    · cases hs : Prog.run σ ω with
      | error e => rw [hs] at h; exact .inl (.seqHalt h)
      | ok σ₁ =>
        rw [hs] at h
        rcases Frames.exec_run I κ σ₁ with h' | h'
        · exact .inl (.seq h h')
        · exact .inr (.seq h h')
    · exact .inr (.seqViolated h)
  | _, .pop _ h κ, σ => (Frames.exec_run I κ (σ.drop h)).imp .pop .pop
  | _, .drop h κ, σ => (Frames.exec_run I κ (σ.thin h)).imp .drop .drop

end Det

/-! ## With no payment, the run is the deterministic one -/

section NoPay

mutual

/-- **A statement that pays nothing has one callback run**, the
deterministic one. -/
theorem Stmt.eq_run (I : Invariant C) : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') →
    Stmt.hasTransfer s = false → ∀ {σ : State C Γ} {o : COut C Γ'}, ExecS I σ s o →
      o = .ofRes (s.run σ)
  | _, _, .transfer .., ht, _, _, _ | _, _, .send .., ht, _, _, _
  | _, _, .tryCall .., ht, _, _, _ => by simp only [Stmt.hasTransfer, Bool.true_eq_false] at ht
  | _, _, .ite c thn els, ht, σ, _, h => by
    simp only [Stmt.hasTransfer, Bool.or_eq_false_iff] at ht
    cases h with
    | det _ => rfl
    | iteHalt hc =>
      show _ = COut.ofRes (Run.ite _ _ _ _ _ _)
      rw [Run.ite_evalB, hc]
      rfl
    | iteThen hc h =>
      rw [Prog.eq_run I thn ht.1 h]
      show _ = COut.ofRes (Run.ite _ _ _ _ _ _)
      rw [Run.ite_evalB, hc]
      exact COut.map_ofRes _ _
    | iteElse hc h =>
      rw [Prog.eq_run I els ht.2 h]
      show _ = COut.ofRes (Run.ite _ _ _ _ _ _)
      rw [Run.ite_evalB, hc]
      exact COut.map_ofRes _ _
  | _, _, .call f args ret body, ht, σ, _, h => by
    simp only [Stmt.hasTransfer] at ht
    cases h with
    | det _ => rfl
    | callArgs ha =>
      show _ = COut.ofRes (Run.call _ _ _ _ _)
      rw [Run.call_args ha]
      rfl
    | callEnter ha he =>
      show _ = COut.ofRes (Run.call _ _ _ _ _)
      rw [Run.call_enter ha he]
      rfl
    | callBody ha he h =>
      rw [Prog.eq_run I body ht h]
      show _ = COut.ofRes (Run.call _ _ _ _ _)
      rw [Run.call_body ha he, COut.map_ofRes]
      rfl
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
  | _, _, .push .., _, _, _, h | _, _, .pop .., _, _, _, h | _, _, .declMem .., _, _, _, h
  | _, _, .rebindMem .., _, _, _, h | _, _, .assignFromMem .., _, _, _, h
  | _, _, .assignMem .., _, _, _, h | _, _, .delete .., _, _, _, h
  | _, _, .deleteMem .., _, _, _, h | _, _, .assignNew .., _, _, _, h
  | _, _, .require .., _, _, _, h | _, _, .assert .., _, _, _, h
  | _, _, .revert, _, _, _, h => by cases h; rfl

/-- The same, for a sequence. -/
theorem Prog.eq_run (I : Invariant C) : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') →
    Prog.hasTransfer P = false → ∀ {σ : State C Γ} {o : COut C Γ'}, ExecP I σ P o →
      o = .ofRes (Prog.run σ P)
  | _, _, .nil, _, _, _, h => by cases h; rfl
  | _, _, .cons s P, ht, σ, _, h => by
    simp only [Prog.hasTransfer_cons, Bool.or_eq_false_iff] at ht
    rw [Prog.run_cons]
    cases h with
    | cons hs hP =>
      have e₁ := Stmt.eq_run I s ht.1 hs
      revert e₁
      cases s.run σ with
      | error _ => exact fun e₁ => nomatch e₁
      | ok υ =>
        intro e₁
        cases e₁
        exact Prog.eq_run I P ht.2 hP
    | halt hs =>
      have e₁ := Stmt.eq_run I s ht.1 hs
      revert e₁
      cases s.run σ with
      | error _ => intro e₁; cases e₁; rfl
      | ok _ => exact fun e₁ => nomatch e₁
    | violated hs =>
      have e₁ := Stmt.eq_run I s ht.1 hs
      revert e₁
      cases s.run σ <;> exact fun e₁ => nomatch e₁

end

/-- **A statement that pays nothing has one callback run** (`Stmt.eq_run`). -/
theorem ExecS.eq_run {I : Invariant C} {Γ Γ' : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ'}
    {o : COut C Γ'} (h : ExecS I σ s o) (ht : Stmt.hasTransfer s = false) :
    o = .ofRes (s.run σ) :=
  Stmt.eq_run I s ht h

/-- The same, for a sequence. -/
theorem ExecP.eq_run {I : Invariant C} {Γ Γ' : Ctx} {σ : State C Γ} {P : Prog C Γ Γ'}
    {o : COut C Γ'} (h : ExecP I σ P o) (ht : Prog.hasTransfer P = false) :
    o = .ofRes (Prog.run σ P) :=
  Prog.eq_run I P ht h

/-- The same, for frames. -/
theorem ExecF.eq_run {I : Invariant C} {Γ₀ : Ctx} {Γ : Ctx} {σ : State C Γ} {κ : Frames C Γ Γ₀}
    {o : COut C Γ₀} (h : ExecF I σ κ o) (ht : κ.hasTransfer = false) : o = .ofRes (κ.run σ) := by
  induction h with
  | nil => rfl
  | @seq _ _ σ _ ω κ _ hω _ ih =>
    simp only [Frames.hasTransfer_seq, Bool.or_eq_false_iff] at ht
    have e₁ := ExecP.eq_run hω ht.1
    show _ = COut.ofRes ((Prog.run σ ω).bind (Frames.run · κ))
    revert e₁
    cases Prog.run σ ω with
    | error _ => exact fun e₁ => nomatch e₁
    | ok _ => intro e₁; cases e₁; exact ih ht.2
  | @seqHalt _ _ σ ω κ _ hω =>
    simp only [Frames.hasTransfer_seq, Bool.or_eq_false_iff] at ht
    have e₁ := ExecP.eq_run hω ht.1
    show _ = COut.ofRes ((Prog.run σ ω).bind (Frames.run · κ))
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

/-- With no payment, a property of every callback run of a sequence is one
of its deterministic run. -/
theorem ExecP.forall_iff {I : Invariant C} {Γ Γ' : Ctx} {σ : State C Γ} {P : Prog C Γ Γ'}
    (hP : Prog.hasTransfer P = false) (Q : COut C Γ' → Prop) :
    (∀ o, ExecP I σ P o → Q o) ↔ Q (.ofRes (Prog.run σ P)) := by
  refine ⟨fun H => ?_, fun H o h => ExecP.eq_run h hP ▸ H⟩
  rcases Prog.exec_run I P σ with h | h
  · exact H _ h
  · have e := ExecP.eq_run h hP
    revert e
    cases Prog.run σ P <;> exact fun e => nomatch e

/-- The same, for frames. -/
theorem ExecF.forall_iff {I : Invariant C} {Γ₀ Γ : Ctx} {σ : State C Γ} {κ : Frames C Γ Γ₀}
    (hκ : κ.hasTransfer = false) (Q : COut C Γ₀ → Prop) :
    (∀ o, ExecF I σ κ o → Q o) ↔ Q (.ofRes (κ.run σ)) := by
  refine ⟨fun H => ?_, fun H o h => ExecF.eq_run h hκ ▸ H⟩
  rcases Frames.exec_run I κ σ with h | h
  · exact H _ h
  · have e := ExecF.eq_run h hκ
    revert e
    cases κ.run σ <;> exact fun e => nomatch e

theorem _root_.Solidity.Modality.afterRunC_congr {α : Type} (m : Modality) {p q : α → Prop}
    (h : ∀ a, p a ↔ q a) (r : Res α) : m.afterRunC p r ↔ m.afterRunC q r := by
  cases r with
  | ok a => exact and_congr_left fun _ => h a
  | error _ => exact Iff.rfl

theorem _root_.Solidity.Modality.afterC_congr {α : Type} (m : Modality) {p q : α → Prop}
    (h : ∀ a, p a ↔ q a) (r : Res α) : m.afterC p r ↔ m.afterC q r := by
  cases r with
  | ok a => exact h a
  | error _ => exact Iff.rfl

/-- A modality after its program, with callbacks: the frames' outcome. -/
theorem after_frames_iff {I : Invariant C} {Γ₁ Γ₀ : Ctx} (m : Modality) {κ : Frames C Γ₁ Γ₀}
    (hκ : κ.hasTransfer = false) (p : State C Γ₀ → Prop) (r : Res (State C Γ₁)) :
    (COut.ofRes r).after m (fun σ₁ => ∀ o', ExecF I σ₁ κ o' → o'.after m p) ↔
      m.afterRunC p (r.bind (Frames.run · κ)) := by
  cases r with
  | ok σ₁ =>
    show (∀ o', ExecF I σ₁ κ o' → o'.after m p) ↔ _
    rw [ExecF.forall_iff hκ, COut.after_ofRes]
    rfl
  | error e =>
    exact ⟨fun h => ⟨h.1, fun h' => h.2 (Except.error.inj h')⟩,
      fun h => ⟨h.1, fun h' => h.2 (h' ▸ rfl)⟩⟩

/-- **With no payment, the two readings agree.** -/
theorem holdsC_iff_holds {I : Invariant C} : {Γ : Ctx} → (φ : Fml C Γ) → φ.hasTransfer = false →
    ∀ σ : State C Γ, (holdsC I σ φ ↔ holds σ φ)
  | _, .tt, _, _ | _, .eq .., _, _ | _, .defined _, _, _ => Iff.rfl
  | _, .not φ, h, σ => not_congr (holdsC_iff_holds φ h σ)
  | _, .and φ ψ, h, σ => by
    simp only [Fml.hasTransfer_and, Bool.or_eq_false_iff] at h
    exact and_congr (holdsC_iff_holds φ h.1 σ) (holdsC_iff_holds ψ h.2 σ)
  | _, .imp φ ψ, h, σ => by
    simp only [Fml.hasTransfer_imp, Bool.or_eq_false_iff] at h
    exact imp_congr (holdsC_iff_holds φ h.1 σ) (holdsC_iff_holds ψ h.2 σ)
  | _, .upd m U φ, h, σ => Modality.afterC_congr m (holdsC_iff_holds φ h) (U.apply σ)
  | _, .modal m P κ φ, h, σ => by
    simp only [Fml.hasTransfer_modal, Bool.or_eq_false_iff] at h
    show (∀ o, ExecP I σ P o → _) ↔ m.afterRunC (holds · φ) ((Prog.run σ P).bind (Frames.run · κ))
    rw [ExecP.forall_iff h.1.1, after_frames_iff m h.1.2]
    exact Modality.afterRunC_congr m (holdsC_iff_holds φ h.2) _
  | _, .havoc φ, h, σ => forall_congr' fun _ => forall_congr' fun _ => holdsC_iff_holds φ h _
  | _, .all _ _ φ, h, σ => forall_congr' fun _ => imp_congr_right fun _ => holdsC_iff_holds φ h _
  | _, .bind _ _ φ, h, σ => forall_congr' fun _ => holdsC_iff_holds φ h _
  | _, .anon _ φ, h, σ => forall_congr' fun _ => holdsC_iff_holds φ h _

/-- **A modal formula true with callbacks is true without**, when its frames
and postcondition pay nothing: the deterministic run is among the callback
runs (`Prog.exec_run`), and none of those breaks the invariant. -/
theorem holds_of_holdsC_modal {I : Invariant C} {Γ Γ₁ Γ₀ : Ctx} {σ : State C Γ} {m : Modality}
    {P : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀} (H : holdsC I σ (.modal m P κ φ))
    (hκ : κ.hasTransfer = false) (hφ : φ.hasTransfer = false) : holds σ (.modal m P κ φ) := by
  rcases Prog.exec_run I P σ with he | he
  · have := (after_frames_iff m hκ _ _).1 (H _ he)
    exact (Modality.afterRunC_congr m (holdsC_iff_holds φ hφ) _).1 this
  · exact (H _ he).elim

/-- A precondition and a modal formula, true with callbacks, are true
without, when only the program pays. -/
theorem holds_of_holdsC_imp {I : Invariant C} {Γ Γ₁ Γ₀ : Ctx} {σ : State C Γ} {a : Fml C Γ}
    {m : Modality} {P : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀}
    (H : holdsC I σ (.imp a (.modal m P κ φ))) (ha : a.hasTransfer = false)
    (hκ : κ.hasTransfer = false) (hφ : φ.hasTransfer = false) :
    holds σ (.imp a (.modal m P κ φ)) :=
  fun h => holds_of_holdsC_modal (H ((holdsC_iff_holds a ha σ).2 h)) hκ hφ

/-- **Valid with callbacks is valid without**, for `pre → [ P ] post`. -/
theorem valid_of_validC {I : Invariant C} {Γ₁ Γ₀ : Ctx} {a : Fml C []} {m : Modality}
    {P : Prog C [] Γ₁} {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀}
    (H : ValidC I (.imp a (.modal m P κ φ))) (ha : a.hasTransfer = false)
    (hκ : κ.hasTransfer = false) (hφ : φ.hasTransfer = false) :
    Valid (.imp a (.modal m P κ φ)) :=
  fun σ => holds_of_holdsC_imp (H σ) ha hκ hφ

end NoPay

end Solidity.Core
