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
  | _, _, .transfer .. | _, _, .send .. | _, _, .tryCall .. => true
  | _, _, .ite _ thn els => Prog.hasTransfer thn || Prog.hasTransfer els
  | _, _, .call _ _ _ body => Prog.hasTransfer body
  | _, _, .loop _ _ body => Prog.hasTransfer body
  | _, _, .block body => Prog.hasTransfer body
  | _, _, .assign .. | _, _, .rebind .. | _, _, .assignLocal .. | _, _, .declLocal ..
  | _, _, .declStorage .. | _, _, .opAssign .. | _, _, .incDec .. | _, _, .assignIncDec ..
  | _, _, .push .. | _, _, .pop .. | _, _, .declMem .. | _, _, .rebindMem ..
  | _, _, .assignFromMem .. | _, _, .assignMem .. | _, _, .delete .. | _, _, .deleteMem ..
  | _, _, .assignNew .. | _, _, .require .. | _, _, .assert .. | _, _, .revert => false

def Prog.hasTransfer : {Γ Γ' : Ctx} → Prog C Γ Γ' → Bool
  | _, _, .nil => false
  | _, _, .cons s P => Stmt.hasTransfer s || Prog.hasTransfer P

end

/-- The statements the relation does not take from `Stmt.run`: a `transfer`,
a `send`, a `try`, the two that run others by a choice (`if`, a call), and
a loop or a block whose body pays. -/
def Stmt.forks {Γ Γ' : Ctx} : Stmt C Γ Γ' → Bool
  | .transfer .. | .send .. | .tryCall .. | .ite .. | .call .. => true
  | .loop _ _ body | .block body => Prog.hasTransfer body
  | _ => false

/-- Whether a `transfer` occurs in a program of the frames. -/
def Frames.hasTransfer {Γ₀ : Ctx} : {Γ : Ctx} → Frames C Γ Γ₀ → Bool
  | _, .nil => false
  | _, .seq ω κ => Prog.hasTransfer ω || Frames.hasTransfer κ
  | _, .pop _ _ κ | _, .drop _ κ => Frames.hasTransfer κ

/-- Whether a `transfer` occurs in a program of the formula. -/
def Fml.hasTransfer : {Γ : Ctx} → Fml C Γ → Bool
  | _, .tt | _, .eq .. | _, .defined _ => false
  | _, .not φ | _, .upd _ _ φ | _, .havoc φ | _, .all _ _ φ | _, .bind _ _ φ | _, .anon _ φ =>
    φ.hasTransfer
  | _, .and φ ψ | _, .imp φ ψ => φ.hasTransfer || ψ.hasTransfer
  | _, .modal _ P κ φ => Prog.hasTransfer P || κ.hasTransfer || φ.hasTransfer

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
      args.eval σ = .ok a → ret.enter σ.glob = .error e → ExecS I σ (.call f args ret body) (.halt e)
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

end Solidity.Core
