import Solidity.Scratch.ITree.Tree
import Solidity.Calculus.CallerModelRun

/-!
# Scratch (itree-inspection, Experiment B): `ExecS` parametrized by a resumption predicate

`CallerModel.lean`'s `ExecSM`/`ExecPM`/`ExecFM`, `CallerModelRun.lean`'s
`mono` and `execM_run`, rewritten (mechanically) over an allowance
`A : Allow C` instead of `M.Allows J`.  Then `ExecS J` would be
`ExecSA anyA J` and `ExecSM M J` would be `ExecSA (M.Allows J) J`: one
relation, one `exec_run`, and the `any` bridge is definitional.  Not for
merge: `docs/audits/itree-inspection.md`.
-/

namespace Solidity.Scratch.ITree

open Solidity
open Solidity.Semantics (Word lookupBy)
open Solidity (Modality)

variable {C : Contract}

mutual

/-- `ExecSA A J σ s o`: run from `σ`, `s` may end in `o` when every callee
that calls back may (`ExecS J`), leaving only what `M` allows: `ExecS`'s
constructors, the three resumptions with `M.Allows` as a premise more. -/
inductive ExecSA (A : Allow C) (J : StateInv C) : {Γ Γ' : Ctx} → (σ : State C Γ) → Stmt C Γ Γ' →
    COut C σ.H Γ' → Prop where
  /-- A statement that runs no other by a choice and hands control to no
  callee that calls back runs as `Stmt.run`: a `transfer` and a `send` among
  them unless `J.pay`. -/
  | det {Γ Γ' : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ'} :
      s.forksIn J.pay = false → ExecSA A J σ s (.ofRes (s.run σ))
  /-- A transfer whose operands halt. -/
  | transferHalt {Γ : Ctx} {σ : State C Γ} {r a : Val C Γ .uint} {e : THalt} :
      J.pay = true → TRun.transfer r a σ = .error e → ExecSA A J σ (.transfer r a) (.halt e)
  /-- KeY's "invariant on exit": control leaves with `J` broken. -/
  | transferViolated {Γ : Ctx} {σ : State C Γ} {r a : Val C Γ .uint} {o₁ : Out C σ.H Γ} :
      J.pay = true → TRun.transfer r a σ = .ok o₁ → ¬ J.at o₁.st →
        ExecSA A J σ (.transfer r a) .violated
  /-- KeY's "resume after callback": control leaves with `J` kept and comes
  back to any state the callee may leave in which `J` holds. -/
  | transferResume {Γ : Ctx} {σ : State C Γ} {r a : Val C Γ .uint} {o₁ : Out C σ.H Γ}
      {st : Storage C} {nt : Ledger} {sb : PrimTy.uint.Denote} :
      J.pay = true → TRun.transfer r a σ = .ok o₁ → J.at o₁.st → J.at (o₁.st.havoc st nt sb) →
        A o₁.st st nt sb →
        ExecSA A J σ (.transfer r a) (.ok ⟨o₁.st.havoc st nt sb, o₁.ext⟩)
  /-- A send that halts, where its transfer would; it calls back under
  `J.pay` or forwarding all the gas (`full`, a value call). -/
  | sendHalt {Γ : Ctx} {σ : State C Γ} {pv : Idx Γ (.val .bool)} {r a : Val C Γ .uint}
      {full : Bool} {e : THalt} :
      (J.pay || full) = true → TRun.send pv r a σ = .error e →
        ExecSA A J σ (.send pv r a full) (.halt e)
  /-- KeY's "send failed": the callee reverts, nothing is booked and `pv`
  is `false`, whatever the transaction's oracle says. -/
  | sendFailed {Γ : Ctx} {σ : State C Γ} {pv : Idx Γ (.val .bool)} {r a : Val C Γ .uint}
      {full : Bool} {o₁ : Out C σ.H Γ} :
      (J.pay || full) = true → TRun.transfer r a σ = .ok o₁ →
        ExecSA A J σ (.send pv r a full) (.ok ⟨σ.setLocal pv (false : Bool), List.prefix_refl _⟩)
  /-- A fundedness or oracle refusal returns `false`, without booking a
  payment or entering a callback. Operand evaluation errors still halt. -/
  | sendRefused {Γ : Ctx} {σ : State C Γ} {pv : Idx Γ (.val .bool)} {r a : Val C Γ .uint}
      {full : Bool} :
      (J.pay || full) = true →
      TRun.send pv r a σ = .ok ⟨σ.setLocal pv (false : Bool), List.prefix_refl _⟩ →
        ExecSA A J σ (.send pv r a full) (.ok ⟨σ.setLocal pv (false : Bool), List.prefix_refl _⟩)
  /-- KeY's "invariant on exit", the payment booked. -/
  | sendViolated {Γ : Ctx} {σ : State C Γ} {pv : Idx Γ (.val .bool)} {r a : Val C Γ .uint}
      {full : Bool} {o₁ : Out C σ.H Γ} :
      (J.pay || full) = true → TRun.transfer r a σ = .ok o₁ → ¬ J.at o₁.st →
        ExecSA A J σ (.send pv r a full) .violated
  /-- KeY's "send succeeded": the payment booked, `J` kept, any state the
  callee may leave in which `J` holds, `pv` then `true`. -/
  | sendResume {Γ : Ctx} {σ : State C Γ} {pv : Idx Γ (.val .bool)} {r a : Val C Γ .uint}
      {full : Bool} {o₁ : Out C σ.H Γ} {st : Storage C} {nt : Ledger} {sb : PrimTy.uint.Denote} :
      (J.pay || full) = true → TRun.transfer r a σ = .ok o₁ → J.at o₁.st →
        J.at (o₁.st.havoc st nt sb) → A o₁.st st nt sb →
        ExecSA A J σ (.send pv r a full)
          (.ok ⟨(o₁.st.havoc st nt sb).setLocal pv (true : Bool), o₁.ext⟩)
  | iteHalt {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {c : Val C Γ .bool} {thn : Prog C Γ Γ₁}
      {els : Prog C Γ Γ₂} {e : THalt} :
      c.evalT σ = .error e → ExecSA A J σ (.ite c thn els) (.halt e)
  /-- The branch the condition picks, its locals popped. -/
  | iteThen {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {c : Val C Γ .bool} {thn : Prog C Γ Γ₁}
      {els : Prog C Γ Γ₂} {o : COut C σ.H Γ₁} :
      c.evalT σ = .ok true → ExecPA A J σ thn o →
        ExecSA A J σ (.ite c thn els) (o.map (Out.drop thn.ext))
  | iteElse {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {c : Val C Γ .bool} {thn : Prog C Γ Γ₁}
      {els : Prog C Γ Γ₂} {o : COut C σ.H Γ₂} :
      c.evalT σ = .ok false → ExecPA A J σ els o →
        ExecSA A J σ (.ite c thn els) (o.map (Out.drop els.ext))
  /-- A call whose arguments halt. -/
  | callArgs {Γ Γ' ps rs Γf : Ctx} {σ : State C Γ} {f : Name} {args : Args C Γ ps}
      {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf} {e : THalt} :
      args.evalT σ = .error e → ExecSA A J σ (.call f args ret body) (.halt e)
  /-- The body run in the callee's frame, and what the call leaves the
  caller (`TRun.call`). -/
  | callBody {Γ Γ' ps rs Γf : Ctx} {σ : State C Γ} {f : Name} {args : Args C Γ ps}
      {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf} {a : TEnv C σ.H ps}
      {o : COut C (ret.enterT (σ.withEnv a)).st.H Γf} :
      args.evalT σ = .ok a → ExecPA A J (ret.enterT (σ.withEnv a)).st body o →
        ExecSA A J σ (.call f args ret body)
          (o.map (TRun.callLeave ret body.ext σ (ret.enterT (σ.withEnv a))))
  /-- A recursive call runs as the call of its body (`Stmt.run_callRec`). -/
  | callRec {Γ Γ' ps rs : Ctx} {σ : State C Γ} {f : Name} {d : Nat} {args : Args C Γ ps}
      {ret : CallRet Γ rs Γ'} {body : Unit → Prog C (rs ++ ps) (rs ++ ps)} {o : COut C σ.H Γ'} :
      ExecSA A J σ (.call f args ret (body ())) o → ExecSA A J σ (.callRec f d args ret body) o
  /-- `f().push(e)` and `f().pop()` continue the getter's callback run once. -/
  | callReceiver {Γ ps Γf : Ctx} {E : Ty} {σ : State C Γ} {f : Name}
      {args : Args C Γ ps} {r : Var} {body : Prog C ([.alias (.array E)] ++ ps) Γf}
      {op : ReceiverOp C Γ E} {o : COut C σ.H (.alias (.array E) :: Γ)} :
      ExecSA A J σ (.call f args (.storage _ r) body) o →
        ExecSA A J σ (.callReceiver f args r body op) (o.receiverOp op)
  /-- A successful getter precedes every callback in the deferred operand. -/
  | callReceiverPush {Γ ps Γf Γv : Ctx} {E : Ty} {σ : State C Γ} {f : Name}
      {args : Args C Γ ps} {r : Var} {body : Prog C ([.alias (.array E)] ++ ps) Γf}
      {code : Prog C Γ Γv} {value : Src C Γv E}
      {a : Out C σ.H (.alias (.array E) :: Γ)} {ref : SRef C (.array E)}
      {u : COut C a.st.H Γv} :
      ExecSA A J σ (.call f args (.storage _ r) body) (.ok a) →
      a.st.env.1 = some ref → ExecPA A J (a.st.drop (.push .refl)) code u →
      ExecSA A J σ (.callReceiverPush f args r body code value)
        ((u.pushPrefix code.ext value ref).map (fun b => ⟨b.st, a.ext.trans b.ext⟩))
  /-- An unset getter result reverts before the operand's first effect. -/
  | callReceiverPushUnset {Γ ps Γf Γv : Ctx} {E : Ty} {σ : State C Γ} {f : Name}
      {args : Args C Γ ps} {r : Var} {body : Prog C ([.alias (.array E)] ++ ps) Γf}
      {code : Prog C Γ Γv} {value : Src C Γv E}
      {a : Out C σ.H (.alias (.array E) :: Γ)} :
      ExecSA A J σ (.call f args (.storage _ r) body) (.ok a) → a.st.env.1 = none →
      ExecSA A J σ (.callReceiverPush f args r body code value) (.halt .revert)
  /-- Getter failure stops `f().push(e)` before its operand. -/
  | callReceiverPushHalt {Γ ps Γf Γv : Ctx} {E : Ty} {σ : State C Γ} {f : Name}
      {args : Args C Γ ps} {r : Var} {body : Prog C ([.alias (.array E)] ++ ps) Γf}
      {code : Prog C Γ Γv} {value : Src C Γv E} {err : THalt} :
      ExecSA A J σ (.call f args (.storage _ r) body) (.halt err) →
      ExecSA A J σ (.callReceiverPush f args r body code value) (.halt err)
  /-- A getter's invariant violation stops `f().push(e)` before its operand. -/
  | callReceiverPushViolated {Γ ps Γf Γv : Ctx} {E : Ty} {σ : State C Γ} {f : Name}
      {args : Args C Γ ps} {r : Var} {body : Prog C ([.alias (.array E)] ++ ps) Γf}
      {code : Prog C Γ Γv} {value : Src C Γv E} :
      ExecSA A J σ (.call f args (.storage _ r) body) .violated →
      ExecSA A J σ (.callReceiverPush f args r body code value) .violated
  /-- The call reverts in the caller: no code at the address, or the callee
  reverts. -/
  | tryRevert {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {self : Bool} :
      ExecSA A J σ (.tryCall call rets ok err code pnc other sargs sbody self) (.halt .revert)
  /-- Data that the return variables do not decode. -/
  | tryDecode {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {self : Bool} {vs : List Word} {e : THalt} :
      rets.decodeT (C := C) (H := σ.H) vs = .error e →
        ExecSA A J σ (.tryCall call rets ok err code pnc other sargs sbody self) (.halt e)
  /-- KeY's "invariant on exit": control leaves with `J` broken. -/
  | tryViolated {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {self : Bool} :
      ¬ J.at σ → ExecSA A J σ (.tryCall call rets ok err code pnc other sargs sbody self) .violated
  /-- KeY's "call succeeded": `J` kept, any state the callee may leave in
  which `J` holds and `M` allows, the return data bound, the clause run, its
  locals popped.
  A self-call reaches the oracle only at another contract's address (the
  last premise, `TRun.tryCall`'s order). -/
  | tryOk {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {self : Bool} {st : Storage C} {nt : Ledger} {sb : PrimTy.uint.Denote}
      {vs rest : List Word} {r : TEnv C σ.H ρ} {o : COut C σ.H Γ₁} :
      J.at σ → J.at (σ.havoc st nt sb) → A σ st nt sb →
        rets.decodeT vs = .ok (r, rest) →
        ExecPA A J ((σ.havoc st nt sb).withEnv (TEnv.append ρ r σ.env)) ok o →
        (self = true → (call.addr.evalT σ).1 ≠ 0 ∧
          (call.addr.evalT σ).1 ≠ σ.tx.selfAddress.1) →
          ExecSA A J σ (.tryCall call rets ok err code pnc other sargs sbody self)
            (o.map (Out.drop ((Ext.append Γ ρ).trans ok.ext)))
  /-- "Error caught": the call reverted, and its effects with it.  A
  self-call goes here only at another contract's address: the contract's own
  callee fails by `trySelfError`, `trySelfPanic`, `trySelfOther`. -/
  | tryError {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {self : Bool} {o : COut C σ.H Γ₂} :
      (self = true → (call.addr.evalT σ).1 ≠ σ.tx.selfAddress.1) → ExecPA A J σ err o →
        ExecSA A J σ (.tryCall call rets ok err code pnc other sargs sbody self) (o.map (Out.drop err.ext))
  /-- "Panic caught", with the code bound. -/
  | tryPanic {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {self : Bool} {v : Word} {o : COut C σ.H Γ₃} :
      (self = true → (call.addr.evalT σ).1 ≠ σ.tx.selfAddress.1) →
      ExecPA A J (σ.withEnv (TEnv.append κ (code.decodeT v) σ.env)) pnc o →
        ExecSA A J σ (.tryCall call rets ok err code pnc other sargs sbody self)
          (o.map (Out.drop ((Ext.append Γ κ).trans pnc.ext)))
  /-- "Other failure caught". -/
  | tryOther {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {self : Bool} {o : COut C σ.H Γ₄} :
      (self = true → (call.addr.evalT σ).1 ≠ σ.tx.selfAddress.1) → ExecPA A J σ other o →
        ExecSA A J σ (.tryCall call rets ok err code pnc other sargs sbody self) (o.map (Out.drop other.ext))
  /-- A self-call (`Stmt.tryCall`'s `self`, `docs/options.md` O8): the
  receiver is the contract, whose function runs as an inlined call, and the
  success clause from the state it leaves, its locals popped. -/
  | trySelfOk {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf}
      {o₁ : Out C σ.H (ρ ++ Γ)} {o : COut C o₁.st.H Γ₁} :
      (call.addr.evalT σ).1 ≠ 0 → (call.addr.evalT σ).1 = σ.tx.selfAddress.1 →
      ExecSA A J σ (.call call.fn sargs (.rets rets.toRet) sbody) (.ok o₁) → ExecPA A J o₁.st ok o →
        ExecSA A J σ (.tryCall call rets ok err code pnc other sargs sbody true)
          (o.map fun o' => ⟨o'.st.drop ((Ext.append Γ ρ).trans ok.ext), o₁.ext.trans o'.ext⟩)
  /-- A self-call whose callee exhausts or diverges: the caller does too. -/
  | trySelfHalt {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {e : THalt} :
      (call.addr.evalT σ).1 ≠ 0 → (call.addr.evalT σ).1 = σ.tx.selfAddress.1 →
      ExecSA A J σ (.call call.fn sargs (.rets rets.toRet) sbody) (.halt e) → e ≠ .revert → e ≠ .panic →
        (∀ d, e ≠ .revertWith d) →
        ExecSA A J σ (.tryCall call rets ok err code pnc other sargs sbody true) (.halt e)
  /-- A self-call whose callee reverts with data: the `Error` clause, from the
  caller's state (the callee's effects undone); taken when the data decodes
  as `Error(string)` (`TRun.tryCall`), here for any data. -/
  | trySelfError {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {o : COut C σ.H Γ₂}
      {d : List UInt8} :
      (call.addr.evalT σ).1 ≠ 0 → (call.addr.evalT σ).1 = σ.tx.selfAddress.1 →
      ExecSA A J σ (.call call.fn sargs (.rets rets.toRet) sbody) (.halt (.revertWith d)) → ExecPA A J σ err o →
        ExecSA A J σ (.tryCall call rets ok err code pnc other sargs sbody true)
          (o.map (Out.drop err.ext))
  /-- A self-call whose callee reverts: the catch-all, from the caller's
  state. -/
  | trySelfOther {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {o : COut C σ.H Γ₄}
      {e : THalt} :
      (call.addr.evalT σ).1 ≠ 0 → (call.addr.evalT σ).1 = σ.tx.selfAddress.1 →
      ExecSA A J σ (.call call.fn sargs (.rets rets.toRet) sbody) (.halt e) →
      (e = .revert ∨ ∃ d, e = .revertWith d) → ExecPA A J σ other o →
        ExecSA A J σ (.tryCall call rets ok err code pnc other sargs sbody true)
          (o.map (Out.drop other.ext))
  /-- A self-call whose callee panics: the `Panic` clause, with the code its
  data carries (`TRun.tryCall`), any code where it panics by a halt of its own
  (the transaction's, `TRun.selfPanicCode`). -/
  | trySelfPanic {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {v : Word}
      {o : COut C σ.H Γ₃} {e : THalt} :
      (call.addr.evalT σ).1 ≠ 0 → (call.addr.evalT σ).1 = σ.tx.selfAddress.1 →
      ExecSA A J σ (.call call.fn sargs (.rets rets.toRet) sbody) (.halt e) →
      (e = .panic ∨ ∃ d, e = .revertWith d ∧ Semantics.decodePanic d = some v) →
      ExecPA A J (σ.withEnv (TEnv.append κ (code.decodeT v) σ.env)) pnc o →
        ExecSA A J σ (.tryCall call rets ok err code pnc other sargs sbody true)
          (o.map (Out.drop ((Ext.append Γ κ).trans pnc.ext)))
  /-- A self-call whose callee leaves the contract with `J` broken. -/
  | trySelfViolated {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ}
      {rets : Binders ρ} {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} :
      (call.addr.evalT σ).1 ≠ 0 → (call.addr.evalT σ).1 = σ.tx.selfAddress.1 →
      ExecSA A J σ (.call call.fn sargs (.rets rets.toRet) sbody) .violated →
        ExecSA A J σ (.tryCall call rets ok err code pnc other sargs sbody true) .violated
  /-- A loop that pays, whose condition halts. -/
  | loopHalt {Γ Γ₁ : Ctx} {σ : State C Γ} {a : LoopAnn C Γ} {c : Val C Γ .bool}
      {body : Prog C Γ Γ₁} {e : THalt} :
      Prog.callsBack J.pay body = true → c.evalT σ = .error e → ExecSA A J σ (.loop a c body) (.halt e)
  /-- The condition is false: the loop ends where it is. -/
  | loopExit {Γ Γ₁ : Ctx} {σ : State C Γ} {a : LoopAnn C Γ} {c : Val C Γ .bool}
      {body : Prog C Γ Γ₁} :
      Prog.callsBack J.pay body = true → c.evalT σ = .ok false →
        ExecSA A J σ (.loop a c body) (.ok ⟨σ, List.prefix_refl _⟩)
  /-- One iteration, its locals popped, and the loop again. -/
  | loopIter {Γ Γ₁ : Ctx} {σ : State C Γ} {a : LoopAnn C Γ} {c : Val C Γ .bool}
      {body : Prog C Γ Γ₁} {υ : Out C σ.H Γ₁} {o : COut C (υ.st.drop body.ext).H Γ} :
      Prog.callsBack J.pay body = true → c.evalT σ = .ok true → ExecPA A J σ body (.ok υ) →
        ExecSA A J (υ.st.drop body.ext) (.loop a c body) o →
          ExecSA A J σ (.loop a c body) (o.map (Out.cat (Out.drop body.ext υ)))
  /-- An iteration whose body halts or breaks the invariant. -/
  | loopStop {Γ Γ₁ : Ctx} {σ : State C Γ} {a : LoopAnn C Γ} {c : Val C Γ .bool}
      {body : Prog C Γ Γ₁} {o : COut C σ.H Γ₁} :
      Prog.callsBack J.pay body = true → c.evalT σ = .ok true → ExecPA A J σ body o → o.isOk = false →
        ExecSA A J σ (.loop a c body) (o.map (Out.drop body.ext))
  /-- A loop that pays may diverge: an over-approximation, which a box
  accepts and a diamond does not. -/
  | loopDiverge {Γ Γ₁ : Ctx} {σ : State C Γ} {a : LoopAnn C Γ} {c : Val C Γ .bool}
      {body : Prog C Γ Γ₁} :
      Prog.callsBack J.pay body = true → ExecSA A J σ (.loop a c body) (.halt .diverge)
  /-- A block that pays, statement by statement, its locals popped. -/
  | block {Γ Γ₁ : Ctx} {σ : State C Γ} {body : Prog C Γ Γ₁} {o : COut C σ.H Γ₁} :
      Prog.callsBack J.pay body = true → ExecPA A J σ body o →
        ExecSA A J σ (.block body) (o.map (Out.drop body.ext))
  /-- A `catch` clause binding the data whose callee or body may call back
(`Stmt.catchData`): it halts as any statement may, or binds some data — any:
the data a callee that called back reverts with is not the run's to say —
and runs its body, its locals popped. -/
  | catchDataHalt {Γ ρ ps Γf Γ₁ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {self : Bool} {kind : CatchKind}
      {x : Var} {body : Prog C (.mem bytesR :: Γ) Γ₁} {e : THalt} :
      (Prog.callsBack J.pay sbody || Prog.callsBack J.pay body) = true → e ≠ .panic →
        ExecSA A J σ (.catchData call rets sargs sbody self kind x body) (.halt e)
  | catchDataBody {Γ ρ ps Γf Γ₁ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {self : Bool} {kind : CatchKind}
      {x : Var} {body : Prog C (.mem bytesR :: Γ) Γ₁} {bs : List UInt8}
      {o₁ : Out C σ.H (.mem bytesR :: Γ)} {o : COut C o₁.st.H Γ₁} :
      (Prog.callsBack J.pay sbody || Prog.callsBack J.pay body) = true →
      TRun.litBytesT bs TRun.nil σ = .ok o₁ → ExecPA A J o₁.st body o →
        ExecSA A J σ (.catchData call rets sargs sbody self kind x body)
          (o.map fun o' => ⟨o'.st.drop ((Ext.push .refl).trans body.ext), o₁.ext.trans o'.ext⟩)

/-- `ExecPA A J σ P o`: the same, for a sequence. -/
inductive ExecPA (A : Allow C) (J : StateInv C) : {Γ Γ' : Ctx} → (σ : State C Γ) → Prog C Γ Γ' →
    COut C σ.H Γ' → Prop where
  | nil {Γ : Ctx} {σ : State C Γ} : ExecPA A J σ .nil (.ok ⟨σ, List.prefix_refl _⟩)
  | cons {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ₁} {P : Prog C Γ₁ Γ₂}
      {o₁ : Out C σ.H Γ₁} {o : COut C o₁.st.H Γ₂} :
      ExecSA A J σ s (.ok o₁) → ExecPA A J o₁.st P o → ExecPA A J σ (.cons s P) (o.map (Out.cat o₁))
  | halt {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ₁} {P : Prog C Γ₁ Γ₂} {e : THalt} :
      ExecSA A J σ s (.halt e) → ExecPA A J σ (.cons s P) (.halt e)
  | violated {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ₁} {P : Prog C Γ₁ Γ₂} :
      ExecSA A J σ s .violated → ExecPA A J σ (.cons s P) .violated

end

/-- `ExecFA A J σ κ o`: the frames after a program (`Frames.run`), with
callbacks: the rest of the program run so, a scope's locals popped. -/
inductive ExecFA (A : Allow C) (J : StateInv C) {Γ₀ : Ctx} : {Γ : Ctx} → (σ : State C Γ) → Frames C Γ Γ₀ →
    COut C σ.H Γ₀ → Prop where
  | nil {σ : State C Γ₀} : ExecFA A J σ .nil (.ok ⟨σ, List.prefix_refl _⟩)
  | seq {Γ Γ₁ : Ctx} {σ : State C Γ} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} {o₁ : Out C σ.H Γ₁}
      {o : COut C o₁.st.H Γ₀} :
      ExecPA A J σ ω (.ok o₁) → ExecFA A J o₁.st κ o → ExecFA A J σ (.seq ω κ) (o.map (Out.cat o₁))
  | seqHalt {Γ Γ₁ : Ctx} {σ : State C Γ} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} {e : THalt} :
      ExecPA A J σ ω (.halt e) → ExecFA A J σ (.seq ω κ) (.halt e)
  | seqViolated {Γ Γ₁ : Ctx} {σ : State C Γ} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} :
      ExecPA A J σ ω .violated → ExecFA A J σ (.seq ω κ) .violated
  | pop {Γ Γ' : Ctx} {σ : State C Γ'} {b : BlockKind} {h : Ext Γ Γ'} {κ : Frames C Γ Γ₀}
      {o : COut C σ.H Γ₀} :
      ExecFA A J (σ.drop h) κ o → ExecFA A J σ (.pop b h κ) o
  | drop {Γ Γ' : Ctx} {σ : State C Γ'} {h : Thin Γ Γ'} {κ : Frames C Γ Γ₀} {o : COut C σ.H Γ₀} :
      ExecFA A J (σ.thin h) κ o → ExecFA A J σ (.drop h κ) o

section Mono

variable {A A' : Allow C} {J : StateInv C}

mutual

/-- **A run under `M` is a run under any `M'` allowing more.** -/
theorem ExecSA.mono (hA : ∀ {Γ : Ctx} (σ : State C Γ) st nt sb, A σ st nt sb → A' σ st nt sb) : {Γ Γ' : Ctx} → {σ : State C Γ} → {s : Stmt C Γ Γ'} →
    {o : COut C σ.H Γ'} → ExecSA A J σ s o → ExecSA A' J σ s o
  | _, _, _, _, _, .det a0 => .det a0
  | _, _, _, _, _, .transferHalt a0 a1 => .transferHalt a0 a1
  | _, _, _, _, _, .transferViolated a0 a1 a2 => .transferViolated a0 a1 a2
  | _, _, _, _, _, .transferResume a0 a1 a2 a3 a4 => .transferResume a0 a1 a2 a3 (hA _ _ _ _ a4)
  | _, _, _, _, _, .sendHalt a0 a1 => .sendHalt a0 a1
  | _, _, _, _, _, .sendFailed a0 a1 => .sendFailed a0 a1
  | _, _, _, _, _, .sendRefused a0 a1 => .sendRefused a0 a1
  | _, _, _, _, _, .sendViolated a0 a1 a2 => .sendViolated a0 a1 a2
  | _, _, _, _, _, .sendResume a0 a1 a2 a3 a4 => .sendResume a0 a1 a2 a3 (hA _ _ _ _ a4)
  | _, _, _, _, _, .iteHalt a0 => .iteHalt a0
  | _, _, _, _, _, .iteThen a0 a1 => .iteThen a0 (ExecPA.mono hA a1)
  | _, _, _, _, _, .iteElse a0 a1 => .iteElse a0 (ExecPA.mono hA a1)
  | _, _, _, _, _, .callArgs a0 => .callArgs a0
  | _, _, _, _, _, .callBody a0 a1 => .callBody a0 (ExecPA.mono hA a1)
  | _, _, _, _, _, .callRec a0 => .callRec (ExecSA.mono hA a0)
  | _, _, _, _, _, .callReceiver a0 => .callReceiver (ExecSA.mono hA a0)
  | _, _, _, _, _, .callReceiverPush a0 a1 a2 => .callReceiverPush (ExecSA.mono hA a0) a1 (ExecPA.mono hA a2)
  | _, _, _, _, _, .callReceiverPushUnset a0 a1 => .callReceiverPushUnset (ExecSA.mono hA a0) a1
  | _, _, _, _, _, .callReceiverPushHalt a0 => .callReceiverPushHalt (ExecSA.mono hA a0)
  | _, _, _, _, _, .callReceiverPushViolated a0 => .callReceiverPushViolated (ExecSA.mono hA a0)
  | _, _, _, _, _, .tryRevert => .tryRevert
  | _, _, _, _, _, .tryDecode a0 => .tryDecode a0
  | _, _, _, _, _, .tryViolated a0 => .tryViolated a0
  | _, _, _, _, _, .tryOk a0 a1 a2 a3 a4 a5 => .tryOk a0 a1 (hA _ _ _ _ a2) a3 (ExecPA.mono hA a4) a5
  | _, _, _, _, _, .tryError a0 a1 => .tryError a0 (ExecPA.mono hA a1)
  | _, _, _, _, _, .tryPanic a0 a1 => .tryPanic a0 (ExecPA.mono hA a1)
  | _, _, _, _, _, .tryOther a0 a1 => .tryOther a0 (ExecPA.mono hA a1)
  | _, _, _, _, _, .trySelfOk a0 a1 a2 a3 => .trySelfOk a0 a1 (ExecSA.mono hA a2) (ExecPA.mono hA a3)
  | _, _, _, _, _, .trySelfHalt a0 a1 a2 a3 a4 a5 => .trySelfHalt a0 a1 (ExecSA.mono hA a2) a3 a4 a5
  | _, _, _, _, _, .trySelfError a0 a1 a2 a3 => .trySelfError a0 a1 (ExecSA.mono hA a2) (ExecPA.mono hA a3)
  | _, _, _, _, _, .trySelfOther a0 a1 a2 a3 a4 => .trySelfOther a0 a1 (ExecSA.mono hA a2) a3 (ExecPA.mono hA a4)
  | _, _, _, _, _, .trySelfPanic a0 a1 a2 a3 a4 => .trySelfPanic a0 a1 (ExecSA.mono hA a2) a3 (ExecPA.mono hA a4)
  | _, _, _, _, _, .trySelfViolated a0 a1 a2 => .trySelfViolated a0 a1 (ExecSA.mono hA a2)
  | _, _, _, _, _, .loopHalt a0 a1 => .loopHalt a0 a1
  | _, _, _, _, _, .loopExit a0 a1 => .loopExit a0 a1
  | _, _, _, _, _, .loopIter a0 a1 a2 a3 => .loopIter a0 a1 (ExecPA.mono hA a2) (ExecSA.mono hA a3)
  | _, _, _, _, _, .loopStop a0 a1 a2 a3 => .loopStop a0 a1 (ExecPA.mono hA a2) a3
  | _, _, _, _, _, .loopDiverge a0 => .loopDiverge a0
  | _, _, _, _, _, .block a0 a1 => .block a0 (ExecPA.mono hA a1)
  | _, _, _, _, _, .catchDataHalt a0 a1 => .catchDataHalt a0 a1
  | _, _, _, _, _, .catchDataBody a0 a1 a2 => .catchDataBody a0 a1 (ExecPA.mono hA a2)
  termination_by structural _ _ _ _ _ h => h

/-- The same, for a sequence. -/
theorem ExecPA.mono (hA : ∀ {Γ : Ctx} (σ : State C Γ) st nt sb, A σ st nt sb → A' σ st nt sb) : {Γ Γ' : Ctx} → {σ : State C Γ} → {P : Prog C Γ Γ'} →
    {o : COut C σ.H Γ'} → ExecPA A J σ P o → ExecPA A' J σ P o
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .cons a0 a1 => .cons (ExecSA.mono hA a0) (ExecPA.mono hA a1)
  | _, _, _, _, _, .halt a0 => .halt (ExecSA.mono hA a0)
  | _, _, _, _, _, .violated a0 => .violated (ExecSA.mono hA a0)
  termination_by structural _ _ _ _ _ h => h

end

/-- The same, for the frames. -/
theorem ExecFA.mono (hA : ∀ {Γ : Ctx} (σ : State C Γ) st nt sb, A σ st nt sb → A' σ st nt sb) {Γ₀ : Ctx} : {Γ : Ctx} → {σ : State C Γ} → {κ : Frames C Γ Γ₀} →
    {o : COut C σ.H Γ₀} → ExecFA A J (Γ₀ := Γ₀) σ κ o → ExecFA A' J (Γ₀ := Γ₀) σ κ o
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .seq a0 a1 => .seq (ExecPA.mono hA a0) (ExecFA.mono hA a1)
  | _, _, _, _, .seqHalt a0 => .seqHalt (ExecPA.mono hA a0)
  | _, _, _, _, .seqViolated a0 => .seqViolated (ExecPA.mono hA a0)
  | _, _, _, _, .pop a0 => .pop (ExecFA.mono hA a0)
  | _, _, _, _, .drop a0 => .drop (ExecFA.mono hA a0)

end Mono

section Det

variable {Γ : Ctx}

mutual

/-- **The run `Stmt.run` makes is a callback run**, the callee changing
nothing, unless it leaves `J` broken on the way. -/
theorem execA_runS (A : Allow C) (hA : ∀ {Γ : Ctx} (σ : State C Γ), A σ σ.storage σ.net σ.selfBalance) (J : StateInv C) : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → ∀ σ : State C Γ,
    ExecSA A J σ s (.ofRes (s.run σ)) ∨ ExecSA A J σ s .violated
  | _, _, .transfer r a, σ => by
    cases hp : J.pay with
    | false => exact .inl (.det hp)
    | true =>
      show ExecSA A J σ _ (.ofRes (TRun.transfer r a σ)) ∨ _
      cases h : TRun.transfer r a σ with
      | error e => exact .inl (.transferHalt hp h)
      | ok o₁ =>
        by_cases hI : J.at o₁.st
        · exact .inl (ExecSA.transferResume (st := o₁.st.storage) (nt := o₁.st.net) (sb := o₁.st.selfBalance) hp h hI hI (hA _))
        · exact .inr (.transferViolated hp h hI)
  | _, _, .send pv r a full, σ => by
    cases hp : (J.pay || full) with
    | false => exact .inl (.det hp)
    | true =>
      show ExecSA A J σ _ (.ofRes (TRun.send pv r a σ)) ∨ _
      rcases TRun.send_cases pv r a σ with ⟨e, hs⟩ | ⟨o₁, ht, hs⟩ | hs
      · rw [hs]; exact .inl (.sendHalt hp hs)
      · rw [hs]
        by_cases hI : J.at o₁.st
        · exact .inl (ExecSA.sendResume (st := o₁.st.storage) (nt := o₁.st.net) (sb := o₁.st.selfBalance) hp ht hI hI (hA _))
        · exact .inr (.sendViolated hp ht hI)
      · rw [hs]; exact .inl (.sendRefused hp hs)
  | _, _, .ite c thn els, σ => by
    show ExecSA A J σ _ (.ofRes (TRun.ite c thn.ext thn.runR els.ext els.runR σ)) ∨ _
    rw [TRun.ite_eval]
    cases hc : c.evalT σ with
    | error e => exact .inl (.iteHalt hc)
    | ok b =>
      cases b with
      | true =>
        dsimp only
        rw [← COut.map_ofRes]
        rcases execA_runP A hA J thn σ with h | h
        · exact .inl (.iteThen hc h)
        · exact .inr (.iteThen (o := .violated) hc h)
      | false =>
        dsimp only
        rw [← COut.map_ofRes]
        rcases execA_runP A hA J els σ with h | h
        · exact .inl (.iteElse hc h)
        · exact .inr (.iteElse (o := .violated) hc h)
  | _, _, .call f args ret body, σ => by
    show ExecSA A J σ _ (.ofRes (TRun.call args ret body.ext body.runR σ)) ∨ _
    rw [TRun.call_eq]
    cases ha : args.evalT σ with
    | error e => exact .inl (.callArgs ha)
    | ok a =>
      show ExecSA A J σ _
        (.ofRes (TRun.callFrom ret body.ext body.runR σ (ret.enterT (σ.withEnv a)))) ∨ _
      rw [TRun.callFrom_eq, ← COut.map_ofRes]
      rcases execA_runP A hA J body (ret.enterT (σ.withEnv a)).st with h | h
      · exact .inl (ExecSA.callBody (f := f) ha h)
      · exact .inr (ExecSA.callBody (f := f) (o := .violated) ha h)
  | _, _, .callRec f d args ret body, σ => by
    show ExecSA A J σ _ (.ofRes (TRun.call args ret (body ()).ext (body ()).runR σ)) ∨ _
    rw [TRun.call_eq]
    cases ha : args.evalT σ with
    | error e => exact .inl (.callRec (.callArgs ha))
    | ok a =>
      show ExecSA A J σ _
        (.ofRes (TRun.callFrom ret (body ()).ext (body ()).runR σ (ret.enterT (σ.withEnv a)))) ∨ _
      rw [TRun.callFrom_eq, ← COut.map_ofRes]
      rcases execA_runP A hA J (body ()) (ret.enterT (σ.withEnv a)).st with h | h
      · exact .inl (.callRec (ExecSA.callBody (f := f) ha h))
      · exact .inr (.callRec (ExecSA.callBody (f := f) (o := .violated) ha h))
  | _, _, .callReceiver f args r body op, σ => by
    have hc : ExecSA A J σ (.call f args (.storage _ r) body)
        (.ofRes (TRun.call args (.storage _ r) body.ext body.runR σ)) ∨
        ExecSA A J σ (.call f args (.storage _ r) body) .violated := by
      rw [TRun.call_eq]
      cases ha : args.evalT σ with
      | error e => exact .inl (.callArgs ha)
      | ok a =>
        change ExecSA A J σ _ (.ofRes (TRun.callFrom (.storage _ r) body.ext body.runR σ
          ⟨σ.withEnv (none, a), List.prefix_refl _⟩)) ∨ _
        rw [TRun.callFrom_eq, ← COut.map_ofRes]
        rcases execA_runP A hA J body (σ.withEnv (none, a)) with h | h
        · exact .inl (ExecSA.callBody (f := f) ha h)
        · exact .inr (ExecSA.callBody (f := f) (o := .violated) ha h)
    rcases hc with h | h
    · exact .inl (by
        simpa only [COut.receiverOp_of_call] using (ExecSA.callReceiver (op := op) h))
    · exact .inr (ExecSA.callReceiver (op := op) h)
  | _, _, .callReceiverPush f args r body code value, σ => by
    change ExecSA A J σ _ (.ofRes (TRun.callReceiverPush args r body.ext body.runR
      code.ext code.runR value σ)) ∨ _
    have hc : ExecSA A J σ (.call f args (.storage _ r) body)
        (.ofRes (TRun.call args (.storage _ r) body.ext body.runR σ)) ∨
        ExecSA A J σ (.call f args (.storage _ r) body) .violated := by
      rw [TRun.call_eq]
      cases ha : args.evalT σ with
      | error e => exact .inl (.callArgs ha)
      | ok a =>
        change ExecSA A J σ _ (.ofRes (TRun.callFrom (.storage _ r) body.ext body.runR σ
          ⟨σ.withEnv (none, a), List.prefix_refl _⟩)) ∨ _
        rw [TRun.callFrom_eq, ← COut.map_ofRes]
        rcases execA_runP A hA J body (σ.withEnv (none, a)) with h | h
        · exact .inl (ExecSA.callBody (f := f) ha h)
        · exact .inr (ExecSA.callBody (f := f) (o := .violated) ha h)
    rcases hc with h | h
    · cases hg : TRun.call args (.storage _ r) body.ext body.runR σ with
      | error err =>
        rw [hg] at h
        exact .inl (by
          simpa only [TRun.callReceiverPush, hg, bind, Except.bind,
            COut.ofRes] using (ExecSA.callReceiverPushHalt (code := code) (value := value) h))
      | ok a =>
        rw [hg] at h
        cases hp : a.st.env.1 with
        | none =>
          exact .inl (by
            simpa only [TRun.callReceiverPush, hg,
              TRun.afterReceiverPrefix, SPath.resolveT, TEnv.get, hp, bind, Except.bind,
              Except.map, COut.ofRes] using
              (ExecSA.callReceiverPushUnset (code := code) (value := value) h hp))
        | some ref =>
          rcases execA_runP A hA J code (a.st.drop (.push .refl)) with hu | hu
          · exact .inl (by
              simpa only [TRun.callReceiverPush, hg,
                TRun.afterReceiverPrefix, SPath.resolveT, TEnv.get, hp, bind, Except.bind,
                COut.pushPrefix_ofRes, Prog.run, COut.map_ofRes] using
                (ExecSA.callReceiverPush (value := value) h hp hu))
          · exact .inr (ExecSA.callReceiverPush (value := value) h hp hu)
    · exact .inr (ExecSA.callReceiverPushViolated (code := code) (value := value) h)
  | _, _, .tryCall call rets ok err code pnc other sargs sbody self, σ => by
    show ExecSA A J σ _ (.ofRes (TRun.tryCall call rets ok.ext ok.runR err.ext err.runR code
      pnc.ext pnc.runR other.ext other.runR sargs sbody.ext sbody.runR self σ)) ∨ _
    have hErr : (self = true → (call.addr.evalT σ).1 ≠ σ.tx.selfAddress.1) →
        ExecSA A J σ (.tryCall call rets ok err code pnc other sargs sbody self)
        (.ofRes ((err.runR σ).map fun o => ⟨o.st.drop err.ext, o.ext⟩)) ∨
        ExecSA A J σ (.tryCall call rets ok err code pnc other sargs sbody self) .violated := by
      intro hsf
      rw [← COut.map_ofRes]
      rcases execA_runP A hA J err σ with h | h
      · exact .inl (.tryError hsf h)
      · exact .inr (.tryError (o := .violated) hsf h)
    have hOth : (self = true → (call.addr.evalT σ).1 ≠ σ.tx.selfAddress.1) →
        ExecSA A J σ (.tryCall call rets ok err code pnc other sargs sbody self)
        (.ofRes ((other.runR σ).map fun o => ⟨o.st.drop other.ext, o.ext⟩)) ∨
        ExecSA A J σ (.tryCall call rets ok err code pnc other sargs sbody self) .violated := by
      intro hsf
      rw [← COut.map_ofRes]
      rcases execA_runP A hA J other σ with h | h
      · exact .inl (.tryOther hsf h)
      · exact .inr (.tryOther (o := .violated) hsf h)
    have hPnc : (self = true → (call.addr.evalT σ).1 ≠ σ.tx.selfAddress.1) →
        ∀ v, ExecSA A J σ (.tryCall call rets ok err code pnc other sargs sbody self)
        (.ofRes ((pnc.runR (σ.withEnv (TEnv.append _ (code.decodeT v) σ.env))).map
          fun o => ⟨o.st.drop ((Ext.append _ _).trans pnc.ext), o.ext⟩)) ∨
        ExecSA A J σ (.tryCall call rets ok err code pnc other sargs sbody self) .violated := by
      intro hsf v
      rw [← COut.map_ofRes]
      rcases execA_runP A hA J pnc (σ.withEnv (TEnv.append _ (code.decodeT v) σ.env)) with h | h
      · exact .inl (.tryPanic hsf h)
      · exact .inr (.tryPanic (o := .violated) hsf h)
    unfold TRun.tryCall
    split
    · exact .inl .tryRevert
    rename_i hz
    split
    · rename_i hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨rfl, hs⟩ := hs
      have hc : ExecSA A J σ (.call call.fn sargs (.rets rets.toRet) sbody)
          (.ofRes (TRun.call sargs (.rets rets.toRet) sbody.ext sbody.runR σ)) ∨
          ExecSA A J σ (.call call.fn sargs (.rets rets.toRet) sbody) .violated := by
        rw [TRun.call_eq]
        cases ha : sargs.evalT σ with
        | error e => exact .inl (.callArgs ha)
        | ok a =>
          show ExecSA A J σ _ (.ofRes (TRun.callFrom (.rets rets.toRet) sbody.ext sbody.runR σ
            ((CallRet.rets rets.toRet).enterT (σ.withEnv a)))) ∨ _
          rw [TRun.callFrom_eq, ← COut.map_ofRes]
          rcases execA_runP A hA J sbody ((CallRet.rets rets.toRet).enterT (σ.withEnv a)).st with h | h
          · exact .inl (ExecSA.callBody (f := call.fn) ha h)
          · exact .inr (ExecSA.callBody (f := call.fn) (o := .violated) ha h)
      rcases hc with hc | hc
      · revert hc
        cases TRun.call sargs (.rets rets.toRet) sbody.ext sbody.runR σ with
        | ok o₁ =>
          intro hc
          dsimp only
          rw [← COut.map_ofRes]
          rcases execA_runP A hA J ok o₁.st with h | h
          · exact .inl (ExecSA.trySelfOk hz hs hc h)
          · exact .inr (ExecSA.trySelfOk (o := .violated) hz hs hc h)
        | error e =>
          intro hc
          cases e with
          | revert =>
            dsimp only
            rw [← COut.map_ofRes]
            rcases execA_runP A hA J other σ with h | h
            · exact .inl (.trySelfOther hz hs hc (.inl rfl) h)
            · exact .inr (.trySelfOther (o := .violated) hz hs hc (.inl rfl) h)
          | revertWith d =>
            dsimp only
            split
            · rw [← COut.map_ofRes]
              rcases execA_runP A hA J err σ with h | h
              · exact .inl (.trySelfError hz hs hc h)
              · exact .inr (.trySelfError (o := .violated) hz hs hc h)
            · split
              · rename_i v hv
                rw [← COut.map_ofRes]
                rcases execA_runP A hA J pnc
                  (σ.withEnv (TEnv.append _ (code.decodeT v) σ.env)) with h | h
                · exact .inl (.trySelfPanic hz hs hc (.inr ⟨d, rfl, hv⟩) h)
                · exact .inr (.trySelfPanic (o := .violated) hz hs hc (.inr ⟨d, rfl, hv⟩) h)
              · rw [← COut.map_ofRes]
                rcases execA_runP A hA J other σ with h | h
                · exact .inl (.trySelfOther hz hs hc (.inr ⟨d, rfl⟩) h)
                · exact .inr (.trySelfOther (o := .violated) hz hs hc (.inr ⟨d, rfl⟩) h)
          | panic =>
            rw [← COut.map_ofRes]
            rcases execA_runP A hA J pnc
              (σ.withEnv (TEnv.append _ (code.decodeT (TRun.selfPanicCode call σ)) σ.env)) with h | h
            · exact .inl (.trySelfPanic hz hs hc (.inl rfl) h)
            · exact .inr (.trySelfPanic (o := .violated) hz hs hc (.inl rfl) h)
          | diverge => exact .inl (ExecSA.trySelfHalt hz hs hc (by decide) (by decide) nofun)
          | exhausted => exact .inl (ExecSA.trySelfHalt hz hs hc (by decide) (by decide) nofun)
      · exact .inr (ExecSA.trySelfViolated hz hs hc)
    rename_i hns
    have hg : self = true → (call.addr.evalT σ).1 ≠ 0 ∧
        (call.addr.evalT σ).1 ≠ σ.tx.selfAddress.1 := fun hself =>
      ⟨hz, fun he => hns (by simp only [hself, he, decide_true, Bool.and_self])⟩
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
          rcases execA_runP A hA J ok (σ.withEnv (TEnv.append _ r σ.env)) with h | h
          · exact .inl (ExecSA.tryOk (st := σ.storage) (nt := σ.net) (sb := σ.selfBalance) hI hI (hA _) hd h hg)
          · exact .inr (ExecSA.tryOk (st := σ.storage) (nt := σ.net) (sb := σ.selfBalance) (o := .violated) hI hI (hA _) hd h hg)
        · exact .inr (.tryViolated hI)
    · exact hErr fun h => (hg h).2
    · exact hPnc (fun h => (hg h).2) v
    · exact hOth fun h => (hg h).2
  | Γ, _, .loop a c body, σ => by
    cases ht : Prog.callsBack J.pay body with
    | false => exact .inl (.det (by simp only [Stmt.forksIn, ht]))
    | true =>
      show ExecSA A J σ _ (.ofRes (TRun.loop c body.ext body.runR σ)) ∨ _
      rw [TRun.loop_eq]
      have key : ∀ (n : Nat) (τ : State C Γ) (r : TRes (Out C τ.H Γ)),
          TLoop.iterN (TRun.loopBody body.ext body.runR τ.H) (fun o => c.evalT o.st) n
              ⟨τ, List.prefix_refl _⟩ = .inr r →
            ExecSA A J τ (.loop a c body) (.ofRes r) ∨ ExecSA A J τ (.loop a c body) .violated := by
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
              rcases execA_runP A hA J body τ with h | h
              · change ExecPA A J τ body (.ofRes (body.runR τ)) at h
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
    cases ht : Prog.callsBack J.pay body with
    | false => exact .inl (.det (by simp only [Stmt.forksIn, ht]))
    | true =>
      show ExecSA A J σ _ (.ofRes ((body.runR σ).map (Out.drop body.ext))) ∨ _
      rw [← COut.map_ofRes]
      rcases execA_runP A hA J body σ with h | h
      · exact .inl (.block ht h)
      · exact .inr (.block (o := .violated) ht h)
  | Γ, _, @Stmt.catchData _ _ _ _ _ Γ₁ c rets sargs sbody self kind x body, σ => by
    cases hf : (Stmt.catchData c rets sargs sbody self kind x body).forksIn J.pay with
    | false => exact .inl (.det hf)
    | true =>
      show ExecSA A J σ _ (.ofRes (TRun.catchData c rets sargs sbody.ext sbody.runR self kind
        body.ext body.runR σ)) ∨ _
      unfold TRun.catchData
      cases hb : TRun.catchBytes c rets sargs sbody.ext sbody.runR self σ with
      | error e => exact .inl (.catchDataHalt hf (TRun.catchBytes_ne_panic hb))
      | ok d =>
        simp only [bind, Except.bind]
        cases kind.decode d with
        | none => exact .inl (.catchDataHalt hf nofun)
        | some bs =>
          dsimp only
          rw [TRun.litBytesT_seq]
          unfold TRun.seq
          cases hl : TRun.litBytesT bs TRun.nil σ with
          | error e =>
            refine .inl (.catchDataHalt hf fun hp => ?_)
            subst hp
            exact TRun.litBytesT_noPanic (k := TRun.nil) (fun _ => TRes.NoPanic.ok _) bs σ hl
          | ok o₁ =>
            dsimp only
            have hm : ∀ r : TRes (Out C o₁.st.H Γ₁),
                (COut.ofRes ((r.map fun o' => (⟨o'.st, o₁.ext.trans o'.ext⟩ : Out C σ.H Γ₁)).map
                  fun o => (⟨o.st.drop ((Ext.push .refl).trans body.ext), o.ext⟩ : Out C σ.H Γ))) =
                (COut.ofRes r).map fun o' =>
                  ⟨o'.st.drop ((Ext.push .refl).trans body.ext), o₁.ext.trans o'.ext⟩ := by
              intro r; cases r <;> rfl
            rw [hm]
            rcases execA_runP A hA J body o₁.st with h | h
            · exact .inl (.catchDataBody hf hl h)
            · exact .inr (.catchDataBody (o := .violated) hf hl h)
  | _, _, .assign .., _ | _, _, .rebind .., _ | _, _, .assignLocal .., _ | _, _, .declLocal .., _
  | _, _, .declStorage .., _ | _, _, .opAssign .., _ | _, _, .incDec .., _
  | _, _, .assignIncDec .., _ | _, _, .assignLocalPush .., _ | _, _, .push .., _
  | _, _, .pushOpAssign .., _ | _, _, .pushIncDec .., _
  | _, _, .pop .., _ | _, _, .declMem .., _
  | _, _, .rebindMem .., _ | _, _, .assignFromMem .., _ | _, _, .assignMem .., _
  | _, _, .delete .., _ | _, _, .deleteMem .., _ | _, _, .assignNew .., _ | _, _, .require .., _
  | _, _, .assert .., _ | _, _, .revert, _ | _, _, .assumeFalse, _
  | _, _, .revertData .., _ => .inl (.det rfl)

/-- The same, for a sequence. -/
theorem execA_runP (A : Allow C) (hA : ∀ {Γ : Ctx} (σ : State C Γ), A σ σ.storage σ.net σ.selfBalance) (J : StateInv C) : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → ∀ σ : State C Γ,
    ExecPA A J σ P (.ofRes (Prog.run σ P)) ∨ ExecPA A J σ P .violated
  | _, _, .nil, _ => .inl .nil
  | _, _, .cons s P, σ => by
    rcases execA_runS A hA J s σ with h | h
    · cases hs : Stmt.run σ s with
      | error e =>
        rw [hs] at h
        show ExecPA A J σ _ (.ofRes (TRun.seq s.runR P.runR σ)) ∨ _
        unfold TRun.seq
        rw [show s.runR σ = .error e from hs]
        exact .inl (.halt h)
      | ok o₁ =>
        rw [hs] at h
        rw [Prog.run_cons_ok hs, ← COut.map_ofRes]
        rcases execA_runP A hA J P o₁.st with h' | h'
        · exact .inl (.cons h h')
        · exact .inr (.cons (o := .violated) h h')
    · exact .inr (.violated h)

end

/-- The same, for the frames after a program. -/
theorem execA_runF (A : Allow C) (hA : ∀ {Γ : Ctx} (σ : State C Γ), A σ σ.storage σ.net σ.selfBalance) (J : StateInv C) {Γ₀ : Ctx} : {Γ : Ctx} → (κ : Frames C Γ Γ₀) →
    ∀ σ : State C Γ, ExecFA A J σ κ (.ofRes (κ.run σ)) ∨ ExecFA A J σ κ .violated
  | _, .nil, _ => .inl .nil
  | _, .seq ω κ, σ => by
    show ExecFA A J σ _ (.ofRes (TRun.seq (fun τ => Prog.run τ ω) (fun τ => Frames.run τ κ) σ)) ∨ _
    unfold TRun.seq
    dsimp only
    rcases execA_runP A hA J ω σ with h | h
    · cases hs : Prog.run σ ω with
      | error e => rw [hs] at h; exact .inl (.seqHalt h)
      | ok o₁ =>
        rw [hs] at h
        dsimp only
        rw [← COut.map_ofRes]
        rcases execA_runF A hA J κ o₁.st with h' | h'
        · exact .inl (.seq h h')
        · exact .inr (.seq (o := .violated) h h')
    · exact .inr (.seqViolated h)
  | _, .pop _ h κ, σ => (execA_runF A hA J κ (σ.drop h)).imp .pop .pop
  | _, .drop h κ, σ => (execA_runF A hA J κ (σ.thin h)).imp .drop .drop



end Det

/-! ## What becomes of the bridges -/

section Bridges

variable {J : StateInv C}

/-- `ExecSM .any` is the havoc reading by definition (was `ExecSM.toExecS` +
`ExecS.ofExecSM`, 145 lines). -/
theorem execSA_any {Γ Γ' : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ'} {o : COut C σ.H Γ'} :
    ExecSA (CallerModel.any.Allows J) J σ s o ↔ ExecSA anyA J σ s o := Iff.rfl

/-- A run under any allowance is a havoc run (`ExecSM.toExecS`). -/
theorem ExecSA.toAny {A : Allow C} {Γ Γ' : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ'}
    {o : COut C σ.H Γ'} (h : ExecSA A J σ s o) : ExecSA anyA J σ s o :=
  h.mono (fun _ _ _ _ _ => trivial)

/-- `Prog.exec_run` and `Prog.execM_run` are instances of one theorem. -/
theorem prog_execM_run (M : CallerModel C) {Γ Γ' : Ctx} (P : Prog C Γ Γ') (σ : State C Γ) :
    ExecPA (M.Allows J) J σ P (.ofRes (P.run σ)) ∨ ExecPA (M.Allows J) J σ P .violated :=
  execA_runP _ (fun σ => M.allows_refl J σ) J P σ

theorem prog_exec_run {Γ Γ' : Ctx} (P : Prog C Γ Γ') (σ : State C Γ) :
    ExecPA anyA J σ P (.ofRes (P.run σ)) ∨ ExecPA anyA J σ P .violated :=
  execA_runP _ (fun _ => trivial) J P σ

end Bridges

end Solidity.Scratch.ITree
