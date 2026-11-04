import Solidity.Calculus.CallbackHolds

/-!
# Caller models: what a callee that calls back may do

`docs/options.md`'s O11 (`docs/feature-work/calculus-modes.md`): a lattice
of attackers `none < staticOnly < nonReentrant R < any`, read as an argument
of the validity statement (`ValidM M ts φ`), as `ValidT ts φ` reads the
transfer semantics; never a global setting.

* `none`: no callee calls back.  The reading is `Fml.Valid`, the
  deterministic run: every callee keeps the contract's state, and answers by
  the transaction's oracle, a function of the call (`ExtCall.keyT`), since
  it cannot observe the contract either.
* `staticOnly`: a callee may call back by `STATICCALL` only (EIP-214,
  `CallMode.static`; `Mode.readOnly` frames): it may read the contract, so
  its answers are any, but it leaves the storage, the ledger and the balance
  as they were.
* `nonReentrant R`: a callee may call back only into the entries `R` does
  not guard by the contract's reentrancy lock (`Reentry`), each such call a
  callback run of its body (`ExecP`, nested callbacks read as `any`), in
  sequence (`Reentry.Reach`).  `Reentry.Guards` is the lock judgment:
  a guarded entry never completes while the lock is held, and
  `Reentry.reachAny_iff` proves that then a callee calling any entry reaches
  exactly what `nonReentrant` allows.
* `any`: the callee leaves any state in which the invariant holds; today's
  callback reading, `ValidT` (`validM_any`).

The runs `ExecSM M J` are `ExecS J` (`Semantics/Callback.lean`) with one
premise more at each resumption (`transferResume`, `sendResume`, `tryOk`):
the state the callee leaves is one `M` allows (`CallerModel.Allows`).  The
transfer semantics stays orthogonal: it says whether a `transfer` and a
`send` call back at all (`J.pay`), the caller model what a callee that does
may do.  The theorems are `Calculus/CallerModelRun.lean`'s (the runs) and
`Calculus/CallerModelValid.lean`'s (the readings, the weakening theorem).

This module is the stable interface other lanes build on (O12).
-/

namespace Solidity

open Semantics (Word)
open Solidity (Modality)

variable {C : Contract}

/-! ## Re-entry and the reentrancy lock -/

/-- **A contract's re-entry points and its reentrancy lock**: the entries a
callee may call back (`body`, run from the contract's state with no locals),
the ones the lock guards (`guarded`, solc's `nonReentrant` modifier), and
when the lock is held (`held`, a predicate of the storage: OpenZeppelin's
`_status == ENTERED`). -/
structure Reentry (C : Contract) where
  Entry : Type
  body : Entry → Prog C [] []
  guarded : Entry → Bool
  held : Storage C → Prop

namespace Reentry

/-- The frame a re-entrant call runs in: the contract's storage, ledger and
balance, a fresh memory, the re-entrant call's transaction `tx`. -/
def frame (g : State C []) (tx : TTx) : State C [] :=
  { storage := g.storage, H := [], heap := Heap.empty, env := (), net := g.net,
    selfBalance := g.selfBalance, tx := tx }

/-- **One re-entrant call of the entry `f`** from `g`, ending in `g'`: a
callback run of its body that completes, from a transaction at the
contract's address with no value; `g'` is `g` with the storage, the ledger
and the balance the run leaves. -/
def Call (R : Reentry C) (J : StateInv C) (f : R.Entry) (g g' : State C []) : Prop :=
  ∃ (tx : TTx) (o : Out C (frame g tx).H []), tx.selfAddress = g.tx.selfAddress ∧
    tx.msgValue.1 = 0 ∧ ExecP J (frame g tx) (R.body f) (.ok o) ∧
    g' = g.havoc o.st.storage o.st.net o.st.selfBalance

/-- A re-entrant call into an entry the lock does not guard. -/
def Step (R : Reentry C) (J : StateInv C) (g g' : State C []) : Prop :=
  ∃ f, R.guarded f = false ∧ R.Call J f g g'

/-- A re-entrant call into any entry. -/
def StepAny (R : Reentry C) (J : StateInv C) (g g' : State C []) : Prop :=
  ∃ f, R.Call J f g g'

/-- Finitely many steps of `r`, in order. -/
inductive Chain {α : Type} (r : α → α → Prop) : α → α → Prop where
  | refl (a : α) : Chain r a a
  | tail {a b c : α} : Chain r a b → r b c → Chain r a c

/-- What a callee calling back only into unguarded entries may leave. -/
def Reach (R : Reentry C) (J : StateInv C) : State C [] → State C [] → Prop :=
  Chain (R.Step J)

/-- What a callee calling back into any entry may leave. -/
def ReachAny (R : Reentry C) (J : StateInv C) : State C [] → State C [] → Prop :=
  Chain (R.StepAny J)

/-- **The lock judgment**: an entry the lock guards never completes from a
state in which the lock is held (its `require(_status != ENTERED)` reverts). -/
def Guards (R : Reentry C) (J : StateInv C) : Prop :=
  ∀ f, R.guarded f = true → ∀ g g', R.held g.storage → ¬ R.Call J f g g'

/-- An unguarded entry that completes leaves a held lock held. -/
def KeepsHeld (R : Reentry C) (J : StateInv C) : Prop :=
  ∀ f, R.guarded f = false → ∀ g g', R.held g.storage → R.Call J f g g' → R.held g'.storage

end Reentry

/-! ## The lattice -/

/-- **Who may call back, and how** (`docs/options.md`, O11). -/
inductive CallerModel (C : Contract) where
  | none
  | staticOnly
  | nonReentrant (R : Reentry C)
  | any

namespace CallerModel

/-- **What a callee may leave**, from the state `σ` control leaves in, as the
storage `st`, the ledger `nt` and the balance `sb` it resumes with (`J`
is checked apart, `ExecSM`).  Under `none` no callee calls back, so it
leaves `σ` as it was, as under `staticOnly`; `none`'s validity does not read
these runs (`ValidM`). -/
def Allows : CallerModel C → StateInv C → {Γ : Ctx} → State C Γ → Storage C → Ledger →
    PrimTy.uint.Denote → Prop
  | .none, _, _, σ, st, nt, sb | .staticOnly, _, _, σ, st, nt, sb =>
    st = σ.storage ∧ nt = σ.net ∧ sb = σ.selfBalance
  | .nonReentrant R, J, _, σ, st, nt, sb =>
    R.Reach J (σ.withEnv (Δ := []) ()) ((σ.havoc st nt sb).withEnv (Δ := []) ())
  | .any, _, _, _, _, _, _ => True

/-- Every caller model allows a callee that changes nothing. -/
theorem allows_refl (M : CallerModel C) (J : StateInv C) {Γ : Ctx} (σ : State C Γ) :
    M.Allows J σ σ.storage σ.net σ.selfBalance := by
  cases M with
  | none | staticOnly => exact ⟨rfl, rfl, rfl⟩
  | nonReentrant R => exact Reentry.Chain.refl _
  | any => trivial

/-- **The order**: `none ≤ staticOnly ≤ nonReentrant R ≤ any`. -/
inductive Le : CallerModel C → CallerModel C → Prop where
  | refl (M : CallerModel C) : Le M M
  | none (M : CallerModel C) : Le .none M
  | any (M : CallerModel C) : Le M .any
  | staticNr (R : Reentry C) : Le .staticOnly (.nonReentrant R)

instance : LE (CallerModel C) := ⟨Le⟩

end CallerModel

/-! ## The runs under a caller model -/

mutual

/-- `ExecSM M J σ s o`: run from `σ`, `s` may end in `o` when every callee
that calls back may (`ExecS J`), leaving only what `M` allows: `ExecS`'s
constructors, the three resumptions with `M.Allows` as a premise more. -/
inductive ExecSM (M : CallerModel C) (J : StateInv C) : {Γ Γ' : Ctx} → (σ : State C Γ) → Stmt C Γ Γ' →
    COut C σ.H Γ' → Prop where
  /-- A statement that runs no other by a choice and hands control to no
  callee that calls back runs as `Stmt.run`: a `transfer` and a `send` among
  them unless `J.pay`. -/
  | det {Γ Γ' : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ'} :
      s.forksIn J.pay = false → ExecSM M J σ s (.ofRes (s.run σ))
  /-- A transfer whose operands halt. -/
  | transferHalt {Γ : Ctx} {σ : State C Γ} {r a : Val C Γ .uint} {e : THalt} :
      J.pay = true → TRun.transfer r a σ = .error e → ExecSM M J σ (.transfer r a) (.halt e)
  /-- KeY's "invariant on exit": control leaves with `J` broken. -/
  | transferViolated {Γ : Ctx} {σ : State C Γ} {r a : Val C Γ .uint} {o₁ : Out C σ.H Γ} :
      J.pay = true → TRun.transfer r a σ = .ok o₁ → ¬ J.at o₁.st →
        ExecSM M J σ (.transfer r a) .violated
  /-- KeY's "resume after callback": control leaves with `J` kept and comes
  back to any state the callee may leave in which `J` holds. -/
  | transferResume {Γ : Ctx} {σ : State C Γ} {r a : Val C Γ .uint} {o₁ : Out C σ.H Γ}
      {st : Storage C} {nt : Ledger} {sb : PrimTy.uint.Denote} :
      J.pay = true → TRun.transfer r a σ = .ok o₁ → J.at o₁.st → J.at (o₁.st.havoc st nt sb) →
        M.Allows J o₁.st st nt sb →
        ExecSM M J σ (.transfer r a) (.ok ⟨o₁.st.havoc st nt sb, o₁.ext⟩)
  /-- A send that halts, where its transfer would; it calls back under
  `J.pay` or forwarding all the gas (`full`, a value call). -/
  | sendHalt {Γ : Ctx} {σ : State C Γ} {pv : Idx Γ (.val .bool)} {r a : Val C Γ .uint}
      {full : Bool} {e : THalt} :
      (J.pay || full) = true → TRun.send pv r a σ = .error e →
        ExecSM M J σ (.send pv r a full) (.halt e)
  /-- KeY's "send failed": the callee reverts, nothing is booked and `pv`
  is `false`, whatever the transaction's oracle says. -/
  | sendFailed {Γ : Ctx} {σ : State C Γ} {pv : Idx Γ (.val .bool)} {r a : Val C Γ .uint}
      {full : Bool} {o₁ : Out C σ.H Γ} :
      (J.pay || full) = true → TRun.transfer r a σ = .ok o₁ →
        ExecSM M J σ (.send pv r a full) (.ok ⟨σ.setLocal pv (false : Bool), List.prefix_refl _⟩)
  /-- A fundedness or oracle refusal returns `false`, without booking a
  payment or entering a callback. Operand evaluation errors still halt. -/
  | sendRefused {Γ : Ctx} {σ : State C Γ} {pv : Idx Γ (.val .bool)} {r a : Val C Γ .uint}
      {full : Bool} :
      (J.pay || full) = true →
      TRun.send pv r a σ = .ok ⟨σ.setLocal pv (false : Bool), List.prefix_refl _⟩ →
        ExecSM M J σ (.send pv r a full) (.ok ⟨σ.setLocal pv (false : Bool), List.prefix_refl _⟩)
  /-- KeY's "invariant on exit", the payment booked. -/
  | sendViolated {Γ : Ctx} {σ : State C Γ} {pv : Idx Γ (.val .bool)} {r a : Val C Γ .uint}
      {full : Bool} {o₁ : Out C σ.H Γ} :
      (J.pay || full) = true → TRun.transfer r a σ = .ok o₁ → ¬ J.at o₁.st →
        ExecSM M J σ (.send pv r a full) .violated
  /-- KeY's "send succeeded": the payment booked, `J` kept, any state the
  callee may leave in which `J` holds, `pv` then `true`. -/
  | sendResume {Γ : Ctx} {σ : State C Γ} {pv : Idx Γ (.val .bool)} {r a : Val C Γ .uint}
      {full : Bool} {o₁ : Out C σ.H Γ} {st : Storage C} {nt : Ledger} {sb : PrimTy.uint.Denote} :
      (J.pay || full) = true → TRun.transfer r a σ = .ok o₁ → J.at o₁.st →
        J.at (o₁.st.havoc st nt sb) → M.Allows J o₁.st st nt sb →
        ExecSM M J σ (.send pv r a full)
          (.ok ⟨(o₁.st.havoc st nt sb).setLocal pv (true : Bool), o₁.ext⟩)
  | iteHalt {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {c : Val C Γ .bool} {thn : Prog C Γ Γ₁}
      {els : Prog C Γ Γ₂} {e : THalt} :
      c.evalT σ = .error e → ExecSM M J σ (.ite c thn els) (.halt e)
  /-- The branch the condition picks, its locals popped. -/
  | iteThen {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {c : Val C Γ .bool} {thn : Prog C Γ Γ₁}
      {els : Prog C Γ Γ₂} {o : COut C σ.H Γ₁} :
      c.evalT σ = .ok true → ExecPM M J σ thn o →
        ExecSM M J σ (.ite c thn els) (o.map (Out.drop thn.ext))
  | iteElse {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {c : Val C Γ .bool} {thn : Prog C Γ Γ₁}
      {els : Prog C Γ Γ₂} {o : COut C σ.H Γ₂} :
      c.evalT σ = .ok false → ExecPM M J σ els o →
        ExecSM M J σ (.ite c thn els) (o.map (Out.drop els.ext))
  /-- A call whose arguments halt. -/
  | callArgs {Γ Γ' ps rs Γf : Ctx} {σ : State C Γ} {f : Name} {args : Args C Γ ps}
      {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf} {e : THalt} :
      args.evalT σ = .error e → ExecSM M J σ (.call f args ret body) (.halt e)
  /-- The body run in the callee's frame, and what the call leaves the
  caller (`TRun.call`). -/
  | callBody {Γ Γ' ps rs Γf : Ctx} {σ : State C Γ} {f : Name} {args : Args C Γ ps}
      {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf} {a : TEnv C σ.H ps}
      {o : COut C (ret.enterT (σ.withEnv a)).st.H Γf} :
      args.evalT σ = .ok a → ExecPM M J (ret.enterT (σ.withEnv a)).st body o →
        ExecSM M J σ (.call f args ret body)
          (o.map (TRun.callLeave ret body.ext σ (ret.enterT (σ.withEnv a))))
  /-- A recursive call runs as the call of its body (`Stmt.run_callRec`). -/
  | callRec {Γ Γ' ps rs : Ctx} {σ : State C Γ} {f : Name} {d : Nat} {args : Args C Γ ps}
      {ret : CallRet Γ rs Γ'} {body : Unit → Prog C (rs ++ ps) (rs ++ ps)} {o : COut C σ.H Γ'} :
      ExecSM M J σ (.call f args ret (body ())) o → ExecSM M J σ (.callRec f d args ret body) o
  /-- `f().push(e)` and `f().pop()` continue the getter's callback run once. -/
  | callReceiver {Γ ps Γf : Ctx} {E : Ty} {σ : State C Γ} {f : Name}
      {args : Args C Γ ps} {r : Var} {body : Prog C ([.alias (.array E)] ++ ps) Γf}
      {op : ReceiverOp C Γ E} {o : COut C σ.H (.alias (.array E) :: Γ)} :
      ExecSM M J σ (.call f args (.storage _ r) body) o →
        ExecSM M J σ (.callReceiver f args r body op) (o.receiverOp op)
  /-- A successful getter precedes every callback in the deferred operand. -/
  | callReceiverPush {Γ ps Γf Γv : Ctx} {E : Ty} {σ : State C Γ} {f : Name}
      {args : Args C Γ ps} {r : Var} {body : Prog C ([.alias (.array E)] ++ ps) Γf}
      {code : Prog C Γ Γv} {value : Src C Γv E}
      {a : Out C σ.H (.alias (.array E) :: Γ)} {ref : SRef C (.array E)}
      {u : COut C a.st.H Γv} :
      ExecSM M J σ (.call f args (.storage _ r) body) (.ok a) →
      a.st.env.1 = some ref → ExecPM M J (a.st.drop (.push .refl)) code u →
      ExecSM M J σ (.callReceiverPush f args r body code value)
        ((u.pushPrefix code.ext value ref).map (fun b => ⟨b.st, a.ext.trans b.ext⟩))
  /-- An unset getter result reverts before the operand's first effect. -/
  | callReceiverPushUnset {Γ ps Γf Γv : Ctx} {E : Ty} {σ : State C Γ} {f : Name}
      {args : Args C Γ ps} {r : Var} {body : Prog C ([.alias (.array E)] ++ ps) Γf}
      {code : Prog C Γ Γv} {value : Src C Γv E}
      {a : Out C σ.H (.alias (.array E) :: Γ)} :
      ExecSM M J σ (.call f args (.storage _ r) body) (.ok a) → a.st.env.1 = none →
      ExecSM M J σ (.callReceiverPush f args r body code value) (.halt .revert)
  /-- Getter failure stops `f().push(e)` before its operand. -/
  | callReceiverPushHalt {Γ ps Γf Γv : Ctx} {E : Ty} {σ : State C Γ} {f : Name}
      {args : Args C Γ ps} {r : Var} {body : Prog C ([.alias (.array E)] ++ ps) Γf}
      {code : Prog C Γ Γv} {value : Src C Γv E} {err : THalt} :
      ExecSM M J σ (.call f args (.storage _ r) body) (.halt err) →
      ExecSM M J σ (.callReceiverPush f args r body code value) (.halt err)
  /-- A getter's invariant violation stops `f().push(e)` before its operand. -/
  | callReceiverPushViolated {Γ ps Γf Γv : Ctx} {E : Ty} {σ : State C Γ} {f : Name}
      {args : Args C Γ ps} {r : Var} {body : Prog C ([.alias (.array E)] ++ ps) Γf}
      {code : Prog C Γ Γv} {value : Src C Γv E} :
      ExecSM M J σ (.call f args (.storage _ r) body) .violated →
      ExecSM M J σ (.callReceiverPush f args r body code value) .violated
  /-- The call reverts in the caller: no code at the address, or the callee
  reverts. -/
  | tryRevert {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {self : Bool} :
      ExecSM M J σ (.tryCall call rets ok err code pnc other sargs sbody self) (.halt .revert)
  /-- Data that the return variables do not decode. -/
  | tryDecode {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {self : Bool} {vs : List Word} {e : THalt} :
      rets.decodeT (C := C) (H := σ.H) vs = .error e →
        ExecSM M J σ (.tryCall call rets ok err code pnc other sargs sbody self) (.halt e)
  /-- KeY's "invariant on exit": control leaves with `J` broken. -/
  | tryViolated {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {self : Bool} :
      ¬ J.at σ → ExecSM M J σ (.tryCall call rets ok err code pnc other sargs sbody self) .violated
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
      J.at σ → J.at (σ.havoc st nt sb) → M.Allows J σ st nt sb →
        rets.decodeT vs = .ok (r, rest) →
        ExecPM M J ((σ.havoc st nt sb).withEnv (TEnv.append ρ r σ.env)) ok o →
        (self = true → (call.addr.evalT σ).1 ≠ 0 ∧
          (call.addr.evalT σ).1 ≠ σ.tx.selfAddress.1) →
          ExecSM M J σ (.tryCall call rets ok err code pnc other sargs sbody self)
            (o.map (Out.drop ((Ext.append Γ ρ).trans ok.ext)))
  /-- "Error caught": the call reverted, and its effects with it.  A
  self-call goes here only at another contract's address: the contract's own
  callee fails by `trySelfError`, `trySelfPanic`, `trySelfOther`. -/
  | tryError {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {self : Bool} {o : COut C σ.H Γ₂} :
      (self = true → (call.addr.evalT σ).1 ≠ σ.tx.selfAddress.1) → ExecPM M J σ err o →
        ExecSM M J σ (.tryCall call rets ok err code pnc other sargs sbody self) (o.map (Out.drop err.ext))
  /-- "Panic caught", with the code bound. -/
  | tryPanic {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {self : Bool} {v : Word} {o : COut C σ.H Γ₃} :
      (self = true → (call.addr.evalT σ).1 ≠ σ.tx.selfAddress.1) →
      ExecPM M J (σ.withEnv (TEnv.append κ (code.decodeT v) σ.env)) pnc o →
        ExecSM M J σ (.tryCall call rets ok err code pnc other sargs sbody self)
          (o.map (Out.drop ((Ext.append Γ κ).trans pnc.ext)))
  /-- "Other failure caught". -/
  | tryOther {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {self : Bool} {o : COut C σ.H Γ₄} :
      (self = true → (call.addr.evalT σ).1 ≠ σ.tx.selfAddress.1) → ExecPM M J σ other o →
        ExecSM M J σ (.tryCall call rets ok err code pnc other sargs sbody self) (o.map (Out.drop other.ext))
  /-- A self-call (`Stmt.tryCall`'s `self`, `docs/options.md` O8): the
  receiver is the contract, whose function runs as an inlined call, and the
  success clause from the state it leaves, its locals popped. -/
  | trySelfOk {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf}
      {o₁ : Out C σ.H (ρ ++ Γ)} {o : COut C o₁.st.H Γ₁} :
      (call.addr.evalT σ).1 ≠ 0 → (call.addr.evalT σ).1 = σ.tx.selfAddress.1 →
      ExecSM M J σ (.call call.fn sargs (.rets rets.toRet) sbody) (.ok o₁) → ExecPM M J o₁.st ok o →
        ExecSM M J σ (.tryCall call rets ok err code pnc other sargs sbody true)
          (o.map fun o' => ⟨o'.st.drop ((Ext.append Γ ρ).trans ok.ext), o₁.ext.trans o'.ext⟩)
  /-- A self-call whose callee exhausts or diverges: the caller does too. -/
  | trySelfHalt {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {e : THalt} :
      (call.addr.evalT σ).1 ≠ 0 → (call.addr.evalT σ).1 = σ.tx.selfAddress.1 →
      ExecSM M J σ (.call call.fn sargs (.rets rets.toRet) sbody) (.halt e) → e ≠ .revert → e ≠ .panic →
        (∀ d, e ≠ .revertWith d) →
        ExecSM M J σ (.tryCall call rets ok err code pnc other sargs sbody true) (.halt e)
  /-- A self-call whose callee reverts with data: the `Error` clause, from the
  caller's state (the callee's effects undone); taken when the data decodes
  as `Error(string)` (`TRun.tryCall`), here for any data. -/
  | trySelfError {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {o : COut C σ.H Γ₂}
      {d : List UInt8} :
      (call.addr.evalT σ).1 ≠ 0 → (call.addr.evalT σ).1 = σ.tx.selfAddress.1 →
      ExecSM M J σ (.call call.fn sargs (.rets rets.toRet) sbody) (.halt (.revertWith d)) → ExecPM M J σ err o →
        ExecSM M J σ (.tryCall call rets ok err code pnc other sargs sbody true)
          (o.map (Out.drop err.ext))
  /-- A self-call whose callee reverts: the catch-all, from the caller's
  state. -/
  | trySelfOther {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {o : COut C σ.H Γ₄}
      {e : THalt} :
      (call.addr.evalT σ).1 ≠ 0 → (call.addr.evalT σ).1 = σ.tx.selfAddress.1 →
      ExecSM M J σ (.call call.fn sargs (.rets rets.toRet) sbody) (.halt e) →
      (e = .revert ∨ ∃ d, e = .revertWith d) → ExecPM M J σ other o →
        ExecSM M J σ (.tryCall call rets ok err code pnc other sargs sbody true)
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
      ExecSM M J σ (.call call.fn sargs (.rets rets.toRet) sbody) (.halt e) →
      (e = .panic ∨ ∃ d, e = .revertWith d ∧ Semantics.decodePanic d = some v) →
      ExecPM M J (σ.withEnv (TEnv.append κ (code.decodeT v) σ.env)) pnc o →
        ExecSM M J σ (.tryCall call rets ok err code pnc other sargs sbody true)
          (o.map (Out.drop ((Ext.append Γ κ).trans pnc.ext)))
  /-- A self-call whose callee leaves the contract with `J` broken. -/
  | trySelfViolated {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} {σ : State C Γ} {call : ExtCall C Γ}
      {rets : Binders ρ} {ok : Prog C (ρ ++ Γ) Γ₁} {err : Prog C Γ Γ₂} {code : CodeBinder κ}
      {pnc : Prog C (κ ++ Γ) Γ₃} {other : Prog C Γ Γ₄}
      {ps Γf : Ctx} {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} :
      (call.addr.evalT σ).1 ≠ 0 → (call.addr.evalT σ).1 = σ.tx.selfAddress.1 →
      ExecSM M J σ (.call call.fn sargs (.rets rets.toRet) sbody) .violated →
        ExecSM M J σ (.tryCall call rets ok err code pnc other sargs sbody true) .violated
  /-- A loop that pays, whose condition halts. -/
  | loopHalt {Γ Γ₁ : Ctx} {σ : State C Γ} {a : LoopAnn C Γ} {c : Val C Γ .bool}
      {body : Prog C Γ Γ₁} {e : THalt} :
      Prog.callsBack J.pay body = true → c.evalT σ = .error e → ExecSM M J σ (.loop a c body) (.halt e)
  /-- The condition is false: the loop ends where it is. -/
  | loopExit {Γ Γ₁ : Ctx} {σ : State C Γ} {a : LoopAnn C Γ} {c : Val C Γ .bool}
      {body : Prog C Γ Γ₁} :
      Prog.callsBack J.pay body = true → c.evalT σ = .ok false →
        ExecSM M J σ (.loop a c body) (.ok ⟨σ, List.prefix_refl _⟩)
  /-- One iteration, its locals popped, and the loop again. -/
  | loopIter {Γ Γ₁ : Ctx} {σ : State C Γ} {a : LoopAnn C Γ} {c : Val C Γ .bool}
      {body : Prog C Γ Γ₁} {υ : Out C σ.H Γ₁} {o : COut C (υ.st.drop body.ext).H Γ} :
      Prog.callsBack J.pay body = true → c.evalT σ = .ok true → ExecPM M J σ body (.ok υ) →
        ExecSM M J (υ.st.drop body.ext) (.loop a c body) o →
          ExecSM M J σ (.loop a c body) (o.map (Out.cat (Out.drop body.ext υ)))
  /-- An iteration whose body halts or breaks the invariant. -/
  | loopStop {Γ Γ₁ : Ctx} {σ : State C Γ} {a : LoopAnn C Γ} {c : Val C Γ .bool}
      {body : Prog C Γ Γ₁} {o : COut C σ.H Γ₁} :
      Prog.callsBack J.pay body = true → c.evalT σ = .ok true → ExecPM M J σ body o → o.isOk = false →
        ExecSM M J σ (.loop a c body) (o.map (Out.drop body.ext))
  /-- A loop that pays may diverge: an over-approximation, which a box
  accepts and a diamond does not. -/
  | loopDiverge {Γ Γ₁ : Ctx} {σ : State C Γ} {a : LoopAnn C Γ} {c : Val C Γ .bool}
      {body : Prog C Γ Γ₁} :
      Prog.callsBack J.pay body = true → ExecSM M J σ (.loop a c body) (.halt .diverge)
  /-- A block that pays, statement by statement, its locals popped. -/
  | block {Γ Γ₁ : Ctx} {σ : State C Γ} {body : Prog C Γ Γ₁} {o : COut C σ.H Γ₁} :
      Prog.callsBack J.pay body = true → ExecPM M J σ body o →
        ExecSM M J σ (.block body) (o.map (Out.drop body.ext))
  /-- A `catch` clause binding the data whose callee or body may call back
(`Stmt.catchData`): it halts as any statement may, or binds some data — any:
the data a callee that called back reverts with is not the run's to say —
and runs its body, its locals popped. -/
  | catchDataHalt {Γ ρ ps Γf Γ₁ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {self : Bool} {kind : CatchKind}
      {x : Var} {body : Prog C (.mem bytesR :: Γ) Γ₁} {e : THalt} :
      (Prog.callsBack J.pay sbody || Prog.callsBack J.pay body) = true → e ≠ .panic →
        ExecSM M J σ (.catchData call rets sargs sbody self kind x body) (.halt e)
  | catchDataBody {Γ ρ ps Γf Γ₁ : Ctx} {σ : State C Γ} {call : ExtCall C Γ} {rets : Binders ρ}
      {sargs : Args C Γ ps} {sbody : Prog C (ρ ++ ps) Γf} {self : Bool} {kind : CatchKind}
      {x : Var} {body : Prog C (.mem bytesR :: Γ) Γ₁} {bs : List UInt8}
      {o₁ : Out C σ.H (.mem bytesR :: Γ)} {o : COut C o₁.st.H Γ₁} :
      (Prog.callsBack J.pay sbody || Prog.callsBack J.pay body) = true →
      TRun.litBytesT bs TRun.nil σ = .ok o₁ → ExecPM M J o₁.st body o →
        ExecSM M J σ (.catchData call rets sargs sbody self kind x body)
          (o.map fun o' => ⟨o'.st.drop ((Ext.push .refl).trans body.ext), o₁.ext.trans o'.ext⟩)

/-- `ExecPM M J σ P o`: the same, for a sequence. -/
inductive ExecPM (M : CallerModel C) (J : StateInv C) : {Γ Γ' : Ctx} → (σ : State C Γ) → Prog C Γ Γ' →
    COut C σ.H Γ' → Prop where
  | nil {Γ : Ctx} {σ : State C Γ} : ExecPM M J σ .nil (.ok ⟨σ, List.prefix_refl _⟩)
  | cons {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ₁} {P : Prog C Γ₁ Γ₂}
      {o₁ : Out C σ.H Γ₁} {o : COut C o₁.st.H Γ₂} :
      ExecSM M J σ s (.ok o₁) → ExecPM M J o₁.st P o → ExecPM M J σ (.cons s P) (o.map (Out.cat o₁))
  | halt {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ₁} {P : Prog C Γ₁ Γ₂} {e : THalt} :
      ExecSM M J σ s (.halt e) → ExecPM M J σ (.cons s P) (.halt e)
  | violated {Γ Γ₁ Γ₂ : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ₁} {P : Prog C Γ₁ Γ₂} :
      ExecSM M J σ s .violated → ExecPM M J σ (.cons s P) .violated

end

/-- `ExecFM M J σ κ o`: the frames after a program (`Frames.run`), with
callbacks: the rest of the program run so, a scope's locals popped. -/
inductive ExecFM (M : CallerModel C) (J : StateInv C) {Γ₀ : Ctx} : {Γ : Ctx} → (σ : State C Γ) → Frames C Γ Γ₀ →
    COut C σ.H Γ₀ → Prop where
  | nil {σ : State C Γ₀} : ExecFM M J σ .nil (.ok ⟨σ, List.prefix_refl _⟩)
  | seq {Γ Γ₁ : Ctx} {σ : State C Γ} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} {o₁ : Out C σ.H Γ₁}
      {o : COut C o₁.st.H Γ₀} :
      ExecPM M J σ ω (.ok o₁) → ExecFM M J o₁.st κ o → ExecFM M J σ (.seq ω κ) (o.map (Out.cat o₁))
  | seqHalt {Γ Γ₁ : Ctx} {σ : State C Γ} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} {e : THalt} :
      ExecPM M J σ ω (.halt e) → ExecFM M J σ (.seq ω κ) (.halt e)
  | seqViolated {Γ Γ₁ : Ctx} {σ : State C Γ} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} :
      ExecPM M J σ ω .violated → ExecFM M J σ (.seq ω κ) .violated
  | pop {Γ Γ' : Ctx} {σ : State C Γ'} {b : BlockKind} {h : Ext Γ Γ'} {κ : Frames C Γ Γ₀}
      {o : COut C σ.H Γ₀} :
      ExecFM M J (σ.drop h) κ o → ExecFM M J σ (.pop b h κ) o
  | drop {Γ Γ' : Ctx} {σ : State C Γ'} {h : Thin Γ Γ'} {κ : Frames C Γ Γ₀} {o : COut C σ.H Γ₀} :
      ExecFM M J (σ.thin h) κ o → ExecFM M J σ (.drop h κ) o

/-! ## The readings -/

/-- `p` after a run of a program, then of its frames `κ`, under `M`
(`COut.thenF`). -/
def COut.thenFM (M : CallerModel C) (J : StateInv C) {H : HTy} {Γ₁ Γ₀ : Ctx}
    (κ : Frames C Γ₁ Γ₀) (m : Modality) (p : State C Γ₀ → Prop) : COut C H Γ₁ → Prop
  | .ok o => ∀ o', ExecFM M J o.st κ o' → o'.after m p
  | .halt e => m.onTHalt e ∧ e ≠ .panic
  | .violated => False

/-- **Whether `φ` holds in `σ` when callees call back as `M` allows** into a
contract with invariant `I`: `holdsC`, its modalities over `ExecPM M`. -/
def holdsR (M : CallerModel C) (I : Fml C []) (pay : Bool) : {Γ : Ctx} → State C Γ → Fml C Γ → Prop
  | _, _, .tt => True
  | _, σ, .eq a b => holds σ (.eq a b)
  | _, σ, .wellFormed t => holds σ (.wellFormed t)
  | _, σ, .not φ => ¬ holdsR M I pay σ φ
  | _, σ, .and φ ψ => holdsR M I pay σ φ ∧ holdsR M I pay σ ψ
  | _, σ, .imp φ ψ => holdsR M I pay σ φ → holdsR M I pay σ ψ
  | _, σ, .upd m U φ => U.afterT m σ (holdsR M I pay · φ)
  | _, σ, .modal m P κ φ =>
    ∀ o, ExecPM M (I.stateInv pay) σ P o →
      o.thenFM M (I.stateInv pay) κ m (holdsR M I pay · φ)
  | _, σ, .havoc φ => ∀ st nt sb, holdsR M I pay (σ.havoc st nt sb) φ
  | _, σ, .all _ p φ => ∀ v : p.Denote, holdsR M I pay (σ.push (t := .val p) v) φ
  | _, σ, .bind m _ t φ => m.forallB fun v : t.TDenote C σ.H => holdsR M I pay (σ.push v) φ
  | _, σ, .anon xs φ => ∀ b, holdsR M I pay (σ.anon xs b) φ
  | _, σ, .allocAll _ A φ => ∀ o : MObj σ.H A,
      holdsR M I pay ((σ.alloc o).1.push (t := .mem A) (some (σ.alloc o).2)) φ
  | _, σ, .grow φ => ∀ g : Grown σ.H (fun _ => Unit), Heap.Keeps g.ext σ.heap g.heap →
      holdsR M I pay (σ.adopt g).1 φ

/-- **Valid under the caller model `M` and the transfer semantics `ts`**:
under `none`, `Fml.Valid` (no callee calls back); otherwise true in every
typed state when callees call back as `M` allows, keeping `ts`'s invariant,
a `transfer` and a `send` calling back as `ts` says. -/
def ValidM : CallerModel C → TransferSem C → Fml C [] → Prop
  | .none, _, φ => Fml.Valid φ
  | .staticOnly, ts, φ => ∀ σ : State C [], holdsR .staticOnly ts.inv.fml ts.pay σ φ
  | .nonReentrant R, ts, φ => ∀ σ : State C [], holdsR (.nonReentrant R) ts.inv.fml ts.pay σ φ
  | .any, ts, φ => ∀ σ : State C [], holdsR .any ts.inv.fml ts.pay σ φ

/-- `⊨ᶠₘ[M; ts] φ`: `φ` valid under the caller model `M` and the transfer
semantics `ts`. -/
scoped notation:25 "⊨ᶠₘ[" M "; " ts "] " φ:26 => ValidM M ts φ

end Solidity
