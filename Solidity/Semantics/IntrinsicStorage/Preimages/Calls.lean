import Solidity.Semantics.IntrinsicStorage.Preimages.Run.Control

/-! The observed run with fuel of typed programs and the completed typed-frame observers
`Frame.call` and `Frame.create`: a finite observation approximates the actual frame
result and keeps the inputs it hashed, also before a caught or uncaught revert. -/
namespace Solidity.Semantics.IntrinsicStorage

open Solidity.Storage

namespace Observe

open Audit (lift atRef)
variable {C : Contract} {Γ : Ctx}

mutual
/-- The compiled typed run with fuel of a statement. -/
noncomputable def statement (n : Nat) : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Step C Γ Γ'
  | _, _, .assign l r => Run.assign l r
  | _, _, .rebind i r => Run.rebind i r
  | _, _, .assignLocal i r => Run.assignLocal i r
  | _, _, .declLocal p _ init => Run.declLocal p init
  | _, _, .declStorage R _ init => Run.declStorage R init
  | _, _, .opAssign op _ _ l r => Run.opAssign op l r
  | _, _, .incDec op _ l => Run.incDec op l
  | _, _, .pushOpAssign op _ _ b r => Run.pushOpAssign op b r
  | _, _, .pushIncDec op _ b => Run.pushIncDec op b
  | _, _, .assignIncDec i op _ l _ => Run.assignIncDec i op l
  | _, _, .assignLocalPush i b => Run.assignLocalPush i b
  | _, _, .push b v _ => Run.push b v
  | _, _, .pop b => Run.pop b
  | _, _, .transfer r a => Run.transfer r a
  | _, _, .send pv r a _ => Run.send pv r a
  | _, _, .declMem R _ init _ hm => Run.declMem R init hm
  | _, _, .rebindMem i r => Run.rebindMem i r
  | _, _, .assignFromMem l p => Run.assignFromMem l p
  | _, _, .assignMem l r => Run.assignMem l r
  | _, _, .delete l => Run.delete l
  | _, _, .deleteMem p _ => Run.deleteMem p
  | _, _, .assignNew l n' h => Run.assignNew l n' h
  | _, _, .ite c thn els => Run.ite c thn.ext (program n thn) els.ext (program n els)
  | _, _, .require c => Run.require c
  | _, _, .assert c => Run.assert c
  | _, _, .revert => fun _ => Audit.lift (.error .revert)
  | _, _, .assumeFalse => fun _ => Audit.lift (.error .exhausted)
  | _, _, .call _ args ret body => Run.call args ret body.ext (program n body)
  | _, _, .callReceiver _ args r body op =>
    Run.callReceiver args r body.ext (program n body) op
  | _, _, .callReceiverPush _ args r body code value =>
    Run.callReceiverPush args r body.ext (program n body)
      code.ext (program n code) value
  | _, _, .tryCall call rets ok err code pnc other sargs sbody self =>
    Run.tryCall call rets ok.ext (program n ok) err.ext (program n err) code pnc.ext
      (program n pnc) other.ext (program n other) sargs sbody.ext (program n sbody) self
  | _, _, .loop _ c body => Run.loop n c body.ext (program n body)
  | _, _, .block body => Run.block body.ext (program n body)
  | _, _, .callRec _ _ args ret body =>
    Run.call args ret (body ()).ext (program n (body ()))
  | _, _, .revertData d => Run.revertData d
  | _, _, .catchData c rets sargs sbody self kind _ body =>
    Run.catchData c rets sargs sbody.ext (program n sbody) self kind body.ext (program n body)

/-- The compiled typed run with fuel of a sequence. -/
noncomputable def program (n : Nat) : {Γ Γ' : Ctx} → Prog C Γ Γ' → Step C Γ Γ'
  | _, _, .nil => Run.nil
  | _, _, .cons s P => Run.seq (statement n s) (program n P)
end

mutual
theorem statement_project (n : Nat) : {Γ Δ : Ctx} → (s : Stmt C Γ Δ) →
    Run.project (statement n s) = s.runFC n
  | _, _, .assign .. | _, _, .rebind .. | _, _, .assignLocal .. | _, _, .declLocal ..
  | _, _, .declStorage .. | _, _, .opAssign .. | _, _, .incDec .. | _, _, .pushOpAssign ..
  | _, _, .pushIncDec .. | _, _, .assignIncDec .. | _, _, .assignLocalPush .. | _, _, .push ..
  | _, _, .pop .. | _, _, .transfer .. | _, _, .send .. | _, _, .declMem .. | _, _, .rebindMem ..
  | _, _, .assignFromMem .. | _, _, .assignMem .. | _, _, .delete .. | _, _, .deleteMem ..
  | _, _, .assignNew .. | _, _, .ite .. | _, _, .require .. | _, _, .assert .. | _, _, .revert ..
  | _, _, .assumeFalse .. | _, _, .call .. | _, _, .callReceiver .. | _, _, .callReceiverPush ..
  | _, _, .tryCall .. | _, _, .loop .. | _, _, .block .. | _, _, .callRec ..
  | _, _, .revertData .. | _, _, .catchData .. => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.assign_result, Run.rebind_result, Run.assignLocal_result,
      Run.declLocal_result, Run.declStorage_result, Run.opAssign_result, Run.incDec_result,
      Run.pushOpAssign_result, Run.pushIncDec_result, Run.assignIncDec_result,
      Run.assignLocalPush_result, Run.push_result, Run.pop_result, Run.transfer_result,
      Run.send_result, Run.declMem_result, Run.rebindMem_result, Run.assignFromMem_result,
      Run.assignMem_result, Run.delete_result, Run.deleteMem_result, Run.assignNew_result,
      Run.ite_result, program_project, Run.require_result, Run.assert_result, Audit.result_lift,
      Run.call_result, Run.callReceiver_result, Run.callReceiverPush_result, Run.tryCall_result,
      Run.loop_result, Run.block_result, Run.revertData_result, Run.catchData_result]

theorem program_project (n : Nat) : {Γ Δ : Ctx} → (p : Prog C Γ Δ) →
    Run.project (program n p) = p.runFC n
  | _, _, .nil => funext Run.nil_result
  | _, _, .cons s p => by
    funext σ
    change (program n (.cons s p) σ).result = _
    rw [program, Prog.runFC, Run.seq_result, statement_project, program_project]
end

theorem program_result (n : Nat) {Γ Δ : Ctx} (p : Prog C Γ Δ) (σ : State C Γ) :
    (program n p σ).result = p.runFC n σ := congrFun (program_project n p) σ

/-- Every finite observation projects to the unchanged actual run, or reports
that its loop prefix has not yet finished. This includes actual error results. -/
theorem program_approx (n : Nat) {Γ Δ : Ctx} (p : Prog C Γ Δ) (σ : State C Γ) :
    TRes.Approx (program n p σ).result (p.run σ) := by
  rw [program_result, ← Prog.runF_eq]
  exact Prog.runF_approx n p σ

theorem program_agrees (n : Nat) {Γ Δ : Ctx} (p : Prog C Γ Δ) (σ : State C Γ)
    (finished : (program n p σ).result ≠ .error .diverge) :
    (program n p σ).result = p.run σ := (program_approx n p σ).eq finished

/-- A later halt cannot erase a previously reached statement's slot inputs. -/
theorem cons_slots {Γ Δ Ξ : Ctx} (n : Nat) (s : Stmt C Γ Δ) (p : Prog C Δ Ξ)
    (σ : State C Γ) {b : List UInt8} (h : b ∈ (statement n s σ).inputs.slots) :
    b ∈ (program n (.cons s p) σ).inputs.slots :=
  Audit.bind_slots_left _ _ h

end Observe

namespace Frame

open ContractWorld
variable {K : Type} [DecidableEq K] {contracts : K → Contract}

/-- The actual guarded callee frame, with observations retained independently
of its result. Only loop observation is bounded; entry and settlement are unchanged. -/
noncomputable def callFrame (n : Nat) (w : World contracts) {k : K} {α : Type}
    (r : Handle k) (entry : Entry (contracts k) α) (ctx : Context) :
    Audit (World contracts × State (contracts k) entry.locals) := do
  if w.isLibrary k || (ctx.isStatic && !(emptyBody entry.body)) then
    Audit.lift (.error .revert)
  else
    let st ← Audit.lift (TRes.ofOpt (w.storage? r))
    let σ ← Audit.lift (w.enter r.address ctx st entry.payable)
    let o ← Observe.program n entry.body σ
    let next ← Audit.lift (w.finish r.address o.st)
    pure (next, o.st)

theorem callFrame_approx (n : Nat) (w : World contracts) {k : K} {α : Type}
    (r : Handle k) (entry : Entry (contracts k) α) (ctx : Context) :
    TRes.Approx (callFrame n w r entry ctx).result (w.callFrame r entry ctx) := by
  unfold callFrame World.callFrame
  split
  · exact .refl _
  · simp only [Audit.result_bind, Audit.result_lift, Audit.result_pure]
    exact .bind (.refl _) fun _ => .bind (.refl _) fun σ =>
      .bind (Observe.program_approx n entry.body σ) fun _ => .refl _

noncomputable def call (n : Nat) (w : World contracts) {k : K} {α : Type}
    (r : Handle k) (entry : Entry (contracts k) α) (ctx : Context) :
    Audit (World contracts × α) := do
  let (next, σ) ← callFrame n w r entry ctx
  let result ← Audit.lift (entry.result σ)
  pure (next, result)

theorem call_approx (n : Nat) (w : World contracts) {k : K} {α : Type}
    (r : Handle k) (entry : Entry (contracts k) α) (ctx : Context) :
    TRes.Approx (call n w r entry ctx).result (w.call r entry ctx) := by
  simpa only [call, World.call, Audit.result_bind, Audit.result_lift, Audit.result_pure] using
    TRes.Approx.bind (callFrame_approx n w r entry ctx) (fun _ => .refl _)

noncomputable def create (n : Nat) (w : World contracts) (k : K) (self : Address)
    (ctor : Prog (contracts k) [] []) (ctx : Context) : Audit (World contracts × Handle k) :=
  if w.isLibrary k then Audit.lift (.error .revert) else do
    if (w.accounts self).isSome || decide (self = ctx.sender) || ctx.isStatic then
      Audit.lift (.error .revert)
    else
      let σ ← Audit.lift (w.enter self ctx (Storage.init (contracts k))
        (((contracts k).ctor.map (·.payable)).getD false))
      let o ← Observe.program n ctor σ
      let next ← Audit.lift (w.finish self o.st)
      pure (next, ⟨self⟩)

omit [DecidableEq K] in
theorem create_approx (n : Nat) (w : World contracts) (k : K) (self : Address)
    (ctor : Prog (contracts k) [] []) (ctx : Context) :
    TRes.Approx (create n w k self ctor ctx).result (w.create k self ctor ctx) := by
  unfold create World.create
  split
  · exact .refl _
  · show TRes.Approx _ (ite _ _ _)
    split
    · exact .refl _
    · simp only [Audit.result_bind, Audit.result_lift, Audit.result_pure]
      exact .bind (.refl _) fun σ => .bind (Observe.program_approx n ctor σ) fun _ => .refl _

/-- Atomic rollback changes the returned world, never the observed inputs. -/
def atomic (w : World contracts) (a : Audit (World contracts × α)) :
    (World contracts × TRes α) × Inputs := (ContractWorld.atomic w a.result, a.inputs)

omit [DecidableEq K] in
theorem atomic_failed (w : World contracts) (a : Audit (World contracts × α))
    {e : THalt} (h : a.result = .error e) :
    atomic w a = ((w, .error e), a.inputs) := by
  simp only [atomic, h, ContractWorld.atomic]

end Frame

end Solidity.Semantics.IntrinsicStorage
