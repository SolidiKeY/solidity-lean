import Solidity.Semantics.IntrinsicStorage.Preimages.Run

/-! Observed control-flow steps, the observed run with fuel of typed programs, and
the completed typed-frame observers `Frame.call` and `Frame.create`: some fuel
gives the actual frame result together with the inputs it hashed. -/
namespace Solidity.Semantics.IntrinsicStorage

open Solidity.Storage

namespace Observe

open Audit (lift atRef)
variable {C : Contract} {Γ : Ctx}

namespace Run

noncomputable def ite {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (h₁ : Ext Γ Γ₁)
    (thn : Step C Γ Γ₁) (h₂ : Ext Γ Γ₂) (els : Step C Γ Γ₂) : Step C Γ Γ := fun σ => do
  let v ← value σ c
  if boolT v then (thn σ).map fun o => ⟨o.st.drop h₁, o.ext⟩
  else (els σ).map fun o => ⟨o.st.drop h₂, o.ext⟩

noncomputable def call {Γ' ps rs Γf : Ctx} (a : Args C Γ ps) (ret : CallRet Γ rs Γ')
    (hb : Ext (rs ++ ps) Γf) (body : Step C (rs ++ ps) Γf) : Step C Γ Γ' := fun σ => do
  let a ← args σ a
  let o₁ := ret.enterT (σ.withEnv a)
  let o ← body o₁.st
  let e : σ.H <+: o.st.H := o₁.ext.trans o.ext
  pure ⟨o.st.withEnv
    (ret.leaveT (TEnv.wk e Γ σ.env) (TEnv.take rs (TEnv.drop hb o.st.env))), e⟩

noncomputable def receiverOp {E : Ty} (op : ReceiverOp C Γ E)
    (b : SPath C Γ (.array E)) : Step C Γ Γ := match op with
  | .push v _ => push b v
  | .pop => pop b

noncomputable def callReceiver {ps Γf : Ctx} {E : Ty} (a : Args C Γ ps) (r : Var)
    (h : Ext ([.alias (.array E)] ++ ps) Γf)
    (body : Step C ([.alias (.array E)] ++ ps) Γf) (op : ReceiverOp C Γ E) :
    Step C Γ Γ := fun σ => do
  let o ← call a (.storage (.array E) r) h body σ
  let o' ← receiverOp (op.wk (.drop .refl)) (.alias .here) o.st
  pure ⟨o'.st.drop (.push .refl), o.ext.trans o'.ext⟩

noncomputable def pushAfterPrefix {Γv : Ctx} {E : Ty} (h : Ext Γ Γv) (code : Step C Γ Γv)
    (v : Src C Γv E) (ref : SRef C (.ref (.array E))) : Step C Γ Γ := fun σ => do
  let a ← code σ
  let v ← source a.st v
  if a.st.storage.full ref then atRef ref (.error .exhausted) else
  let st ← Audit.push a.st.storage ref (fun _ => some v.strip)
  pure ⟨(a.st.withStorage st).drop h, a.ext⟩

noncomputable def afterReceiverPrefix {Γv : Ctx} {E : Ty} (he : Ext Γ Γv)
    (code : Step C Γ Γv) (v : Src C Γv E) : Step C (.alias (.array E) :: Γ) Γ := fun σ => do
  let ref ← path σ (.alias .here)
  pushAfterPrefix he code v ref (σ.drop (.push .refl))

noncomputable def callReceiverPush {ps Γf Γv : Ctx} {E : Ty} (a : Args C Γ ps) (r : Var)
    (hb : Ext ([.alias (.array E)] ++ ps) Γf) (body : Step C ([.alias (.array E)] ++ ps) Γf)
    (he : Ext Γ Γv) (code : Step C Γ Γv) (v : Src C Γv E) : Step C Γ Γ := fun σ => do
  let a ← call a (.storage (.array E) r) hb body σ
  (afterReceiverPrefix he code v a.st).map fun b => ⟨b.st, a.ext.trans b.ext⟩

noncomputable def tryCall {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} (ec : ExtCall C Γ) (rets : Binders ρ)
    (h₁ : Ext (ρ ++ Γ) Γ₁) (ok : Step C (ρ ++ Γ) Γ₁)
    (h₂ : Ext Γ Γ₂) (err : Step C Γ Γ₂) (code : CodeBinder κ)
    (h₃ : Ext (κ ++ Γ) Γ₃) (pnc : Step C (κ ++ Γ) Γ₃)
    (h₄ : Ext Γ Γ₄) (other : Step C Γ Γ₄) (sargs : Args C Γ ps)
    (hs : Ext (ρ ++ ps) Γf) (sbody : Step C (ρ ++ ps) Γf) (self : Bool) : Step C Γ Γ := fun σ =>
  if (ec.addr.evalT σ).1 = 0 then lift (.error .revert) else
  if self && decide ((ec.addr.evalT σ).1 = σ.tx.selfAddress.1) then
    Audit.follow (call sargs (.rets rets.toRet) hs sbody σ) fun res => match res with
    | .ok o => (ok o.st).map fun o' =>
      ⟨o'.st.drop ((Ext.append Γ ρ).trans h₁), o.ext.trans o'.ext⟩
    | .error .revert => (other σ).map fun o => ⟨o.st.drop h₄, o.ext⟩
    | .error (.revertWith d) =>
      match Semantics.decodeError d with
      | some _ => (err σ).map fun o => ⟨o.st.drop h₂, o.ext⟩
      | none => match Semantics.decodePanic d with
        | some c => (pnc (σ.withEnv (TEnv.append κ (code.decodeT (H := σ.H) c) σ.env))).map
            fun o => ⟨o.st.drop ((Ext.append Γ κ).trans h₃), o.ext⟩
        | none => (other σ).map fun o => ⟨o.st.drop h₄, o.ext⟩
    | .error .panic =>
      (pnc (σ.withEnv (TEnv.append κ (code.decodeT (H := σ.H) (TRun.selfPanicCode ec σ)) σ.env))).map
        fun o => ⟨o.st.drop ((Ext.append Γ κ).trans h₃), o.ext⟩
    | .error e => lift (.error e)
  else match lookupBy (ec.keyT σ) σ.tx.ext with
  | none => lift (.error .revert)
  | some (.ok vs) => do
    let (r, _) ← lift (rets.decodeT (H := σ.H) vs)
    (ok (σ.withEnv (TEnv.append ρ r σ.env))).map fun o =>
      ⟨o.st.drop ((Ext.append Γ ρ).trans h₁), o.ext⟩
  | some (.error _) => (err σ).map fun o => ⟨o.st.drop h₂, o.ext⟩
  | some (.panic c) =>
    (pnc (σ.withEnv (TEnv.append κ (code.decodeT (H := σ.H) c) σ.env))).map
      fun o => ⟨o.st.drop ((Ext.append Γ κ).trans h₃), o.ext⟩
  | some (.other _) => (other σ).map fun o => ⟨o.st.drop h₄, o.ext⟩

/-- Finite observed loop prefixes use exactly the existing loop-fuel convention. -/
def iterate (body : α → Audit α) (cond : α → Audit Bool) : Nat → α → Audit α
  | 0, _ => lift (.error .diverge)
  | n + 1, σ => do
    let b ← cond σ
    if b then iterate body cond n (← body σ) else pure σ

noncomputable def loop {Γ₁ : Ctx} (n : Nat) (c : Val C Γ .bool) (h : Ext Γ Γ₁)
    (body : Step C Γ Γ₁) : Step C Γ Γ := fun σ => iterate
  (fun o : Out C σ.H Γ => (body o.st).map fun o' => ⟨o'.st.drop h, o.ext.trans o'.ext⟩)
  (fun o => value o.st c) n ⟨σ, List.prefix_refl _⟩

def block {Γ₁ : Ctx} (h : Ext Γ Γ₁) (body : Step C Γ Γ₁) : Step C Γ Γ := fun σ =>
  (body σ).map fun o => ⟨o.st.drop h, o.ext⟩

def seq {Γ₁ Γ₂ : Ctx} (s : Step C Γ Γ₁) (p : Step C Γ₁ Γ₂) : Step C Γ Γ₂ := fun σ => do
  let o ← s σ
  (p o.st).map fun o' => ⟨o'.st, o.ext.trans o'.ext⟩

def nil : Step C Γ Γ := fun σ => pure ⟨σ, List.prefix_refl _⟩

noncomputable def revPart (σ : State C Γ) : RevPart C Γ → Audit (List UInt8)
  | .word v => do
    let x ← value σ v
    pure (Semantics.wordBytes (PrimTy.toWord x).1.toNat)
  | .bytes bs => lift (RevPart.evalT σ (.bytes bs))
  | .sel sig => ⟨RevPart.evalT σ (.sel sig), ⟨[], [sig.toUTF8.data.toList]⟩⟩
  | .mem kind src => lift (RevPart.evalT σ (.mem kind src))

noncomputable def revertData (d : List (RevPart C Γ)) : Step C Γ Γ := fun σ => do
  let bs ← d.mapM (revPart σ)
  lift (.error (THalt.ofData bs.flatten))

noncomputable def litWrites {Γ₁ : Ctx} : List UInt8 → Nat →
    Step C (.mem bytesR :: Γ) Γ₁ → Step C (.mem bytesR :: Γ) Γ₁
  | [], _, k => k
  | b :: bs, i, k => if hi : i < 2 ^ 256 then
      seq (assignMem (litLoc i hi) (litSrc b)) (litWrites bs (i + 1) k)
    else k

noncomputable def litBytes {Γ₁ : Ctx} (bs : List UInt8)
    (k : Step C (.mem bytesR :: Γ) Γ₁) : Step C Γ Γ₁ :=
  if hn : bs.length < 2 ^ 256 then
    seq (declMem bytesR (some (.newArr (.lit (bs.length : Int) (PrimTy.inRange_uint_of_lt hn)) rfl)) rfl)
      (litWrites bs 0 k)
  else seq (declMem bytesR none rfl) k

noncomputable def catchBytes {ρ ps Γf : Ctx} (ec : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (hs : Ext (ρ ++ ps) Γf) (sbody : Step C (ρ ++ ps) Γf)
    (self : Bool) (σ : State C Γ) : Audit (List UInt8) :=
  if (ec.addr.evalT σ).1 = 0 then lift (.error .revert) else
  if self && decide ((ec.addr.evalT σ).1 = σ.tx.selfAddress.1) then
    Audit.follow (call sargs (.rets rets.toRet) hs sbody σ) fun res => match res with
    | .ok _ => lift (.error .revert)
    | .error .revert => pure []
    | .error (.revertWith d) => pure d
    | .error .panic => pure (Semantics.encodePanic (TRun.selfPanicCode ec σ).1.toNat)
    | .error e => lift (.error e)
  else lift (TRun.catchBytes ec rets sargs hs (fun σ => (sbody σ).result) self σ)

noncomputable def catchData {ρ ps Γf Γ₁ : Ctx} (ec : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (hs : Ext (ρ ++ ps) Γf) (sbody : Step C (ρ ++ ps) Γf)
    (self : Bool) (kind : CatchKind) (h₁ : Ext (.mem bytesR :: Γ) Γ₁)
    (body : Step C (.mem bytesR :: Γ) Γ₁) : Step C Γ Γ := fun σ => do
  let d ← catchBytes ec rets sargs hs sbody self σ
  match kind.decode d with
  | none => lift (.error .revert)
  | some bs => (litBytes bs body σ).map fun o => ⟨o.st.drop ((Ext.push .refl).trans h₁), o.ext⟩

def project {Γ Δ : Ctx} (s : Step C Γ Δ) : TStep C Γ Δ := fun σ => (s σ).result

theorem iterate_result (body : α → Audit α) (cond : α → Audit Bool) (n : Nat) (σ : α) :
    (iterate body cond n σ).result =
      TLoop.runF (fun x => (body x).result) (fun x => (cond x).result) n σ := by
  induction n generalizing σ with
  | zero => rfl
  | succ n ih =>
    simp only [iterate, Audit.result_bind]
    cases hc : (cond σ).result with
    | error e => simp only [hc, Solidity.error_bind, TLoop.runF, TLoop.iterN, TLoop.step]
    | ok b => cases b <;> cases hb : (body σ).result <;>
        simp [Solidity.ok_bind, Solidity.error_bind, Audit.result_bind, ih, hb, hc,
          TLoop.runF, TLoop.iterN, TLoop.step] <;> rfl

theorem ite_result {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (h₁ : Ext Γ Γ₁)
    (thn : Step C Γ Γ₁) (h₂ : Ext Γ Γ₂) (els : Step C Γ Γ₂) (σ : State C Γ) :
    (ite c h₁ thn h₂ els σ).result = TRun.ite c h₁ (project thn) h₂ (project els) σ := by
  simp only [ite, TRun.ite, Audit.result_bind, Audit.result_map_direct, value_result, apply_ite Audit.result, project]

theorem call_result {Γ' ps rs Γf : Ctx} (a : Args C Γ ps) (ret : CallRet Γ rs Γ')
    (hb : Ext (rs ++ ps) Γf) (body : Step C (rs ++ ps) Γf) (σ : State C Γ) :
    (call a ret hb body σ).result = TRun.call a ret hb (project body) σ := by
  simp only [call, TRun.call, Audit.result_bind, Audit.result_pure, args_result, project]

theorem receiverOp_result {E : Ty} (op : ReceiverOp C Γ E)
    (b : SPath C Γ (.array E)) (σ : State C Γ) :
    (receiverOp op b σ).result = TRun.receiverOp op b σ := by
  cases op <;> simp only [receiverOp, TRun.receiverOp, push_result, pop_result]

theorem callReceiver_result {ps Γf : Ctx} {E : Ty} (a : Args C Γ ps) (r : Var)
    (h : Ext ([.alias (.array E)] ++ ps) Γf)
    (body : Step C ([.alias (.array E)] ++ ps) Γf) (op : ReceiverOp C Γ E) (σ : State C Γ) :
    (callReceiver a r h body op σ).result = TRun.callReceiver a r h (project body) op σ := by
  simp only [callReceiver, TRun.callReceiver, Audit.result_bind, Audit.result_pure, call_result, receiverOp_result]

theorem pushAfterPrefix_result {Γv : Ctx} {E : Ty} (h : Ext Γ Γv) (code : Step C Γ Γv)
    (v : Src C Γv E) (ref : SRef C (.ref (.array E))) (σ : State C Γ) :
    (pushAfterPrefix h code v ref σ).result = TRun.pushAfterPrefix h (project code) v ref σ := by
  simp only [pushAfterPrefix, TRun.pushAfterPrefix, Audit.result_bind, Audit.result_pure, Audit.result_atRef, Audit.result_push, source_result, apply_ite Audit.result, project]

theorem afterReceiverPrefix_result {Γv : Ctx} {E : Ty} (he : Ext Γ Γv)
    (code : Step C Γ Γv) (v : Src C Γv E) (σ : State C (.alias (.array E) :: Γ)) :
    (afterReceiverPrefix he code v σ).result = TRun.afterReceiverPrefix he (project code) v σ := by
  simp only [afterReceiverPrefix, TRun.afterReceiverPrefix, Audit.result_bind, path_result, pushAfterPrefix_result]

theorem callReceiverPush_result {ps Γf Γv : Ctx} {E : Ty} (a : Args C Γ ps) (r : Var)
    (hb : Ext ([.alias (.array E)] ++ ps) Γf) (body : Step C ([.alias (.array E)] ++ ps) Γf)
    (he : Ext Γ Γv) (code : Step C Γ Γv) (v : Src C Γv E) (σ : State C Γ) :
    (callReceiverPush a r hb body he code v σ).result = TRun.callReceiverPush a r hb (project body) he (project code) v σ := by
  simp only [callReceiverPush, TRun.callReceiverPush, Audit.result_bind, Audit.result_map_direct, call_result, afterReceiverPrefix_result]

theorem tryCall_result {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} (ec : ExtCall C Γ) (rets : Binders ρ)
    (h₁ : Ext (ρ ++ Γ) Γ₁) (ok : Step C (ρ ++ Γ) Γ₁)
    (h₂ : Ext Γ Γ₂) (err : Step C Γ Γ₂) (code : CodeBinder κ)
    (h₃ : Ext (κ ++ Γ) Γ₃) (pnc : Step C (κ ++ Γ) Γ₃)
    (h₄ : Ext Γ Γ₄) (other : Step C Γ Γ₄) (sargs : Args C Γ ps)
    (hs : Ext (ρ ++ ps) Γf) (sbody : Step C (ρ ++ ps) Γf) (self : Bool) (σ : State C Γ) :
    (tryCall ec rets h₁ ok h₂ err code h₃ pnc h₄ other sargs hs sbody self σ).result = TRun.tryCall ec rets h₁ (project ok) h₂ (project err) code h₃ (project pnc) h₄ (project other) sargs hs (project sbody) self σ := by
  simp only [tryCall, TRun.tryCall, Audit.result_lift, Audit.result_follow, apply_ite Audit.result, call_result, project]
  all_goals repeat first | simp_all only [Audit.result_map_direct, Audit.result_lift, Audit.result_bind] | split

theorem loop_result {Γ₁ : Ctx} (n : Nat) (c : Val C Γ .bool) (h : Ext Γ Γ₁)
    (body : Step C Γ Γ₁) (σ : State C Γ) :
    (loop n c h body σ).result = TRun.loopF n c h (project body) σ := by
  simp only [loop, TRun.loopF, Audit.result_map_direct, value_result, iterate_result, project]

theorem block_result {Γ₁ : Ctx} (h : Ext Γ Γ₁) (body : Step C Γ Γ₁) (σ : State C Γ) :
    (block h body σ).result = TRun.block h (project body) σ := by
  simp only [block, TRun.block, Audit.result_map_direct, project]

theorem seq_result {Γ₁ Γ₂ : Ctx} (s : Step C Γ Γ₁) (p : Step C Γ₁ Γ₂) (σ : State C Γ) :
    (seq s p σ).result = TRun.seq (project s) (project p) σ := by
  simp only [seq, TRun.seq, Audit.result_bind, Audit.result_map_direct, project]
  cases (s σ).result <;> rfl

theorem nil_result (σ : State C Γ) : (nil σ).result = TRun.nil σ := rfl

theorem revPart_result (σ : State C Γ) (p : RevPart C Γ) :
    (revPart σ p).result = p.evalT σ := by
  cases p <;> simp only [revPart, RevPart.evalT, Audit.result_bind,
    Audit.result_pure, Audit.result_lift, value_result]

theorem revertData_result (d : List (RevPart C Γ)) (σ : State C Γ) :
    (revertData d σ).result = TRun.revertData d σ := by
  simp only [revertData, TRun.revertData, Audit.result_bind, Audit.result_mapM,
    revPart_result, Audit.result_lift]

theorem litWrites_result {Γ₁ : Ctx} (bs : List UInt8) (i : Nat)
    (k : Step C (.mem bytesR :: Γ) Γ₁) (σ : State C (.mem bytesR :: Γ)) :
    (litWrites bs i k σ).result = TRun.litWritesT bs i (project k) σ := by
  induction bs generalizing i σ with
  | nil => rfl
  | cons b bs ih =>
    rw [litWrites, TRun.litWritesT]
    split <;> simp only [seq_result, TRun.seq, project, assignMem_result, ih]

theorem litBytes_result {Γ₁ : Ctx} (bs : List UInt8)
    (k : Step C (.mem bytesR :: Γ) Γ₁) (σ : State C Γ) :
    (litBytes bs k σ).result = TRun.litBytesT bs (project k) σ := by
  unfold litBytes TRun.litBytesT
  split <;> rw [seq_result] <;>
    simp only [TRun.seq, project, declMem_result, litWrites_result]

theorem catchBytes_result {ρ ps Γf : Ctx} (ec : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (hs : Ext (ρ ++ ps) Γf) (sbody : Step C (ρ ++ ps) Γf)
    (self : Bool) (σ : State C Γ) :
    (catchBytes ec rets sargs hs sbody self σ).result =
      TRun.catchBytes ec rets sargs hs (project sbody) self σ := by
  unfold catchBytes
  split
  · simp only [Audit.result_lift, TRun.catchBytes, * , ↓reduceIte]
  · split
    · simp only [Audit.result_follow, call_result, TRun.catchBytes, *, ↓reduceIte]
      repeat first | simp_all only [Audit.result_lift, Audit.result_pure] | split | rfl
    · rfl

theorem catchData_result {ρ ps Γf Γ₁ : Ctx} (ec : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (hs : Ext (ρ ++ ps) Γf) (sbody : Step C (ρ ++ ps) Γf)
    (self : Bool) (kind : CatchKind) (h₁ : Ext (.mem bytesR :: Γ) Γ₁)
    (body : Step C (.mem bytesR :: Γ) Γ₁) (σ : State C Γ) :
    (catchData ec rets sargs hs sbody self kind h₁ body σ).result =
      TRun.catchData ec rets sargs hs (project sbody) self kind h₁ (project body) σ := by
  simp only [catchData, TRun.catchData, Audit.result_bind, catchBytes_result]
  congr 1
  funext d
  split <;> simp_all only [Audit.result_lift, Audit.result_map_direct, litBytes_result]

end Run

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
    rw [program, Prog.runFC, Run.seq_result]
    rw [statement_project, program_project]

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
  simp only [call, World.call, Audit.result_bind, Audit.result_lift, Audit.result_pure]
  exact TRes.Approx.bind (callFrame_approx n w r entry ctx) (fun _ => .refl _)

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
