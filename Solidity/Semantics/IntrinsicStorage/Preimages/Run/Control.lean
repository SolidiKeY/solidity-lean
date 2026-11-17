import Solidity.Semantics.IntrinsicStorage.Preimages.Run

/-! Observed control-flow steps of the typed run: conditionals, calls, receivers,
`try`, loops, blocks and revert data, each returning the actual typed run result. -/
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

end Observe

end Solidity.Semantics.IntrinsicStorage
