import Solidity.Calculus.Blocks
import Solidity.Semantics.NoPanic

/-!
# The data a revert carries comes from the program

`Stmt.revertDatas` (`Calculus/Blocks.lean`) reads off a program the data
its reverts may carry: a revert with data (`THalt.revertWith`) is raised by
a `revert(d)` only (`TRun.revertData`), every other step halts with no data
(an evaluator only reverts, `TRes.RevertOnly`), and a `try`'s self-call
callee reverts into its `try`, not past it.  So a run's data is one the
program lists (`Prog.run_dataS`): what `catchDataBox`'s goals range over
(`docs/semantic-gaps.md`, "Revert data").  The proofs follow
`Semantics/NoPanic.lean`'s, step by step.
-/

namespace Solidity

variable {C : Contract} {K : List UInt8 → Prop} {S : DSet}

/-! ## Typed results -/

/-- A typed result whose data, if it reverts with some that `K` keeps, is
one of `S` (`DSet.Mem`: literal, or matching a datum known in part). -/
def TRes.DataS {α : Type} (K : List UInt8 → Prop) (S : DSet) (t : TRes α) : Prop :=
  ∀ d, t = .error (.revertWith d) → K d → S.Mem d

theorem DSet.mem_left (A B : DSet) : ∀ d, A.Mem d → DSet.Mem (A.1 ++ B.1, A.2 ++ B.2) d
  | _, .inl h => .inl (List.mem_append_left _ h)
  | _, .inr ⟨p, hp, hm⟩ => .inr ⟨p, List.mem_append_left _ hp, hm⟩

theorem DSet.mem_right (A B : DSet) : ∀ d, B.Mem d → DSet.Mem (A.1 ++ B.1, A.2 ++ B.2) d
  | _, .inl h => .inl (List.mem_append_right _ h)
  | _, .inr ⟨p, hp, hm⟩ => .inr ⟨p, List.mem_append_right _ hp, hm⟩

/-- Data known in part, appended, stand for the data appended. -/
theorem Pat.Matches.append {p q : Pat} {d e : List UInt8} (hp : p.Matches d) (hq : q.Matches e) :
    (p ++ q).Matches (d ++ e) := by
  refine ⟨by simp only [List.length_append, hp.1, hq.1], fun i b h => ?_⟩
  by_cases hi : i < p.length
  · rw [List.getElem?_append_left hi] at h
    rw [List.getElem?_append_left (hp.1 ▸ hi)]
    exact hp.2 i b h
  · have hi' : p.length ≤ i := Nat.le_of_not_lt hi
    rw [List.getElem?_append_right hi'] at h
    rw [List.getElem?_append_right (hp.1 ▸ hi'), ← hp.1]
    exact hq.2 _ b h

/-- Literal bytes stand for themselves. -/
theorem Pat.matches_lit (bs : List UInt8) : Pat.Matches (bs.map some) bs :=
  ⟨List.length_map _, fun i b h => by
    rw [List.getElem?_map] at h
    cases hb : bs[i]? with
    | none => rw [hb] at h; cases h
    | some c => rw [hb] at h; cases h; rfl⟩

/-- A word of unknown bytes stands for any word. -/
theorem Pat.matches_word (n : Nat) : Pat.Matches (List.replicate 32 none) (Semantics.wordBytes n) :=
  ⟨by simp only [List.length_replicate, Semantics.wordBytes, List.length_map, List.length_range],
    fun i b h => by
      rw [List.getElem?_replicate] at h
      split at h <;> cases h⟩

/-- The data a clause keeps: every datum for the raw data, one that decodes
as `Error` for `catch Error(string memory r)`. -/
def dataKeep (raw : Bool) (d : List UInt8) : Prop :=
  raw = true ∨ (Semantics.decodeError d).isSome = true

namespace TRes.DataS

theorem ok {α : Type} (a : α) : TRes.DataS K S (Except.ok a : TRes α) := fun _ h => nomatch h

theorem revert {α : Type} : TRes.DataS K S (Except.error .revert : TRes α) := fun _ h => nomatch h

theorem exhausted {α : Type} : TRes.DataS K S (Except.error .exhausted : TRes α) :=
  fun _ h => nomatch h

theorem diverge {α : Type} : TRes.DataS K S (Except.error .diverge : TRes α) := fun _ h => nomatch h

theorem panic {α : Type} : TRes.DataS K S (Except.error .panic : TRes α) := fun _ h => nomatch h

theorem bind {α γ : Type} {t : TRes α} (h : t.DataS K S) {k : α → TRes γ}
    (hk : ∀ a, (k a).DataS K S) : (t >>= k).DataS K S := by
  match t with
  | .ok a => exact hk a
  | .error e => exact fun d h' => h d (by cases h'; rfl)

theorem map {α γ : Type} {t : TRes α} (h : t.DataS K S) (k : α → γ) : TRes.DataS K S (t.map k) := by
  match t with
  | .ok _ => exact fun _ h' => nomatch h'
  | .error e => exact fun d h' => h d (by cases (h' : Except.error e = .error (.revertWith d)); rfl)

theorem ofOpt {α : Type} (x : Option α) : (TRes.ofOpt x).DataS K S := by
  cases x <;> exact fun _ h => nomatch h

theorem mono {α : Type} {t : TRes α} {S' : DSet} (h : t.DataS K S)
    (hS : ∀ d, S.Mem d → S'.Mem d) : t.DataS K S' := fun d hd hk => hS d (h d hd hk)

end TRes.DataS

theorem TRes.RevertOnly.dataS {α : Type} {t : TRes α} (h : t.RevertOnly) : t.DataS K S :=
  fun _ h' => nomatch h _ h'

/-- A loop whose body and condition carry data of `S` carries data of `S`. -/
theorem TLoop.run_dataS {α : Type} {body : α → TRes α} {c : α → TRes Bool}
    (hb : ∀ a, (body a).DataS K S) (hc : ∀ a, (c a).DataS K S) (σ : α) :
    (TLoop.run body c σ).DataS K S := by
  refine TLoop.run_induct (P := fun _ => True) (Q := TRes.DataS K S) trivial (fun τ _ => ?_)
    TRes.DataS.diverge
  unfold TLoop.step
  cases hc' : c τ with
  | error e => exact fun d h' => hc τ d (by cases h'; exact hc')
  | ok v =>
    cases v with
    | false => exact TRes.DataS.ok _
    | true =>
      cases hb' : body τ with
      | error e => exact fun d h' => hb τ d (by cases h'; exact hb')
      | ok _ => trivial

/-! ## An expression carries no data -/

section Eval

variable {Γ : Ctx}

theorem SPath.resolveT_dataS (σ : State C Γ) {T : Ty} (b : SPath C Γ T) :
    (b.resolveT σ).DataS K S := (SPath.resolveT_revertOnly σ b).dataS
theorem Loc.resolveT_dataS (σ : State C Γ) {T : Ty} (l : Loc C Γ T) :
    (l.resolveT σ).DataS K S := (Loc.resolveT_revertOnly σ l).dataS
theorem MPath.mvalT_dataS (σ : State C Γ) {T : Ty} (b : MPath C Γ T) :
    (b.mvalT σ).DataS K S := (MPath.mvalT_revertOnly σ b).dataS
theorem MLoc.addrT_dataS (σ : State C Γ) {T : Ty} (l : MLoc C Γ T) :
    (l.addrT σ).DataS K S := (MLoc.addrT_revertOnly σ l).dataS
theorem Val.evalT_dataS (σ : State C Γ) {p : PrimTy} (v : Val C Γ p) :
    (v.evalT σ).DataS K S := (Val.evalT_revertOnly σ v).dataS
theorem Src.valueT_dataS (σ : State C Γ) {T : Ty} (r : Src C Γ T) : (r.valueT σ).DataS K S :=
  (Src.valueT_revertOnly σ r).dataS

end Eval

/-! ## Operations carry no data -/

section Ops

variable {Γ : Ctx} (σ : State C Γ)

theorem ARhs.evalT_dataS {R : RefTy} : (r : ARhs C Γ R) → (r.evalT σ).DataS K S
  | .path p => (p.resolveT_dataS σ).bind fun _ => TRes.DataS.ok _
  | .push b _ => (b.resolveT_dataS σ).bind fun r => by
    show (if σ.storage.full r then .error .exhausted else do
      let (st, n) ← TRes.ofOpt (σ.storage.pushPlace r)
      pure (st, r.index (.arr .dyn) n) : TRes _).DataS K S
    split
    · exact TRes.DataS.exhausted
    · exact (TRes.DataS.ofOpt _).bind fun _ => TRes.DataS.ok _

theorem MRhs.evalT_dataS {R : RefTy} (r : MRhs C Γ R) : (r.evalT σ).DataS K S :=
  (MRhs.evalT_revertOnly σ r).dataS
theorem opStoreT_dataS (op : BinOp) {p : PrimTy} (r : SRef C (.prim p)) (v : p.Denote) :
    (opStoreT σ op r v).DataS K S := (opStoreT_revertOnly σ op r v).dataS
theorem opMemT_dataS (op : BinOp) {p : PrimTy} (a : MAddr σ.H (.prim p)) (v : p.Denote) :
    (opMemT σ op a v).DataS K S := (opMemT_revertOnly σ op a v).dataS
theorem OpLoc.storeT_dataS (op : BinOp) {p : PrimTy} (l : OpLoc C Γ p) (v : p.Denote) :
    (l.storeT σ op v).DataS K S := (OpLoc.storeT_revertOnly σ op l v).dataS
theorem bumpStoreT_dataS (op : IncDec) {p : PrimTy} (r : SRef C (.prim p)) :
    (bumpStoreT σ op r).DataS K S := (bumpStoreT_revertOnly σ op r).dataS
theorem bumpMemT_dataS (op : IncDec) {p : PrimTy} (a : MAddr σ.H (.prim p)) :
    (bumpMemT σ op a).DataS K S := (bumpMemT_revertOnly σ op a).dataS
theorem OpLoc.bumpT_dataS (op : IncDec) {p : PrimTy} (l : OpLoc C Γ p) :
    (l.bumpT σ op).DataS K S := (OpLoc.bumpT_revertOnly σ op l).dataS
theorem Args.evalT_dataS {ps : Ctx} (as : Args C Γ ps) : (as.evalT σ).DataS K S :=
  (Args.evalT_revertOnly σ as).dataS

end Ops

theorem Binders.decodeT_dataS {H : HTy} : {ρ : Ctx} → (bs : Binders ρ) →
    (vs : List Semantics.Word) → (Binders.decodeT (C := C) (H := H) bs vs).DataS K S
  | _, .nil, _ => TRes.DataS.ok _
  | _, .snoc bs p _, vs => (Binders.decodeT_dataS bs vs).bind fun (_, rest) => by
    dsimp only
    split
    · split
      · exact TRes.DataS.ok _
      · exact TRes.DataS.revert
    · exact TRes.DataS.revert

/-! ## Steps carry no data

Each step of `TRun` but `assert`, its sub-steps assumed not to panic. -/

namespace TRun

variable {Γ : Ctx}

/-- `values.push() += e` may revert or exhaust, but cancarry no data. -/
theorem pushOpAssign_dataS {p : PrimTy} (op : BinOp) (b : SPath C Γ (.array (.prim p)))
    (r : Val C Γ p) (σ : State C Γ) : (pushOpAssign op b r σ).DataS K S := by
  unfold pushOpAssign
  refine (r.evalT_dataS σ).bind fun value => (b.resolveT_dataS σ).bind fun ref => ?_
  split
  · exact TRes.DataS.exhausted
  · exact (TRes.DataS.ofOpt _).bind fun pair => opStoreT_dataS _ op _ value

/-- `values.push()++` and `--values.push()` may revert or exhaust, but cancarry no data. -/
theorem pushIncDec_dataS {p : PrimTy} (op : IncDec) (b : SPath C Γ (.array (.prim p)))
    (σ : State C Γ) : (pushIncDec op b σ).DataS K S := by
  unfold pushIncDec
  refine (b.resolveT_dataS σ).bind fun ref => ?_
  split
  · exact TRes.DataS.exhausted
  · exact (TRes.DataS.ofOpt _).bind fun pair =>
      (bumpStoreT_dataS _ op _).bind fun _ => TRes.DataS.ok _

theorem push_dataS {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E))
    (σ : State C Γ) : (push b v σ).DataS K S := by
  unfold push
  refine (b.resolveT_dataS σ).bind fun ref => ?_
  cases v with
  | none =>
    dsimp only
    split
    · exact TRes.DataS.exhausted
    · exact (TRes.DataS.ofOpt _).bind fun _ => TRes.DataS.ok _
  | some r =>
    refine (r.valueT_dataS σ).bind fun _ => ?_
    dsimp only
    split
    · exact TRes.DataS.exhausted
    · exact (TRes.DataS.ofOpt _).bind fun _ => TRes.DataS.ok _

theorem clearT_dataS (σ : State C Γ) : {T : Ty} → (a : MAddr σ.H T) →
    (hm : T.mapFree = true) → (clearT σ a hm).DataS K S
  | .prim _, _, _ => (TRes.DataS.ofOpt _).bind fun _ => TRes.DataS.ok _
  | .ref R, a, hm => by
    simp only [clearT]
    split
    · exact TRes.DataS.ok _
    · exact TRes.DataS.revert

theorem deleteMem_dataS {T : Ty} (p : MPath C Γ T) (σ : State C Γ) :
    (deleteMem p σ).DataS K S := by
  unfold deleteMem
  cases p with
  | var _ _ => exact TRes.DataS.ok _
  | loc l => exact (l.addrT_dataS σ).bind fun a => clearT_dataS σ a l.mapFree

theorem assignNew_dataS {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint)
    (h : R.newArrOk = true) (σ : State C Γ) : (assignNew l n h σ).DataS K S := by
  unfold assignNew
  cases l with
  | store l => exact (l.resolveT_dataS _).bind fun _ => (TRes.DataS.ofOpt _).bind fun _ =>
      TRes.DataS.ok _
  | mem l => exact (l.addrT_dataS _).bind fun _ => (TRes.DataS.ofOpt _).bind fun _ =>
      TRes.DataS.ok _

theorem ite_dataS {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (h₁ : Ext Γ Γ₁) (thn : TStep C Γ Γ₁)
    (h₂ : Ext Γ Γ₂) (els : TStep C Γ Γ₂) (ht : ∀ σ, (thn σ).DataS K S)
    (he : ∀ σ, (els σ).DataS K S) (σ : State C Γ) : (ite c h₁ thn h₂ els σ).DataS K S := by
  unfold ite
  refine (c.evalT_dataS σ).bind fun v => ?_
  split
  · exact (ht σ).map _
  · exact (he σ).map _

theorem require_dataS (c : Val C Γ .bool) (σ : State C Γ) : (require c σ).DataS K S := by
  unfold require
  refine (c.evalT_dataS σ).bind fun v => ?_
  split
  · exact TRes.DataS.ok _
  · exact TRes.DataS.revert

theorem call_dataS {Γ' ps rs Γf : Ctx} (args : Args C Γ ps) (ret : CallRet Γ rs Γ')
    (hb : Ext (rs ++ ps) Γf) (body : TStep C (rs ++ ps) Γf) (hbody : ∀ σ, (body σ).DataS K S)
    (σ : State C Γ) : (call args ret hb body σ).DataS K S := by
  unfold call
  exact (Args.evalT_dataS σ args).bind fun _ => (hbody _).bind fun _ => TRes.DataS.ok _

theorem receiverOp_dataS {E : Ty} (op : ReceiverOp C Γ E)
    (b : SPath C Γ (.array E)) (σ : State C Γ) : (receiverOp op b σ).DataS K S := by
  cases op with
  | push v _ => exact push_dataS b v σ
  | pop =>
    exact (b.resolveT_dataS σ).bind fun _ => (TRes.DataS.ofOpt _).bind
      fun _ => TRes.DataS.ok _

theorem callReceiver_dataS {ps Γf : Ctx} {E : Ty} (args : Args C Γ ps) (r : Var)
    (hb : Ext ([.alias (.array E)] ++ ps) Γf)
    (body : TStep C ([.alias (.array E)] ++ ps) Γf) (op : ReceiverOp C Γ E)
    (hbody : ∀ σ, (body σ).DataS K S) (σ : State C Γ) :
    (callReceiver args r hb body op σ).DataS K S := by
  unfold callReceiver
  exact (call_dataS args (.storage (.array E) r) hb body hbody σ).bind fun o =>
    (receiverOp_dataS _ _ o.st).bind fun _ => TRes.DataS.ok _

/-- `f().push(i++)` can panic only in its getter or operand prefix. -/
theorem callReceiverPush_dataS {ps Γf Γv : Ctx} {E : Ty} (args : Args C Γ ps) (r : Var)
    (hb : Ext ([.alias (.array E)] ++ ps) Γf)
    (body : TStep C ([.alias (.array E)] ++ ps) Γf)
    (he : Ext Γ Γv) (code : TStep C Γ Γv) (value : Src C Γv E)
    (hbody : ∀ σ, (body σ).DataS K S) (hcode : ∀ σ, (code σ).DataS K S) (σ : State C Γ) :
    (callReceiverPush args r hb body he code value σ).DataS K S := by
  unfold callReceiverPush afterReceiverPrefix pushAfterPrefix
  apply (call_dataS args (.storage (.array E) r) hb body hbody σ).bind
  intro a
  apply TRes.DataS.map
  apply (SPath.resolveT_dataS a.st (.alias .here)).bind
  intro ref
  apply (hcode _).bind
  intro b
  apply (Src.valueT_dataS b.st value).bind
  intro v
  split
  · exact TRes.DataS.exhausted
  · exact (TRes.DataS.ofOpt _).bind fun _ => TRes.DataS.ok _

theorem loop_dataS {Γ₁ : Ctx} (c : Val C Γ .bool) (h : Ext Γ Γ₁) (body : TStep C Γ Γ₁)
    (hbody : ∀ σ, (body σ).DataS K S) (σ : State C Γ) : (loop c h body σ).DataS K S := by
  unfold loop
  exact TLoop.run_dataS (fun o : Out C σ.H Γ => (hbody o.st).map _)
    (fun o : Out C σ.H Γ => c.evalT_dataS o.st) _

theorem block_dataS {Γ₁ : Ctx} (h : Ext Γ Γ₁) (body : TStep C Γ Γ₁)
    (hbody : ∀ σ, (body σ).DataS K S) (σ : State C Γ) : (block h body σ).DataS K S :=
  (hbody σ).map _

theorem seq_dataS {Γ₁ Γ₂ : Ctx} (s : TStep C Γ Γ₁) (P : TStep C Γ₁ Γ₂)
    (hs : ∀ σ, (s σ).DataS K S) (hP : ∀ σ, (P σ).DataS K S) (σ : State C Γ) :
    (seq s P σ).DataS K S := by
  unfold seq
  split
  · exact (hP _).map _
  · rename_i e he
    exact fun d h' => hs σ d (by cases h'; exact he)


theorem assert_dataS (c : Val C Γ .bool) (σ : State C Γ) : (assert c σ).DataS K S := by
  unfold assert
  refine (c.evalT_dataS σ).bind fun v => ?_
  split
  · exact TRes.DataS.ok _
  · exact TRes.DataS.panic

theorem tryCall_dataS {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} (c : ExtCall C Γ) (rets : Binders ρ)
    (h₁ : Ext (ρ ++ Γ) Γ₁) (ok : TStep C (ρ ++ Γ) Γ₁)
    (h₂ : Ext Γ Γ₂) (err : TStep C Γ Γ₂) (code : CodeBinder κ)
    (h₃ : Ext (κ ++ Γ) Γ₃) (pnc : TStep C (κ ++ Γ) Γ₃)
    (h₄ : Ext Γ Γ₄) (other : TStep C Γ Γ₄) (sargs : Args C Γ ps) (hs : Ext (ρ ++ ps) Γf)
    (sbody : TStep C (ρ ++ ps) Γf) (self : Bool) (hok : ∀ σ, (ok σ).DataS K S)
    (herr : ∀ σ, (err σ).DataS K S) (hpnc : ∀ σ, (pnc σ).DataS K S)
    (hother : ∀ σ, (other σ).DataS K S) (σ : State C Γ) :
    (tryCall c rets h₁ ok h₂ err code h₃ pnc h₄ other sargs hs sbody self σ).DataS K S := by
  unfold tryCall
  split
  · exact TRes.DataS.revert
  split
  · split
    · exact (hok _).map _
    · exact (hother σ).map _
    · split
      · exact (herr σ).map _
      · split
        · exact (hpnc _).map _
        · exact (hother σ).map _
    · exact (hpnc _).map _
    · rename_i e _ _ h2 _ _
      exact fun d h => (h2 d (by cases h; rfl)).elim
  split
  · exact TRes.DataS.revert
  · exact (Binders.decodeT_dataS rets _).bind fun _ => (hok _).map _
  · exact (herr σ).map _
  · exact (hpnc _).map _
  · exact (hother σ).map _

/-- The parts of `revert(d)` evaluated, when they are literal: their bytes. -/
theorem RevPart.mapM_litData (σ : State C Γ) : (d : List (RevPart C Γ)) → {bs : List UInt8} →
    RevPart.litData d = some bs → ∃ ps, d.mapM (fun p => p.evalT σ) = .ok ps ∧ ps.flatten = bs
  | [], _, h => by cases h; exact ⟨[], rfl, rfl⟩
  | .bytes b :: d, bs, h => by
    simp only [RevPart.litData, Option.map_eq_some_iff] at h
    obtain ⟨bs', hd, rfl⟩ := h
    obtain ⟨ps, hm, hf⟩ := RevPart.mapM_litData σ d hd
    refine ⟨b :: ps, ?_, by rw [List.flatten_cons, hf]⟩
    rw [List.mapM_cons, hm]
    rfl
  | .sel _ :: _, _, h => nomatch h
  | .word _ :: _, _, h => nomatch h

theorem revertData_dataS (d : List (RevPart C Γ)) {bs : List UInt8}
    (hd : RevPart.litData d = some bs) (σ : State C Γ) : (revertData d σ).DataS K ([bs], []) := by
  unfold revertData
  obtain ⟨ps, hm, hf⟩ := RevPart.mapM_litData σ d hd
  rw [hm]
  show TRes.DataS K ([bs], []) (Except.error (THalt.ofData ps.flatten) : TRes (Out C σ.H Γ))
  rw [hf]
  intro d' h
  cases bs with
  | nil => exact nomatch h
  | cons b bs => cases h; exact fun _ => .inl (List.mem_singleton_self _)

/-- The parts of `revert(d)` evaluated, when they are known in part: bytes
the pattern stands for. -/
theorem RevPart.mapM_pat (σ : State C Γ) : (d : List (RevPart C Γ)) → {p : Pat} →
    RevPart.pat? d = some p → ∀ ps, d.mapM (fun q => q.evalT σ) = .ok ps → p.Matches ps.flatten
  | [], _, h, ps, hm => by cases h; cases hm; exact ⟨rfl, fun _ _ h => nomatch h⟩
  | .bytes b :: d, p, h, ps, hm => by
    simp only [RevPart.pat?, Option.map_eq_some_iff] at h
    obtain ⟨p', hd, rfl⟩ := h
    rw [List.mapM_cons] at hm
    cases hr : d.mapM (fun q => q.evalT σ) with
    | error e => rw [hr] at hm; cases hm
    | ok ps' =>
      rw [hr] at hm
      cases hm
      rw [List.flatten_cons]
      exact (Pat.matches_lit b).append (RevPart.mapM_pat σ d hd ps' hr)
  | .word v :: d, p, h, ps, hm => by
    simp only [RevPart.pat?, Option.map_eq_some_iff] at h
    obtain ⟨p', hd, rfl⟩ := h
    rw [List.mapM_cons] at hm
    cases hv : v.evalT σ with
    | error e =>
      have : (RevPart.word v).evalT σ = .error e := by
        show (do let x ← v.evalT σ; pure _) = _; rw [hv]; rfl
      rw [this] at hm; cases hm
    | ok x =>
      have : (RevPart.word v).evalT σ = .ok (Semantics.wordBytes (PrimTy.toWord x).1.toNat) := by
        show (do let x ← v.evalT σ; pure _) = _; rw [hv]; rfl
      rw [this] at hm
      cases hr : d.mapM (fun q => q.evalT σ) with
      | error e => rw [hr] at hm; cases hm
      | ok ps' =>
        rw [hr] at hm
        cases hm
        rw [List.flatten_cons]
        exact (Pat.matches_word _).append (RevPart.mapM_pat σ d hd ps' hr)
  | .sel _ :: _, _, h, _, _ => nomatch h
/-- An evaluated part carries no data: only a value's evaluation can fail,
and it only reverts. -/
theorem RevPart.mapM_revertOnly (σ : State C Γ) (l : List (RevPart C Γ)) :
    (l.mapM (fun p : RevPart C Γ => p.evalT σ)).RevertOnly := by
  induction l with
  | nil => exact TRes.RevertOnly.ok _
  | cons a l ih =>
    rw [List.mapM_cons]
    refine TRes.RevertOnly.bind ?_ fun _ => ih.bind fun _ => TRes.RevertOnly.ok _
    cases a with
    | bytes => exact TRes.RevertOnly.ok _
    | sel => exact TRes.RevertOnly.ok _
    | word v => exact (Val.evalT_revertOnly σ v).bind fun _ => TRes.RevertOnly.ok _

/-- A datum that cannot decode as `Error` (`RevPart.notError`) is none a
`catch Error(string memory r)` keeps. -/
theorem revertData_dataS_notError (d : List (RevPart C Γ)) (hd : RevPart.notError d = true)
    (σ : State C Γ) (hK : ∀ d', K d' → (Semantics.decodeError d').isSome = true) :
    (revertData d σ).DataS K ([], []) := by
  unfold revertData
  cases hm : d.mapM (fun p : RevPart C Γ => p.evalT σ) with
  | error e =>
    intro d' h _
    have he := RevPart.mapM_revertOnly σ d e hm
    subst he
    cases h
  | ok ps =>
    intro d' h hk
    have hdec := hK d' hk
    match d, hd with
    | .bytes bs :: rest, hd =>
      simp only [RevPart.notError, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not] at hd
      rw [List.mapM_cons] at hm
      cases hr : rest.mapM (fun p : RevPart C Γ => p.evalT σ) with
      | error e' =>
        rw [hr] at hm
        cases hm
      | ok ps' =>
        rw [hr] at hm
        cases hm
        have hflat : (bs :: ps').flatten = bs ++ ps'.flatten := List.flatten_cons
        change (Except.error (THalt.ofData (bs :: ps').flatten) : TRes (Out C σ.H Γ)) =
          .error (.revertWith d') at h
        rw [hflat] at h
        have hd' : d' = bs ++ ps'.flatten := by
          unfold THalt.ofData at h
          split at h
          · cases h
          · cases h; rfl
        subst hd'
        exfalso
        have htake : (bs ++ ps'.flatten).take 4 = bs.take 4 := List.take_append_of_le_length hd.1
        simp only [Semantics.decodeError, htake, if_neg hd.2, Option.isSome_none,
          Bool.false_eq_true] at hdec

/-- `revert(d)` of data known in part reverts with data the pattern stands
for. -/
theorem revertData_dataS_pat (d : List (RevPart C Γ)) {p : Pat}
    (hd : RevPart.pat? d = some p) (σ : State C Γ) : (revertData d σ).DataS K ([], [p]) := by
  unfold revertData
  cases hm : d.mapM (fun q : RevPart C Γ => q.evalT σ) with
  | error e =>
    intro d' h _
    have he := RevPart.mapM_revertOnly σ d e hm
    subst he
    cases h
  | ok ps =>
    intro d' h _
    change (Except.error (THalt.ofData ps.flatten) : TRes (Out C σ.H Γ)) =
      .error (.revertWith d') at h
    have hd' : d' = ps.flatten := by
      unfold THalt.ofData at h
      split at h
      · cases h
      · cases h; rfl
    subst hd'
    exact .inr ⟨p, List.mem_singleton_self _, RevPart.mapM_pat σ d hd ps hm⟩

theorem litWritesT_dataS {Γ₁ : Ctx} {k : TStep C (.mem bytesR :: Γ) Γ₁}
    (hk : ∀ σ, (k σ).DataS K S) : (bs : List UInt8) → (i : Nat) → (σ : State C (.mem bytesR :: Γ)) →
    (litWritesT bs i k σ).DataS K S
  | [], _, σ => hk σ
  | b :: bs, i, σ => by
    unfold litWritesT
    split
    · exact seq_dataS _ _ (fun σ => (MSrc.mvalT_revertOnly σ _).dataS.bind fun _ =>
        (MLoc.addrT_dataS σ _).bind fun _ => (TRes.DataS.ofOpt _).bind fun _ =>
          TRes.DataS.ok _) (litWritesT_dataS hk bs (i + 1)) σ
    · exact hk σ

theorem litBytesT_dataS {Γ₁ : Ctx} {k : TStep C (.mem bytesR :: Γ) Γ₁}
    (hk : ∀ σ, (k σ).DataS K S) (bs : List UInt8) (σ : State C Γ) : (litBytesT bs k σ).DataS K S := by
  unfold litBytesT
  split
  · exact seq_dataS _ _ (fun σ => (MRhs.evalT_dataS σ _).bind fun _ => TRes.DataS.ok _)
      (litWritesT_dataS hk bs 0) σ
  · exact seq_dataS _ _ (fun _ => TRes.DataS.ok _) hk σ

theorem catchBytes_dataS {ρ ps Γf : Ctx} (c : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (hs : Ext (ρ ++ ps) Γf) (sbody : TStep C (ρ ++ ps) Γf) (self : Bool)
    (σ : State C Γ) : (catchBytes c rets sargs hs sbody self σ).DataS K S := by
  unfold catchBytes
  split
  · exact TRes.DataS.revert
  split
  · split
    · exact TRes.DataS.revert
    · exact TRes.DataS.ok _
    · exact TRes.DataS.ok _
    · exact TRes.DataS.ok _
    · rename_i e _ _ h2 _ _
      exact fun d h => (h2 d (by cases h; rfl)).elim
  · split <;> first | exact TRes.DataS.ok _ | exact TRes.DataS.revert

theorem catchData_dataS {ρ ps Γf Γ₁ : Ctx} (c : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (hs : Ext (ρ ++ ps) Γf) (sbody : TStep C (ρ ++ ps) Γf) (self : Bool)
    (kind : CatchKind) (h₁ : Ext (.mem bytesR :: Γ) Γ₁) (body : TStep C (.mem bytesR :: Γ) Γ₁)
    (hbody : ∀ σ, (body σ).DataS K S) (σ : State C Γ) :
    (catchData c rets sargs hs sbody self kind h₁ body σ).DataS K S := by
  unfold catchData
  refine (catchBytes_dataS c rets sargs hs sbody self σ).bind fun d => ?_
  split
  · exact TRes.DataS.revert
  · exact (litBytesT_dataS hbody _ σ).map _

end TRun

/-! ## A program's data is one it lists -/

theorem optCatD_eq_some {a b : Option DSet} {S : DSet} (h : optCatD a b = some S) :
    ∃ Sa Sb, a = some Sa ∧ b = some Sb ∧ S = (Sa.1 ++ Sb.1, Sa.2 ++ Sb.2) := by
  cases a <;> cases b <;> simp only [optCatD, reduceCtorEq, Option.some.injEq] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

mutual

/-- **The data a statement's run reverts with is one it lists**
(`Stmt.revertDatas`). -/
theorem Stmt.run_dataS (raw : Bool) : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') →
    {S : DSet} → s.revertDatas raw = some S → ∀ σ : State C Γ,
      (s.run σ).DataS (dataKeep raw) S
  | _, _, .assign l r, _, _, σ => (r.valueT_dataS σ).bind fun _ => (l.resolveT_dataS σ).bind
      fun _ => (TRes.DataS.ofOpt _).bind fun _ => TRes.DataS.ok _
  | _, _, .rebind _ r, _, _, σ => (r.evalT_dataS σ).bind fun _ => TRes.DataS.ok _
  | _, _, .assignLocal _ r, _, _, σ => (r.evalT_dataS σ).bind fun _ => TRes.DataS.ok _
  | _, _, .declLocal p _ init, _, _, σ => by
    cases init with
    | none => exact TRes.DataS.ok _
    | some e => exact (e.evalT_dataS σ).bind fun _ => TRes.DataS.ok _
  | _, _, .declStorage R _ init, _, _, σ => by
    cases init with
    | none => exact TRes.DataS.ok _
    | some r => exact (r.evalT_dataS σ).bind fun _ => TRes.DataS.ok _
  | _, _, .opAssign op _ _ l r, _, _, σ => (r.evalT_dataS σ).bind fun _ =>
      OpLoc.storeT_dataS σ op l _
  | _, _, .incDec op _ l, _, _, σ => (OpLoc.bumpT_dataS σ op l).bind fun _ => TRes.DataS.ok _
  | _, _, .pushOpAssign op _ _ b r, _, _, σ => TRun.pushOpAssign_dataS op b r σ
  | _, _, .pushIncDec op _ b, _, _, σ => TRun.pushIncDec_dataS op b σ
  | _, _, .assignIncDec _ op _ l _, _, _, σ => (OpLoc.bumpT_dataS σ op l).bind fun _ =>
      TRes.DataS.ok _
  | _, _, .assignLocalPush i b, _, _, σ => (TRun.push_dataS b none σ).bind fun _ =>
      TRes.DataS.ok _
  | _, _, .push b v _, _, _, σ => TRun.push_dataS b v σ
  | _, _, .pop b, _, _, σ => (b.resolveT_dataS σ).bind fun _ => (TRes.DataS.ofOpt _).bind
      fun _ => TRes.DataS.ok _
  | _, _, .transfer r a, _, _, σ => (r.evalT_dataS σ).bind fun _ => (a.evalT_dataS σ).bind
      fun _ => TRes.DataS.ok _
  | _, _, .send _ r a _, _, _, σ => (r.evalT_dataS σ).bind fun _ => (a.evalT_dataS σ).bind
      fun _ => TRes.DataS.ok _
  | _, _, .declMem R _ init _ _, _, _, σ => by
    cases init with
    | none => exact TRes.DataS.ok _
    | some r => exact (r.evalT_dataS σ).bind fun _ => TRes.DataS.ok _
  | _, _, .rebindMem _ r, _, _, σ => (r.evalT_dataS σ).bind fun _ => TRes.DataS.ok _
  | _, _, .assignFromMem l p, _, _, σ => (p.mvalT_dataS σ).bind fun _ =>
      (l.resolveT_dataS σ).bind fun _ => (TRes.DataS.ofOpt _).bind fun _ => TRes.DataS.ok _
  | _, _, .assignMem l r, _, _, σ => (MSrc.mvalT_revertOnly σ r).dataS.bind fun _ => (l.addrT_dataS σ).bind
      fun _ => (TRes.DataS.ofOpt _).bind fun _ => TRes.DataS.ok _
  | _, _, .delete l, _, _, σ => (l.resolveT_dataS σ).bind fun _ => (TRes.DataS.ofOpt _).bind
      fun _ => TRes.DataS.ok _
  | _, _, .deleteMem p _, _, _, σ => TRun.deleteMem_dataS p σ
  | _, _, .assignNew l n h, _, _, σ => TRun.assignNew_dataS l n h σ
  | _, _, .ite c thn els, _, h, σ => by
    obtain ⟨S₁, S₂, h₁, h₂, rfl⟩ := optCatD_eq_some
      (show optCatD (Prog.revertDatas raw thn) (Prog.revertDatas raw els) = some _ from h)
    exact TRun.ite_dataS c _ _ _ _ (fun σ => (Prog.run_dataS raw thn h₁ σ).mono
      (DSet.mem_left _ _)) (fun σ => (Prog.run_dataS raw els h₂ σ).mono
      (DSet.mem_right _ _)) σ
  | _, _, .require c, _, _, σ => TRun.require_dataS c σ
  | _, _, .assert c, _, _, σ => TRun.assert_dataS c σ
  | _, _, .revert, _, _, _ => TRes.DataS.revert
  | _, _, .assumeFalse, _, _, _ => TRes.DataS.exhausted
  | _, _, .callRec .., _, h, _ => nomatch h
  | _, _, .call _ args ret body, _, h, σ =>
    TRun.call_dataS args ret _ _ (Prog.run_dataS raw body h) σ
  | _, _, .callReceiver _ args r body op, _, h, σ =>
    TRun.callReceiver_dataS args r _ _ op (Prog.run_dataS raw body h) σ
  | _, _, .callReceiverPush _ args r body code value, _, h, σ => by
    obtain ⟨S₁, S₂, h₁, h₂, rfl⟩ := optCatD_eq_some
      (show optCatD (Prog.revertDatas raw body) (Prog.revertDatas raw code) = some _ from h)
    exact TRun.callReceiverPush_dataS args r _ _ _ _ value
      (fun σ => (Prog.run_dataS raw body h₁ σ).mono (DSet.mem_left _ _))
      (fun σ => (Prog.run_dataS raw code h₂ σ).mono (DSet.mem_right _ _)) σ
  | _, _, .tryCall call rets ok err code pnc other sargs sbody self, _, h, σ => by
    obtain ⟨S₁, S₂, h₁, h₂, rfl⟩ := optCatD_eq_some
      (show optCatD (optCatD (Prog.revertDatas raw ok) (Prog.revertDatas raw err))
        (optCatD (Prog.revertDatas raw pnc) (Prog.revertDatas raw other)) = some _ from h)
    obtain ⟨Sa, Sb, ha, hb, rfl⟩ := optCatD_eq_some h₁
    obtain ⟨Sc, Sd, hc, hd, rfl⟩ := optCatD_eq_some h₂
    exact TRun.tryCall_dataS call rets _ _ _ _ code _ _ _ _ sargs _ _ self
      (fun σ => (Prog.run_dataS raw ok ha σ).mono fun d hx =>
        DSet.mem_left _ _ d (DSet.mem_left _ _ d hx))
      (fun σ => (Prog.run_dataS raw err hb σ).mono fun d hx =>
        DSet.mem_left _ _ d (DSet.mem_right _ _ d hx))
      (fun σ => (Prog.run_dataS raw pnc hc σ).mono fun d hx =>
        DSet.mem_right _ _ d (DSet.mem_left _ _ d hx))
      (fun σ => (Prog.run_dataS raw other hd σ).mono fun d hx =>
        DSet.mem_right _ _ d (DSet.mem_right _ _ d hx))
      σ
  | _, _, .loop _ c body, _, h, σ => TRun.loop_dataS c _ _ (Prog.run_dataS raw body h) σ
  | _, _, .block body, _, h, σ => TRun.block_dataS _ _ (Prog.run_dataS raw body h) σ
  | _, _, .revertData d, _, h, σ => by
    have h' : RevPart.datas raw d = some _ := h
    unfold RevPart.datas at h'
    split at h'
    · rename_i hn
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hn
      cases h'
      exact TRun.revertData_dataS_notError d hn.2 σ (fun _ hk => by
        rcases hk with hk | hk
        · rw [hn.1] at hk; cases hk
        · exact hk)
    · split at h'
      · rename_i bs hbs
        cases h'
        exact TRun.revertData_dataS d hbs σ
      · simp only [Option.map_eq_some_iff] at h'
        obtain ⟨p, hp, rfl⟩ := h'
        exact TRun.revertData_dataS_pat d hp σ
  | _, _, .catchData c rets sargs sbody self kind _ body, _, h, σ =>
    TRun.catchData_dataS c rets sargs _ _ self kind _ _ (Prog.run_dataS raw body h) σ

/-- **The data a sequence's run reverts with is one it lists.** -/
theorem Prog.run_dataS (raw : Bool) : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') →
    {S : DSet} → P.revertDatas raw = some S → ∀ σ : State C Γ,
      (P.run σ).DataS (dataKeep raw) S
  | _, _, .nil, _, _, _ => TRes.DataS.ok _
  | _, _, .cons s P, _, h, σ => by
    obtain ⟨S₁, S₂, h₁, h₂, rfl⟩ := optCatD_eq_some
      (show optCatD (Stmt.revertDatas raw s) (Prog.revertDatas raw P) = some _ from h)
    exact TRun.seq_dataS _ _ (fun σ => (Stmt.run_dataS raw s h₁ σ).mono
      (DSet.mem_left _ _)) (fun σ => (Prog.run_dataS raw P h₂ σ).mono
      (DSet.mem_right _ _)) σ

end

/-- Data known in part that `Pat.notPanic` keeps decodes as no `Panic`. -/
theorem Pat.notPanic_decode {p : Pat} {d : List UInt8} (hp : p.notPanic = true)
    (hm : p.Matches d) : Semantics.decodePanic d = none := by
  unfold Semantics.decodePanic
  split
  · rename_i h
    exfalso
    obtain ⟨h4, h36⟩ := h
    simp only [Pat.notPanic, bne_iff_ne, ne_eq, Bool.or_eq_true,
      List.any_eq_true, List.mem_range] at hp
    rcases hp with hl | ⟨i, hi, hb⟩
    · exact hl (hm.1 ▸ h36)
    · split at hb
      · rename_i b hpi
        have hd := hm.2 i b hpi
        have hs : Semantics.panicSelector[i]? = some b := by
          rw [← h4, List.getElem?_take_of_lt hi, hd]
        have : Semantics.panicSelector[i]! = b := by
          rw [getElem!_def, hs]
        rw [this] at hb
        simp only [bne_self_eq_false, Bool.false_eq_true] at hb
      · exact absurd hb Bool.false_ne_true
  · rfl

/-- **A self-call's callee panics with a code it lists** (`Prog.panicCodes`,
`trySelfStep`'s `Panic` goal): the call halts by no panic of its own, and
data it reverts with that decode as `Panic` carry one of the codes. -/
theorem Prog.panicCodes_call {Γ ρ ps Γf : Ctx} {sbody : Prog C (ρ ++ ps) Γf}
    {ks : List Semantics.Word} (hK : sbody.panicCodes = some ks) (sargs : Args C Γ ps)
    (rets : Binders ρ) (σ : State C Γ) {e : THalt}
    (h : TRun.call sargs (.rets rets) sbody.ext sbody.runR σ = .error e) :
    e ≠ .panic ∧ ∀ d v, e = .revertWith d → Semantics.decodePanic d = some v → v ∈ ks := by
  unfold Prog.panicCodes at hK
  split at hK
  · cases hK
  rename_i hat
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hat
  split at hK
  · rename_i S hS
    split at hK
    · rename_i hall
      cases hK
      refine ⟨fun he => ?_, fun d v hd hv => ?_⟩
      · subst he
        exact TRun.call_noPanic sargs (.rets rets) sbody.ext sbody.runR
          (fun τ => Prog.run_noPanic sbody hat.1 τ) σ h
      · subst hd
        rcases TRun.call_dataS sargs (.rets rets) _ _ (Prog.run_dataS true sbody hS) σ d h
            (.inl rfl) with hm | ⟨p, hp, hm⟩
        · exact List.mem_filterMap.2 ⟨d, hm, hv⟩
        · rw [Pat.notPanic_decode (List.all_eq_true.1 hall p hp) hm] at hv
          cases hv
    · cases hK
  · cases hK

/-- A callee whose codes are known pays nobody (`Prog.panicCodes`). -/
theorem Prog.panicCodes_hasTransfer {Γ Γ' : Ctx} {P : Prog C Γ Γ'} {ks : List Semantics.Word}
    (hK : P.panicCodes = some ks) : P.hasTransfer = false := by
  unfold Prog.panicCodes at hK
  split at hK
  · cases hK
  · rename_i h
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at h
    exact h.2

/-- A panic's data matches `Panic`'s, whatever its code. -/
theorem Pat.matches_panic (c : Nat) : Pat.panic.Matches (Semantics.encodePanic c) :=
  (Pat.matches_lit Semantics.panicSelector).append (Pat.matches_word c)

end Solidity
