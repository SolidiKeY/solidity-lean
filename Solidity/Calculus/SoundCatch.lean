import Solidity.Calculus.SoundCalls
import Solidity.Calculus.DataIn
import Solidity.Semantics.AllocBytes
import Solidity.Theory.Typed.Mem

/-!
# The rule of a `catch` clause that binds the data is sound

`catchDataStep` (`Calculus/Blocks.lean`) against `TRun.catchData`
(`docs/semantic-gaps.md`, "Revert data").  The clause binds what the call
reverts with, read from the state the `try` started in.  For a self-call the
callee's run gives it: its data is one its body lists (`Prog.run_dataS`,
`Calculus/DataIn.lean`), so one of the rule's goals is the clause after
that datum's allocation (`Prog.run_litBytes`); with `raw`, the body has no
`assert` (`Prog.asserts_of_revertDatas`), so the callee does not panic and
no `Panic` data, the transaction's, is bound.  At another receiver the rule's
goal is `false` (`assert(false);` after the `require`s), so nothing is to
show there.
-/

namespace Solidity

open Solidity (Modality)

variable {C : Contract} {Γ : Ctx}

/-- `Panic` data has `Panic`'s selector: no `Error` reason decodes from it. -/
theorem Semantics.decodeError_encodePanic (c : Nat) :
    Semantics.decodeError (Semantics.encodePanic c) = none := by
  simp only [Semantics.decodeError, Semantics.encodePanic, Semantics.panicSelector,
    Semantics.errorSelector, List.cons_append, List.take_succ_cons,
    List.take_zero, List.nil_append]
  rfl

/-- The data a self-call's callee reverts with, where a clause of `kind`
binds something of it, is one `kind.datas` lists. -/
theorem catchBytes_self_mem {ρ ps Γf : Ctx} (call : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf) (kind : CatchKind) (σ : State C Γ)
    {ds : DSet} (hd : kind.datas sbody = some ds) {d bs : List UInt8}
    (hb : (match TRun.call sargs (.rets rets) sbody.ext sbody.runR σ with
      | .ok _ => .error .revert
      | .error .revert => .ok []
      | .error (.revertWith d) => .ok d
      | .error .panic => .ok (Semantics.encodePanic (TRun.selfPanicCode call σ).1.toNat)
      | .error e => .error e : TRes (List UInt8)) = .ok d)
    (hk : kind.decode d = some bs) : ds.Mem d := by
  cases kind with
  | reason =>
    have hS : sbody.revertDatas false = some ds := hd
    have hk' : Semantics.decodeError d = some bs := CatchKind.decode_reason hk
    revert hb
    cases hc : TRun.call sargs (.rets rets) sbody.ext sbody.runR σ with
    | ok => intro hb; cases hb
    | error e =>
      cases e with
      | revert => intro hb; cases hb; exact absurd hk' (by simp [Semantics.decodeError])
      | revertWith d' =>
        intro hb; cases hb
        exact TRun.call_dataS sargs (.rets rets) _ _ (Prog.run_dataS false sbody hS) σ d hc
          (.inr (by rw [hk']; rfl))
      | panic =>
        intro hb; cases hb
        rw [Semantics.decodeError_encodePanic] at hk'
        cases hk'
      | diverge | exhausted => intro hb; cases hb
  | raw =>
    have hd' : ((sbody.revertDatas true).map fun S => ([] :: S.1, S.2)) = some ds := hd
    simp only [Option.map_eq_some_iff] at hd'
    obtain ⟨S, hS, rfl⟩ := hd'
    revert hb
    cases hc : TRun.call sargs (.rets rets) sbody.ext sbody.runR σ with
    | ok => intro hb; cases hb
    | error e =>
      cases e with
      | revert => intro hb; cases hb; exact .inl List.mem_cons_self
      | revertWith d' =>
        intro hb; cases hb
        rcases TRun.call_dataS sargs (.rets rets) _ _ (Prog.run_dataS true sbody hS) σ d hc
          (.inl rfl) with h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inr h
      | panic =>
        intro _
        exact absurd hc (TRun.call_noPanic sargs (.rets rets) _ _
          (Prog.run_noPanic sbody (Prog.asserts_of_revertDatas sbody hS)) σ)
      | diverge | exhausted => intro hb; cases hb

theorem Pat.lenTm_eval (σ : State C Γ) (bs : List UInt8) (hn : bs.length < 2 ^ 256) :
    (Pat.lenTm (C := C) (Γ := Γ)).eval (σ.allocPush (bytesObj σ.H bs hn)) =
      some (uintOfNat bs.length) := by
  show (σ.alloc (bytesObj σ.H bs hn)).1.glob.memT.lenId (.prim .uint)
    ((σ.alloc (bytesObj σ.H bs hn)).2 : HRef _ bytesR).id = _
  rw [Grown.lenId_ref (σ.alloc (bytesObj σ.H bs hn)).1.glob.memT (σ.alloc (bytesObj σ.H bs hn)).2]
  show some (Heap.lenU (σ.heap.alloc (bytesObj σ.H bs hn)).1
    (σ.heap.alloc (bytesObj σ.H bs hn)).2) = _
  simp only [Heap.lenU, Heap.len, Heap.get_alloc, MObj.elems_dyn, MObj.wk, List.length_map]
  rw [uintOfNat_eq_lenU hn]

theorem Pat.byteTm_eval (σ : State C Γ) (bs : List UInt8) (hn : bs.length < 2 ^ 256) (i : Nat)
    (b : UInt8) (hb : bs[i]? = some b) :
    (Pat.byteTm (C := C) (Γ := Γ) i).eval (σ.allocPush (bytesObj σ.H bs hn)) =
      some (uintOfNat b.toNat) := by
  have hi : i < 2 ^ 256 := Nat.lt_trans (List.getElem?_eq_some_iff.1 hb).1 hn
  show (σ.alloc (bytesObj σ.H bs hn)).1.glob.memT.readT
    (MAddrT.index ((σ.alloc (bytesObj σ.H bs hn)).2 : HRef _ bytesR).id .dyn (Pat.word i)) = _
  simp only [Grown.readT, MAddrT.resolve, HRef.ofId?_self, Option.map_some, bind, Option.bind]
  show Heap.index (σ.heap.alloc (bytesObj σ.H bs hn)).1 (σ.heap.alloc (bytesObj σ.H bs hn)).2 .dyn
    (Pat.word i) = _
  simp only [Heap.index, Heap.get_alloc, MObj.elems_dyn, MObj.wk, Pat.word_eq hi, uintOfNat_val hi,
    Int.toNat_natCast, List.getElem?_map, hb, Option.map_some]
  rw [uintOfNat_eq_lenU (Nat.lt_trans b.toNat_lt (by decide))]
  rfl

theorem Pat.byteFmls_holds (σ : State C Γ) {bs : List UInt8} (hn : bs.length < 2 ^ 256) :
    (p : Pat) → (i : Nat) → (∀ j b, p[j]? = some (some b) → bs[i + j]? = some b) →
      ∀ ψ ∈ Pat.byteFmls (C := C) (Γ := Γ) p i, holds (σ.allocPush (bytesObj σ.H bs hn)) ψ
  | [], _, _ => fun _ h => nomatch h
  | none :: p, i, h => Pat.byteFmls_holds σ hn p (i + 1) fun j b hj => by
      have := h (j + 1) b (by simpa only [List.getElem?_cons_succ] using hj)
      rwa [show i + (j + 1) = i + 1 + j by omega] at this
  | some c :: p, i, h => by
    intro ψ hψ
    rcases List.mem_cons.1 hψ with rfl | hψ
    · exact (holds_eq_of_eval (Pat.byteTm_eval σ bs hn i c
        (by simpa only [Nat.add_zero] using h 0 c rfl)) rfl).2
        (Pat.word_eq (Nat.lt_trans c.toNat_lt (by decide))).symm
    · exact Pat.byteFmls_holds σ hn p (i + 1) (fun j b hj => by
        have := h (j + 1) b (by simpa only [List.getElem?_cons_succ] using hj)
        rwa [show i + (j + 1) = i + 1 + j by omega] at this) ψ hψ

/-- **A datum known in part says what the fresh object of the bytes it
stands for holds** (`Pat.fml`): their length and known bytes. -/
theorem Pat.fml_holds (σ : State C Γ) {p : Pat} {bs : List UInt8} (hn : bs.length < 2 ^ 256)
    (hm : p.Matches bs) : holds (σ.allocPush (bytesObj σ.H bs hn)) (Pat.fml (C := C) p) := by
  rw [Pat.fml, holds_conj]
  intro ψ hψ
  rcases List.mem_cons.1 hψ with rfl | hψ
  · exact (holds_eq_of_eval (Pat.lenTm_eval σ bs hn) rfl).2 (by rw [hm.1, Pat.word_eq hn])
  · exact Pat.byteFmls_holds σ hn p 0 (fun j b hj => by rw [Nat.zero_add]; exact hm.2 j b hj) ψ hψ

/-- The goal for data of any contents (`Premise.allocBranches`,
`Fml.allocGoal`): past the `require`s `Q`, which pass, the clause for every
fresh `bytes` of which `h` holds gives the clause after the allocation of
the bytes `bs`, where `h` holds of them (`TRun.litBytesT_alloc`). -/
theorem catch_alloc_sound {Γ₁ Γ₂ Γ₀ : Ctx} (σ : State C Γ) (Q : Prog C Γ Γ)
    (hQ : Prog.runSt σ Q = .ok σ) (x : Var) (body : Prog C (.mem bytesR :: Γ) Γ₁)
    (ω : Prog C Γ Γ₂) (κ : Frames C Γ₂ Γ₀) (φ : Fml C Γ₀) (bs : List UInt8)
    (hn : bs.length < 2 ^ 256) (hy : Option (Fml C (.mem bytesR :: Γ)))
    (hh : ∀ c, hy = some c → holds (σ.allocPush (bytesObj σ.H bs hn)) c)
    (h : holds σ (Fml.allocGoal .box Q x bytesR hy
      (.modalK .box body (.pop .block ((Ext.push .refl).trans body.ext) (.seq ω κ)) φ))) :
    Modality.afterRunTR .box (holds · φ)
      ((((TRun.litBytesT bs body.runR σ).map fun o =>
          (⟨o.st.drop ((Ext.push .refl).trans body.ext), o.ext⟩ : Out C σ.H Γ)).map (·.st)).bind
        fun υ => (Prog.runSt υ ω).bind (Frames.runSt · κ)) := by
  unfold Fml.allocGoal at h
  rw [holds_modal_iff, hQ] at h
  have ha := h.1 (bytesObj σ.H bs hn)
  have hG : holds (σ.allocPush (bytesObj σ.H bs hn))
      (.modalK .box body (.pop .block ((Ext.push .refl).trans body.ext) (.seq ω κ)) φ) := by
    cases hy with
    | none => exact ha
    | some c => exact ha (hh c rfl)
  have h0 := holds_modalK_pop _ _ _ ω κ φ hG
  rw [TRes.map_st _ _ (State.drop ((Ext.push .refl).trans body.ext)) fun _ => rfl,
    TRun.litBytesT_alloc σ bs hn]
  exact h0

/-- **`catchDataBox`** (Lean): for a self-call whose callee's data are known,
the clause after the allocation of each literal datum it may bind, and for
every fresh `bytes` each datum known in part stands for; at another
receiver, or where the data are not known, the clause after the allocation
of any bytes (`catch_alloc_sound`). -/
theorem Premise.sound_catchDataBox {ρ ps Γf Γ₁ : Ctx} (call : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf) (self : Bool) (kind : CatchKind) (x : Var)
    (body : Prog C (.mem bytesR :: Γ) Γ₁) (σ : State C Γ) :
    Premise.Sound .box (.catchData call rets sargs sbody self kind x body)
      (catchDataStep .box call sbody self kind x body) σ := by
  intro _ _ ω κ φ h
  rw [holds_modal_iff, runSt_cons_frames]
  show Modality.afterRunTR .box _ (((TRun.catchData call rets sargs sbody.ext sbody.runR self kind
    body.ext body.runR σ).map (·.st)).bind _)
  unfold TRun.catchData
  cases hb : TRun.catchBytes call rets sargs sbody.ext sbody.runR self σ with
  | error e =>
    exact afterRunTR_box_error (TRun.catchBytes_ne_panic hb)
  | ok d =>
  rw [ok_bind]
  cases hk : kind.decode d with
  | none => exact afterRunTR_box_error nofun
  | some bs =>
  dsimp only
  have hn : bs.length < 2 ^ 256 := CatchKind.decode_lt hk
  have hz : ¬ (call.addr.evalT σ).1 = 0 := by
    intro hz
    unfold TRun.catchBytes at hb
    rw [if_pos hz] at hb
    cases hb
  have hc : call.hasCode.evalT σ = .ok true := by
    rw [ExtCall.hasCode_evalT]; simp only [hz, decide_false, Bool.not_false]
  have hQ : Prog.runSt σ (.cons (.require call.hasCode) .nil) = .ok σ := by
    rw [Prog.runSt_require_true hc]; rfl
  have none_holds : ∀ c, (none : Option (Fml C (.mem bytesR :: Γ))) = some c →
      holds (σ.allocPush (bytesObj σ.H bs hn)) c := fun _ h => nomatch h
  cases self with
  | false =>
    exact catch_alloc_sound σ _ hQ x body ω κ φ bs hn none none_holds
      (by unfold catchDataStep at h; exact h)
  | true =>
  cases hd : kind.datas sbody with
  | none =>
    exact catch_alloc_sound σ _ hQ x body ω κ φ bs hn none none_holds
      (by unfold catchDataStep at h; rw [hd] at h; exact h)
  | some ds =>
  have h' := h
  unfold catchDataStep at h'
  rw [hd] at h'
  have hall := (holds_conj _).1 h'
  unfold TRun.catchBytes at hb
  rw [if_neg hz] at hb
  split at hb
  · rename_i hs
    simp only [Bool.true_and, decide_eq_true_eq] at hs
    have hi : call.isSelf.evalT σ = .ok true := by
      rw [ExtCall.isSelf_evalT]; simp only [hs, decide_true]
    rcases catchBytes_self_mem call rets sargs sbody kind σ hd hb hk with hbs | ⟨p, hp, hm⟩
    · have hψ : holds σ (Fml.modalK .box (.cons (.require call.hasCode)
          (.cons (.require call.isSelf) (catchLit x kind d body)))
          (.pop .block ((Ext.append Γ []).trans (Prog.cons (.require call.hasCode)
            (.cons (.require call.isSelf) (catchLit x kind d body))).ext) (.seq ω κ)) φ) :=
        hall _ (List.mem_append_left _ (List.mem_map.2 ⟨_, List.mem_map.2 ⟨d, hbs, rfl⟩, rfl⟩))
      have hl : catchLit x kind d body = litBytes x bs body := by
        unfold catchLit; rw [hk]
      have h0 := holds_modalK_pop σ _ _ ω κ φ hψ
      rw [Prog.runSt_require_true hc, Prog.runSt_require_true hi, hl] at h0
      have e : Prog.runSt σ (litBytes x bs body) = (TRun.litBytesT bs body.runR σ).map (·.st) := by
        show (Prog.run σ (litBytes x bs body)).map (·.st) = _
        rw [Prog.run_litBytes]
      rw [e, show (Ext.append Γ []).trans (Prog.cons (.require call.hasCode)
        (.cons (.require call.isSelf) (litBytes x bs body))).ext =
        (Ext.push .refl).trans body.ext from Subsingleton.elim _ _] at h0
      rw [TRes.map_st _ _ (State.drop ((Ext.push .refl).trans body.ext)) fun _ => rfl]
      exact h0
    · have hQs : Prog.runSt σ (.cons (.require call.hasCode) (.cons (.require call.isSelf) .nil)) =
          .ok σ := by rw [Prog.runSt_require_true hc, Prog.runSt_require_true hi]; rfl
      refine catch_alloc_sound σ _ hQs x body ω κ φ bs hn (kind.patFml p) ?_
        (hall _ (List.mem_append_right _ (List.mem_map.2 ⟨_, List.mem_append_left _
          (List.mem_map.2 ⟨p, hp, rfl⟩), rfl⟩)))
      intro c hc'
      cases kind with
      | reason => cases hc'
      | raw =>
        cases hc'
        have hdb : d = bs := by
          simp only [CatchKind.decode] at hk
          split at hk
          · cases hk; rfl
          · cases hk
        subst hdb
        exact Pat.fml_holds σ hn hm
  · rename_i hs
    simp only [Bool.true_and, decide_eq_true_eq] at hs
    have hn' : call.notSelf.evalT σ = .ok true := by
      rw [ExtCall.notSelf_evalT]; simp only [hs, decide_false, Bool.not_false]
    exact catch_alloc_sound σ _
      (by rw [Prog.runSt_require_true hc, Prog.runSt_require_true hn']; rfl) x body ω κ φ bs hn
      none none_holds
      (hall _ (List.mem_append_right _ (List.mem_map.2 ⟨_, List.mem_append_right _
        (List.mem_singleton_self _), rfl⟩)))

/-- **The rule of a `catch` clause binding the data is sound**: `catchDataBox`
under the box, `false` under the diamond. -/
theorem Stmt.sound_catchData (k : Nat) (m : Modality) {ρ ps Γf Γ₁ : Ctx} (call : ExtCall C Γ)
    (rets : Binders ρ) (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf) (self : Bool)
    (kind : CatchKind) (x : Var) (body : Prog C (.mem bytesR :: Γ) Γ₁) (σ : State C Γ)
    (pr : Premise C Γ Γ)
    (hp : Stmt.step k m (.catchData call rets sargs sbody self kind x body) = pr) :
    Premise.Runs m (.catchData call rets sargs sbody self kind x body) pr σ := by
  change catchDataStep m call sbody self kind x body = pr at hp
  cases m with
  | box =>
    cases hp
    have hs : Premise.Sound .box (.catchData call rets sargs sbody self kind x body)
        (catchDataStep .box call sbody self kind x body) σ :=
      Premise.sound_catchDataBox call rets sargs sbody self kind x body σ
    revert hs
    unfold catchDataStep
    split <;> exact id
  | diamond => cases hp; exact Premise.sound_done σ false nofun

end Solidity
