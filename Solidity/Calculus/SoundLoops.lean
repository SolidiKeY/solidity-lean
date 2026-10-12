import Solidity.Theory.Bridge.Denote
import Solidity.Calculus.SoundArms
import Solidity.Calculus.SoundCalls

/-!
# The rules of loops are sound

`Calculus/Blocks.lean`'s `loopStep` against the typed run
(`TRun.loop`, `TLoop.run`), in the shape of `Calculus/SoundKit.lean`.

* `whileUnwind` is one turn of the loop (`TLoop.run_unfold`,
  `Stmt.runSt_loop_unfold`), `loopExit` its exit; `whileClose` and
  `whileNoVariantDiamond` close to `false`.
* The invariant rules: every loop head is a state the body's frame allows
  from the first (`Prog.run_frame`), so the premise read under
  `{anon(xs)}` holds there (`holds_anonHavoc`, from
  `State.eq_anonHavoc`); the invariant holds at every head by induction on
  the iterations (`TLoop.run_induct`).  Under the diamond the body is read
  under the variant's local (`Prog.wk up`), which it keeps
  (`Prog.run_wk`), and the variant bounds the iterations left
  (`TLoop.run_variant`).  A condition is a `bool` of the typed state, so it
  is `true` or `false` wherever it is read; what the rule's terms read on
  the erasure is the typed value (`holds_isBoolD_lower`, from
  `Val.lower_evalT` (`Calculus/LowerRun.lean`), `Val.evalT_ends` and the term bridge `Tm.denote_eval`, `Calculus/SeqRewrite.lean`).
-/

namespace Solidity
open Semantics (Value Res Halt)
open Solidity (Modality Mutability)

variable {C : Contract}

/-- `a < b`, `a <= b` between `uint`s true: both sides are numbers, so
ordered (master's `Term.cmp_true`, `Calculus/SoundLoop` at `ad728b16`,
on values). -/
theorem evalBinop_cmp_true {op : BinOp} (hop : op = .lt ∨ op = .le) {a : Value} {rb : Res Value}
    (h : evalBinop op .uint a rb = .ok (.bool true)) :
    ∃ x y : Int, a = .int x ∧ rb = .ok (.int y) ∧ (op = .lt → x < y) ∧ (op = .le → x ≤ y) := by
  rcases hop with rfl | rfl <;> cases rb with
  | error e => cases a <;> cases h
  | ok vb =>
    cases a with
    | bool => cases h
    | int x =>
      cases vb with
      | bool => cases h
      | int y =>
        have h' : decide _ = true := Semantics.PrimVal.bool.inj (Except.ok.inj h)
        refine ⟨x, y, rfl, rfl, fun hh => ?_, fun hh => ?_⟩ <;>
          first | exact of_decide_eq_true h' | cases hh

section Cond

variable {Γ : Ctx}

/-- `t ≐ b` holds over the typed state where `t` returns `b` on the
erasure. -/
theorem holds_isBoolD (t : Tm C Γ .val) (σ : State C Γ) (b : Bool) :
    holds σ (Fml.isBoolD t b) ↔ t.eval σ.erase = .ok (.bool b) := by
  constructor
  · rintro ⟨⟨x, hx⟩, _, he⟩
    have he' : Theory.StValue.Equiv (.prim x) (.prim (.bool b)) := by
      rw [← Tm.denote_eval σ.erase t x hx]; exact he
    rw [Theory.StValue.Equiv.prim_iff] at he'
    cases he'
    exact hx
  · intro h
    refine ⟨⟨_, h⟩, ⟨_, rfl⟩, ?_⟩
    show Theory.StValue.Equiv (t.denote σ.erase) (.prim (.bool b))
    rw [Tm.denote_eval σ.erase t _ h]
    exact Theory.StValue.Equiv.refl _

/-- **`eqD` is the interpreter's equation** over the typed state: both
sides return, with one value, on the erasure. -/
theorem holds_eqD_iffS {σ : State C Γ} {a b : Tm C Γ .val} :
    holds σ (Fml.eqD a b) ↔ ∃ x, a.eval σ.erase = .ok x ∧ b.eval σ.erase = .ok x := by
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩, he⟩
    have he' : Theory.StValue.Equiv (.prim x) (.prim y) := by
      rw [← Tm.denote_eval σ.erase a x hx, ← Tm.denote_eval σ.erase b y hy]; exact he
    rw [Theory.StValue.Equiv.prim_iff] at he'
    cases he'
    exact ⟨x, hx, hy⟩
  · rintro ⟨x, hx, hy⟩
    refine ⟨⟨x, hx⟩, ⟨x, hy⟩, ?_⟩
    show Theory.StValue.Equiv (a.denote σ.erase) (b.denote σ.erase)
    rw [Tm.denote_eval σ.erase a x hx, Tm.denote_eval σ.erase b x hy]
    exact Theory.StValue.Equiv.refl _

/-- A value that returns over the typed state: its lowered term reads its
erasure on the erased state (`Val.lower_evalT`). -/
theorem Val.lower_eval_ok {p : PrimTy} (v : Val C Γ p) (σ : State C Γ) {x : p.Denote}
    (h : v.evalT σ = .ok x) : v.lower.eval σ.erase = .ok (PrimTy.erase x) :=
  (Val.lower_evalT σ v).eq_ok h

/-- What a value's lowered term reads on the erased state, where the typed
value halts: a halt too, for it never diverges. -/
theorem Val.lower_eval_error {p : PrimTy} (v : Val C Γ p) (σ : State C Γ) {e : THalt}
    (h : v.evalT σ = .error e) : ∃ e', v.lower.eval σ.erase = .error e' := by
  have hnd := Val.evalT_ends σ v
  rw [h] at hnd
  exact (Val.lower_evalT σ v).eq_error h (fun hd => hnd.1 (hd ▸ rfl)) (fun hx => hnd.2 (hx ▸ rfl))

/-- **A lowered condition** holds `b` over the typed state where it
evaluates to `b`. -/
theorem holds_isBoolD_lower (c : Val C Γ .bool) (σ : State C Γ) (b : Bool) :
    holds σ (Fml.isBoolD c.lower b) ↔ c.evalT σ = .ok b := by
  rw [holds_isBoolD]
  cases h : c.evalT σ with
  | ok v =>
    rw [Val.lower_eval_ok c σ h]
    constructor
    · intro h'
      have : v = b := Semantics.PrimVal.bool.inj (Except.ok.inj h')
      rw [this]
    · intro h'
      rw [show v = b from Except.ok.inj h']
      rfl
  | error e =>
    obtain ⟨e', he'⟩ := Val.lower_eval_error c σ h
    rw [he']
    exact ⟨nofun, nofun⟩

end Cond

/-! ## The loop, one turn -/

section Turn

variable {Γ Γ₁ : Ctx}

/-- A loop started from an outcome runs, read through its states, as the
loop from that outcome's state: the heap's extension it carries plays no
part. -/
theorem Stmt.run_loop_from (σ : State C Γ) (a : LoopAnn C Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Γ₁) (τ : Out C σ.H Γ) :
    (TLoop.run (fun o : Out C σ.H Γ => (Prog.run o.st body).map
          fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩)
        (fun o => c.evalT o.st) τ).map (·.st) =
      (Stmt.run τ.st (.loop a c body)).map (·.st) := by
  rw [Stmt.run_loop]
  have hm := TLoop.run_map (body := fun o : Out C τ.st.H Γ => (Prog.run o.st body).map
          fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩)
    (c := fun o => c.evalT o.st)
    (body' := fun o : Out C σ.H Γ => (Prog.run o.st body).map
          fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩)
    (c' := fun o => c.evalT o.st)
    (fun o : Out C τ.st.H Γ => (⟨o.st, τ.ext.trans o.ext⟩ : Out C σ.H Γ)) (fun _ => rfl)
    (fun a => by dsimp only; cases Prog.run a.st body <;> rfl) ⟨τ.st, List.prefix_refl _⟩
  rw [show (⟨τ.st, τ.ext.trans (List.prefix_refl _)⟩ : Out C σ.H Γ) = τ from rfl] at hm
  rw [hm]
  cases TLoop.run _ _ (⟨τ.st, List.prefix_refl _⟩ : Out C τ.st.H Γ) <;> rfl

/-- **One turn of a loop**, read through its states: the condition, then the
body, its locals popped, and the loop again. -/
theorem Stmt.runSt_loop_unfold (σ : State C Γ) (a : LoopAnn C Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Γ₁) :
    Stmt.runSt σ (.loop a c body) =
      (c.evalT σ).bind fun v => if boolT v then
        ((Prog.runSt σ body).map (State.drop body.ext)).bind fun τ =>
          Stmt.runSt τ (.loop a c body)
      else .ok σ := by
  unfold Stmt.runSt
  rw [Stmt.run_loop, TLoop.run_unfold]
  unfold TLoop.step
  dsimp only
  cases c.evalT σ with
  | error => rfl
  | ok v =>
    cases v with
    | false => rfl
    | true =>
      show _ = ((Prog.runSt σ body).map _).bind _
      unfold Prog.runSt
      cases Prog.run σ body with
      | error => rfl
      | ok o => exact Stmt.run_loop_from σ a c body _

/-- A block, read through its states: the body, its locals popped. -/
theorem Stmt.runSt_block (σ : State C Γ) (P : Prog C Γ Γ₁) :
    Stmt.runSt σ (.block P) = (Prog.runSt σ P).map (State.drop P.ext) :=
  TRes.map_st _ _ _ fun _ => rfl

/-- An `if`, read through its states. -/
theorem Stmt.runSt_ite {Γ₂ : Ctx} (σ : State C Γ) (c : Val C Γ .bool) (thn : Prog C Γ Γ₁)
    (els : Prog C Γ Γ₂) :
    Stmt.runSt σ (.ite c thn els) =
      (c.evalT σ).bind fun v => if boolT v then (Prog.runSt σ thn).map (State.drop thn.ext)
        else (Prog.runSt σ els).map (State.drop els.ext) := by
  unfold Stmt.runSt
  show (TRun.ite c thn.ext thn.runR els.ext els.runR σ).map _ = _
  unfold TRun.ite
  cases c.evalT σ with
  | error => rfl
  | ok v => cases v <;> exact TRes.map_st _ _ _ fun _ => rfl

/-- The loop's annotation plays no part in its run. -/
theorem Stmt.runSt_loop_ann (σ : State C Γ) (a a' : LoopAnn C Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Γ₁) : Stmt.runSt σ (.loop a c body) = Stmt.runSt σ (.loop a' c body) :=
  rfl

/-- `whileUnwind`: `⟨[ while (nse) body ]⟩ ⇝ ⟨[ if (nse) { { body } while (nse) body } ]⟩`. -/
theorem Premise.sound_whileUnwind {m : Modality} (n : Nat) (c : Val C Γ .bool)
    (body : Prog C Γ Γ₁) (σ : State C Γ) :
    Premise.Runs m (.loop (.unwind (n + 1)) c body)
      (.unfold (.cons (.ite c (.cons (.block body) (.cons (.loop (.unwind n) c body) .nil)) .nil)
        .nil) .refl) σ := by
  refine Premise.sound_unfold σ ?_
  rw [Prog.runSt_single, Stmt.runSt_ite, Stmt.runSt_loop_unfold]
  cases c.evalT σ with
  | error => rfl
  | ok v =>
    cases v with
    | false => rfl
    | true =>
      show ((Prog.runSt σ (.cons (.block body) (.cons (.loop (.unwind n) c body) .nil))).map
        (State.drop (Ext.refl (Γ := Γ)))).map (State.drop .refl) = _
      rw [Prog.runSt_cons, Stmt.runSt_block]
      cases (Prog.runSt σ body).map (State.drop body.ext) with
      | error => rfl
      | ok τ =>
        show ((Prog.runSt τ (.cons (.loop (.unwind n) c body) .nil)).map _).map _ = _
        rw [Prog.runSt_single, Stmt.runSt_loop_ann τ (.unwind n) (.unwind (n + 1))]
        show _ = Stmt.runSt τ (.loop (.unwind (n + 1)) c body)
        cases Stmt.runSt τ (.loop (.unwind (n + 1)) c body) <;> rfl

/-- `loopExit`: `⟨[ while (nse) body ]⟩ ⇝ nse = FALSE ⟹ ⟨[ ]⟩ ; nse = FALSE`. -/
theorem Premise.sound_loopExit {m : Modality} (c : Val C Γ .bool) (body : Prog C Γ Γ₁)
    (σ : State C Γ) :
    Premise.Runs m (.loop (.unwind 0) c body) (.check (Fml.isBoolD c.lower false)) σ :=
  Premise.sound_check σ fun h => by
    rw [Stmt.runSt_loop_unfold, (holds_isBoolD_lower c σ false).1 h]
    rfl

end Turn

/-! ## The invariant rules -/

section Inv

variable {Γ Γ₁ : Ctx}

/-- **A state in a loop body's frame is one its anonymised premise covers**
(`holds_anonHavoc`, over the typed state): `{anon(xs)}` (`{havoc}` when
`hv`) of the loop's first state reaches every state that agrees with it but
where the body may write. -/
theorem holds_anonHavoc {σ τ : State C Γ} {xs : List ((t : LTy) × Idx Γ t)} {hv : Bool}
    {W : List (LTy × Nat)}
    (hxs : ∀ t (i : Idx Γ t), (t, i.toNat) ∈ W → (⟨t, i⟩ : (t : LTy) × Idx Γ t) ∈ xs)
    (hg : TGFrame (frameMut hv) σ τ) (ha : TLocAgree 0 W σ.env τ.env) {ψ : Fml C Γ}
    (h : holds σ (Fml.anonHavoc xs hv ψ)) : holds τ ψ := by
  obtain ⟨b, hb⟩ := State.eq_anonHavoc hxs hg ha
  cases hv with
  | false =>
    have hk := hg.keeps (by simp only [frameMut]; decide)
    have hτ : τ = σ.anon xs b := by rw [hb, hk.1, hk.2]; rfl
    rw [hτ]
    exact h b
  | true =>
    rw [hb]
    exact h b τ.storage τ.net

/-- The loop's run from `σ`, read through its states, then the rest. -/
abbrev loopThen {Γ₂ Γ₀ : Ctx} (σ : State C Γ) (ω : Prog C Γ Γ₂) (κ : Frames C Γ₂ Γ₀)
    (r : TRes (Out C σ.H Γ)) : TRes (State C Γ₀) :=
  (r.map (·.st)).bind fun τ => (Prog.runSt τ ω).bind (Frames.runSt · κ)

/-- **`whileInvariantBox` is sound** over the typed state. -/
theorem Premise.sound_whileInvBox (k : Nat) (I c : Val C Γ .bool)
    (dec : Option (Val C Γ .uint)) (body : Prog C Γ Γ₁) {xs : List ((t : LTy) × Idx Γ t)}
    {hv : Bool} (hf : body.frame = some (xs, hv)) (σ : State C Γ) :
    Premise.Runs .box (.loop (.inv I dec) c body)
      (.inv (.isBoolD I.lower true) xs hv (Upd.nil.decl (fse k) (.val (p := .bool) c.lower))
        (.isBoolD (.pvV (p := .bool) .here) true) (.isBoolD (.pvV (p := .bool) .here) false)
        .refl (.push .refl) body (.isBoolD I.lower true)) σ := by
  intro _ _ ω κ φ hp
  obtain ⟨hI0, hA⟩ := hp
  obtain ⟨hwμ, hxs⟩ := Prog.frame_some hf
  rw [holds_modal_iff, runSt_cons_frames]
  show Modality.afterRunTR .box _ (loopThen σ ω κ (TLoop.run
    (fun o : Out C σ.H Γ => (Prog.run o.st body).map
      fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩)
    (fun o => c.evalT o.st) ⟨σ, List.prefix_refl _⟩))
  refine TLoop.run_induct
    (P := fun a : Out C σ.H Γ => TGFrame (frameMut hv) σ a.st ∧
      TLocAgree 0 (Prog.writesAt 0 body) σ.env a.st.env ∧ holds a.st (Fml.isBoolD I.lower true))
    (Q := fun r => Modality.afterRunTR .box (holds · φ) (loopThen σ ω κ r))
    ⟨TGFrame.refl σ, TLocAgree.refl _, hI0⟩ (fun a ha => ?_) ⟨trivial, nofun⟩
  obtain ⟨hg, hag, hI⟩ := ha
  have hY := holds_anonHavoc hxs hg hag hA hI
  unfold TLoop.step
  dsimp only
  cases hc : c.evalT a.st with
  | error e =>
    refine ⟨trivial, fun h => ?_⟩
    cases h
    exact Val.evalT_noPanic a.st c hc
  | ok v =>
    have hU : (Upd.nil.decl (fse k) (.val (p := .bool) c.lower)).apply a.st.erase =
        .ok (a.st.push (t := .val .bool) v).erase := by
      show (do let τ₀ ← pure a.st.erase
               pure (τ₀.push (t := .val .bool) (← c.lower.eval a.st.erase))) = _
      rw [Val.lower_eval_ok c a.st hc]
      rfl
    change Modality.afterC .box _ (Upd.apply _ _) at hY
    rw [hU] at hY
    obtain ⟨hT, hF⟩ := hY _ rfl (List.prefix_refl _)
    cases v with
    | false =>
      have hF' := hF ((holds_isBoolD _ _ _).2 rfl) a.st rfl (List.prefix_refl _)
      exact (holds_modal_iff a.st ω κ φ).1 (holds_modalK a.st ω κ φ hF')
    | true =>
      have hT' := hT ((holds_isBoolD _ _ _).2 rfl) a.st rfl (List.prefix_refl _)
      have h' := (holds_modal_iff a.st body _ _).1 (holds_modalK a.st body _ _ hT')
      unfold Prog.runSt at h'
      dsimp only
      cases hb : Prog.run a.st body with
      | error e =>
        rw [hb] at h'
        exact ⟨trivial, fun h => h'.2 (by cases h; rfl)⟩
      | ok o =>
        rw [hb] at h'
        obtain ⟨hg', ha'⟩ := Prog.run_frame body hwμ 0 hb
        exact ⟨hg.trans (hg'.withEnv _), hag.trans ha', h'.1⟩

/-- A block's run, its frame popped with nothing after it, read through
its states. -/
theorem frames_pop_nil_run {H : HTy} {Γ' : Ctx} (b : BlockKind) (X : TRes (Out C H Γ₁))
    (h : Ext Γ' Γ₁) :
    (X.map (·.st)).bind (Frames.runSt · (.pop b h .nil)) = (X.map (Out.drop h)).map (·.st) := by
  cases X <;> rfl

/-- `TLoop.run_variant`, where the body may also halt with a halt of `X`
(`exhausted`, which both modalities accept, decision 15): the loop ends well
or halts so. -/
theorem TLoop.run_variant_or {α : Type} {body : α → TRes α} {c : α → TRes Bool}
    {H G : α → Prop} {X : THalt → Prop} {D : α → TRes Int}
    (hstep : ∀ τ, H τ → ∃ d, D τ = .ok d ∧
      (c τ = .ok true ∨ c τ = .ok false) ∧
      (c τ = .ok false → G τ) ∧
      (c τ = .ok true → (∃ e, body τ = .error e ∧ X e) ∨ ∃ τ₁, body τ = .ok τ₁ ∧ H τ₁ ∧
        (c τ₁ = .ok true → ∃ a : Int, D τ₁ = .ok a ∧ 0 ≤ a ∧ a < d)))
    {σ : α} (h0 : H σ) :
    (∃ τ, TLoop.run body c σ = .ok τ ∧ G τ) ∨ ∃ e, TLoop.run body c σ = .error e ∧ X e := by
  have exit : ∀ τ, c τ = .ok false → TLoop.run body c τ = .ok τ := fun τ hc => by
    rw [TLoop.run_unfold]; simp only [TLoop.step, hc]
  have next : ∀ τ τ₁, c τ = .ok true → body τ = .ok τ₁ →
      TLoop.run body c τ = TLoop.run body c τ₁ := fun τ τ₁ hc hb => by
    rw [TLoop.run_unfold (σ := τ)]; simp only [TLoop.step, hc, hb]
  have halt : ∀ τ e, c τ = .ok true → body τ = .error e → TLoop.run body c τ = .error e :=
    fun τ e hc hb => by rw [TLoop.run_unfold (σ := τ)]; simp only [TLoop.step, hc, hb]
  have T : ∀ n : Nat, ∀ τ, H τ →
      (c τ = .ok true → ∃ a : Int, D τ = .ok a ∧ 0 ≤ a ∧ a < n) →
      (∃ τf, TLoop.run body c τ = .ok τf ∧ G τf) ∨ ∃ e, TLoop.run body c τ = .error e ∧ X e := by
    intro n
    induction n with
    | zero =>
      intro τ hH hb
      obtain ⟨_, _, hcov, hex, _⟩ := hstep τ hH
      rcases hcov with hc | hc
      · obtain ⟨a, _, h₁, h₂⟩ := hb hc
        omega
      · exact .inl ⟨τ, exit τ hc, hex hc⟩
    | succ n ih =>
      intro τ hH hb
      obtain ⟨d, hd, hcov, hex, hbody⟩ := hstep τ hH
      rcases hcov with hc | hc
      · obtain ⟨a, hda, h₁, h₂⟩ := hb hc
        rcases hbody hc with ⟨e, hbe, hX⟩ | ⟨τ₁, hb₁, hH₁, hdec⟩
        · exact .inr ⟨e, halt τ e hc hbe, hX⟩
        rw [next τ τ₁ hc hb₁]
        refine ih τ₁ hH₁ fun hc₁ => ?_
        obtain ⟨a₁, hd₁, h₃, h₄⟩ := hdec hc₁
        rw [hda] at hd
        cases hd
        exact ⟨a₁, hd₁, h₃, by omega⟩
      · exact .inl ⟨τ, exit τ hc, hex hc⟩
  obtain ⟨d, _, hcov, hex, hbody⟩ := hstep σ h0
  rcases hcov with hc | hc
  · rcases hbody hc with ⟨e, hbe, hX⟩ | ⟨τ₁, hb₁, hH₁, hdec⟩
    · exact .inr ⟨e, halt σ e hc hbe, hX⟩
    rw [next σ τ₁ hc hb₁]
    refine T d.toNat τ₁ hH₁ fun hc₁ => ?_
    obtain ⟨a₁, hd₁, h₃, h₄⟩ := hdec hc₁
    exact ⟨a₁, hd₁, h₃, by omega⟩
  · exact .inl ⟨σ, exit σ hc, hex hc⟩

/-- **`whileInvariantDiamond` is sound** over the typed state: the variant
bounds the iterations left. -/
theorem Premise.sound_whileInvDiamond (k : Nat) (I c : Val C Γ .bool) (d : Val C Γ .uint)
    (body : Prog C Γ Γ₁) {xs : List ((t : LTy) × Idx Γ t)} {hv : Bool}
    (hf : body.frame = some (xs, hv)) (σ : State C Γ) {p : Premise C Γ Γ}
    (hp : loopStep k .diamond (.inv I (some d)) c body = p) :
    Premise.Runs .diamond (.loop (.inv I (some d)) c body) p σ := by
  unfold loopStep at hp
  rw [hf] at hp
  dsimp only at hp
  cases hp
  intro _ _ ω κ φ hp
  obtain ⟨hI0, hA⟩ := hp
  obtain ⟨hwμ, hxs⟩ := Prog.frame_some hf
  rw [holds_modal_iff, runSt_cons_frames]
  show Modality.afterRunTR .diamond _ (loopThen σ ω κ (TLoop.run
    (fun o : Out C σ.H Γ => (Prog.run o.st body).map
      fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩)
    (fun o => c.evalT o.st) ⟨σ, List.prefix_refl _⟩))
  suffices key : (∃ τ, TLoop.run
      (fun o : Out C σ.H Γ => (Prog.run o.st body).map
        fun o' => (⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩ : Out C σ.H Γ))
      (fun o => c.evalT o.st) ⟨σ, List.prefix_refl _⟩ = .ok τ ∧
        holds τ.st (Fml.modalK .diamond ω κ φ)) ∨ ∃ e, TLoop.run
      (fun o : Out C σ.H Γ => (Prog.run o.st body).map
        fun o' => (⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩ : Out C σ.H Γ))
      (fun o => c.evalT o.st) ⟨σ, List.prefix_refl _⟩ = .error e ∧ e = .exhausted by
    rcases key with ⟨τf, hrun, hG⟩ | ⟨e, hrun, rfl⟩
    · rw [hrun]
      exact (holds_modal_iff τf.st ω κ φ).1 (holds_modalK τf.st ω κ φ hG)
    · rw [hrun]
      exact ⟨rfl, nofun⟩
  refine TLoop.run_variant_or (X := fun e => e = .exhausted)
    (H := fun a : Out C σ.H Γ => TGFrame (frameMut hv) σ a.st ∧
      TLocAgree 0 (Prog.writesAt 0 body) σ.env a.st.env ∧ holds a.st (Fml.isBoolD I.lower true))
    (D := fun a : Out C σ.H Γ => (d.evalT a.st).map (·.1)) ?_
    ⟨TGFrame.refl σ, TLocAgree.refl _, hI0⟩
  rintro a ⟨hg, hag, hI⟩
  have hY := holds_anonHavoc hxs hg hag hA hI
  change Modality.afterC .diamond _ (Upd.apply _ _) at hY
  have hUe : ((Upd.nil.decl (fie k) (.val (p := .uint) d.lower)).decl (fse k)
      (.val (p := .bool) c.lower)).apply a.st.erase =
      (d.lower.eval a.st.erase >>= fun dv => c.lower.eval a.st.erase >>= fun cv =>
        pure ((a.st.erase.push (t := .val .uint) dv).push (t := .val .bool) cv)) := by
    show (do
      let τ₁ ← (do
        let τ₀ ← pure a.st.erase
        pure (τ₀.push (t := .val .uint) (← d.lower.eval a.st.erase)))
      pure (τ₁.push (t := .val .bool) (← c.lower.eval a.st.erase))) = _
    cases d.lower.eval a.st.erase <;> cases c.lower.eval a.st.erase <;> rfl
  rw [hUe] at hY
  cases hd : d.evalT a.st with
  | error e =>
    obtain ⟨e', he'⟩ := Val.lower_eval_error d a.st hd
    rw [he'] at hY
    exact hY.elim
  | ok dv =>
  cases hc : c.evalT a.st with
  | error e =>
    obtain ⟨e', he'⟩ := Val.lower_eval_error c a.st hc
    rw [Val.lower_eval_ok d a.st hd, he'] at hY
    exact hY.elim
  | ok cv =>
  rw [Val.lower_eval_ok d a.st hd, Val.lower_eval_ok c a.st hc] at hY
  obtain ⟨hT, hF⟩ := hY ((a.st.push (t := .val .uint) dv).push (t := .val .bool) cv) rfl
    (List.prefix_refl _)
  refine ⟨dv.1, by show (d.evalT a.st).map _ = _; rw [hd]; rfl, ?_, fun hc' => ?_, fun hc' => ?_⟩
  · cases cv
    · exact .inr rfl
    · exact .inl rfl
  · have hcv : cv = false := Except.ok.inj hc'
    subst hcv
    have hF' := hF ((holds_isBoolD _ _ _).2 rfl) a.st rfl (List.prefix_refl _)
    exact hF'
  · have hcv : cv = true := Except.ok.inj hc'
    subst hcv
    have hT' := hT ((holds_isBoolD _ _ _).2 rfl) (a.st.push (t := .val .uint) dv) rfl
      (List.prefix_refl _)
    have h' := (holds_modal_iff _ _ _ _).1 (holds_modalK _ _ _ _ hT')
    unfold Prog.runSt at h'
    rw [frames_pop_nil_run, State.push_lift,
      (TWkRel.drop (Prog.wk_over body up)
        (Prog.run_wk body up a.st
          ((dv, a.st.env) : TEnv C a.st.H (.val .uint :: Γ)))).eq_lifted] at h'
    cases hb : Prog.run a.st body with
    | error e =>
      rw [hb] at h'
      exact .inl ⟨e, rfl, h'.1⟩
    | ok o =>
      rw [hb] at h'
      obtain ⟨hg', ha'⟩ := Prog.run_frame body hwμ 0 hb
      obtain ⟨hI₁, hdec⟩ := h'.1
      let τ₀ : State C Γ := o.st.drop body.ext
      change holds (τ₀.push (t := .val .uint) dv) _ at hI₁ hdec
      refine .inr ⟨⟨τ₀, a.ext.trans o.ext⟩, rfl, ⟨hg.trans (hg'.withEnv _), hag.trans ha', ?_⟩,
        fun hc₁ => ?_⟩
      · have hI' := (holds_isBoolD_lower I.up (τ₀.push (t := .val .uint) dv) true).1 hI₁
        rw [Val.evalT_up] at hI'
        exact (holds_isBoolD_lower I τ₀ true).2 hI'
      · change c.evalT τ₀ = _ at hc₁
        have hcu : c.up.evalT (τ₀.push (t := .val .uint) dv) = .ok true := by
          rw [Val.evalT_up]; exact hc₁
        change Modality.afterC .diamond _ (Upd.apply _ _) at hdec
        have hU₁ : (Upd.nil.decl (fse k) (.val (p := .bool) c.up.lower)).apply
            (τ₀.push (t := .val .uint) dv).erase =
            .ok ((τ₀.push (t := .val .uint) dv).push (t := .val .bool) true).erase := by
          show (do
            let υ ← pure (τ₀.push (t := .val .uint) dv).erase
            pure (υ.push (t := .val .bool)
              (← c.up.lower.eval (τ₀.push (t := .val .uint) dv).erase))) = _
          rw [Val.lower_eval_ok _ _ hcu]
          rfl
        rw [hU₁] at hdec
        obtain ⟨hle, hlt⟩ := hdec _ rfl (List.prefix_refl _) ((holds_isBoolD _ _ _).2 rfl)
        rw [holds_isBoolD] at hle hlt
        change evalBinop .le .uint (.int 0) (d.up.up.lower.eval _) = _ at hle
        change (d.up.up.lower.eval _ >>= fun a => evalBinop .lt .uint a (pure (.int dv.1))) = _
          at hlt
        cases hdx : d.evalT τ₀ with
        | error e =>
          have hd₂ : (d.up.up (t := .val .bool)).evalT
              ((τ₀.push (t := .val .uint) dv).push (t := .val .bool) true) = .error e := by
            rw [Val.evalT_up, Val.evalT_up]; exact hdx
          obtain ⟨e', he'⟩ := Val.lower_eval_error _ _ hd₂
          rw [he'] at hle
          obtain ⟨_, _, -, hy, -, -⟩ := evalBinop_cmp_true (.inr rfl) hle
          cases hy
        | ok x =>
          have hd₂ : (d.up.up (t := .val .bool)).evalT
              ((τ₀.push (t := .val .uint) dv).push (t := .val .bool) true) = .ok x := by
            rw [Val.evalT_up, Val.evalT_up]; exact hdx
          rw [Val.lower_eval_ok _ _ hd₂] at hle hlt
          obtain ⟨_, y, hx0, hy, -, hle'⟩ := evalBinop_cmp_true (.inr rfl) hle
          cases hx0
          cases hy
          change evalBinop .lt .uint (.int x.1) (pure (.int dv.1)) = _ at hlt
          obtain ⟨x', z, hx', hz, hlt', -⟩ := evalBinop_cmp_true (.inl rfl) hlt
          cases hx'
          cases hz
          exact ⟨x.1, by show (d.evalT τ₀).map _ = _; rw [hdx]; rfl, hle' rfl, hlt' rfl⟩

end Inv

/-! ## The rule of a loop -/

/-- **The rule of a loop is sound** over the typed state: unwound, ended, by
its invariant, or closed to `false`. -/
theorem Stmt.sound_loop (k : Nat) (m : Modality) {Γ Γ₁ : Ctx} (a : LoopAnn C Γ)
    (c : Val C Γ .bool) (body : Prog C Γ Γ₁) (σ : State C Γ) (p : Premise C Γ Γ)
    (hp : Stmt.step k m (.loop a c body) = p) :
    Premise.Runs m (.loop a c body) p σ := by
  change loopStep k m a c body = p at hp
  cases a with
  | unwind n =>
    cases n with
    | zero =>
      unfold loopStep at hp
      cases hp
      exact Premise.sound_loopExit c body σ
    | succ n =>
      unfold loopStep at hp
      cases hp
      exact Premise.sound_whileUnwind n c body σ
  | inv I dec =>
    cases hf : body.frame with
    | none =>
      unfold loopStep at hp
      rw [hf] at hp
      cases hp
      exact Premise.sound_done σ false nofun
    | some f =>
      obtain ⟨xs, hv⟩ := f
      cases m with
      | box =>
        unfold loopStep at hp
        rw [hf] at hp
        dsimp only at hp
        cases hp
        exact Premise.sound_whileInvBox k I c dec body hf σ
      | diamond =>
        cases dec with
        | none =>
          unfold loopStep at hp
          rw [hf] at hp
          dsimp only at hp
          cases hp
          exact Premise.sound_done σ false nofun
        | some d => exact Premise.sound_whileInvDiamond k I c d body hf σ hp

end Solidity
