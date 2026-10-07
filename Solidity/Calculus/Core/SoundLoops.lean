import Solidity.Calculus.Core.SoundBlocks
import Solidity.Calculus.Core.RunWk
import Solidity.Calculus.Core.RunFrame

/-!
# The loop invariant rules are sound

`whileInvariantBox` and `whileInvariantDiamond` (`Calculus/Core/Blocks.lean`'s
`loopStep`) against `Core.Stmt.run`, as `Calculus/SoundLoop.lean` proves
today's.  Every loop head is a state the body's frame allows from the first
(`Prog.run_frame`), so the premise read under `{anon(xs)}` holds there
(`holds_anonHavoc`); the invariant holds at every head by induction on the
iterations (`Loop.run_induct`).  Under the diamond the body is read under the
variant's local (`Prog.wk up`), which it therefore keeps (`Prog.run_wk`), and
the variant bounds the iterations left (`Loop.run_variant`), and the
rule's cover (`Fml.invCases`) that the condition reads as a `bool`.

The body's own locals are popped at the end of every iteration, so the
frame need not list them (`Calculus/Core/Blocks.lean`): the anonymised
premise is read at the loop's context, where they do not exist.
-/

namespace Solidity.Core

open Semantics (Value Res Halt)
open Solidity (Modality Mutability)

variable {C : Contract}

/-- A block's frame popped, with nothing after it. -/
theorem frames_pop_nil {Γ Γ₁ : Ctx} (b : BlockKind) (r : Res (State C Γ₁)) (h : Ext Γ Γ₁) :
    (do Frames.run (← r) (.pop b h .nil)) = r.map (State.drop h) := by
  cases r <;> rfl

/-! ## The box -/

section Box

variable {Γ Γ₁ : Ctx}

/-- **`whileInvariantBox` is sound.** -/
theorem Premise.Sound.whileInvBox (k : Nat) (I c : Val C Γ .bool) (dec : Option (Val C Γ .uint))
    (body : Prog C Γ Γ₁) {xs : List ((t : LTy) × Idx Γ t)} {hv : Bool}
    (hf : body.frame = some (xs, hv)) (σ : State C Γ) :
    Premise.Sound .box (.loop (.inv I dec) c body)
      (.inv (.isBoolD I.lower true) xs hv (Upd.nil.decl (fse k) (.val (p := .bool) c.lower))
        (.isBoolD (.pvV (p := .bool) .here) true) (.isBoolD (.pvV (p := .bool) .here) false)
        .refl (.push .refl) body (.isBoolD I.lower true)) σ := by
  intro _ _ ω κ φ hp
  obtain ⟨hI0, hA⟩ := hp
  obtain ⟨hwμ, hxs⟩ := Prog.frame_some hf
  show Modality.afterRunC .box _ _
  rw [run_cons_frames]
  show Modality.afterRunC .box (holds · φ)
    (do let τ ← Loop.run (fun τ => (Prog.run τ body).map (State.drop body.ext))
          (fun τ => c.eval τ) σ
        Frames.run (← Prog.run τ ω) κ)
  refine Loop.run_induct
    (P := fun τ => GFrame (frameMut hv) σ τ ∧ LocAgree 0 (Prog.writesAt 0 body) σ.env τ.env ∧
      holds τ (Fml.isBoolD I.lower true))
    (Q := fun r => Modality.afterRunC .box (holds · φ)
      (do let τ ← r; Frames.run (← Prog.run τ ω) κ))
    ⟨GFrame.refl σ, LocAgree.refl _, hI0⟩ (fun τ hτ => ?_) ⟨trivial, nofun⟩
  obtain ⟨hg, ha, hI⟩ := hτ
  have hX := holds_anonHavoc hxs hg ha hA hI
  unfold Loop.step
  dsimp only
  cases hc : c.eval τ with
  | error e =>
    dsimp only
    exact ⟨trivial, fun h => Val.eval_noPanic τ c (hc.trans (by cases h; rfl))⟩
  | ok v =>
    have hU : (Upd.nil.decl (fse k) (.val (p := .bool) c.lower)).apply τ = .ok (τ.push v) := by
      show (do let τ₀ ← pure τ; pure (τ₀.push (t := .val .bool) (← c.lower.eval τ))) = _
      rw [Val.eval_lower, hc]; rfl
    change Modality.afterC .box _ _ at hX
    rw [hU] at hX
    obtain ⟨hT, hF⟩ := hX
    rcases v with n | (_ | _)
    · dsimp only; exact ⟨trivial, nofun⟩
    · dsimp only
      exact (holds_modalK .box ω κ φ τ).1 (hF ((holds_isBoolD _ _ _).2 rfl))
    · dsimp only
      have h' := (holds_modalK .box body (.pop .block body.ext .nil) _ τ).1
        (hT ((holds_isBoolD _ _ _).2 rfl))
      rw [frames_pop_nil] at h'
      cases hb : (Prog.run τ body).map (State.drop body.ext) with
      | error e =>
        dsimp only
        rw [hb] at h'
        exact ⟨trivial, fun hh => h'.2 (by cases hh; rfl)⟩
      | ok τ' =>
        dsimp only
        rw [hb] at h'
        obtain ⟨τ₀, hb', rfl⟩ := map_ok_inv' hb
        obtain ⟨hg', ha'⟩ := Prog.run_frame body hwμ 0 hb'
        exact ⟨hg.trans (hg'.withEnv _), ha.trans ha', h'.1⟩

end Box

/-! ## The diamond -/

namespace Loop

variable {α : Type} {body : α → Res α} {c : α → Res Value}

/-- **A loop with a variant ends**: from every head in `H` the variant `D`
is defined, the condition is `true` or `false`, the loop ends well (`G`)
where it is false, and where it is true the body runs to a head in `H`
where, if the condition holds again, the variant is a smaller `uint`
(`Calculus/SoundLoop.lean`'s, on any state). -/
theorem run_variant {H G : α → Prop} {D : α → Res Value}
    (hstep : ∀ τ, H τ → ∃ d, D τ = .ok d ∧
      (c τ = .ok (.bool true) ∨ c τ = .ok (.bool false)) ∧
      (c τ = .ok (.bool false) → G τ) ∧
      (c τ = .ok (.bool true) → ∃ τ₁, body τ = .ok τ₁ ∧ H τ₁ ∧
        (c τ₁ = .ok (.bool true) → ∃ a b : Int, D τ₁ = .ok (.int a) ∧ d = .int b ∧ 0 ≤ a ∧ a < b)))
    {σ : α} (h0 : H σ) : ∃ τ, Loop.run body c σ = .ok τ ∧ G τ := by
  have exit : ∀ τ, c τ = .ok (.bool false) → Loop.run body c τ = .ok τ := fun τ hc => by
    rw [Loop.run_unfold]; simp only [Loop.step, hc]
  have next : ∀ τ τ₁, c τ = .ok (.bool true) → body τ = .ok τ₁ →
      Loop.run body c τ = Loop.run body c τ₁ := fun τ τ₁ hc hb => by
    rw [Loop.run_unfold (σ := τ)]; simp only [Loop.step, hc, hb]
  have T : ∀ n : Nat, ∀ τ, H τ →
      (c τ = .ok (.bool true) → ∃ a : Int, D τ = .ok (.int a) ∧ 0 ≤ a ∧ a < n) →
      ∃ τf, Loop.run body c τ = .ok τf ∧ G τf := by
    intro n
    induction n with
    | zero =>
      intro τ hH hb
      obtain ⟨_, _, hcov, hex, _⟩ := hstep τ hH
      rcases hcov with hc | hc
      · obtain ⟨a, _, h₁, h₂⟩ := hb hc
        omega
      · exact ⟨τ, exit τ hc, hex hc⟩
    | succ n ih =>
      intro τ hH hb
      obtain ⟨d, hd, hcov, hex, hbody⟩ := hstep τ hH
      rcases hcov with hc | hc
      · obtain ⟨a, hda, h₁, h₂⟩ := hb hc
        obtain ⟨τ₁, hb₁, hH₁, hdec⟩ := hbody hc
        rw [next τ τ₁ hc hb₁]
        refine ih τ₁ hH₁ fun hc₁ => ?_
        obtain ⟨a₁, b, hd₁, rfl, h₃, h₄⟩ := hdec hc₁
        rw [hda] at hd
        cases hd
        exact ⟨a₁, hd₁, h₃, by omega⟩
      · exact ⟨τ, exit τ hc, hex hc⟩
  obtain ⟨d, _, hcov, hex, hbody⟩ := hstep σ h0
  rcases hcov with hc | hc
  · obtain ⟨τ₁, hb₁, hH₁, hdec⟩ := hbody hc
    rw [next σ τ₁ hc hb₁]
    refine T (match d with | .int b => b.toNat | .bool _ => 0) τ₁ hH₁ fun hc₁ => ?_
    obtain ⟨a₁, b, hd₁, rfl, h₃, h₄⟩ := hdec hc₁
    exact ⟨a₁, hd₁, h₃, by simp only; omega⟩
  · exact ⟨σ, exit σ hc, hex hc⟩

end Loop

/-- `a < b`, `a <= b` between `uint`s true: both sides are numbers, so
ordered (`Calculus/SoundLoop.lean`'s `Term.cmp_true`, on values). -/
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

section Diamond

variable {Γ Γ₁ : Ctx}

/-- **`whileInvariantDiamond` is sound**: the cover (`Fml.invCases`) says the
condition reads as a `bool` at every head. -/
theorem Premise.Sound.whileInvDiamond (k : Nat) (I c : Val C Γ .bool) (d : Val C Γ .uint)
    (body : Prog C Γ Γ₁) {xs : List ((t : LTy) × Idx Γ t)} {hv : Bool}
    (hf : body.frame = some (xs, hv)) (σ : State C Γ) {p : Premise C Γ Γ}
    (hp : loopStep k .diamond (.inv I (some d)) c body = some p) :
    Premise.Sound .diamond (.loop (.inv I (some d)) c body) p σ := by
  unfold loopStep at hp
  rw [hf] at hp
  dsimp only at hp
  cases hp
  intro _ _ ω κ φ hp
  obtain ⟨hI0, hA⟩ := hp
  obtain ⟨hwμ, hxs⟩ := Prog.frame_some hf
  have key := Loop.run_variant (body := fun τ => (Prog.run τ body).map (State.drop body.ext))
    (c := fun τ => c.eval τ)
    (H := fun τ => GFrame (frameMut hv) σ τ ∧ LocAgree 0 (Prog.writesAt 0 body) σ.env τ.env ∧
      holds τ (Fml.isBoolD I.lower true))
    (G := fun τ => holds τ (Fml.modalK .diamond ω κ φ)) (D := fun τ => d.eval τ) ?_
    ⟨GFrame.refl σ, LocAgree.refl _, hI0⟩
  · obtain ⟨τf, hrun, hG⟩ := key
    show Modality.afterRunC .diamond _ _
    rw [run_cons_frames]
    show Modality.afterRunC .diamond (holds · φ)
      (do let τ ← Loop.run (fun τ => (Prog.run τ body).map (State.drop body.ext))
            (fun τ => c.eval τ) σ
          Frames.run (← Prog.run τ ω) κ)
    rw [hrun]
    exact (holds_modalK .diamond ω κ φ τf).1 hG
  intro τ ⟨hg, ha, hI⟩
  have hX := holds_anonHavoc hxs hg ha hA hI
  change Modality.afterC .diamond _ (Upd.apply τ _) at hX
  have hU : ((Upd.nil.decl (fie k) (Rhs.val (p := .uint) d.lower)).decl (fse k)
      (Rhs.val (p := .bool) c.lower)).apply τ =
      (d.eval τ >>= fun dv => c.eval τ >>= fun cv =>
        pure ((τ.push (t := .val .uint) dv).push (t := .val .bool) cv)) := by
    show (do
      let τ₁ ← (do let τ₀ ← pure τ; pure (τ₀.push (t := .val .uint) (← d.lower.eval τ)))
      pure (τ₁.push (t := .val .bool) (← c.lower.eval τ))) = _
    rw [Val.eval_lower, Val.eval_lower]
    cases d.eval τ <;> cases c.eval τ <;> rfl
  rw [hU] at hX
  cases hd : d.eval τ with
  | error e => rw [hd] at hX; exact False.elim hX
  | ok dv =>
  cases hc : c.eval τ with
  | error e => rw [hd, hc] at hX; exact False.elim hX
  | ok cv =>
  rw [hd, hc] at hX
  obtain ⟨hT, hF, hcov⟩ := hX
  have hcb : ∃ b : Bool, cv = .bool b :=
    Classical.byContradiction fun hn => hcov
      ⟨fun h => hn ⟨true, Except.ok.inj ((holds_isBoolD _ _ _).1 h)⟩,
        fun h => hn ⟨false, Except.ok.inj ((holds_isBoolD _ _ _).1 h)⟩⟩
  obtain ⟨b, rfl⟩ := hcb
  refine ⟨dv, hd, ?_, fun hc' => ?_, fun hc' => ?_⟩
  · cases b
    · exact .inr hc
    · exact .inl hc
  · have hb : b = false := by
      have := hc.symm.trans hc'
      cases this; rfl
    subst hb
    exact hF ((holds_isBoolD _ _ _).2 rfl)
  · have hb : b = true := by
      have := hc.symm.trans hc'
      cases this; rfl
    subst hb
    have h := (holds_modalK .diamond _ _ _ (τ.push (t := .val .uint) dv)).1
      (hT ((holds_isBoolD _ _ _).2 rfl))
    rw [frames_pop_nil] at h
    let e₁ : Env C (.val .uint :: Γ) := (dv, τ.env)
    have hw := WkRel.eq_lifted (WkRel.drop (Prog.wk_over body up) (Prog.run_wk body up e₁ τ))
    rw [show τ.push (t := .val .uint) dv = τ.lift up e₁ from rfl, hw] at h
    cases hb : (Prog.run τ body).map (State.drop body.ext) with
    | error e => rw [hb] at h; exact False.elim h.1
    | ok τ₁ =>
      rw [hb] at h
      obtain ⟨hI₁, hdec⟩ := h.1
      obtain ⟨τ₀, hb', rfl⟩ := map_ok_inv' hb
      obtain ⟨hg', ha'⟩ := Prog.run_frame body hwμ 0 hb'
      change holds ((State.drop body.ext τ₀).push (t := .val .uint) dv) _ at hI₁ hdec
      refine ⟨_, hb, ⟨hg.trans (hg'.withEnv _), ha.trans ha', ?_⟩, fun hc₁ => ?_⟩
      · rw [holds_isBoolD_lower, Val.eval_up] at hI₁
        exact (holds_isBoolD_lower _ _ _).2 hI₁
      · change c.eval (State.drop body.ext τ₀) = _ at hc₁
        change Modality.afterC .diamond _ (Upd.apply _ _) at hdec
        have hU₁ : (Upd.nil.decl (fse k) (Rhs.val (p := .bool) c.up.lower)).apply
            ((State.drop body.ext τ₀).push (t := .val .uint) dv) =
            .ok (((State.drop body.ext τ₀).push (t := .val .uint) dv).push (t := .val .bool)
              (.bool true)) := by
          show (do
            let υ ← pure ((State.drop body.ext τ₀).push (t := .val .uint) dv)
            pure (υ.push (t := .val .bool)
              (← c.up.lower.eval ((State.drop body.ext τ₀).push (t := .val .uint) dv)))) = _
          rw [Val.eval_lower, Val.eval_up, hc₁]; rfl
        rw [hU₁] at hdec
        obtain ⟨hle, hlt⟩ := hdec ((holds_isBoolD _ _ _).2 rfl)
        rw [holds_isBoolD] at hle hlt
        change evalBinop .le .uint (.int 0) (d.up.up.lower.eval _) = _ at hle
        rw [Val.eval_lower, Val.eval_up, Val.eval_up] at hle
        obtain ⟨x, y, hx, hy, -, hle'⟩ := evalBinop_cmp_true (.inr rfl) hle
        cases hx
        change (d.up.up.lower.eval _ >>= fun a => evalBinop .lt .uint a (pure dv)) = _ at hlt
        rw [Val.eval_lower, Val.eval_up, Val.eval_up, hy] at hlt
        change evalBinop .lt .uint (.int y) (pure dv) = _ at hlt
        obtain ⟨x', z, hx', hz, hlt', -⟩ := evalBinop_cmp_true (.inl rfl) hlt
        cases hx'
        cases hz
        exact ⟨_, _, hy, rfl, hle' rfl, hlt' rfl⟩

end Diamond

/-! ## The rule of a loop -/

/-- **The rule of a loop is sound**: unwound, ended, by its invariant, or
closed to `false`. -/
theorem Stmt.stepSound_loop (k : Nat) (m : Modality) {Γ Γ₁ : Ctx} (a : LoopAnn C Γ)
    (c : Val C Γ .bool) (body : Prog C Γ Γ₁) :
    Stmt.StepSound k m (.loop a c body) := by
  intro σ _ p hp
  change loopStep k m a c body = some p at hp
  cases a with
  | unwind n =>
    cases n with
    | zero =>
      unfold loopStep at hp
      cases hp
      exact Premise.Sound.loopExit c body σ
    | succ n =>
      unfold loopStep at hp
      cases hp
      exact Premise.Sound.whileUnwind n c body σ
  | inv I dec =>
    cases hf : body.frame with
    | none =>
      unfold loopStep at hp
      rw [hf] at hp
      cases hp
      exact Premise.Sound.fail _ σ
    | some f =>
      obtain ⟨xs, hv⟩ := f
      cases m with
      | box =>
        unfold loopStep at hp
        rw [hf] at hp
        dsimp only at hp
        cases hp
        exact Premise.Sound.whileInvBox k I c dec body hf σ
      | diamond =>
        cases dec with
        | none =>
          unfold loopStep at hp
          rw [hf] at hp
          dsimp only at hp
          cases hp
          exact Premise.Sound.fail _ σ
        | some d => exact Premise.Sound.whileInvDiamond k I c d body hf σ hp

end Solidity.Core
