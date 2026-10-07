import Solidity.Calculus.SoundKit
import Solidity.Theory.Bridge.Denote

/-!
# The loop invariant rules are sound

`whileInvariantBox` and `whileInvariantDiamond` (`docs/loops.md`, Decision 4)
against `Loop.run`.  Every loop head is a state the body's frame allows from
the first (`Prog.loopFrame_run`, `Mutability.Frame.trans`), so the premise
read under `{anon(body)}` holds there (`Fml.loopAnon_holds`); the invariant
holds at every head by induction on the iterations (`Loop.run_induct`).
Under the box that is the proof: a body that halts does not panic (the
body's goal is a box), and the loop that ends ends where the condition is
false, where the rest's goal holds.  Under the diamond the variant, a
`uint` below its value at the head wherever the condition holds again,
bounds the iterations left (`loop_inv_diamond_aux`, by induction on that
bound), and the cover says the condition is not stuck.
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-- `cond = TRUE` (`Fml.eqD`) holds where the condition evaluates to `b`. -/
theorem holds_cond_iff {v : Val C .bool} {b : Bool} {τ : State} :
    holds τ (Fml.eqD v.lower (Term.lit (.bool b))) ↔ v.eval τ = .ok (.bool b) := by
  rw [holds_eqD_iff, Val.lower_eval]
  simp only [tm_eval, pure, Except.pure, Except.ok.injEq]
  exact ⟨fun ⟨_, h, e⟩ => e ▸ h, fun h => ⟨_, h, rfl⟩⟩

/-- `a < b`, `a <= b` between `uint`s (as a taclet writes them) true: both
sides are numbers, so ordered. -/
theorem Term.cmp_true {op : BinOp} (hop : op = .lt ∨ op = .le) {a b : Term C} {σ : State}
    (h : (Term.binop op .uint a b).eval σ = .ok (.bool true)) :
    ∃ x y : Int, a.eval σ = .ok (.int x) ∧ b.eval σ = .ok (.int y) ∧
      (op = .lt → x < y) ∧ (op = .le → x ≤ y) := by
  simp only [tm_eval] at h
  cases ha : Tm.eval σ a with
  | error e => simp only [bind, Except.bind, ha, reduceCtorEq] at h
  | ok va =>
    cases hb : Tm.eval σ b with
    | error e =>
      rw [ha, hb] at h
      rcases hop with rfl | rfl <;> simp only [bind, Except.bind, evalBinop, reduceCtorEq] at h
    | ok vb =>
      rw [ha, hb] at h
      rcases hop with rfl | rfl <;> cases va <;> cases vb <;> simp only [bind, Except.bind,
        evalBinop, applyBinOp, Value.asInt, checkArith, Except.ok.injEq, PrimVal.bool.injEq,
        decide_eq_true_eq, PrimVal.int.injEq, forall_const, reduceCtorEq, false_implies, and_true,
        true_and, exists_and_left, exists_eq_left'] at h ⊢
      all_goals exact h

/-- A loop head in the frame of the first, where the invariant holds. -/
def LoopHead (hv : Bool) (xs : List Var) (I : Fml C) (σ τ : State) : Prop :=
  (Mutability.ofHavoc hv).Frame xs σ τ ∧ holds τ I

/-! ## The box -/

/-- `b = TRUE` of a local bound to a value: the value is `TRUE`. -/
theorem holds_setEnv_pv {τ : State} {b : Var} {v w : Value} :
    holds (τ.setEnv b (.val v)) (Fml.eqD (Term.pv b) (Term.lit w) : Fml C) ↔ v = w := by
  rw [holds_eqD_iff]
  simp only [tm_eval, SemanticsProperties.State.getEnv_setEnv_self, bind, Except.bind, pure,
    Except.pure, Except.ok.injEq]
  exact ⟨fun ⟨_, h, e⟩ => h.trans e.symm, fun h => ⟨_, h, rfl⟩⟩

/-- The parts of a loop with an invariant avoid what its parts' vars avoid. -/
theorem Stmt.loop_inv_avoids {inv cond : Val C .bool} {dec : Option (Val C .uint)} {body : Prog C}
    {ns : List Var} (hs : Avoids (Stmt.loop (.inv inv dec) cond body).vars ns) :
    Avoids inv.vars ns ∧ Avoids (optVars Val.vars dec) ns ∧ Avoids cond.vars ns ∧
      Avoids (Prog.vars body) ns :=
  ⟨fun x hx => hs x (by simp only [Stmt.vars, LoopAnn.vars, List.mem_append]; exact .inl (.inl (.inl hx))),
    fun x hx => hs x (by simp only [Stmt.vars, LoopAnn.vars, List.mem_append]; exact .inl (.inl (.inr hx))),
    fun x hx => hs x (by simp only [Stmt.vars, List.mem_append]; exact .inl (.inr hx)),
    fun x hx => hs x (by simp only [Stmt.vars, List.mem_append]; exact .inr hx)⟩

/-- **`whileInvariantBox` is sound**, its local `b` fresh. -/
theorem Stmt.loop_inv_box {inv cond : Val C .bool} {dec : Option (Val C .uint)} {body : Prog C}
    {xs : List Var} {hv : Bool} (hf : Prog.loopFrame body = some (xs, hv)) {ns : List Var}
    {b : Var} (hb : b ∈ ns) (hs : Avoids (Stmt.loop (.inv inv dec) cond body).vars ns)
    (ω : Prog C) (φ : Fml C) (hω : Avoids (Prog.vars ω ++ φ.vars) ns) (σ : State)
    (h : holds σ (Premise.invFml .box (Fml.eqD inv.lower (Term.lit (.bool true)))
      [.val b cond.lower] (Fml.eqD (Term.pv b) (Term.lit (.bool true)))
      (Fml.eqD (Term.pv b) (Term.lit (.bool false))) body
      (Fml.eqD inv.lower (Term.lit (.bool true))) (.modal .box ω φ))) :
    holds σ (.modal .box (.loop (.inv inv dec) cond body :: ω) φ) := by
  obtain ⟨hI0, hA⟩ := h
  obtain ⟨hvi, -, -, hvb⟩ := Stmt.loop_inv_avoids hs
  let I : Fml C := Fml.eqD inv.lower (Term.lit (.bool true))
  let Q : Res State → Prop := fun r =>
    Modality.box.afterRun (holds · φ) (do Prog.run (← r) ω)
  have hrun : Q (Loop.run (fun τ => Prog.run τ body) (fun τ => cond.eval τ) σ) := by
    refine Loop.run_induct (P := LoopHead hv xs I σ) ⟨Mutability.Frame.refl _ xs σ, hI0⟩ ?_ ?_
    · intro τ ⟨hfr, hI⟩
      have hτ := Fml.loopAnon_holds hf hfr hA hI
      simp only [Fml.updIf] at hτ
      change Modality.box.after (fun τ' => holds τ' _) (Upd.apply [.val b cond.lower] τ) at hτ
      simp only [Upd.apply, List.foldlM, UpdElem.write, Val.lower_eval, bind, Except.bind] at hτ
      simp only [Loop.step]
      cases hc : cond.eval τ with
      | error e =>
        exact ⟨trivial, fun he => Val.eval_noPanic τ cond (hc.trans (by cases he; rfl))⟩
      | ok cv =>
        rw [hc] at hτ
        simp only [pure, Except.pure, Modality.after] at hτ
        obtain ⟨hB, hu, -⟩ := hτ
        have hag : EnvAgreeExcept ns (τ.setEnv b (.val cv)) τ :=
          (EnvAgreeExcept.refl ns τ).setEnv_left hb _
        rcases cv with n | bv
        · exact ⟨trivial, nofun⟩
        · cases bv with
          | false =>
            have := (holds_frame (.modal .box ω φ) hω hag).1 (hu (holds_setEnv_pv.2 rfl))
            simpa only [Q, bind, Except.bind] using this
          | true =>
            have hB := hB (holds_setEnv_pv.2 rfl)
            change Modality.box.afterRun (fun τ' => holds τ' _) (Prog.run _ body) at hB
            have hRA := Prog.run_frame hag body hvb
            cases hr' : Prog.run (τ.setEnv b (.val (.bool true))) body with
            | error e' =>
              rw [hr'] at hRA hB
              cases hr : Prog.run τ body with
              | error e =>
                rw [hr] at hRA
                have he : e' = e := hRA
                subst he
                exact ⟨trivial, fun h' => hB.2 (by cases h'; rfl)⟩
              | ok _ => rw [hr] at hRA; exact hRA.elim
            | ok τ₁' =>
              rw [hr'] at hRA hB
              cases hr : Prog.run τ body with
              | error _ => rw [hr] at hRA; exact hRA.elim
              | ok τ₁ =>
                rw [hr] at hRA
                have hag₁ : EnvAgreeExcept ns τ₁' τ₁ := hRA
                exact ⟨hfr.trans (Prog.loopFrame_run hf hr),
                  holds_cond_iff.2 ((inv.eval_frame hag₁ hvi).symm.trans (holds_cond_iff.1 hB.1))⟩
    · exact ⟨trivial, nofun⟩
  simpa only [holds, Prog.run, Stmt.run] using hrun

/-! ## The diamond -/

/-- **A loop with a variant ends**: from every head in `H` the variant `D`
is defined, the condition is `true` or `false`, the loop ends well (`G`)
where it is false, and where it is true the body runs to a head in `H`
where, if the condition holds again, the variant is a smaller `uint`.  Then
the loop from a head in `H` ends, in a state of `G`.  The bound is the
variant's value after the first iteration; before it, the variant may be
anything. -/
theorem Loop.run_variant {body : State → Res State} {c : State → Res Value}
    {H G : State → Prop} {D : State → Res Value}
    (hstep : ∀ τ, H τ → ∃ d, D τ = .ok d ∧
      (c τ = .ok (.bool true) ∨ c τ = .ok (.bool false)) ∧
      (c τ = .ok (.bool false) → G τ) ∧
      (c τ = .ok (.bool true) → ∃ τ₁, body τ = .ok τ₁ ∧ H τ₁ ∧
        (c τ₁ = .ok (.bool true) → ∃ a b : Int, D τ₁ = .ok (.int a) ∧ d = .int b ∧ 0 ≤ a ∧ a < b)))
    {σ : State} (h0 : H σ) : ∃ τ, Loop.run body c σ = .ok τ ∧ G τ := by
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

/-- **`whileInvariantDiamond` is sound**, its locals `variant` and `b` fresh. -/
theorem Stmt.loop_inv_diamond {inv cond : Val C .bool} {dec : Val C .uint} {body : Prog C}
    {xs : List Var} {hv : Bool} (hf : Prog.loopFrame body = some (xs, hv)) {ns : List Var}
    {v b : Var} (hvn : v ∈ ns) (hbn : b ∈ ns) (hvb : b ≠ v)
    (hs : Avoids (Stmt.loop (.inv inv (some dec)) cond body).vars ns) (ω : Prog C) (φ : Fml C)
    (hω : Avoids (Prog.vars ω ++ φ.vars) ns) (σ : State)
    (h : holds σ (Premise.invFml .diamond (Fml.eqD inv.lower (Term.lit (.bool true)))
      [.val v dec.lower, .val b cond.lower] (Fml.eqD (Term.pv b) (Term.lit (.bool true)))
      (Fml.eqD (Term.pv b) (Term.lit (.bool false))) body
      ((Fml.eqD inv.lower (Term.lit (.bool true))).and
        (.upd .diamond [.val b cond.lower] ((Fml.eqD (Term.pv b) (Term.lit (.bool true))).imp
          ((Fml.eqD (Term.binop .le .uint (Term.lit (.int 0)) dec.lower) (Term.lit (.bool true))).and
            (Fml.eqD (Term.binop .lt .uint dec.lower (Term.pv v)) (Term.lit (.bool true)))))))
      (.modal .diamond ω φ))) :
    holds σ (.modal .diamond (.loop (.inv inv (some dec)) cond body :: ω) φ) := by
  obtain ⟨hI0, hA⟩ := h
  obtain ⟨hvi, hvd, hvc, hvbody⟩ := Stmt.loop_inv_avoids hs
  have hvd : Avoids dec.vars ns := by simpa only [optVars] using hvd
  have hwr : v ∉ xs := by
    rw [Prog.loopFrame_writes hf]
    exact fun h => hvbody v (Prog.writes_sub body v h) hvn
  let I : Fml C := Fml.eqD inv.lower (Term.lit (.bool true))
  have key := Loop.run_variant (body := fun τ => Prog.run τ body) (c := fun τ => cond.eval τ)
    (H := LoopHead hv xs I σ) (G := fun τ => holds τ (.modal .diamond ω φ))
    (D := fun τ => dec.eval τ) ?_ ⟨Mutability.Frame.refl _ xs σ, hI0⟩
  · obtain ⟨τf, hrun, hG⟩ := key
    simp only [holds, Prog.run, Stmt.run, hrun, bind, Except.bind]
    exact hG
  intro τ ⟨hfr, hI⟩
  have hτ := Fml.loopAnon_holds hf hfr hA hI
  simp only [Fml.updIf] at hτ
  change Modality.diamond.after (fun τ' => holds τ' _)
    (Upd.apply [.val v dec.lower, .val b cond.lower] τ) at hτ
  simp only [Upd.apply, List.foldlM, UpdElem.write, Val.lower_eval, bind, Except.bind] at hτ
  cases hd : dec.eval τ with
  | error e => rw [hd] at hτ; exact hτ.elim
  | ok d =>
  rw [hd] at hτ
  simp only [pure, Except.pure] at hτ
  cases hc : cond.eval τ with
  | error e => rw [hc] at hτ; exact hτ.elim
  | ok cv =>
  rw [hc] at hτ
  simp only [Modality.after] at hτ
  obtain ⟨hB, hu, hcov⟩ := hτ
  -- the head with the variant's and the condition's values bound
  let τ' := (τ.setEnv v (.val d)).setEnv b (.val cv)
  have hag : EnvAgreeExcept ns τ' τ :=
    ((EnvAgreeExcept.refl ns τ).setEnv_left hvn _).setEnv_left hbn _
  refine ⟨d, hd, ?_, ?_, ?_⟩
  · have hcov' : ¬(¬ holds τ' (Fml.eqD (Term.pv b) (Term.lit (.bool true))) ∧
        ¬ holds τ' (Fml.eqD (Term.pv b) (Term.lit (.bool false)))) :=
      (Premise.coverFml_holds _ _ _ _).1 hcov
    rw [holds_setEnv_pv, holds_setEnv_pv] at hcov'
    by_cases h1 : cv = .bool true
    · exact .inl (hc.trans (congrArg _ h1))
    · exact .inr (hc.trans (congrArg _ (Classical.byContradiction fun h2 => hcov' ⟨h1, h2⟩)))
  · intro hc'
    have hcv : cv = .bool false := Except.ok.inj (hc.symm.trans hc')
    exact (holds_frame (.modal .diamond ω φ) hω hag).1 (hu (holds_setEnv_pv.2 hcv))
  · intro hc'
    have hcv : cv = .bool true := Except.ok.inj (hc.symm.trans hc')
    have hB := hB (holds_setEnv_pv.2 hcv)
    change Modality.diamond.afterRun (fun τ' => holds τ' _) (Prog.run τ' body) at hB
    simp only [Modality.afterRun, Modality.after] at hB
    cases hr' : Prog.run τ' body with
    | error e => rw [hr'] at hB; exact hB.1.elim
    | ok τ₁' =>
    rw [hr'] at hB
    obtain ⟨⟨hI₁, hdec₁⟩, -⟩ := hB
    have hRA := Prog.run_frame hag body hvbody
    rw [hr'] at hRA
    cases hr : Prog.run τ body with
    | error e => rw [hr] at hRA; exact hRA.elim
    | ok τ₁ =>
    rw [hr] at hRA
    have hag₁ : EnvAgreeExcept ns τ₁' τ₁ := hRA
    have ei : inv.eval τ₁' = inv.eval τ₁ := inv.eval_frame hag₁ hvi
    have ec : cond.eval τ₁' = cond.eval τ₁ := cond.eval_frame hag₁ hvc
    refine ⟨τ₁, hr, ⟨hfr.trans (Prog.loopFrame_run hf hr), ?_⟩, fun hc₁ => ?_⟩
    · exact holds_cond_iff.2 (ei ▸ holds_cond_iff.1 hI₁)
    · -- the condition read again after the body: `b := cond`, then the variant's checks
      change Modality.diamond.after (fun ρ => holds ρ _) (Upd.apply [.val b cond.lower] τ₁') at hdec₁
      simp only [Upd.apply, List.foldlM, UpdElem.write, Val.lower_eval, bind, Except.bind, ec,
        hc₁, pure, Except.pure, Modality.after] at hdec₁
      obtain ⟨hle, hlt⟩ := hdec₁ (holds_setEnv_pv.2 rfl)
      obtain ⟨_, hle, hT⟩ := holds_eqD_iff.1 hle
      obtain ⟨_, hlt, hT'⟩ := holds_eqD_iff.1 hlt
      simp only [tm_eval, pure, Except.pure, Except.ok.injEq] at hT hT'
      subst hT hT'
      obtain ⟨z, a, hz, ha, -, hza⟩ := Term.cmp_true (.inr rfl) hle
      obtain ⟨a', c, ha', hb', hab, -⟩ := Term.cmp_true (.inl rfl) hlt
      simp only [tm_eval, pure, Except.pure, Except.ok.injEq, PrimVal.int.injEq] at hz
      subst hz
      rw [Val.lower_eval] at ha ha'
      rw [ha] at ha'
      cases ha'
      have hag₂ : EnvAgreeExcept ns (τ₁'.setEnv b (.val (.bool true))) τ₁ :=
        hag₁.setEnv_left hbn _
      have ed : dec.eval (τ₁'.setEnv b (.val (.bool true))) = dec.eval τ₁ :=
        dec.eval_frame hag₂ hvd
      -- the variant's local still holds its value: the body does not write it
      have hlook : lookupBy v (τ₁'.setEnv b (.val (.bool true))).env = some (.val d) := by
        simp only [State.setEnv, SemanticsProperties.lookupBy_setBy_ne (Ne.symm hvb)]
        rw [← Mutability.Frame.env_of_not_mem (Prog.loopFrame_run hf hr') hwr]
        simp only [τ', State.setEnv, SemanticsProperties.lookupBy_setBy_ne (Ne.symm hvb),
          SemanticsProperties.lookupBy_setBy_self]
      simp only [tm_eval, State.getEnv, hlook, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at hb'
      exact ⟨a, c, ed.symm.trans ha, hb', hza rfl, hab rfl⟩

end Solidity
