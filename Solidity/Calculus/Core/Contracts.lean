import Solidity.Calculus.Core.Derive

/-!
# A scoped formula proved on its erasure: `sol_erase`

A scoped statement proved through its erasure, by a derived rule over
today's run (the scoped contract rule is `Calculus/Core/FunContract.lean`'s).  A formula with no hidden
binder or anonymising update, whose updates and modalities are boxes and
whose programs bind fresh names (`Fml.Plain`), and which is first-order
where it is negated or assumed (`Fml.negFO`), holds where its erasure does
(`holds_of_erase_plain`), so its erasure's validity proves it
(`Valid.of_erase_plain`).  A box modality runs as its erasure: the typed run
erases to M3's (`Prog.trun_erase`, `Frames.trun_erase`), which runs as the
erased program (`Prog.run_rel`, `Frames.run_erase`); a typed run that
diverges or is exhausted satisfies the box, and one that panics is one the
erasure's run panics in too.  Only that direction holds: the erasure's box
reads every outcome of the untyped run, the typed one fewer.

`sol_erase` turns `⊨ φ` (`Core.Valid`) into today's `⊨` of the erasure,
the parameters' `∀` stripped as a leaf's are (`Derive.stripAlls`),
`Fml.Plain` proved by unfolding it (`simp only`, the names compared by
`decide`), `Fml.negFO` by `decide`.
-/

namespace Solidity.Core

open Solidity (Modality)

variable {C : Contract}

/-- No update, modality or binder but `∀` where the formula is negated or
assumed (`Fml.FO`): what it says there reads as its erasure both ways. -/
def Fml.negFO : {Γ : Ctx} → Fml C Γ → Bool
  | _, φ => Fml.casesOn (motive := fun _ _ => Bool) φ
    (tt := true) (eq := fun _ _ => true) (defined := fun _ => true) (not := fun φ => Fml.FO φ)
    (and := fun φ ψ => Fml.negFO φ && Fml.negFO ψ) (imp := fun φ ψ => Fml.FO φ && Fml.negFO ψ)
    (upd := fun _ _ φ => Fml.negFO φ) (modal := fun _ _ _ φ => Fml.negFO φ)
    (havoc := fun φ => Fml.negFO φ) (all := fun _ _ φ => Fml.negFO φ)
    (bind := fun _ _ _ _ => false) (anon := fun _ _ => false)
  termination_by structural _ φ => φ

/-! ## A plain formula, from its erasure -/

/-- **A plain formula holds where its erasure does**, first-order where it
is negated or assumed, in a typed state whose erasure agrees with the
untyped state on the locals named `ns`. -/
theorem holds_of_erase_plain : {Γ : Ctx} → (φ : Fml C Γ) → {ns : List Var} → φ.Plain ns →
    φ.negFO = true → {σ : TState C Γ} → {τ : Semantics.State} → Agree ns σ.erase τ →
    Solidity.holds τ (φ.erase ns) → holds σ φ
  | _, .tt, _, _, _, _, _, _, _ => trivial
  | _, .eq a b, _, hp, _, _, _, hag, h => (holds_erase_fo (.eq a b) hp rfl hag).2 h
  | _, .defined t, _, hp, _, _, _, hag, h => (holds_erase_fo (.defined t) hp rfl hag).2 h
  | _, .not φ, _, hp, hn, _, _, hag, h => (holds_erase_fo (.not φ) hp hn hag).2 h
  | _, .and φ ψ, _, hp, hn, _, _, hag, h => by
    have hn' : φ.negFO = true ∧ ψ.negFO = true := Bool.and_eq_true_iff.mp hn
    exact ⟨holds_of_erase_plain φ hp.1 hn'.1 hag h.1, holds_of_erase_plain ψ hp.2 hn'.2 hag h.2⟩
  | _, .imp a φ, _, hp, hn, _, _, hag, h => by
    have hn' : a.FO = true ∧ φ.negFO = true := Bool.and_eq_true_iff.mp hn
    exact fun ha => holds_of_erase_plain φ hp.2 hn'.2 hag
      (h ((holds_erase_fo a hp.1 hn'.1 hag).1 ha))
  | _, .upd m U φ, ns, hp, hn, σ, τ, hag, h => by
    obtain ⟨rfl, hU, hφ⟩ := hp
    have hrel := Upd.apply_erase hag U hU
    have H₀ := erase_upd_holds.1 h
    show Modality.afterC .box
      (fun τ' => ∀ σ' : TState C _, σ'.erase = τ' → σ.H <+: σ'.H → holds σ' φ) (U.apply σ.erase)
    revert hrel H₀
    cases U.apply σ.erase with
    | error => intro _ _; trivial
    | ok σ₁ =>
      cases Solidity.Upd.apply (U.erase ns) τ with
      | error => intro hrel; exact hrel.elim
      | ok τ₁ =>
        intro hrel H₀ σ' e _
        subst e
        exact holds_of_erase_plain φ hφ hn hrel H₀
  | _, .modal m P κ φ, ns, hp, hn, σ, τ, hag, h => by
    obtain ⟨rfl, hP, hκ, hφ⟩ := hp
    have h : Modality.box.afterRun (Solidity.holds · (φ.erase (κ.outNames (P.outNames ns))))
        (Solidity.Prog.run τ (P.erase ns ++ κ.erase (P.outNames ns))) := h
    rw [Solidity.SemanticsProperties.Prog.run_append] at h
    exact afterRunTR_box_of (Prog.trunFrames_erase σ P κ)
      (Res.Rel.bind (Prog.run_rel hag P hP) fun _ _ h' => Frames.run_erase κ hκ h')
      (fun a _ hR hq => holds_of_erase_plain φ hφ hn hR hq) h
  | _, .havoc φ, _, hp, hn, σ, τ, hag, h => fun st nt => by
    have e : τ.havoc st.erase nt = withLocals (σ.erase.glob.havoc st.erase nt) τ.env := by
      have hw := hag.wl
      generalize τ.env = env at hw ⊢
      subst hw; rfl
    have hag' := hag.withGlob (σ.erase.glob.havoc st.erase nt)
    rw [← e, ← TState.havoc_erase] at hag'
    exact holds_of_erase_plain φ hp hn hag' (h st.erase nt)
  | _, .all x p φ, _, hp, hn, σ, _, hag, h => fun w =>
    holds_of_erase_plain φ hp.2 hn (σ := σ.push (t := .val p) w)
      (hag.push (t := .val p) hp.1 (PrimTy.erase w)) (h _ (PrimTy.admits_erase w))
  | _, .bind .., _, hp, _, _, _, _, _ | _, .anon .., _, hp, _, _, _, _, _ => hp.elim

/-- **A plain scoped formula is valid where its erasure is.** -/
theorem Valid.of_erase_plain {φ : Fml C []} (hp : φ.Plain []) (hn : φ.negFO = true)
    (h : Solidity.Valid (φ.erase [])) : Valid φ :=
  fun σ => holds_of_erase_plain φ hp hn (Agree.nil σ.erase) (h _)

open Lean Elab Tactic Meta in
/-- `sol_erase`: `⊨ φ` scoped, by today's `⊨` of its erasure
(`Valid.of_erase_plain`), its parameters free. -/
elab "sol_erase" : tactic => withMainContext do
  let g ← getMainGoal
  let some (C, φ) ← Symex.validGoal? g | throwError "sol_erase: expected a goal `⊨ φ`, scoped"
  let rest := (← getUnsolvedGoals).erase g
  let nilCtx := mkApp (mkConst ``List.nil [0]) (mkConst ``LTy)
  let nilVar := mkApp (mkConst ``List.nil [0]) (mkConst ``Var)
  let hpTy := mkAppN (mkConst ``Fml.Plain) #[C, nilCtx, nilVar, φ]
  let hp ← mkFreshExprSyntheticOpaqueMVar hpTy
  let tac ← `(tactic| (simp only [Fml.Plain, Prog.Fresh, Stmt.Fresh, Frames.Fresh, CallRet.names,
      Args.names, Args.erase, Arg.separatedFrom, List.not_mem_nil, not_false_eq_true,
      List.mem_cons, List.mem_append, List.cons_append, List.nil_append, List.nodup_cons,
      List.nodup_nil, Var.user.injEq, Var.fresh.injEq, String.reduceEq, Nat.succ_ne_self,
      reduceCtorEq, or_self, or_false, or_true, and_self, and_true, and_false, true_and, not_or,
      forall_eq_or_imp, forall_eq, implies_true, List.contains_eq_mem, decide_false,
      Bool.not_false, Bool.and_true, Bool.or_eq_true, List.all_eq_true] <;> decide))
  setGoals [hp.mvarId!]
  try Term.withoutErrToSorry (evalTactic tac)
  catch _ => throwError "sol_erase: the formula is not plain (`Fml.Plain`)"
  unless (← getUnsolvedGoals).isEmpty do
    throwError "sol_erase: the formula is not plain (`Fml.Plain`)"
  let hnTy ← mkEq (mkAppN (mkConst ``Fml.negFO) #[C, nilCtx, φ]) (mkConst ``Bool.true)
  let hn ← mkFreshExprSyntheticOpaqueMVar hnTy
  setGoals [hn.mvarId!]
  try Term.withoutErrToSorry (evalTactic (← `(tactic| decide)))
  catch _ => throwError "sol_erase: the formula is not first-order where it is negated or \
    assumed (`Fml.negFO`)"
  let erased := mkAppN (mkConst ``Fml.erase) #[C, nilCtx, nilVar, φ]
  let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Solidity.Valid) C erased) (← g.getTag)
  g.assign (mkAppN (mkConst ``Valid.of_erase_plain) #[C, φ, hp, hn, g'])
  setGoals [g'.mvarId!]
  let g'' ← Derive.stripAlls (← Solidity.normValid g'.mvarId!)
  setGoals (g'' :: rest)

end Solidity.Core
