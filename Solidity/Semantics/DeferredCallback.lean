import Solidity.Semantics.DeferredSource
import Solidity.Semantics.Callback

/-!
# Callback composition of a deferred push capture

A deferred operand prefix executes through `ExecP`; only alias validation and
its final push are deterministic. The relational composition laws decompose
an actual typed getter, explicit alias capture and scoped prefix-plus-push
program in both directions. Halts and violated invariants stop later stages,
and heap extensions and scope ends are the ordinary interpreter's.

`ExecAfterGetter` retains both hidden aliases, as the explicit capture does.
These are captured-program composition laws. Forward callback weakening is
proved in `Semantics/CallbackWk.lean` and its converse in
`Semantics/CallbackUnwk.lean`; `Semantics/DeferredCorrespondence.lean` applies
both directions to prove exact direct/captured execution agreement. This module
provides the captured-program decomposition and does not enable effectful source syntax.
Its imports place it above the interpreter and scoped syntax.
-/

namespace Solidity.DeferredSource.Callback

variable {C : Contract} {J : StateInv C} {Γ Δ Ε : Ctx}

theorem map_map {H H' H'' : HTy} {Γ' Γ'' : Ctx}
    (o : COut C H Γ) (f : Out C H Γ → Out C H' Γ') (g : Out C H' Γ' → Out C H'' Γ'') :
    (o.map f).map g = o.map (fun x => g (f x)) := by
  cases o <;> rfl

theorem map_cat_refl (σ : State C Γ) (o : COut C σ.H Δ) :
    o.map (Out.cat (⟨σ, List.prefix_refl _⟩ : Out C σ.H Γ)) = o := by
  cases o <;> rfl

theorem map_cat_assoc {H : HTy} {Γ₁ Γ₂ Γ₃ : Ctx}
    (a : Out C H Γ₁) (b : Out C a.st.H Γ₂) (o : COut C b.st.H Γ₃) :
    (o.map (Out.cat b)).map (Out.cat a) = o.map (Out.cat (Out.cat a b)) := by
  cases o <;> rfl

inductive ExecThen (J : StateInv C) {Γ Δ Ε : Ctx} (σ : State C Γ)
    (P : Prog C Γ Δ) (Q : Prog C Δ Ε) : COut C σ.H Ε → Prop where
  | next {a : Out C σ.H Δ} {b : COut C a.st.H Ε} :
      ExecP J σ P (.ok a) → ExecP J a.st Q b → ExecThen J σ P Q (b.map (Out.cat a))
  | halt {e : THalt} : ExecP J σ P (.halt e) → ExecThen J σ P Q (.halt e)
  | violated : ExecP J σ P .violated → ExecThen J σ P Q .violated

theorem join_of_execThen : {Γ Δ Ε : Ctx} → (P : Prog C Γ Δ) → (Q : Prog C Δ Ε) →
    {σ : State C Γ} → {o : COut C σ.H Ε} → ExecThen J σ P Q o → ExecP J σ (P.join Q) o
  | _, _, _, .nil, Q, σ, o, h => by
    cases h with
    | next hp hq => cases hp; simpa only [map_cat_refl] using hq
    | halt hp => cases hp
    | violated hp => cases hp
  | _, _, _, .cons s P, Q, σ, o, h => by
    cases h with
    | @next a b hp hq =>
      generalize he : COut.ok a = out at hp
      cases hp with
      | @cons _ _ _ _ _ _ a₁ b₁ hs hp =>
        cases b₁ with
        | ok a₂ =>
          cases he
          simpa only [map_cat_assoc] using
            (ExecP.cons hs (join_of_execThen P Q (.next hp hq)))
        | halt err => cases he
        | violated => cases he
      | halt hs => cases he
      | violated hs => cases he
    | @halt err hp =>
      generalize he : COut.halt err = out at hp
      cases hp with
      | @cons _ _ _ _ _ _ a₁ b₁ hs hp =>
        cases b₁ with
        | ok a₂ => cases he
        | halt err =>
          cases he
          exact ExecP.cons hs (join_of_execThen P Q (.halt hp))
        | violated => cases he
      | halt hs => cases he; exact .halt hs
      | violated hs => cases he
    | violated hp =>
      generalize he : COut.violated = out at hp
      cases hp with
      | @cons _ _ _ _ _ _ a₁ b₁ hs hp =>
        cases b₁ with
        | ok a₂ => cases he
        | halt err => cases he
        | violated => exact ExecP.cons hs (join_of_execThen P Q (.violated hp))
      | halt hs => cases he
      | violated hs => exact .violated hs

theorem execThen_of_join : {Γ Δ Ε : Ctx} → (P : Prog C Γ Δ) → (Q : Prog C Δ Ε) →
    {σ : State C Γ} → {o : COut C σ.H Ε} → ExecP J σ (P.join Q) o → ExecThen J σ P Q o
  | _, _, _, .nil, Q, σ, o, h => by
    simpa only [map_cat_refl] using (ExecThen.next (P := .nil) ExecP.nil h)
  | _, _, _, .cons s P, Q, σ, o, h => by
    cases h with
    | cons hs hp =>
      cases execThen_of_join P Q hp with
      | next hpre hpost =>
        simpa only [map_cat_assoc] using (ExecThen.next (ExecP.cons hs hpre) hpost)
      | halt hpre => exact .halt (.cons hs hpre)
      | violated hpre => exact .violated (.cons hs hpre)
    | halt hs => exact .halt (.halt hs)
    | violated hs => exact .violated (.violated hs)

theorem execP_noTransfer (P : Prog C Γ Δ) (σ : State C Γ) (ht : P.callsBack J.pay = false) :
    ExecP J σ P (.ofRes (P.run σ)) := by
  rcases Prog.exec_run J P σ with h | h
  · exact h
  · have he := h.eq_run ht
    cases hr : P.run σ <;> simp only [hr, COut.ofRes, reduceCtorEq] at he

theorem block_of_execP {σ : State C Γ} {P : Prog C Γ Δ} {o : COut C σ.H Δ}
    (h : ExecP J σ P o) : ExecS J σ (.block P) (o.map (Out.drop P.ext)) := by
  cases ht : P.callsBack J.pay with
  | false =>
    rw [h.eq_run ht, COut.map_ofRes]
    exact .det ht
  | true => exact .block ht h

theorem block_iff {σ : State C Γ} {P : Prog C Γ Δ} {o : COut C σ.H Γ} :
    ExecS J σ (.block P) o ↔ ∃ u, ExecP J σ P u ∧ o = u.map (Out.drop P.ext) := by
  constructor
  · intro h
    cases h with
    | det ht =>
      exact ⟨.ofRes (P.run σ), execP_noTransfer P σ ht, (COut.map_ofRes _ _).symm⟩
    | block ht hp => exact ⟨_, hp, rfl⟩
  · rintro ⟨u, h, rfl⟩
    exact block_of_execP h

theorem singleton_iff {Γ' : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ'} {o : COut C σ.H Γ'} :
    ExecP J σ (.cons s .nil) o ↔ ExecS J σ s o := by
  constructor
  · intro h
    cases h with
    | cons hs hp => cases hp; exact hs
    | halt hs => exact hs
    | violated hs => exact hs
  · intro h
    cases o with
    | ok a => exact .cons h .nil
    | halt err => exact .halt h
    | violated => exact .violated h

open Solidity.DeferredSource

/-- Complete a deferred push after one callback outcome of its prefix. -/
def finishPush {E : Ty} (e : Operand C Γ E) (i : Idx Γ (.alias (.array E)))
    {H : HTy} : COut C H e.tailCtx → COut C H Γ
  | .ok a => (COut.ofRes (TRun.push (.alias (i.ext e.code.ext)) (some e.value) a.st)).map
      (fun x => ⟨x.st.drop e.code.ext, a.ext.trans x.ext⟩)
  | .halt err => .halt err
  | .violated => .violated

/-- The prefix uses the callback relation, rather than the deterministic interpreter. -/
def ExecPush {E : Ty} (σ : State C Γ) (e : Operand C Γ E)
    (i : Idx Γ (.alias (.array E))) (o : COut C σ.H Γ) : Prop :=
  ∃ u, ExecP J σ e.code u ∧ o = finishPush e i u

theorem pushBlock_of_prefix {E : Ty} {σ : State C Γ} (e : Operand C Γ E)
    (i : Idx Γ (.alias (.array E))) {u : COut C σ.H e.tailCtx} (h : ExecP J σ e.code u) :
    ExecS J σ (pushBlock e i) (finishPush e i u) := by
  cases u with
  | ok a =>
    have ht : ExecP J a.st (.cons (.push (.alias (i.ext e.code.ext)) (some e.value) rfl) .nil)
        (.ofRes (TRun.push (.alias (i.ext e.code.ext)) (some e.value) a.st)) :=
      singleton_iff.mpr (.det rfl)
    simpa only [pushBlock, finishPush, map_map, join_ext] using
      (block_of_execP (join_of_execThen e.code _ (.next h ht)))
  | halt err => exact block_of_execP (join_of_execThen e.code _ (.halt h))
  | violated => exact block_of_execP (join_of_execThen e.code _ (.violated h))

theorem pushBlock_iff {E : Ty} {σ : State C Γ} (e : Operand C Γ E)
    (i : Idx Γ (.alias (.array E))) {o : COut C σ.H Γ} :
    ExecS J σ (pushBlock e i) o ↔ ExecPush (J := J) σ e i o := by
  constructor
  · intro h
    obtain ⟨u, hu, rfl⟩ := block_iff.mp h
    cases execThen_of_join e.code _ hu with
    | next hp hq =>
      rw [(singleton_iff.mp hq).eq_run rfl]
      exact ⟨_, hp, by simp only [finishPush, map_map, join_ext, Stmt.run]; rfl⟩
    | halt hp => exact ⟨_, hp, rfl⟩
    | violated hp => exact ⟨_, hp, rfl⟩
  · rintro ⟨u, h, rfl⟩
    exact pushBlock_of_prefix e i h

theorem ofRes_eq_ok {H : HTy} {r : TRes (Out C H Γ)} {a : Out C H Γ} :
    COut.ofRes r = .ok a ↔ r = .ok a := by
  cases r <;> simp only [COut.ofRes, reduceCtorEq, COut.ok.injEq, Except.ok.injEq]

theorem ofRes_eq_halt {H : HTy} {r : TRes (Out C H Γ)} {err : THalt} :
    COut.ofRes r = .halt err ↔ r = .error err := by
  cases r <;> simp only [COut.ofRes, reduceCtorEq, COut.halt.injEq, Except.error.injEq]

/-- Capture the validated receiver, then execute the operand prefix with callbacks. -/
inductive ExecAfterGetter {E : Ty} (J : StateInv C) (σ : State C (.alias (.array E) :: Γ))
    (e : Operand C Γ E) : COut C σ.H Γ → Prop where
  | captureHalt {err : THalt} :
      TRun.declStorage (.array E) (some (.path (.alias .here))) σ = .error err →
      ExecAfterGetter J σ e (.halt err)
  | captureOk {a : Out C σ.H (.alias (.array E) :: .alias (.array E) :: Γ)}
      {u : COut C a.st.H (.alias (.array E) :: .alias (.array E) :: Γ)} :
      TRun.declStorage (.array E) (some (.path (.alias .here))) σ = .ok a →
      ExecPush (J := J) a.st ((e.wk (.drop .refl)).wk (.drop .refl)) .here u →
      ExecAfterGetter J σ e
        (u.map (fun x => ⟨x.st.drop (.push (.push .refl)), a.ext.trans x.ext⟩))

theorem captureProgram_iff {E : Ty} {σ : State C (.alias (.array E) :: Γ)}
    (e : Operand C Γ E) {o : COut C σ.H Γ} :
    (∃ u, ExecP J σ (captureProgram e) u ∧ o = u.map (Out.drop (.push (.push .refl)))) ↔
      ExecAfterGetter J σ e o := by
  constructor
  · rintro ⟨u, h, rfl⟩
    cases h with
    | cons hd hp =>
      simpa only [map_map] using (ExecAfterGetter.captureOk
        (ofRes_eq_ok.mp (hd.eq_run rfl).symm)
        ((pushBlock_iff _ _).mp (singleton_iff.mp hp)))
    | halt hd => exact .captureHalt (ofRes_eq_halt.mp (hd.eq_run rfl).symm)
    | violated hd =>
      have he := hd.eq_run rfl
      cases hr : TRun.declStorage (.array E) (some (.path (.alias .here))) σ <;>
        simp only [Stmt.run, Stmt.runR, hr, COut.ofRes, reduceCtorEq] at he
  · intro h
    cases h with
    | @captureHalt err hd =>
      have hs : ExecS J σ (.declStorage (.array E) (.user "sp") (some (.path (.alias .here))))
          (.halt err) := by
        change ExecS J σ _ (.ofRes (.error err))
        rw [← hd]
        exact .det rfl
      exact ⟨_, .halt hs, rfl⟩
    | @captureOk a u hd hp =>
      have hs : ExecS J σ (.declStorage (.array E) (.user "sp") (some (.path (.alias .here))))
          (.ok a) := by
        change ExecS J σ _ (.ofRes (.ok a))
        rw [← hd]
        exact .det rfl
      refine ⟨_, .cons hs (singleton_iff.mpr ((pushBlock_iff _ _).mpr hp)), ?_⟩
      simp only [map_map]
      rfl

/-- A getter callback outcome followed by receiver validation and a deferred push. -/
inductive ExecCall {ps Γf : Ctx} {E : Ty} (J : StateInv C) (σ : State C Γ)
    (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (e : Operand C Γ E) : COut C σ.H Γ → Prop where
  | next {a : Out C σ.H (.alias (.array E) :: Γ)} {o : COut C a.st.H Γ} :
      ExecS J σ (.call f args (.storage _ r) body) (.ok a) →
      ExecAfterGetter J a.st e o → ExecCall J σ f args r body e (o.map (Out.cat a))
  | halt {err : THalt} :
      ExecS J σ (.call f args (.storage _ r) body) (.halt err) →
      ExecCall J σ f args r body e (.halt err)
  | violated : ExecS J σ (.call f args (.storage _ r) body) .violated →
      ExecCall J σ f args r body e .violated

/-- Exact callback agreement with the actual getter, capture and prefix-plus-push program. -/
theorem callProgram_iff {ps Γf : Ctx} {E : Ty} {σ : State C Γ}
    (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (e : Operand C Γ E) {o : COut C σ.H Γ} :
    (∃ u, ExecP J σ (callProgram f args r body e) u ∧ o = u.map (Out.drop (.push (.push .refl)))) ↔
      ExecCall J σ f args r body e o := by
  constructor
  · rintro ⟨u, h, rfl⟩
    cases h with
    | cons hc hp =>
      simpa only [map_map] using
        (ExecCall.next hc ((captureProgram_iff e).mp ⟨_, hp, rfl⟩))
    | halt hc => exact .halt hc
    | violated hc => exact .violated hc
  · intro h
    cases h with
    | next hc hp =>
      obtain ⟨u, hu, rfl⟩ := (captureProgram_iff e).mpr hp
      refine ⟨_, .cons hc hu, ?_⟩
      simp only [map_map]
      rfl
    | halt hc => exact ⟨_, .halt hc, rfl⟩
    | violated hc => exact ⟨_, .violated hc, rfl⟩

/-- The ordinary deferred run is admitted, unless an exit breaks the invariant. -/
theorem execCall_run {ps Γf : Ctx} {E : Ty} (σ : State C Γ)
    (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (e : Operand C Γ E) :
    ExecCall J σ f args r body e (.ofRes (runCall args r body e σ)) ∨
      ExecCall J σ f args r body e .violated := by
  rcases Prog.exec_run J (callProgram f args r body e) σ with h | h
  · left
    apply (callProgram_iff f args r body e).mp
    refine ⟨_, h, ?_⟩
    rw [COut.map_ofRes, callProgram_sound]
  · exact .inr ((callProgram_iff f args r body e).mp ⟨.violated, h, rfl⟩)

end Solidity.DeferredSource.Callback
