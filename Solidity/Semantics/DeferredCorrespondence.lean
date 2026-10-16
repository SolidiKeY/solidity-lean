import Solidity.Semantics.DeferredCallback
import Solidity.Semantics.CallbackUnwk

/-!
# Deferred receiver capture preserves callback outcomes

The direct reading calls the getter once, validates its returned alias, then
runs an operand prefix in the caller's context. The validated receiver is held
outside that prefix. Its final source is read after callbacks, before locals
are dropped, and the push retains heap growth and caller writes.

`captureProgram_direct_iff` and `callProgram_direct_iff` prove exact agreement
with the actual typed two-alias capture program, including halts and invariant
violations. The proofs use both directions of general callback weakening, so
there is no payment-free or prefix-fragment premise. Programs stay interpreted.
These are semantic correspondence laws; native effectful receiver syntax,
source import and the callback calculus still require integration.
-/

namespace Solidity.DeferredSource.Callback

open Solidity.CallbackWk

variable {C : Contract} {J : StateInv C} {Γ Δ : Ctx}

/-- Finish an operand using the receiver already validated before its prefix. -/
def finishAt {E : Ty} (e : Operand C Γ E) (ref : SRef C (.ref (.array E)))
    {H : HTy} : COut C H e.tailCtx → COut C H Γ
  | .ok a => .ofRes (do
      let v ← e.value.valueT a.st
      if a.st.storage.full ref then .error .exhausted else
      let st ← TRes.ofOpt (a.st.storage.push ref fun _ => some v.strip)
      pure ⟨(a.st.withStorage st).drop e.code.ext, a.ext⟩)
  | .halt err => .halt err
  | .violated => .violated

/-- Direct execution retains the validated receiver outside the operand's locals. -/
def ExecPushAt {E : Ty} (σ : State C Γ) (e : Operand C Γ E)
    (ref : SRef C (.ref (.array E))) (o : COut C σ.H Γ) : Prop :=
  ∃ u, ExecP J σ e.code u ∧ o = finishAt e ref u

theorem finishAt_wk {E : Ty} {H : HTy} (e : Operand C Γ E)
    (ref : SRef C (.ref (.array E))) (h : Thin Γ Δ)
    {off : List ((t : LTy) × t.TDenote C H)}
    {u : COut C H e.tailCtx} {u' : COut C H (e.code.wk h).1}
    (hr : CWkRel (e.code.wk h).2.1 off u u') :
    CWkRel h off (finishAt e ref u) (finishAt (e.wk h) ref u') := by
  cases u <;> cases u'
  all_goals first | exact False.elim hr | skip
  all_goals try exact hr
  case ok.ok a b =>
    obtain ⟨d, hd, rfl⟩ := hr
    simp only [finishAt, Operand.wk, Src.valueT_wk]
    cases hv : e.value.valueT a.st with
    | error err => rfl
    | ok v =>
      dsimp only [bind, Except.bind]
      dsimp only [State.lift, State.withEnv]
      cases hf : a.st.storage.full ref with
      | true => rfl
      | false =>
        cases hs : a.st.storage.push ref (fun _ => some v.strip) with
        | none => rfl
        | some st =>
          exact CWkRel.drop (Prog.wk_over e.code h)
            (o := .ok ⟨a.st.withStorage st, a.ext⟩)
            (o' := .ok ⟨(a.st.withStorage st).lift (e.code.wk h).2.1 d, a.ext⟩)
            ⟨d, hd, rfl⟩

theorem drop_freshAlias {R : RefTy} {H : HTy} (d : TEnv C H Γ)
    (p : Option (SRef C (.ref R))) {o : COut C H Γ} {o' : COut C H (.alias R :: Γ)}
    (hr : CWkRel (.drop (t := .alias R) .refl)
      (TEnv.off (.drop (t := .alias R) .refl) (p, d)) o o') :
    o'.map (Out.drop (.push .refl)) = o := by
  rw [hr.eq_lifted]
  cases o <;> rfl

theorem finishPush_atAlias {E : Ty} (e : Operand C Γ E) (σ : State C Γ)
    (ref : SRef C (.ref (.array E)))
    {u : COut C σ.H e.tailCtx}
    {u' : COut C σ.H (e.code.wk (.drop (t := .alias (.array E)) .refl)).1}
    (hr : CWkRel (e.code.wk (.drop .refl)).2.1
      (TEnv.off (.drop (t := .alias (.array E)) .refl) (some ref, σ.env)) u u') :
    finishPush (e.wk (.drop .refl)) .here u' =
      (finishAt e ref u).map (fun x => ⟨x.st.push (t := .alias (.array E)) (some ref), x.ext⟩) := by
  have hf := (CWkRel.drop (Prog.wk_over e.code (.drop .refl)) hr).eq_lifted
  cases u <;> cases u'
  all_goals first | exact False.elim hr | skip
  case halt.halt => cases hr; rfl
  case violated.violated => rfl
  case ok.ok a b =>
    obtain ⟨d, hd, rfl⟩ := hr
    have hout : Out.drop (e.code.wk (.drop .refl)).2.2.ext
        (⟨a.st.lift (e.code.wk (.drop .refl)).2.1 d, a.ext⟩ : Out C σ.H _) =
        (⟨(a.st.drop e.code.ext).push (t := .alias (.array E)) (some ref), a.ext⟩ : Out C σ.H _) :=
      COut.ok.inj hf
    have hp : TEnv.get ((.here : Idx (.alias (.array E) :: Γ) (.alias (.array E))).ext
        (e.code.wk (.drop .refl)).2.2.ext) (a.st.lift (e.code.wk (.drop .refl)).2.1 d).env =
        some ref := by
      simpa only [TEnv.get_ext_drop] using
        congrArg (fun x : Out C σ.H (.alias (.array E) :: Γ) => x.st.env.1) hout
    simp only [finishPush, finishAt, Operand.wk, TRun.push, SPath.resolveT, hp,
      Src.valueT_wk, TRes.ofOpt, bind, Except.bind]
    cases hv : e.value.valueT a.st with
    | error err => rfl
    | ok v =>
      dsimp only [pure, Except.pure, State.lift, State.withEnv, Option.getD]
      cases hc : a.st.storage.full ref with
      | true => rfl
      | false =>
        cases hs : a.st.storage.push ref (fun _ => some v.strip) with
        | none => rfl
        | some st =>
          exact congrArg (fun x : Out C σ.H (.alias (.array E) :: Γ) =>
            COut.ok (⟨x.st.withStorage st, x.ext⟩ : Out C σ.H (.alias (.array E) :: Γ))) hout

theorem execPush_atAlias_iff {E : Ty} (e : Operand C Γ E) (σ : State C Γ)
    (ref : SRef C (.ref (.array E))) {o : COut C σ.H Γ} :
    (∃ v, ExecPush (J := J) (σ.push (some ref)) (e.wk (.drop .refl)) .here v ∧
      o = v.map (Out.drop (.push .refl))) ↔ ExecPushAt (J := J) σ e ref o := by
  constructor
  · rintro ⟨v, ⟨u', hu', rfl⟩, rfl⟩
    obtain ⟨u, hu, hr⟩ := Prog.exec_unwk J e.code (.drop (t := .alias (.array E)) .refl)
      σ (some ref, σ.env) hu'
    refine ⟨u, hu, ?_⟩
    rw [finishPush_atAlias e σ ref hr]
    cases finishAt e ref u <;> rfl
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨u', hu', hr⟩ := Prog.exec_wk J e.code (.drop (t := .alias (.array E)) .refl)
      σ (some ref, σ.env) hu
    refine ⟨_, ⟨u', hu', rfl⟩, ?_⟩
    rw [finishPush_atAlias e σ ref hr]
    cases finishAt e ref u <;> rfl

theorem execPushAt_afterAlias_iff {R : RefTy} {E : Ty} (e : Operand C Γ E) (σ : State C Γ)
    (p : Option (SRef C (.ref R))) (ref : SRef C (.ref (.array E))) {o : COut C σ.H Γ} :
    (∃ v, ExecPushAt (J := J) (σ.push (t := .alias R) p) (e.wk (.drop .refl)) ref v ∧
      o = v.map (Out.drop (.push .refl))) ↔ ExecPushAt (J := J) σ e ref o :=
  ⟨fun ⟨_, ⟨_, hu', hv⟩, ho⟩ =>
    let ⟨u, hu, hr⟩ := Prog.exec_unwk J e.code (.drop (t := .alias R) .refl) σ (p, σ.env) hu'
    ⟨u, hu, (ho.trans (congrArg (COut.map (Out.drop (.push .refl))) hv)).trans
      (drop_freshAlias σ.env p (finishAt_wk e ref (.drop .refl) hr))⟩,
   fun ⟨_, hu, ho⟩ =>
    let ⟨u', hu', hr⟩ := Prog.exec_wk J e.code (.drop (t := .alias R) .refl) σ (p, σ.env) hu
    ⟨_, ⟨u', hu', rfl⟩, ho.trans
      (drop_freshAlias σ.env p (finishAt_wk e ref (.drop .refl) hr)).symm⟩⟩

theorem drop_two {H : HTy} {t t' : LTy} (o : COut C H (t :: t' :: Γ)) :
    (o.map (Out.drop (.push .refl))).map (Out.drop (.push .refl)) =
      o.map (Out.drop (.push (.push .refl))) := by
  cases o <;> rfl

theorem execPush_twoAliases_iff {E : Ty} (e : Operand C Γ E) (σ : State C Γ)
    (ref : SRef C (.ref (.array E))) {o : COut C σ.H Γ} :
    (∃ v, ExecPush (J := J)
      ((σ.push (t := .alias (.array E)) (some ref)).push (t := .alias (.array E)) (some ref))
      ((e.wk (.drop (t := .alias (.array E)) .refl)).wk (.drop .refl)) .here v ∧
      o = v.map (Out.drop (.push (.push .refl)))) ↔ ExecPushAt (J := J) σ e ref o := by
  constructor
  · rintro ⟨v, hv, ho⟩
    exact (execPushAt_afterAlias_iff e σ (some ref) ref).mp
      ⟨_, (execPush_atAlias_iff (e.wk (.drop .refl)) (σ.push (some ref)) ref).mp ⟨v, hv, rfl⟩,
        ho.trans (drop_two v).symm⟩
  · exact fun he =>
      let ⟨w, hw, ho⟩ := (execPushAt_afterAlias_iff e σ (some ref) ref).mpr he
      let ⟨v, hv, hwv⟩ := (execPush_atAlias_iff (e.wk (.drop .refl)) (σ.push (some ref)) ref).mpr hw
      ⟨v, hv, (ho.trans (congrArg (COut.map (Out.drop (.push .refl))) hwv)).trans (drop_two v)⟩

/-- Validate the returned alias before running the operand in its caller's context. -/
def DirectAfterGetter {E : Ty} (σ : State C (.alias (.array E) :: Γ))
    (e : Operand C Γ E) (o : COut C σ.H Γ) : Prop :=
  match σ.env.1 with
  | none => o = .halt .revert
  | some ref => ExecPushAt (J := J) (σ.drop (.push .refl)) e ref o

theorem afterGetter_cases {E : Ty} {σ : State C (.alias (.array E) :: Γ)}
    {e : Operand C Γ E} {o : COut C σ.H Γ} (h : ExecAfterGetter J σ e o) :
    (∃ err, TRun.declStorage (.array E) (some (.path (.alias .here))) σ = .error err ∧
      o = .halt err) ∨
    ∃ (a : Out C σ.H (.alias (.array E) :: .alias (.array E) :: Γ))
      (u : COut C a.st.H (.alias (.array E) :: .alias (.array E) :: Γ)),
      TRun.declStorage (.array E) (some (.path (.alias .here))) σ = .ok a ∧
      ExecPush (J := J) a.st ((e.wk (.drop .refl)).wk (.drop .refl)) .here u ∧
      o = u.map (fun x => ⟨x.st.drop (.push (.push .refl)), a.ext.trans x.ext⟩) := by
  cases h with
  | captureHalt hd => exact .inl ⟨_, hd, rfl⟩
  | captureOk hd hp => exact .inr ⟨_, _, hd, hp, rfl⟩

theorem afterGetter_push_capture_iff {E : Ty} (e : Operand C Γ E) (σ : State C Γ)
    (p : Option (SRef C (.ref (.array E)))) {o : COut C σ.H Γ} :
    ExecAfterGetter J (σ.push p) e o ↔ DirectAfterGetter (J := J) (σ.push p) e o := by
  cases p with
  | none =>
    constructor
    · intro h
      rcases afterGetter_cases h with ⟨err, hd, rfl⟩ | ⟨a, u, hd, hp, ho⟩
      · exact congrArg COut.halt (Except.error.inj hd).symm
      · cases hd
    · exact fun ho => ho.symm ▸ ExecAfterGetter.captureHalt rfl
  | some ref =>
    constructor
    · intro h
      rcases afterGetter_cases h with ⟨err, hd, ho⟩ | ⟨a, u, hd, hp, ho⟩
      · cases hd
      · cases Except.ok.inj hd
        exact (execPush_twoAliases_iff e σ ref).mp ⟨u, hp, ho⟩
    · exact fun he =>
        let ⟨u, hu, ho⟩ := (execPush_twoAliases_iff e σ ref).mpr he
        ho.symm ▸ ExecAfterGetter.captureOk
          (a := ⟨(σ.push (some ref)).push (some ref), List.prefix_refl _⟩) rfl hu

theorem afterGetter_capture_iff {E : Ty} (e : Operand C Γ E)
    (σ : State C (.alias (.array E) :: Γ)) {o : COut C σ.H Γ} :
    ExecAfterGetter J σ e o ↔ DirectAfterGetter (J := J) σ e o :=
  afterGetter_push_capture_iff e (σ.drop (.push .refl)) σ.env.1

theorem captureProgram_direct_iff {E : Ty} (e : Operand C Γ E)
    (σ : State C (.alias (.array E) :: Γ)) {o : COut C σ.H Γ} :
    (∃ u, ExecP J σ (captureProgram e) u ∧ o = u.map (Out.drop (.push (.push .refl)))) ↔
      DirectAfterGetter (J := J) σ e o :=
  (captureProgram_iff e).trans (afterGetter_capture_iff e σ)

/-- Direct receiver evaluation: call once, validate its result, then evaluate the operand. -/
inductive DirectCall {ps Γf : Ctx} {E : Ty} (J : StateInv C) (σ : State C Γ)
    (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (e : Operand C Γ E) : COut C σ.H Γ → Prop where
  | next {a : Out C σ.H (.alias (.array E) :: Γ)} {o : COut C a.st.H Γ} :
      ExecS J σ (.call f args (.storage _ r) body) (.ok a) →
      DirectAfterGetter (J := J) a.st e o → DirectCall J σ f args r body e (o.map (Out.cat a))
  | halt {err : THalt} :
      ExecS J σ (.call f args (.storage _ r) body) (.halt err) →
      DirectCall J σ f args r body e (.halt err)
  | violated : ExecS J σ (.call f args (.storage _ r) body) .violated →
      DirectCall J σ f args r body e .violated

theorem call_capture_iff {ps Γf : Ctx} {E : Ty} {σ : State C Γ}
    (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (e : Operand C Γ E) {o : COut C σ.H Γ} :
    ExecCall J σ f args r body e o ↔ DirectCall J σ f args r body e o := by
  constructor
  · intro h
    cases h with
    | next hc hp => exact .next hc ((afterGetter_capture_iff e _).mp hp)
    | halt hc => exact .halt hc
    | violated hc => exact .violated hc
  · intro h
    cases h with
    | next hc hp => exact .next hc ((afterGetter_capture_iff e _).mpr hp)
    | halt hc => exact .halt hc
    | violated hc => exact .violated hc

/-- Every outcome of the explicit getter/capture program is exactly a direct call outcome. -/
theorem callProgram_direct_iff {ps Γf : Ctx} {E : Ty} {σ : State C Γ}
    (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (e : Operand C Γ E) {o : COut C σ.H Γ} :
    (∃ u, ExecP J σ (callProgram f args r body e) u ∧ o = u.map (Out.drop (.push (.push .refl)))) ↔
      DirectCall J σ f args r body e o :=
  (callProgram_iff f args r body e).trans (call_capture_iff f args r body e)

theorem directCall_run {ps Γf : Ctx} {E : Ty} (σ : State C Γ)
    (f : Name) (args : Args C Γ ps) (r : Var)
    (body : Prog C ([.alias (.array E)] ++ ps) Γf) (e : Operand C Γ E) :
    DirectCall J σ f args r body e (.ofRes (runCall args r body e σ)) ∨
      DirectCall J σ f args r body e .violated :=
  (execCall_run σ f args r body e).elim
    (fun h => .inl ((call_capture_iff f args r body e).mp h))
    (fun h => .inr ((call_capture_iff f args r body e).mp h))

end Solidity.DeferredSource.Callback
