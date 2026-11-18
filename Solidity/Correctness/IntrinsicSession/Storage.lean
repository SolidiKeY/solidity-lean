import Solidity.Goals.IntrinsicStorage
import Solidity.Correctness.IntrinsicSession.Main

/-!
# The intrinsic session: storage and preimage accounting

The storage and preimage laws `Solidity.Goals.IntrinsicSession.StorageLaws` at
`spec F`, `view F` (plan step `is0-intrinsic-session`, goal
`Solidity.Goals.intrinsicStorageAccounting`).

* `stored` is `IntrinsicStorage.stored` by the definition of `view`.
* `call_inputs` / `create_inputs`: a completed transaction or deployment ran its
  frame (`request_frame`, `deploy_frame`), and `hashed` / `slotHashed` of
  `Spec.lean` list the inputs of every executed frame at a fuel that completes
  it (`Frame.inputs_call`, `Frame.inputs_create`).

What is missing is the existence of such a fuel. `Frame.call_approx` and
`Frame.create_approx` say that a fuel's observation is the actual frame or
`diverge`; they do not say that a frame which does not diverge is completed by
some fuel. That is the adequacy of the fuelled run (`FuelAdequate`), a property
of `Prog.runFC` against `Prog.run` (`Semantics/RunFuel.lean`) that no module
proves yet. This module proves the frame-level consequence (`call_done`,
`create_done`) and the storage laws from it; the unconditional goal waits for
the adequacy theorem.
-/

namespace Solidity.Semantics.IntrinsicSession

open Solidity.Roadmap
open Solidity.Goals.IntrinsicSession (Code TypedWorld Good Ends FrameInputs StorageLaws)
open Solidity.ContractWorld (World Handle Entry Context)
open Solidity.Lowering.V08.EnvironmentProjection (liftWord liftAddress requestContext)

/-! ## Fuel adequacy -/

/-- **Adequacy of the fuelled run**: a program run that does not diverge is
completed by the observation at some fuel. -/
def FuelAdequate : Prop :=
  ∀ {C : Contract} {Γ Δ : Ctx} (p : Prog C Γ Δ) (σ : State C Γ),
    p.run σ ≠ .error .diverge →
      ∃ n, (IntrinsicStorage.Observe.program n p σ).result ≠ .error .diverge

section Converge

variable {α β : Type}

/-- A fuel-independent first result, then a continuation some fuel completes. -/
theorem conv_bind (a : TRes α) {f : Nat → α → TRes β} {g : α → TRes β}
    (h : ∀ x, g x ≠ .error .diverge → ∃ n, f n x ≠ .error .diverge) :
    (a >>= g) ≠ .error .diverge → ∃ n, (a >>= f n) ≠ .error .diverge := by
  cases a with
  | error e => exact fun d => ⟨0, d⟩
  | ok x => exact h x

/-- A fuel-dependent first result that approximates the actual one and that
some fuel completes, then a fixed continuation. -/
theorem conv_first {A : Nat → TRes α} {a : TRes α} (approx : ∀ n, TRes.Approx (A n) a)
    (done : a ≠ .error .diverge → ∃ n, A n ≠ .error .diverge) (k : α → TRes β) :
    (a >>= k) ≠ .error .diverge → ∃ n, (A n >>= k) ≠ .error .diverge := by
  intro d
  obtain ⟨n, hn⟩ := done fun e => d (by rw [e]; rfl)
  exact ⟨n, by rw [(approx n).eq hn]; exact d⟩

end Converge

section Frames

variable {K : Type} [DecidableEq K] {contracts : K → Contract}

/-- A call frame that does not diverge is completed by some fuel. -/
theorem callFrame_done (ad : FuelAdequate) (w : World contracts) {k : K} {α : Type}
    (r : Handle k) (entry : Entry (contracts k) α) (ctx : Context)
    (d : w.callFrame r entry ctx ≠ .error .diverge) :
    ∃ n, (IntrinsicStorage.Frame.callFrame n w r entry ctx).result ≠ .error .diverge := by
  unfold IntrinsicStorage.Frame.callFrame
  unfold World.callFrame at d
  split
  · rename_i lib; rw [if_pos lib] at d; exact ⟨0, d⟩
  · rename_i lib
    rw [if_neg lib] at d
    simp only [IntrinsicStorage.Audit.result_bind, IntrinsicStorage.Audit.result_lift,
      IntrinsicStorage.Audit.result_pure]
    exact conv_bind _ (fun _ => conv_bind _ fun σ =>
      conv_first (IntrinsicStorage.Observe.program_approx · entry.body σ) (ad entry.body σ) _) d

/-- **A call that does not diverge is completed by some fuel.** -/
theorem call_done (ad : FuelAdequate) (w : World contracts) {k : K} {α : Type}
    (r : Handle k) (entry : Entry (contracts k) α) (ctx : Context)
    (d : w.call r entry ctx ≠ .error .diverge) :
    ∃ n, (IntrinsicStorage.Frame.call n w r entry ctx).result ≠ .error .diverge := by
  obtain ⟨n, hn⟩ := conv_first (IntrinsicStorage.Frame.callFrame_approx · w r entry ctx)
    (callFrame_done ad w r entry ctx) _ d
  exact ⟨n, by
    simpa only [IntrinsicStorage.Frame.call, IntrinsicStorage.Audit.result_bind,
      IntrinsicStorage.Audit.result_lift, IntrinsicStorage.Audit.result_pure] using hn⟩

omit [DecidableEq K] in
/-- **A creation that does not diverge is completed by some fuel.** -/
theorem create_done (ad : FuelAdequate) (w : World contracts) (k : K)
    (self : ContractWorld.Address) (ctor : Prog (contracts k) [] []) (ctx : Context)
    (d : w.create k self ctor ctx ≠ .error .diverge) :
    ∃ n, (IntrinsicStorage.Frame.create n w k self ctor ctx).result ≠ .error .diverge := by
  unfold IntrinsicStorage.Frame.create
  unfold World.create at d
  split
  · rename_i lib; rw [if_pos lib] at d; exact ⟨0, d⟩
  · rename_i lib
    rw [if_neg lib] at d
    change ((if (w.accounts self).isSome || decide (self = ctx.sender) || ctx.isStatic then
        .error .revert else do
      let σ ← w.enter self ctx (Storage.init (contracts k))
        (((contracts k).ctor.map (·.payable)).getD false)
      let o ← ctor.run σ
      let next ← w.finish self o.st
      pure (next, (⟨self⟩ : Handle k))) : TRes (World contracts × Handle k)) ≠ _ at d
    split
    · rename_i taken; rw [if_pos taken] at d; exact ⟨0, d⟩
    · rename_i taken
      rw [if_neg taken] at d
      simp only [IntrinsicStorage.Audit.result_bind, IntrinsicStorage.Audit.result_lift,
      IntrinsicStorage.Audit.result_pure]
      exact conv_bind _ (fun σ =>
        conv_first (IntrinsicStorage.Observe.program_approx · ctor σ) (ad ctor σ) _) d

end Frames

/-- A completed frame result does not diverge. -/
theorem ends_ne {α : Type} {res : TRes α} (ends : Ends res) : res ≠ .error .diverge := by
  rintro rfl; exact nomatch ends

/-! ## Executed frames -/

section Run

variable {contracts : List Contract}
  {entry : (k : Fin contracts.length) → Bytes → Option (Entry contracts[k] Bytes)}
  {F : Fixed} {wire : Wire} {r : Bound} {e : SessionEnv} {h : List Event} {n : Nat}
  {w : World (catalog contracts)} {a : Action}

/-- The frames of a step lead the run from its boundary. -/
theorem go_step_frames {k : Nat} (next : e.requests h n = some a) :
    (step entry F wire r e h n w a).frames <+: (go entry F wire r e h n w (k + 1)).frames := by
  cases stop : (step entry F wire r e h n w a).stops
  · rw [go_step next stop]; exact List.prefix_append _ _
  · rw [go_stops next stop]; exact List.prefix_refl _

end Run

variable {F : Fixed} {x : Start} {e : SessionEnv} {r : Bound} {h : List Event} {n : Nat}

/-- The frames of the run from the origin are frames of the run at a good bound. -/
theorem origin_frames (good : Good (spec F) r) {h0 : List Event}
    {w0 : World (catalog x.code.contracts)} (o : x.origin F e = some (h0, w0))
    {f : Frame (catalog x.code.contracts)}
    (mem : f ∈ (go x.code.entry F wire (Bound.upto 0) e h0 0 w0 r.horizon).frames) :
    f ∈ (runOf F x e r).frames := by
  obtain ⟨k, rfl⟩ : ∃ k, r = Bound.upto k := ⟨_, good_eq good⟩
  obtain ⟨code, _ | w1⟩ := x
  · have stop : (deployed F code e).stops = false := by
      cases s : (deployed F code e).stops
      · rfl
      · simp [Start.origin, s] at o
    simp only [Start.origin, stop, Bool.false_eq_true, if_false, Option.some.injEq,
      Prod.mk.injEq] at o
    obtain ⟨rfl, rfl⟩ := o
    dsimp only [runOf]
    rw [run_fresh (r := Bound.upto k) stop]
    dsimp only
    rw [deploy_bound (r := Bound.upto k) (r' := Bound.upto 0) rfl,
      go_bound (r := Bound.upto k) (r' := Bound.upto 0) rfl]
    exact List.mem_append_right _ mem
  · simp only [Start.origin, Option.some.injEq, Prod.mk.injEq] at o
    obtain ⟨rfl, rfl⟩ := o
    rw [show runOf F ⟨code, .boundary w1⟩ e (Bound.upto k) =
      go code.entry F wire (Bound.upto 0) e [] 0 w1 k from
      go_bound (r := Bound.upto k) (r' := Bound.upto 0) rfl k [] 0 w1]
    exact mem

/-- **The frames of an action past a boundary are executed** at a good bound
beyond it. -/
theorem request_frame {w : World (catalog x.code.contracts)} {a : Action}
    (b : (view F).Boundary x e h n ⟨x.code, w⟩) (next : e.requests h n = some a)
    (good : Good (spec F) r) (lt : n < r.horizon) {f : Frame (catalog x.code.contracts)}
    (mem : f ∈ (act F x e h n w a).frames) : f ∈ (runOf F x e r).frames := by
  obtain ⟨h0, w0, o, wk⟩ := boundary_mk.1 b
  obtain ⟨_, fs, _, _, eq⟩ := walk_go n wk
  have run := eq (r.horizon - n)
  rw [Nat.add_sub_cancel' (Nat.le_of_lt lt), Nat.zero_add,
    show r.horizon - n = r.horizon - n - 1 + 1 by omega] at run
  refine origin_frames good o ?_
  rw [run]
  exact List.mem_append_right _ ((go_step_frames next).subset mem)

/-- An affordable request to a resolved entry runs the actual call frame, with
no answers. -/
theorem request_frames {w : World (catalog x.code.contracts)} {q : Request}
    {k : Fin x.code.contracts.length} {st : Storage (x.code.catalog k)}
    {en : Entry (x.code.catalog k) Bytes}
    (funded : Solidity.Goals.IntrinsicSession.Funded F e h q)
    (acc : w.accounts (liftAddress q.target) = some ⟨k, st⟩)
    (ent : x.code.entry k q.input = some en) :
    (⟨(w.atTime (liftWord q.timestamp)).resetTransient, .call ⟨liftAddress q.target⟩ en,
      requestContext q []⟩ : Frame (catalog x.code.contracts)) ∈
      (act F x e h n w (.request q)).frames := by
  simp only [act, step, request, if_neg (not_not_intro (show Funded F e h q from funded))]
  split
  · rename_i none; rw [acc] at none; cases none
  · rename_i k' st' some
    rw [acc] at some
    cases some
    simp only [ent]
    repeat' split
    all_goals simp [responses_wire]

/-- The deployment of a resolved constructor runs the actual creation frame,
with no answers. -/
theorem deploy_frame {code : Code} (good : Good (spec F) r) {k : Fin code.contracts.length}
    (main : k.val = code.main) {body : Prog (code.catalog k) [] []}
    (ct : code.ctor k e.deployArgs = some body) :
    (⟨(initial code.roles e).resetTransient,
      .create k (liftAddress (F.createAddress e.deployer e.deployNonce)) body,
      deployContext wire e⟩ : Frame (catalog code.contracts)) ∈
      (runOf F (Start.initial code) e r).frames := by
  obtain ⟨k, hk⟩ := k
  dsimp only at main
  subst main
  have ran : (⟨(initial code.roles e).resetTransient,
      .create ⟨code.main, hk⟩ (liftAddress (F.createAddress e.deployer e.deployNonce)) body,
      deployContext wire e⟩ : Frame (catalog code.contracts)) ∈
      (deploy code.main code.roles code.ctor F wire r e).frames := by
    simp only [deploy, dif_pos hk, ct, good.2.1, Bool.false_eq_true, if_false]
    split
    · simp
    · split <;> simp
  dsimp only [runOf, Start.initial, run]
  split
  · exact ran
  · exact List.mem_append_left _ ran

/-! ## The storage laws -/

/-- **The storage and preimage laws**, from the adequacy of the fuelled run. -/
theorem storage_laws (ad : FuelAdequate) (F : Fixed) : StorageLaws F (spec F) (view F) where
  stored t := view_stored F t
  call_inputs := by
    intro x en h n code cw q k st entry _ b next funded acc ent _ _ _ _ _ _ _ ends r out good pre
    obtain ⟨w, eq, stands⟩ := b
    cases eq
    have b : (view F).Boundary x en h n ⟨x.code, w⟩ := ⟨w, rfl, stands⟩
    have lt : n < r.horizon := by
      refine Nat.lt_of_not_le fun le => ?_
      have below := (Boundary.below b good le).length_le
      have above : (h ++ [_]).length ≤ ((spec F).lang.sem x en r).events.length := pre.length_le
      simp only [List.length_append, List.length_singleton] at above
      omega
    obtain ⟨fuel, res, inputs⟩ := Frame.inputs_call (call_done ad _ _ _ _ (ends_ne ends))
    have ran := request_frame b next good lt (request_frames funded acc ent)
    exact ⟨fuel, res, fun _ mem => frame_slotHashed ran (inputs ▸ mem),
      fun _ mem => frame_hashed ran (inputs ▸ mem)⟩
  create_inputs := by
    intro code en k body _ main ct _ _ _ _ _ _ _ _ _ _ ends r out address good _
    obtain ⟨fuel, res, inputs⟩ := Frame.inputs_create (create_done ad _ _ _ _ _ (ends_ne ends))
    have ran := deploy_frame (F := F) (e := en) good main ct
    exact ⟨fuel, res, fun _ mem => frame_slotHashed ran (inputs ▸ mem),
      fun _ mem => frame_hashed ran (inputs ▸ mem)⟩

/-- **The storage accounting goal, from the adequacy of the fuelled run**: the
laws of `session_semantics_correct` and the storage laws, at `spec F`, `view F`. -/
theorem storage_accounting_of_adequate (ad : FuelAdequate) :
    Solidity.Goals.intrinsicStorageAccounting :=
  fun F => ⟨spec F, view F, laws F, storage_laws ad F⟩

end Solidity.Semantics.IntrinsicSession
