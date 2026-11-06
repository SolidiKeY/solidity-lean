import Solidity.Optimizer.Loads
import Solidity.Semantics.RunFrame

/-!
# O03/X06 loop-invariant code motion

`while (c) { x = e; rest }` becomes `if (c) { x = e; while (c) { rest } }`
when the assignment is loop-invariant: the guarded hoist (`Stmt.licm`).

The guard is what makes the zero-iteration case exact: hoisting `x = e` in
front of a loop that never runs would evaluate `e` (which may revert, e.g. an
overflow) and write `x` where the loop does neither. Under `if (c)`, `e` is
evaluated exactly when the loop's first iteration evaluates it, in the same
state (evaluating `c` changes no state), and fails exactly when that iteration
fails, with the same halt. The side conditions (`licmB`), each used in
`licm_runC`:

* `e` and `c` are invariant expressions (`Val.invB`): literals, locals,
  environment values, operators, and reads of primitive state variables (an
  invariant `sload`); no memory read, no path with an index;
* neither `e` nor `c` reads `x`, so `x = e` changes neither (the hoisted `c`
  is evaluated after `x = e`); `c` is *not* required to be loop-invariant: it is
  re-evaluated every iteration exactly as in the original loop, and `Val.invB c`
  is only what lets it move past `x = e`;
* the loop annotation is an unwind bound or automatic (`LoopAnn.plainB`): a
  written invariant is stated for the original entry state, so annotated loops
  are left as written;
* `rest` is within `nonpayable` (`Prog.within`: no memory statement, no
  allocation; `Prog.run_frame`), writes no local `e` reads and not `x`
  (`Prog.writesAt`, positions), and writes only state variables outside the
  ones `e` reads (`Prog.storeAt = some L`, `Prog.run_keeps`): so every
  iteration leaves `e`'s value and `x` unchanged, and the hoisted `x = e` is
  then a no-op in each later iteration (`TLoop.run_congr_inv`).

Preservation is equality of the typed run in every state (`Prog.licm_runC`),
diverging loops included (`TLoop.run` is the same limit on both sides).
-/
namespace Solidity.Optimizer.ConstFold
open Solidity

variable {C : Contract}

/-! ## Loops that agree on an invariant -/

namespace TLoop

variable {α : Type}

/-- Bounded iterations of two bodies that agree on an invariant the second keeps. -/
theorem iterN_congr_inv {body body' : α → TRes α} {c : α → TRes Bool} {P : α → Prop}
    (hb : ∀ τ, P τ → c τ = .ok true → body τ = body' τ)
    (hinv : ∀ τ τ', P τ → c τ = .ok true → body' τ = .ok τ' → P τ') :
    ∀ (n : Nat) (τ : α), P τ → TLoop.iterN body c n τ = TLoop.iterN body' c n τ
  | 0, _, _ => rfl
  | n + 1, τ, hp => by
    simp only [TLoop.iterN, TLoop.step]
    cases hc : c τ with
    | error e => rfl
    | ok b =>
      cases b with
      | false => rfl
      | true =>
        simp only
        rw [hb τ hp hc]
        cases hbd : body' τ with
        | error e => rfl
        | ok τ' => exact iterN_congr_inv hb hinv n τ' (hinv τ τ' hp hc hbd)

/-- Two loops whose bodies agree on states satisfying an invariant that the
second body keeps run alike from such a state. -/
theorem run_congr_inv {body body' : α → TRes α} {c : α → TRes Bool} {P : α → Prop} {σ : α}
    (hb : ∀ τ, P τ → c τ = .ok true → body τ = body' τ)
    (hinv : ∀ τ τ', P τ → c τ = .ok true → body' τ = .ok τ' → P τ') (h0 : P σ) :
    TLoop.run body c σ = TLoop.run body' c σ := by
  have hit := fun n => iterN_congr_inv hb hinv n σ h0
  by_cases hex : ∃ r n, TLoop.iterN body c n σ = .inr r
  · obtain ⟨r, n, hn⟩ := hex
    rw [TLoop.run_of_iterN hn, TLoop.run_of_iterN ((hit n).symm.trans hn)]
  · have hex' : ¬ ∃ r n, TLoop.iterN body' c n σ = .inr r := fun ⟨r, n, hn⟩ =>
      hex ⟨r, n, (hit n).trans hn⟩
    simp only [TLoop.run, hex, hex', dite_false]

/-- A loop that goes on from `σ` to `τ` runs as from `τ`. -/
theorem run_of_step {body : α → TRes α} {c : α → TRes Bool} {σ τ : α}
    (h : TLoop.step body c σ = .inl τ) : TLoop.run body c σ = TLoop.run body c τ := by
  have hit : ∀ n, TLoop.iterN body c (n + 1) σ = TLoop.iterN body c n τ := fun n => by
    simp only [TLoop.iterN, h]
  by_cases hex : ∃ r n, TLoop.iterN body c n τ = .inr r
  · obtain ⟨r, n, hn⟩ := hex
    rw [TLoop.run_of_iterN hn, TLoop.run_of_iterN ((hit n).trans hn)]
  · have hex' : ¬ ∃ r n, TLoop.iterN body c n σ = .inr r := fun ⟨r, n, hn⟩ => by
      cases n with
      | zero => simp only [TLoop.iterN, reduceCtorEq] at hn
      | succ n => exact hex ⟨r, n, (hit n).symm.trans hn⟩
    simp only [TLoop.run, hex, hex', dite_false]

/-- **The hoist on loops.** The original loop's first iteration from `σ` is
the hoisted loop's first iteration from `σ'` (the state after the hoisted
assignment, where the condition still holds); afterwards the two bodies agree
on states satisfying `P`, which the hoisted body keeps and its first iteration
establishes. -/
theorem hoist_run {body body' : α → TRes α} {c : α → TRes Bool} {P : α → Prop} {σ σ' : α}
    (hc : c σ = .ok true) (hc' : c σ' = .ok true) (hfirst : body σ = body' σ')
    (hb : ∀ τ, P τ → c τ = .ok true → body τ = body' τ)
    (hinv : ∀ τ τ', P τ → c τ = .ok true → body' τ = .ok τ' → P τ')
    (h0 : ∀ τ, body' σ' = .ok τ → P τ) :
    TLoop.run body' c σ' = TLoop.run body c σ := by
  cases hbd : body' σ' with
  | error err =>
    have h1 : TLoop.iterN body c 1 σ = .inr (.error err) := by
      simp only [TLoop.iterN, TLoop.step, hc, hfirst, hbd]
    have h2 : TLoop.iterN body' c 1 σ' = .inr (.error err) := by
      simp only [TLoop.iterN, TLoop.step, hc', hbd]
    rw [TLoop.run_of_iterN h1, TLoop.run_of_iterN h2]
  | ok τ =>
    have h1 : TLoop.step body c σ = .inl τ := by simp only [TLoop.step, hc, hfirst, hbd]
    have h2 : TLoop.step body' c σ' = .inl τ := by simp only [TLoop.step, hc', hbd]
    rw [run_of_step h1, run_of_step h2]
    exact (run_congr_inv hb hinv (h0 τ hbd)).symm

end TLoop

/-! ## Invariant expressions -/

section Inv

variable {Γ : Ctx}

/-- Literals, locals, environment values, operators over them, and reads of
primitive state variables. -/
def _root_.Solidity.Val.invB : {p : PrimTy} → Val C Γ p → Bool
  | _, .simple _ => true
  | _, .read (.root _ _) => true
  | _, .binop _ _ _ a b => Val.invB a && Val.invB b
  | _, .unop _ _ _ a => Val.invB a
  | _, .ternary c a b => Val.invB c && Val.invB a && Val.invB b
  | _, .modular _ a b k => Val.invB a && Val.invB b && Val.invB k
  | _, .read (.field ..) | _, .read (.index ..) | _, .readMem _ | _, .len .. | _, .mlen ..
  | _, .hash .. => false

/-- Does the expression read the local at position `n` (conservatively `true`
outside the fragment)? -/
def _root_.Solidity.Val.readsPos (n : Nat) : {p : PrimTy} → Val C Γ p → Bool
  | _, .simple s => readsAt n s
  | _, .read (.root _ _) => false
  | _, .binop _ _ _ a b => Val.readsPos n a || Val.readsPos n b
  | _, .unop _ _ _ a => Val.readsPos n a
  | _, .ternary c a b => Val.readsPos n c || Val.readsPos n a || Val.readsPos n b
  | _, .modular _ a b k => Val.readsPos n a || Val.readsPos n b || Val.readsPos n k
  | _, .read (.field ..) | _, .read (.index ..) | _, .readMem _ | _, .len .. | _, .mlen ..
  | _, .hash .. => true

/-- The state variables the expression reads. -/
def _root_.Solidity.Val.roots : {p : PrimTy} → Val C Γ p → List Name
  | _, .simple _ => []
  | _, .read (.root r _) => [r]
  | _, .binop _ _ _ a b => Val.roots a ++ Val.roots b
  | _, .unop _ _ _ a => Val.roots a
  | _, .ternary c a b => Val.roots c ++ Val.roots a ++ Val.roots b
  | _, .modular _ a b k => Val.roots a ++ Val.roots b ++ Val.roots k
  | _, .read (.field ..) | _, .read (.index ..) | _, .readMem _ | _, .len .. | _, .mlen ..
  | _, .hash .. => []

/-- What an invariant expression reads agrees in two states. -/
structure InvAgree {p : PrimTy} (v : Val C Γ p) (σ τ : State C Γ) : Prop where
  locals : ∀ (q : PrimTy) (k : Idx Γ (.val q)), v.readsPos k.toNat = true →
    TEnv.get k τ.env = TEnv.get k σ.env
  env : ∀ key, τ.envVal key = σ.envVal key
  roots : ∀ (U : Ty) (r : SRef C U), r.root ∈ v.roots → τ.storage.find r = σ.storage.find r

theorem InvAgree.sub {p q : PrimTy} {v : Val C Γ p} {w : Val C Γ q} {σ τ : State C Γ}
    (h : InvAgree v σ τ) (hl : ∀ n, w.readsPos n = true → v.readsPos n = true)
    (hr : ∀ r, r ∈ w.roots → r ∈ v.roots) : InvAgree w σ τ :=
  ⟨fun q k hk => h.locals q k (hl _ hk), h.env, fun U r hm => h.roots U r (hr _ hm)⟩

theorem _root_.Solidity.Val.evalT_invAgree {σ τ : State C Γ} : {p : PrimTy} → (v : Val C Γ p) → v.invB = true →
    InvAgree v σ τ → v.evalT τ = v.evalT σ
  | _, .simple s, _, h => by
    cases s with
    | lit => rfl
    | bool => rfl
    | «local» k =>
      exact congrArg Except.ok (h.locals _ k (by simp only [Val.readsPos, readsAt, beq_self_eq_true]))
    | env key hp => cases hp; exact congrArg Except.ok (h.env key)
  | _, .read (.root r hr), _, h => by
    simp only [Val.evalT, Loc.resolveT, ok_bind]
    rw [h.roots _ (SRef.ofRoot r hr) (by simp only [Val.roots, SRef.ofRoot, List.mem_singleton])]
  | _, .binop op ha hq a b, hv, h => by
    simp only [Val.invB, Bool.and_eq_true] at hv
    have h1 := Val.evalT_invAgree a hv.1 (h.sub (fun n hn => by simp only [Val.readsPos, hn,
      Bool.true_or]) (fun r hr => by simp only [Val.roots, List.mem_append, hr, true_or]))
    have h2 := Val.evalT_invAgree b hv.2 (h.sub (fun n hn => by simp only [Val.readsPos, hn,
      Bool.or_true]) (fun r hr => by simp only [Val.roots, List.mem_append, hr, or_true]))
    simp only [Val.evalT, h1, h2]
  | _, .unop op ha hq a, hv, h => by
    simp only [Val.invB] at hv
    have h1 := Val.evalT_invAgree a hv (h.sub (fun n hn => by simp only [Val.readsPos, hn])
      (fun r hr => by simp only [Val.roots, hr]))
    simp only [Val.evalT, h1]
  | _, .ternary c a b, hv, h => by
    simp only [Val.invB, Bool.and_eq_true] at hv
    have h0 := Val.evalT_invAgree c hv.1.1 (h.sub (fun n hn => by simp only [Val.readsPos, hn,
      Bool.true_or]) (fun r hr => by simp only [Val.roots, List.mem_append, hr, true_or]))
    have h1 := Val.evalT_invAgree a hv.1.2 (h.sub (fun n hn => by simp only [Val.readsPos, hn,
      Bool.true_or, Bool.or_true]) (fun r hr => by
        simp only [Val.roots, List.mem_append, hr, true_or, or_true]))
    have h2 := Val.evalT_invAgree b hv.2 (h.sub (fun n hn => by simp only [Val.readsPos, hn,
      Bool.or_true]) (fun r hr => by simp only [Val.roots, List.mem_append, hr, or_true]))
    simp only [Val.evalT, h0, h1, h2]
  | _, .modular op a b k, hv, h => by
    simp only [Val.invB, Bool.and_eq_true] at hv
    have h0 := Val.evalT_invAgree a hv.1.1 (h.sub (fun n hn => by simp only [Val.readsPos, hn,
      Bool.true_or]) (fun r hr => by simp only [Val.roots, List.mem_append, hr, true_or]))
    have h1 := Val.evalT_invAgree b hv.1.2 (h.sub (fun n hn => by simp only [Val.readsPos, hn,
      Bool.true_or, Bool.or_true]) (fun r hr => by
        simp only [Val.roots, List.mem_append, hr, true_or, or_true]))
    have h2 := Val.evalT_invAgree k hv.2 (h.sub (fun n hn => by simp only [Val.readsPos, hn,
      Bool.or_true]) (fun r hr => by simp only [Val.roots, List.mem_append, hr, or_true]))
    simp only [Val.evalT, h0, h1, h2]
  | _, .read (.field ..), hv, _ | _, .read (.index ..), hv, _ | _, .readMem _, hv, _
  | _, .len .., hv, _ | _, .mlen .., hv, _ | _, .hash .., hv, _ => by
    simp only [Val.invB, Bool.false_eq_true] at hv

/-- Setting a local an invariant expression does not read leaves its value. -/
theorem _root_.Solidity.Val.evalT_setLocal_inv {p q : PrimTy} (σ : State C Γ) (i : Idx Γ (.val q)) (x : q.Denote)
    (v : Val C Γ p) (hv : v.invB = true) (hi : v.readsPos i.toNat = false) :
    v.evalT (σ.setLocal i x) = v.evalT σ := by
  refine Val.evalT_invAgree v hv ⟨fun q' k hk => ?_, fun _ => rfl, fun _ _ _ => rfl⟩
  have hne : i.toNat ≠ k.toNat := fun e => by rw [e, hk] at hi; exact Bool.noConfusion hi
  exact TEnv.get_set_ne i k x σ.env hne

end Inv

/-! ## What the rest of the body leaves -/

section Frame

variable {Γ : Ctx}

/-- `Prog.run_frame` at the compiled run (`rest` within `nonpayable`). -/
theorem runC_frame {Γ₁ : Ctx} (rest : Prog C Γ Γ₁) (hw : rest.within .nonpayable = true)
    {σ : State C Γ} {o : Out C σ.H Γ₁} (h : Prog.runC rest σ = .ok o) :
    TGFrame .nonpayable σ o.st ∧
      TLocAgree 0 (Prog.writesAt 0 rest) σ.env (TEnv.drop rest.ext o.st.env) :=
  Prog.run_frame rest hw 0 (by show Prog.runR rest σ = _; rw [Prog.runR_eq]; exact h)

/-- `Prog.run_keeps` at the compiled run: roots outside `rest.storeAt` kept. -/
theorem runC_keeps {Γ₁ : Ctx} (rest : Prog C Γ Γ₁) {σ : State C Γ} {o : Out C σ.H Γ₁}
    (h : Prog.runC rest σ = .ok o) : FrameKeeps (Prog.storeAt rest) σ o.st :=
  Prog.run_keeps rest (by show Prog.runR rest σ = _; rw [Prog.runR_eq]; exact h)

/-- A local whose position `rest` does not write reads as it did. -/
theorem runC_local {Γ₁ : Ctx} (rest : Prog C Γ Γ₁) (hw : rest.within .nonpayable = true)
    {σ : State C Γ} {o : Out C σ.H Γ₁} (h : Prog.runC rest σ = .ok o) {q : PrimTy}
    (k : Idx Γ (.val q)) (hk : ∀ w ∈ Prog.writesAt 0 rest, w.2 ≠ k.toNat) :
    TEnv.get k (o.st.drop rest.ext).env = TEnv.get k σ.env := by
  have ha := (runC_frame rest hw h).2 (.val q) k (Nat.zero_le _) (fun hm => hk _ hm (by simp only [Nat.sub_zero]))
  exact eq_of_heq ha

/-- An invariant expression whose locals and state variables `rest` does not
write evaluates as it did. -/
theorem runC_inv {Γ₁ : Ctx} (rest : Prog C Γ Γ₁) (hw : rest.within .nonpayable = true)
    {L : List Name} (hL : rest.storeAt = some L) {p : PrimTy} (v : Val C Γ p)
    (hv : v.invB = true) (hpos : ∀ w ∈ Prog.writesAt 0 rest, v.readsPos w.2 = false)
    (hroots : ∀ r ∈ v.roots, r ∉ L) {σ : State C Γ} {o : Out C σ.H Γ₁}
    (h : Prog.runC rest σ = .ok o) : v.evalT (o.st.drop rest.ext) = v.evalT σ := by
  have hg := (runC_frame rest hw h).1
  have hk := runC_keeps rest h
  rw [hL] at hk
  obtain ⟨hfr, -, hbal⟩ := hk
  refine Val.evalT_invAgree v hv ⟨fun q k hk' => runC_local rest hw h k fun w hm e => ?_,
    fun key => ?_, fun U r hr => hfr.find_eq (hroots _ hr)⟩
  · rw [← e, hpos w hm] at hk'
    exact Bool.noConfusion hk'
  · cases key <;> simp only [State.envVal, State.drop, hg.tx, hbal]

end Frame

/-! ## The hoist -/

section Hoist

variable {Γ : Ctx}

/-- `while (c) { x = e; rest }` may become `if (c) { x = e; while (c) { rest } }`. -/
def licmB {q : PrimTy} {Γ₁ : Ctx} (c : Val C Γ .bool) (x : Idx Γ (.val q)) (e : Val C Γ q)
    (rest : Prog C Γ Γ₁) : Bool :=
  c.invB && !c.readsPos x.toNat && e.invB && !e.readsPos x.toNat &&
    rest.within .nonpayable &&
    (Prog.writesAt 0 rest).all (fun w => !e.readsPos w.2 && w.2 != x.toNat) &&
    match rest.storeAt with
    | some L => e.roots.all fun r => !L.contains r
    | none => false

/-- The side conditions of the hoist, as propositions (`licmB_ok`). -/
structure LicmOk {q : PrimTy} {Γ₁ : Ctx} (c : Val C Γ .bool) (x : Idx Γ (.val q))
    (e : Val C Γ q) (rest : Prog C Γ Γ₁) : Prop where
  cinv : c.invB = true
  cx : c.readsPos x.toNat = false
  einv : e.invB = true
  ex : e.readsPos x.toNat = false
  within : rest.within .nonpayable = true
  epos : ∀ w ∈ Prog.writesAt 0 rest, e.readsPos w.2 = false
  xpos : ∀ w ∈ Prog.writesAt 0 rest, w.2 ≠ x.toNat
  keeps : ∃ L, rest.storeAt = some L ∧ ∀ r ∈ e.roots, r ∉ L

/-- The decided side conditions give `LicmOk`. -/
theorem licmB_ok {q : PrimTy} {Γ₁ : Ctx} {c : Val C Γ .bool} {x : Idx Γ (.val q)}
    {e : Val C Γ q} {rest : Prog C Γ Γ₁} (h : licmB c x e rest = true) : LicmOk c x e rest := by
  unfold licmB at h
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.all_eq_true,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hc, hcx⟩, he⟩, hex⟩, hw⟩, hall⟩, hst⟩ := h
  cases hs : rest.storeAt with
  | none => simp only [hs, Bool.false_eq_true] at hst
  | some L =>
    simp only [hs, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.contains_eq_mem, decide_eq_false_iff_not] at hst
    exact ⟨hc, hcx, he, hex, hw, fun w hm => (hall w hm).1, fun w hm => (hall w hm).2, ⟨L, hs, hst⟩⟩

end Hoist

section Main

variable {Γ : Ctx}

/-- Setting a local to its own value changes nothing. -/
theorem tenv_set_get {H : HTy} : {Γ : Ctx} → {t : LTy} → (i : Idx Γ t) → (e : TEnv C H Γ) →
    TEnv.set i (TEnv.get i e) e = e
  | _, _, .here, _ => rfl
  | _, _, .there i, e => congrArg (Prod.mk e.1) (tenv_set_get i e.2)

/-- **The guarded hoist runs as the loop**: `if (c) { x = e; while (c) { rest } }` and `while (c) { x = e; rest }` (`while (i < 3) { x = total + 1; i = i + 1; }`), in every state, including when the loop runs zero times and when `e` reverts. -/
theorem licm_runC (a : LoopAnn C Γ) (c : Val C Γ .bool) {q : PrimTy} (x : Idx Γ (.val q))
    (e : Val C Γ q) {Γ₁ : Ctx} (rest : Prog C Γ Γ₁) (h : LicmOk c x e rest) :
    Stmt.runC (.ite c (.cons (.assignLocal x e) (.cons (.loop a c rest) .nil)) .nil) =
      Stmt.runC (.loop a c (.cons (.assignLocal x e) rest)) := by
  funext σ
  obtain ⟨hcinv, hcx, heinv, hex, hw, hepos, hxpos, L, hL, hroots⟩ := h
  -- the hoisted loop's body, and the invariant: `x` holds `e`'s value
  let F2 : Out C σ.H Γ → TRes (Out C σ.H Γ) := fun o =>
    (Prog.runC rest o.st).map fun o' => ⟨o'.st.drop rest.ext, o.ext.trans o'.ext⟩
  let Inv : Out C σ.H Γ → Prop := fun o => e.evalT o.st = .ok (TEnv.get x o.st.env)
  have hinv : ∀ τ τ', Inv τ → c.evalT τ.st = .ok true → F2 τ = .ok τ' → Inv τ' := by
    intro τ τ' hτ _ hF
    simp only [F2] at hF
    cases hr : Prog.runC rest τ.st with
    | error err => simp only [hr, Except.map, reduceCtorEq] at hF
    | ok o =>
      simp only [hr, Except.map, Except.ok.injEq] at hF
      subst hF
      show e.evalT (o.st.drop rest.ext) = .ok (TEnv.get x (o.st.drop rest.ext).env)
      rw [runC_inv rest hw hL e heinv hepos hroots hr, hτ,
        runC_local rest hw hr x hxpos]
  have hb : ∀ τ, Inv τ → c.evalT τ.st = .ok true →
      ((TRun.seq (Stmt.runC (.assignLocal x e)) (Prog.runC rest) τ.st).map fun o' =>
        (⟨o'.st.drop (Prog.cons (.assignLocal x e) rest).ext, τ.ext.trans o'.ext⟩ :
          Out C σ.H Γ)) = F2 τ := by
    intro τ hτ _
    have hτ' : e.evalT τ.st = .ok (TEnv.get x τ.st.env) := hτ
    have hset : ∀ σ₀ : State C Γ,
        Prog.runC rest (σ₀.setLocal x (TEnv.get x σ₀.env)) = Prog.runC rest σ₀ := by
      intro σ₀
      obtain ⟨st, H, hp, env, net, bal, tx⟩ := σ₀
      simp only [State.setLocal]
      rw [tenv_set_get]
    simp only [F2, TRun.seq, Stmt.runC, TRun.assignLocal, hτ', ok_bind, pure, Except.pure]
    rw [Subsingleton.elim (Prog.cons (.assignLocal x e) rest).ext rest.ext]
    rw [hset τ.st]
    cases Prog.runC rest τ.st <;> rfl
  let F1 : Out C σ.H Γ → TRes (Out C σ.H Γ) := fun o =>
    (Prog.runC (.cons (.assignLocal x e) rest) o.st).map fun o' =>
      ⟨o'.st.drop (Prog.cons (.assignLocal x e) rest).ext, o.ext.trans o'.ext⟩
  let cnd : Out C σ.H Γ → TRes Bool := fun o => c.evalT o.st
  have hR : Stmt.runC (.loop a c (.cons (.assignLocal x e) rest)) σ =
      TLoop.run F1 cnd ⟨σ, List.prefix_refl _⟩ := rfl
  rw [hR]
  have hcσ : ∀ v, c.evalT (σ.setLocal x v) = c.evalT σ := fun v =>
    Val.evalT_setLocal_inv σ x v c hcinv hcx
  simp only [Stmt.runC, Prog.runC, TRun.ite, TRun.seq, TRun.nil, TRun.assignLocal, TRun.loop]
  cases hc : c.evalT σ with
  | error err =>
    have h1 : TLoop.iterN F1 cnd 1 ⟨σ, List.prefix_refl _⟩ = .inr (.error err) := by
      simp only [TLoop.iterN, TLoop.step, cnd, hc]
    rw [TLoop.run_of_iterN h1]
    rfl
  | ok b =>
    cases b with
    | false =>
      have h1 : TLoop.iterN F1 cnd 1 ⟨σ, List.prefix_refl _⟩ =
          .inr (.ok ⟨σ, List.prefix_refl _⟩) := by
        simp only [TLoop.iterN, TLoop.step, cnd, hc]
      rw [TLoop.run_of_iterN h1]
      rfl
    | true =>
      cases he : e.evalT σ with
      | error err =>
        have h1 : TLoop.iterN F1 cnd 1 ⟨σ, List.prefix_refl _⟩ = .inr (.error err) := by
          simp only [TLoop.iterN, TLoop.step, cnd, hc, F1, Prog.runC, TRun.seq, Stmt.runC,
            TRun.assignLocal, he]
          rfl
        rw [TLoop.run_of_iterN h1]
        rfl
      | ok v =>
        have hc2 : cnd ⟨σ.setLocal x v, List.prefix_refl _⟩ = .ok true := by
          show c.evalT (σ.setLocal x v) = _
          rw [hcσ, hc]
        have hInv0 : Inv ⟨σ.setLocal x v, List.prefix_refl _⟩ := by
          show e.evalT (σ.setLocal x v) = .ok (TEnv.get x (TEnv.set x v σ.env))
          rw [Val.evalT_setLocal_inv σ x v e heinv hex, he, TEnv.get_set]
        have hfirst : F1 ⟨σ, List.prefix_refl _⟩ = F2 ⟨σ.setLocal x v, List.prefix_refl _⟩ := by
          simp only [F1, F2, Prog.runC, TRun.seq, Stmt.runC, TRun.assignLocal, he, ok_bind, pure,
            Except.pure]
          rw [Subsingleton.elim (Prog.cons (.assignLocal x e) rest).ext rest.ext]
          cases Prog.runC rest (σ.setLocal x v) <;> rfl
        rw [← TLoop.hoist_run (body := F1) (body' := F2) (c := cnd) (P := Inv) hc hc2 hfirst
          (fun τ hτ hcτ => hb τ hτ hcτ) hinv (fun τ hτ => hinv _ τ hInv0 hc2 hτ)]
        simp only [ok_bind, boolT, ite_true, pure, Except.pure]
        simp only [F2, cnd]
        split
        · next o heq => exact Eq.trans rfl heq.symm
        · next err heq => exact Eq.trans rfl heq.symm

end Main

/-! ## The pass -/

section Pass

variable {Γ : Ctx}

/-- A sequence that starts with a local assignment: the assignment and the rest. -/
def splitAssign? {Δ : Ctx} : Prog C Γ Δ →
    Option ((q : PrimTy) × Idx Γ (.val q) × Val C Γ q × Prog C Γ Δ)
  | .nil => none
  | .cons s P =>
    match s, P with
    | .assignLocal x e, P => some ⟨_, x, e, P⟩
    | .assign .., _ | .rebind .., _ | .declLocal .., _ | .declStorage .., _ | .opAssign .., _ | .incDec .., _ | .assignIncDec .., _ | .assignLocalPush .., _ | .push .., _ | .pop .., _ | .transfer .., _ | .send .., _ | .declMem .., _ | .rebindMem .., _ | .assignFromMem .., _ | .assignMem .., _ | .delete .., _ | .deleteMem .., _ | .assignNew .., _ | .ite .., _ | .require .., _ | .assert .., _ | .revert, _ | .assumeFalse, _ | .call .., _ | .tryCall .., _ | .loop .., _ | .block .., _ | .pushOpAssign .., _ | .pushIncDec .., _ | .callReceiver .., _ | .callReceiverPush .., _ | .callRec .., _ | .revertData .., _ | .catchData .., _ => none

/-- A split sequence is its assignment and its rest. -/
theorem splitAssign?_eq {Δ : Ctx} {P : Prog C Γ Δ} {q : PrimTy} {x : Idx Γ (.val q)}
    {e : Val C Γ q} {rest : Prog C Γ Δ} (h : splitAssign? P = some ⟨q, x, e, rest⟩) :
    P = .cons (.assignLocal x e) rest := by
  cases P with
  | nil => simp only [splitAssign?, reduceCtorEq] at h
  | cons s Q =>
    cases s with
    | assignLocal x' e' =>
      simp only [splitAssign?, Option.some.injEq, Sigma.mk.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      simp only [heq_eq_eq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl, rfl⟩ := h2
      rfl
    | assign | rebind | declLocal | declStorage | opAssign | incDec | assignIncDec | assignLocalPush | push | pop | transfer | send | declMem | rebindMem | assignFromMem | assignMem | delete | deleteMem | assignNew | ite | require | assert | revert | assumeFalse | call | tryCall | loop | block | pushOpAssign | pushIncDec | callReceiver | callReceiverPush | callRec | revertData | catchData => simp only [splitAssign?, reduceCtorEq] at h

/-- A loop annotation the hoist keeps meaningful: an unwind bound or automatic
unwinding (the hoisted loop runs the same iterations). An invariant or variant
(`LoopAnn.inv`, `.invLex`) is stated for the loop's entry state, which the hoist
moves past `x = e`, so such loops are left as written. -/
def _root_.Solidity.LoopAnn.plainB {Γ : Ctx} : LoopAnn C Γ → Bool
  | .unwind _ | .auto => true
  | .inv .. | .invLex .. => false

/-- The loop `while (c) body`, its leading invariant assignment hoisted under
the guard `if (c)` when `licmB` allows it and the annotation is plain. -/
def hoist {Γ₁ : Ctx} (a : LoopAnn C Γ) (c : Val C Γ .bool) (body : Prog C Γ Γ₁) : Stmt C Γ Γ :=
  match splitAssign? body with
  | some ⟨_, x, e, rest⟩ =>
    if a.plainB && licmB c x e rest then
      .ite c (.cons (.assignLocal x e) (.cons (.loop a c rest) .nil)) .nil
    else .loop a c body
  | none => .loop a c body

/-- The hoist (or the loop left as written) runs as the loop. -/
theorem hoist_runC {Γ₁ : Ctx} (a : LoopAnn C Γ) (c : Val C Γ .bool) (body : Prog C Γ Γ₁) :
    Stmt.runC (hoist a c body) = Stmt.runC (.loop a c body) := by
  unfold hoist
  split
  · next q x e rest hs =>
    split
    · next hl =>
      rw [splitAssign?_eq hs]
      exact licm_runC a c x e rest (licmB_ok (Bool.and_eq_true _ _ ▸ hl).2)
    · rfl
  · rfl

end Pass

mutual
/-- Loop-invariant code motion in every loop of a statement, innermost first. -/
def Stmt.licm : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Stmt C Γ Γ'
  | _, _, .ite c thn els => .ite c (Prog.licm thn) (Prog.licm els)
  | _, _, .block body => .block (Prog.licm body)
  | _, _, .loop a c body => hoist a c (Prog.licm body)
  | _, _, s@(.assign ..) => s
  | _, _, s@(.rebind ..) => s
  | _, _, s@(.assignLocal ..) => s
  | _, _, s@(.declLocal ..) => s
  | _, _, s@(.declStorage ..) => s
  | _, _, s@(.opAssign ..) => s
  | _, _, s@(.incDec ..) => s
  | _, _, s@(.assignIncDec ..) => s
  | _, _, s@(.assignLocalPush ..) => s
  | _, _, s@(.push ..) => s
  | _, _, s@(.pop ..) => s
  | _, _, s@(.transfer ..) => s
  | _, _, s@(.send ..) => s
  | _, _, s@(.declMem ..) => s
  | _, _, s@(.rebindMem ..) => s
  | _, _, s@(.assignFromMem ..) => s
  | _, _, s@(.assignMem ..) => s
  | _, _, s@(.delete ..) => s
  | _, _, s@(.deleteMem ..) => s
  | _, _, s@(.assignNew ..) => s
  | _, _, s@(.require ..) => s
  | _, _, s@(.assert ..) => s
  | _, _, s@(.revert) => s
  | _, _, s@(.assumeFalse) => s
  | _, _, s@(.call ..) => s
  | _, _, s@(.tryCall ..) => s
  | _, _, s@(.pushOpAssign ..) => s
  | _, _, s@(.pushIncDec ..) => s
  | _, _, s@(.callReceiver ..) => s
  | _, _, s@(.callReceiverPush ..) => s
  | _, _, s@(.callRec ..) => s
  | _, _, s@(.revertData ..) => s
  | _, _, s@(.catchData ..) => s

/-- Loop-invariant code motion in a sequence. -/
def Prog.licm : {Γ Γ' : Ctx} → Prog C Γ Γ' → Prog C Γ Γ'
  | _, _, .nil => .nil
  | _, _, .cons s P => .cons (Stmt.licm s) (Prog.licm P)
end

mutual
theorem Stmt.licm_runC : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → Stmt.runC (Stmt.licm s) = Stmt.runC s
  | _, _, .ite c thn els => by
    simp only [Stmt.licm, Stmt.runC]
    rw [Prog.licm_runC thn, Prog.licm_runC els]
    exact TRun.ite_congr (fun _ => rfl) _ _ _ _ _ _
  | _, _, .block body => by
    simp only [Stmt.licm, Stmt.runC]
    rw [Prog.licm_runC body]
    exact TRun.block_congr _ _ _
  | _, _, .loop a c body => by
    simp only [Stmt.licm]
    rw [hoist_runC]
    simp only [Stmt.runC]
    rw [Prog.licm_runC body]
    exact TRun.loop_congr (fun _ => rfl) _ _ _
  | _, _, .assign ..
  | _, _, .rebind ..
  | _, _, .assignLocal ..
  | _, _, .declLocal ..
  | _, _, .declStorage ..
  | _, _, .opAssign ..
  | _, _, .incDec ..
  | _, _, .assignIncDec ..
  | _, _, .assignLocalPush ..
  | _, _, .push ..
  | _, _, .pop ..
  | _, _, .transfer ..
  | _, _, .send ..
  | _, _, .declMem ..
  | _, _, .rebindMem ..
  | _, _, .assignFromMem ..
  | _, _, .assignMem ..
  | _, _, .delete ..
  | _, _, .deleteMem ..
  | _, _, .assignNew ..
  | _, _, .require ..
  | _, _, .assert ..
  | _, _, .revert
  | _, _, .assumeFalse
  | _, _, .call ..
  | _, _, .tryCall ..
  | _, _, .pushOpAssign ..
  | _, _, .pushIncDec ..
  | _, _, .callReceiver ..
  | _, _, .callReceiverPush ..
  | _, _, .callRec ..
  | _, _, .revertData ..
  | _, _, .catchData .. => rfl

theorem Prog.licm_runC : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → Prog.runC (Prog.licm P) = Prog.runC P
  | _, _, .nil => rfl
  | _, _, .cons s P => by
    simp only [Prog.licm, Prog.runC]
    rw [Stmt.licm_runC s, Prog.licm_runC P]
end

/-- Loop-invariant code motion as an O01 pass preserving `SameRun`. -/
theorem licm_preserves (Γ Γ' : Ctx) :
    Preserves (SameRun (C := C) (Γ := Γ) (Γ' := Γ')) (Prog.licm : Lowering.Pass C Γ Γ') :=
  fun P => (Prog.licm_runC P).symm

end Solidity.Optimizer.ConstFold
