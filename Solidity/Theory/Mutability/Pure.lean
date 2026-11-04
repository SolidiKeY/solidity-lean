import Solidity.Theory.Mutability.View

/-!
# A pure body does not read the state (S3.1, pure)

`docs/feature-work/semantics-extensions.md`, S3.1: a `pure` body's result
does not depend on the state.

A body a `pure` function may run is `Prog.within .pure`
(`Calculus/Blocks.lean`): beyond `view`'s restrictions, no value it evaluates
reads the storage, memory or the environment (`Val.readsState`), and it binds
no storage alias.  What it may not read is the **outside** of a state
(`Outside`): the typed storage (persistent and transient roots), the ledger,
the contract's balance and the transaction (`msg.sender`, `msg.value`,
`block.timestamp`, `address(this)`).

The theorem is a commutation: running from `σ` with its outside replaced by
`w` is running from `σ` and replacing the outside of the end state by `w`
(`Prog.run_withOutside`), halts included.  So the outcome a pure body
reaches, its locals (the result) and how it halts, is the same from every
outside (`Prog.pure_independent`, `Prog.pure_local_independent`).

The proof is by structural recursion over the intrinsic syntax, one case per
statement a pure body may contain; a loop's run is related through
`TLoop.run_map`.
-/

namespace Solidity.Theory.Mutability

open Solidity

variable {C : Contract}

/-- The part of a state a `pure` body may not read: the committed globals and
the transaction. -/
structure Outside (C : Contract) where
  storage : Storage C
  net : Ledger
  selfBalance : PrimTy.uint.Denote
  tx : TTx

/-- The outside of `σ`. -/
def outside {Γ : Ctx} (σ : State C Γ) : Outside C := ⟨σ.storage, σ.net, σ.selfBalance, σ.tx⟩

/-- `σ` with its outside replaced by `w`: the same heap typing, heap and locals. -/
def withOutside {Γ : Ctx} (σ : State C Γ) (w : Outside C) : State C Γ :=
  { σ with storage := w.storage, net := w.net, selfBalance := w.selfBalance, tx := w.tx }

theorem withOutside_outside {Γ : Ctx} (σ : State C Γ) : withOutside σ (outside σ) = σ := rfl

theorem outside_withOutside {Γ : Ctx} (σ : State C Γ) (w : Outside C) :
    outside (withOutside σ w) = w := rfl

theorem withOutside_withOutside {Γ : Ctx} (σ : State C Γ) (w w' : Outside C) :
    withOutside (withOutside σ w) w' = withOutside σ w' := rfl

/-- An outcome with its end state's outside replaced. -/
def Out.withOutside {H : HTy} {Γ : Ctx} (w : Outside C) (o : Out C H Γ) : Out C H Γ :=
  ⟨Mutability.withOutside o.st w, o.ext⟩

theorem TRes.map_map {α β γ : Type} (f : α → β) (g : β → γ) (x : TRes α) :
    (x.map f).map g = x.map (g ∘ f) := by
  cases x <;> rfl

/-! ## Loops -/

namespace TLoop

open Solidity.TLoop

variable {α β : Type}

theorem step_map (f : α → β) {body : α → TRes α} {c : α → TRes Bool} {body' : β → TRes β}
    {c' : β → TRes Bool} (hb : ∀ a, body' (f a) = (body a).map f) (hc : ∀ a, c' (f a) = c a)
    (a : α) : step body' c' (f a) = Sum.map f (Except.map f) (step body c a) := by
  unfold step
  rw [hc a, hb a]
  cases c a with
  | error e => rfl
  | ok b =>
    cases b with
    | false => rfl
    | true => cases body a <;> rfl

theorem iterN_map (f : α → β) {body : α → TRes α} {c : α → TRes Bool} {body' : β → TRes β}
    {c' : β → TRes Bool} (hb : ∀ a, body' (f a) = (body a).map f) (hc : ∀ a, c' (f a) = c a) :
    (n : Nat) → (a : α) → iterN body' c' n (f a) = Sum.map f (Except.map f) (iterN body c n a)
  | 0, _ => rfl
  | n + 1, a => by
    simp only [iterN]
    rw [step_map f hb hc a]
    cases step body c a with
    | inl τ => exact iterN_map f hb hc n τ
    | inr r => rfl

/-- **A loop's run commutes with a map** its body and condition commute
with. -/
theorem run_map (f : α → β) {body : α → TRes α} {c : α → TRes Bool} {body' : β → TRes β}
    {c' : β → TRes Bool} (hb : ∀ a, body' (f a) = (body a).map f) (hc : ∀ a, c' (f a) = c a)
    (a : α) : run body' c' (f a) = (run body c a).map f := by
  by_cases hex : ∃ r n, iterN body c n a = .inr r
  · obtain ⟨r, n, hn⟩ := hex
    have h' : iterN body' c' n (f a) = .inr (r.map f) := by
      rw [iterN_map f hb hc n a, hn]
      rfl
    rw [run_of_iterN h', run_of_iterN hn]
  · have hex' : ¬ ∃ r n, iterN body' c' n (f a) = .inr r := by
      rintro ⟨r, n, hn⟩
      rw [iterN_map f hb hc n a] at hn
      cases h : iterN body c n a with
      | inl τ => rw [h] at hn; cases hn
      | inr r₀ => exact hex ⟨r₀, n, h⟩
    unfold run
    simp only [hex, hex', dite_false]
    rfl

end TLoop

/-! ## Expressions that do not read the state -/

section Eval

variable {Γ : Ctx} (σ : State C Γ) (w : Outside C)

theorem Simple.evalT_withOutside {p : PrimTy} : (s : Simple C Γ p) →
    (Val.simple s).readsState = false → s.evalT (withOutside σ w) = s.evalT σ
  | .lit .., _ => rfl
  | .bool _, _ => rfl
  | .local _, _ => rfl
  | .env .., h => by simp only [Val.readsState, Bool.true_eq_false] at h

theorem Val.evalT_withOutside : {p : PrimTy} → (v : Val C Γ p) → v.readsState = false →
    v.evalT (withOutside σ w) = v.evalT σ
  | _, .simple s, h => congrArg Except.ok (Simple.evalT_withOutside σ w s h)
  | _, .read _, h => by simp only [Val.readsState, Bool.true_eq_false] at h
  | _, .readMem _, h => by simp only [Val.readsState, Bool.true_eq_false] at h
  | _, .len .., h => by simp only [Val.readsState, Bool.true_eq_false] at h
  | _, .mlen .., h => by simp only [Val.readsState, Bool.true_eq_false] at h
  | _, .hash .., h => by simp only [Val.readsState, Bool.true_eq_false] at h
  | _, .binop op _ hq a b, h => by
    simp only [Val.readsState, Bool.or_eq_false_iff] at h
    simp only [Val.evalT, Val.evalT_withOutside a h.1, Val.evalT_withOutside b h.2]
  | _, .unop op _ hq a, h => by
    simp only [Val.readsState] at h
    simp only [Val.evalT, Val.evalT_withOutside a h]
  | _, .ternary c a b, h => by
    simp only [Val.readsState, Bool.or_eq_false_iff] at h
    simp only [Val.evalT, Val.evalT_withOutside c h.1.1, Val.evalT_withOutside a h.1.2,
      Val.evalT_withOutside b h.2]
  | _, .modular op a b k, h => by
    simp only [Val.readsState, Bool.or_eq_false_iff] at h
    simp only [Val.evalT, Val.evalT_withOutside a h.1.1, Val.evalT_withOutside b h.1.2,
      Val.evalT_withOutside k h.2]

theorem Val.evalT_withOutside_pure {p : PrimTy} (v : Val C Γ p) (h : v.readsIn .pure = true) :
    v.evalT (withOutside σ w) = v.evalT σ := by
  apply Val.evalT_withOutside σ w v
  simpa only [Val.readsIn, bne_self_eq_false, Bool.false_or, Bool.not_eq_true'] using h

theorem Args.evalT_withOutside : {ps : Ctx} → (as : Args C Γ ps) → as.readsIn .pure = true →
    as.evalT (withOutside σ w) = as.evalT σ
  | _, .nil, _ => rfl
  | _, .snoc xs _ _ e, h => by
    have h' : (Args.readsIn .pure xs && e.readsIn .pure) = true := h
    rw [Bool.and_eq_true] at h'
    have hx := Args.evalT_withOutside xs h'.1
    have he := Val.evalT_withOutside_pure σ w e h'.2
    change (Args.evalT (withOutside σ w) xs >>= fun r =>
        e.evalT (withOutside σ w) >>= fun v => pure ((v, r) : TEnv C σ.H (.val _ :: _))) =
      (Args.evalT σ xs >>= fun r => e.evalT σ >>= fun v => pure ((v, r) : TEnv C σ.H (.val _ :: _)))
    rw [hx, he]
    cases Args.evalT σ xs <;> cases Val.evalT σ e <;> rfl
  | _, .snocStorage as _ _ _, h => by
    have h' : (Args.readsIn .pure as && Mutability.pure != .pure) = true := h
    simp only [bne_self_eq_false, Bool.and_false, Bool.false_eq_true] at h'
  | _, .snocMemory as _ _ _, h => by
    have h' : (Args.readsIn .pure as && Mutability.pure != .pure) = true := h
    simp only [bne_self_eq_false, Bool.and_false, Bool.false_eq_true] at h'

theorem RevPart.evalT_withOutside (d : RevPart C Γ)
    (h : (match d with | .word v => v.readsIn .pure | _ => true) = true) :
    d.evalT (withOutside σ w) = d.evalT σ := by
  cases d with
  | bytes => rfl
  | sel => rfl
  | word v => simp only [RevPart.evalT, Val.evalT_withOutside_pure σ w v h]
  | mem =>
    dsimp only [RevPart.evalT, MPath.mvalT, withOutside]
    split <;> rfl

theorem RevPart.mapM_withOutside : (d : List (RevPart C Γ)) →
    (∀ p ∈ d, (match p with | .word v => v.readsIn .pure | _ => true) = true) →
    d.mapM (·.evalT (withOutside σ w)) = d.mapM (·.evalT σ)
  | [], _ => rfl
  | p :: d, h => by
    simp only [List.mapM_cons, RevPart.evalT_withOutside σ w p (h p List.mem_cons_self),
      RevPart.mapM_withOutside d (fun q hq => h q (List.mem_cons_of_mem _ hq))]

end Eval

/-! ## Entering and leaving a call -/

theorem RetBinders.enterT_withOutside {ps : Ctx} (w : Outside C) : {ρ : Ctx} →
    (bs : RetBinders ρ) → bs.noMem = true → (τ : State C ps) →
    bs.enterT (withOutside τ w) = Out.withOutside w (bs.enterT τ)
  | _, .nil, _, _ => rfl
  | _, .snoc bs p _, h, τ => by
    show (⟨(bs.enterT (withOutside τ w)).st.push (t := .val p) (PrimTy.dflt p),
      (bs.enterT (withOutside τ w)).ext⟩ : Out C τ.H _) = _
    rw [RetBinders.enterT_withOutside w bs h τ]
    rfl
  | _, .snocMem .., h, _ => absurd h Bool.false_ne_true

theorem CallRet.enterT_withOutside {Γ Γ' rs ps : Ctx} (w : Outside C) (ret : CallRet Γ rs Γ')
    (hm : ret.noMem = true) (τ : State C ps) :
    ret.enterT (withOutside τ w) = Out.withOutside w (ret.enterT τ) := by
  cases ret with
  | none | val | storage => rfl
  | rets bs => exact RetBinders.enterT_withOutside w bs hm τ
  | mem => exact absurd hm Bool.false_ne_true

/-! ## Programs -/

section Progs

/-- The `within .pure` of a statement that only `nonpayable` admits. -/
theorem pure_beq_nonpayable : (Mutability.pure == .nonpayable) = false := rfl

/-- A call whose arguments read no state, with no memory return, of a body
that commutes with replacing the outside, commutes with it too. -/
theorem call_withOutside {Γ Γ' ps rs Γf : Ctx} (args : Args C Γ ps) (ret : CallRet Γ rs Γ')
    (body : Prog C (rs ++ ps) Γf) (ha : args.readsIn .pure = true) (hm : ret.noMem = true)
    (ih : ∀ (τ : State C (rs ++ ps)) (w : Outside C),
      Prog.run (withOutside τ w) body = (Prog.run τ body).map (Out.withOutside w))
    (σ : State C Γ) (w : Outside C) :
    TRun.call args ret body.ext body.runR (withOutside σ w) =
      (TRun.call args ret body.ext body.runR σ).map (Out.withOutside w) := by
  rw [TRun.call_eq, TRun.call_eq, Args.evalT_withOutside σ w args ha]
  cases args.evalT σ with
  | error e => rfl
  | ok a =>
    show TRun.callFrom ret body.ext body.runR (withOutside σ w)
        (ret.enterT (withOutside (σ.withEnv a) w)) =
      (TRun.callFrom ret body.ext body.runR σ (ret.enterT (σ.withEnv a))).map (Out.withOutside w)
    rw [CallRet.enterT_withOutside w ret hm (σ.withEnv a)]
    generalize ret.enterT (σ.withEnv a) = o₁
    unfold TRun.callFrom
    have hb : body.runR (withOutside o₁.st w) = (body.runR o₁.st).map (Out.withOutside w) :=
      ih o₁.st w
    change (body.runR (withOutside o₁.st w) >>= _) = _
    rw [hb]
    cases body.runR o₁.st <;> rfl

mutual

/-- **A pure statement commutes with replacing the outside.** -/
theorem Stmt.run_withOutside : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → Stmt.within .pure s = true →
    (σ : State C Γ) → (w : Outside C) →
    Stmt.run (withOutside σ w) s = (Stmt.run σ s).map (Out.withOutside w)
  | _, _, .assign .., h, _, _ => absurd h Bool.false_ne_true
  | _, _, .rebind _ r, h, _, _ => by
    cases r <;> exact absurd h Bool.false_ne_true
  | _, _, .assignLocal i r, h, σ, w => by
    change TRun.assignLocal i r (withOutside σ w) = (TRun.assignLocal i r σ).map _
    simp only [TRun.assignLocal, Val.evalT_withOutside_pure σ w r h]
    cases r.evalT σ <;> rfl
  | _, _, .declLocal p _ init, h, σ, w => by
    change TRun.declLocal p init (withOutside σ w) = (TRun.declLocal p init σ).map _
    cases init with
    | none => rfl
    | some e =>
      simp only [TRun.declLocal, Val.evalT_withOutside_pure σ w e h]
      cases e.evalT σ <;> rfl
  | _, _, .declStorage R _ init, h, σ, w => by
    cases init with
    | none => rfl
    | some r => cases r <;> exact absurd h Bool.false_ne_true
  | _, _, .opAssign op _ _ l r, h, σ, w => by
    have h' : (r.readsIn .pure && l.writableIn .pure) = true := h
    rw [Bool.and_eq_true] at h'
    change TRun.opAssign op l r (withOutside σ w) = (TRun.opAssign op l r σ).map _
    cases l with
    | «local» i =>
      simp only [TRun.opAssign, Val.evalT_withOutside_pure σ w r h'.1]
      cases r.evalT σ with
      | error e => rfl
      | ok v =>
        simp only [bind, Except.bind, OpLoc.storeT]
        dsimp only [withOutside]
        cases compoundT op _ (PrimTy.key (TEnv.get i σ.env)) (PrimTy.key v) <;> rfl
    | _ => exact absurd h'.2 Bool.false_ne_true
  | _, _, .incDec op _ l, h, σ, w => by
    change TRun.incDec op l (withOutside σ w) = (TRun.incDec op l σ).map _
    cases l with
    | «local» i =>
      simp only [TRun.incDec, OpLoc.bumpT, bind, Except.bind]
      dsimp only [withOutside]
      cases Solidity.bumpT op _ (PrimTy.key (TEnv.get i σ.env)) <;> rfl
    | _ => exact absurd h Bool.false_ne_true
  | _, _, .assignIncDec j op _ l _, h, σ, w => by
    change TRun.assignIncDec j op l (withOutside σ w) = (TRun.assignIncDec j op l σ).map _
    cases l with
    | «local» i =>
      simp only [TRun.assignIncDec, OpLoc.bumpT, bind, Except.bind]
      dsimp only [withOutside]
      cases Solidity.bumpT op _ (PrimTy.key (TEnv.get i σ.env)) <;> rfl
    | _ => exact absurd h Bool.false_ne_true
  | _, _, .assignLocalPush .., h, _, _ => absurd h Bool.false_ne_true
  | _, _, .push .., h, _, _ => absurd h Bool.false_ne_true
  | _, _, .pop _, h, _, _ => absurd h Bool.false_ne_true
  | _, _, .transfer .., h, _, _ => absurd h Bool.false_ne_true
  | _, _, .send .., h, _, _ => absurd h Bool.false_ne_true
  | _, _, .declMem .., h, _, _ => absurd h Bool.false_ne_true
  | _, _, .rebindMem .., h, _, _ => absurd h Bool.false_ne_true
  | _, _, .assignFromMem .., h, _, _ => absurd h Bool.false_ne_true
  | _, _, .assignMem .., h, _, _ => absurd h Bool.false_ne_true
  | _, _, .delete _, h, _, _ => absurd h Bool.false_ne_true
  | _, _, .deleteMem .., h, _, _ => absurd h Bool.false_ne_true
  | _, _, .assignNew .., h, _, _ => absurd h Bool.false_ne_true
  | _, _, .pushOpAssign .., h, _, _ => absurd h Bool.false_ne_true
  | _, _, .pushIncDec .., h, _, _ => absurd h Bool.false_ne_true
  | _, _, .callReceiver .., h, _, _ => absurd h Bool.false_ne_true
  | _, _, .callReceiverPush .., h, _, _ => absurd h Bool.false_ne_true
  | _, _, .catchData .., h, _, _ => absurd h Bool.false_ne_true
  | _, _, .tryCall .., h, _, _ => by
    simp only [Stmt.within, pure_beq_nonpayable, Bool.false_and, Bool.false_eq_true] at h
  | _, _, .ite c thn els, h, σ, w => by
    have h' : (c.readsIn .pure && Prog.within .pure thn && Prog.within .pure els) = true := h
    simp only [Bool.and_eq_true] at h'
    change TRun.ite c thn.ext thn.runR els.ext els.runR (withOutside σ w) =
      (TRun.ite c thn.ext thn.runR els.ext els.runR σ).map _
    simp only [TRun.ite, Val.evalT_withOutside_pure σ w c h'.1.1]
    cases c.evalT σ with
    | error e => rfl
    | ok v =>
      simp only [bind, Except.bind]
      split
      · change (Prog.run (withOutside σ w) thn).map _ = _
        rw [Prog.run_withOutside thn h'.1.2 σ w, TRes.map_map, TRes.map_map]
        rfl
      · change (Prog.run (withOutside σ w) els).map _ = _
        rw [Prog.run_withOutside els h'.2 σ w, TRes.map_map, TRes.map_map]
        rfl
  | _, _, .require c, h, σ, w => by
    change TRun.require c (withOutside σ w) = (TRun.require c σ).map _
    simp only [TRun.require, Val.evalT_withOutside_pure σ w c h]
    cases c.evalT σ with
    | error e => rfl
    | ok v =>
      simp only [bind, Except.bind]
      split <;> rfl
  | _, _, .assert c, h, σ, w => by
    change TRun.assert c (withOutside σ w) = (TRun.assert c σ).map _
    simp only [TRun.assert, Val.evalT_withOutside_pure σ w c h]
    cases c.evalT σ with
    | error e => rfl
    | ok v =>
      simp only [bind, Except.bind]
      split <;> rfl
  | _, _, .revert, _, _, _ => rfl
  | _, _, .assumeFalse, _, _, _ => rfl
  | _, _, .call _ args ret body, h, σ, w => by
    have h' : (args.readsIn .pure && ret.noMem && Prog.within .pure body) = true := h
    simp only [Bool.and_eq_true] at h'
    exact call_withOutside args ret body h'.1.1 h'.1.2 (Prog.run_withOutside body h'.2) σ w
  | _, _, .callRec _ _ args ret body, h, σ, w => by
    have h' : (args.readsIn .pure && ret.noMem && Prog.within .pure (body ())) = true := h
    simp only [Bool.and_eq_true] at h'
    exact call_withOutside args ret (body ()) h'.1.1 h'.1.2
      (Prog.run_withOutside (body ()) h'.2) σ w
  | _, _, .loop _ c body, h, σ, w => by
    have h' : (c.readsIn .pure && Prog.within .pure body) = true := h
    rw [Bool.and_eq_true] at h'
    rw [Stmt.run_loop, Stmt.run_loop]
    refine TLoop.run_map (Out.withOutside w) ?_ ?_ ⟨σ, List.prefix_refl _⟩
    · intro o
      show (Prog.run (withOutside o.st w) body).map _ = _
      rw [Prog.run_withOutside body h'.2 o.st w, TRes.map_map, TRes.map_map]
      rfl
    · intro o
      exact Val.evalT_withOutside_pure o.st w c h'.1
  | _, _, .block body, h, σ, w => by
    change ((Prog.run (withOutside σ w) body)).map _ = ((Prog.run σ body).map _).map _
    rw [Prog.run_withOutside body h σ w, TRes.map_map, TRes.map_map]
    rfl
  | _, _, .revertData d, h, σ, w => by
    have hall : ∀ p ∈ d, (match p with | .word v => v.readsIn .pure | _ => true) = true :=
      List.all_eq_true.1 h
    change TRun.revertData d (withOutside σ w) = (TRun.revertData d σ).map _
    have hm : d.mapM (·.evalT (withOutside σ w)) = d.mapM (·.evalT σ) := by
      exact RevPart.mapM_withOutside σ w d hall
    simp only [TRun.revertData, hm]
    cases d.mapM (·.evalT σ) <;> rfl
  termination_by structural _ _ s => s

/-- **A pure program commutes with replacing the outside.** -/
theorem Prog.run_withOutside : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → Prog.within .pure P = true →
    (σ : State C Γ) → (w : Outside C) →
    Prog.run (withOutside σ w) P = (Prog.run σ P).map (Out.withOutside w)
  | _, _, .nil, _, _, _ => rfl
  | _, _, .cons s P, h, σ, w => by
    have h' : (Stmt.within .pure s && Prog.within .pure P) = true := h
    rw [Bool.and_eq_true] at h'
    change TRun.seq s.runR P.runR (withOutside σ w) = (TRun.seq s.runR P.runR σ).map _
    unfold TRun.seq
    have hs : s.runR (withOutside σ w) = (s.runR σ).map (Out.withOutside w) :=
      Stmt.run_withOutside s h'.1 σ w
    rw [hs]
    cases s.runR σ with
    | error e => rfl
    | ok o =>
      have hp : P.runR (withOutside o.st w) = (P.runR o.st).map (Out.withOutside w) :=
        Prog.run_withOutside P h'.2 o.st w
      show (P.runR (withOutside o.st w)).map _ = ((P.runR o.st).map _).map _
      rw [hp, TRes.map_map, TRes.map_map]
      rfl
  termination_by structural _ _ P => P

end

end Progs

/-! ## Consequences -/

/-- **S3.1 (pure): a pure body's outcome does not depend on the state.**  From
any two outsides `w` and `w'` (storage, ledger, balance, transaction) the
runs agree but for the outside itself: `function sq(uint x) pure returns
(uint) { return x * x; }` returns the same value, or overflows alike,
whatever the contract's storage or `msg.value`. -/
theorem Prog.pure_independent {Γ Γ' : Ctx} (P : Prog C Γ Γ') (hw : Prog.within .pure P = true)
    (σ : State C Γ) (w w' : Outside C) :
    Prog.run (withOutside σ w) P = (Prog.run (withOutside σ w') P).map (Out.withOutside w) := by
  rw [Prog.run_withOutside P hw σ w, Prog.run_withOutside P hw σ w', TRes.map_map]
  rfl

/-- A pure body halts, and how, independently of the outside. -/
theorem Prog.pure_halt_independent {Γ Γ' : Ctx} (P : Prog C Γ Γ')
    (hw : Prog.within .pure P = true) (σ : State C Γ) (w : Outside C) :
    (Prog.run (withOutside σ w) P).halt? = (Prog.run σ P).halt? := by
  rw [Prog.run_withOutside P hw σ w]
  cases Prog.run σ P <;> rfl

/-- **A pure body's result** (every local it leaves, its return values among
them) is the one it computes from any other outside. -/
theorem Prog.pure_local_independent {Γ Γ' : Ctx} {P : Prog C Γ Γ'}
    (hw : Prog.within .pure P = true) {σ : State C Γ} {o : Out C σ.H Γ'}
    (h : Prog.run σ P = .ok o) (w : Outside C) :
    Prog.run (withOutside σ w) P = .ok (Out.withOutside w o) ∧
      (Out.withOutside w o).st.env = o.st.env := by
  refine ⟨?_, rfl⟩
  rw [Prog.run_withOutside P hw σ w, h]
  rfl

/-- A pure body is in particular read-only: it commits its entry's
outside (`Prog.committed_readOnly`), so its successful run from `withOutside σ
w` ends with outside `w`, the transaction included. -/
theorem Prog.pure_outside {Γ Γ' : Ctx} {P : Prog C Γ Γ'} (hw : Prog.within .pure P = true)
    {σ : State C Γ} {o : Out C σ.H Γ'} (h : Prog.run σ P = .ok o) :
    outside o.st = outside σ := by
  have hg := (Prog.run_frame P hw 0 h).1
  have hk := hg.keeps pure_ne_nonpayable
  simp only [outside, hk.1, hk.2, hg.selfBalance pure_ne_nonpayable, hg.tx]

end Solidity.Theory.Mutability
