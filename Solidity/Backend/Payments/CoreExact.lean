import Solidity.Evm.Correct

/-!
# G43: the core compiler never refuses a payment the typed run made

`Evm.compile_correct` (`Solidity/Evm/Correct.lean`) lists a third outcome
for code that `pays`: the machine reverts at a refused payment while the
typed run succeeds. This module proves that outcome never happens on the
core fragment, with no premise beyond `compile_correct`'s own: `Sim.funds`
(the typed balance is the machine's) and the premise `Sim.oracle` (the typed
world's `ext` answers each (recipient, amount) as the machine's `accepts`
does) make `State.canPay` the machine's check, so a `transfer` the typed run
makes is one the machine makes, and one it refuses both refuse
(`transfer_paid`). The disjunct was vacuous under those premises (the
never-constructed `refused` case, G04 R32). Recipients are a fixed
(address, amount) oracle: no recipient code, gas or stipend is modelled.

The proof re-runs `stmt_sim`/`prog_sim`'s structural recursion with the
`pays` flag of `StmtOut` fixed at `false`, which rules out its `refused` arm
and its paid `diverge` arm. Every statement lemma of `Evm/Stmt.lean` other
than `transfer_sim` already has `pays = false`; `ite_sim` and `call_family`
fix the flag to the sub-programs' `Prog.pays`, so the generic forms are
restated here (`ite_flags`, `call_flags`). Nothing in `Evm/` is edited and no
frozen statement changes: `compile_correct` stands, and `compile_paid` is the
separate, stronger statement.

`compile_success` is the compiler-success direction G43 needs (OBL-SUCCESS):
a typed run that succeeds is matched by a machine run that succeeds, in a
represented state.
-/

namespace Solidity.Evm.Payments

open Solidity.Evm
open Semantics (structDef lookupBy)
open Solidity (Ctx Idx Ext TEnv State SRef TRes HTy)

variable {C : Contract}

section Generic

variable {L b : Nat} {Γ : Ctx} {F : Frag Γ} {σ : State C Γ} {m : Machine}

/-- `ite_sim` with the branches' flags arbitrary. -/
theorem ite_flags {Γ₁ Γ₂ : Ctx} (c : Solidity.Val C Γ .bool)
    (t : Solidity.Prog C Γ Γ₁) (e : Solidity.Prog C Γ Γ₂) {F₁ : Frag Γ₁}
    {F₂ : Frag Γ₂} {L' : Nat} {sh₁ p₁ a₁ sh₂ p₂ a₂ : Bool} (hm : Sim C L b F σ m)
    (hwc : valIn F c = true)
    (iht : StmtOut C L' b F₁ sh₁ p₁ a₁
      (Solidity.Prog.run σ t) (run (compileProg b t) m) m)
    (ihe : StmtOut C L' b F₂ sh₂ p₂ a₂
      (Solidity.Prog.run σ e) (run (compileProg b e) m) m) :
    StmtOut C L' b ((F₁.restrict Γ).meet (F₂.restrict Γ)) (sh₁ || sh₂) (p₁ || p₂) (a₁ || a₂)
      (Solidity.Stmt.run σ (.ite c t e)) (run (compileStmt b (.ite c t e)) m) m := by
  show StmtOut C L' b _ _ _ _ (Solidity.TRun.ite c t.ext t.runR e.ext e.runR σ) _ m
  simp only [compileStmt, List.append_assoc]
  rcases val_sim c hm hwc with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
  · obtain rfl := hrc.bool_inv
    rw [run_append_ok hrunc]
    simp only [Solidity.TRun.ite, hvc, bind, Except.bind, Solidity.boolT]
    cases vc
    · rw [run_append_skip (m' := m) (k := (compileProg b t).length + 1) rfl, exec_skip_append,
        show exec ([Instr.jump (compileProg b e).length] ++ compileProg b e) 1 m =
          run (compileProg b e) m from rfl]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact (ihe.drop e.ext).weaken (fun i _ hg hd => Frag.get_meet_right _ _ i hg hd)
        (by simp_all only [Bool.or_true, implies_true])
        (by simp_all only [Bool.or_true, implies_true])
        (by simp_all only [Bool.or_true, implies_true])
    · rw [run_append_skip (m' := m) (k := 0) rfl]
      simp only [↓reduceIte]
      refine (StmtOut.drop (sh := sh₁) (pays := p₁) (asserts := a₁) t.ext ?_).weaken
        (fun i _ hg hd => Frag.get_meet _ _ i hg hd)
        (by simp_all only [Bool.true_or, implies_true])
        (by simp_all only [Bool.true_or, implies_true])
        (by simp_all only [Bool.true_or, implies_true])
      rcases iht with ⟨τ', m', hτ', hrun', hst', hk', hm'⟩ | ⟨hτ', hrun'⟩ | ⟨ha, hτ', hrun'⟩ |
          ⟨hp, hrun', τ', m', hτ', hk', hm'⟩ | ⟨hτ', hrun'⟩
      · refine .inl ⟨τ', m', hτ', ?_, hst', hk', hm'⟩
        change run _ m = _
        rw [run_append_skip (k := 0) hrun']
        exact exec_length (.jump (compileProg b e).length :: compileProg b e) m' |>.trans rfl
      · exact .inr ⟨hτ', run_append_revert hrun'⟩
      · exact .panic ha ⟨hτ', run_append_revert hrun'⟩
      · exact .refused hp ⟨run_append_revert hrun', τ', m', hτ', hk', hm'⟩
      · exact .diverge ⟨hτ', divOut_append hrun'⟩
  · exact .inr ⟨by simp only [Solidity.TRun.ite, hvc, bind, Except.bind],
      run_append_revert hrunc⟩

/-- `call_family` with the body's `pays` flag arbitrary. -/
theorem call_flags {Γ' ps rs Γf : Ctx} (f : Name) (args : Solidity.Args C Γ ps)
    (ret : Solidity.CallRet Γ rs Γ') (body : Solidity.Prog C (rs ++ ps) Γf) {pays : Bool}
    {F' : Frag Γ'} (hm : Sim C L b F σ m)
    (hw : inFrag F (.call f args ret body) = some F')
    (ih : ∀ {G : Frag Γf} {τ : State C (rs ++ ps)} {m₂ : Machine},
      inFragP (Frag.init (rs ++ ps)) body = some G →
      Sim C L (b + Γ.length) (Frag.init (rs ++ ps)) τ m₂ →
      StmtOut C (L + Prog.pushes body) (b + Γ.length) G (Prog.shrinks body) pays
        (Prog.asserts body) (Solidity.Prog.run τ body)
        (run (compileProg (b + Γ.length) body) m₂) m₂) :
    StmtOut C (L + Stmt.pushes (.call f args ret body)) b F'
      (Stmt.shrinks (.call f args ret body)) pays
      (Stmt.asserts (.call f args ret body)) (Solidity.Stmt.run σ (.call f args ret body))
      (run (compileStmt b (.call f args ret body)) m) m := by
  obtain ⟨hwa, ⟨G, hb⟩, hret⟩ := call_frag hw
  cases ret with
  | none =>
    cases hret
    exact callNone_sim f args body (Nat.le_add_right _ _) hm hwa fun hm₂ => ⟨G, ih hb hm₂⟩
  | val p r res =>
    cases hret
    exact callVal_sim f args p r res body (Nat.le_add_right _ _) hm hwa
      fun hm₂ => ⟨G, ih hb hm₂⟩
  | rets _ => cases hret
  | mem _ _ _ _ => cases hret
  | storage _ _ => cases hret

/-- **A payment the typed run makes, the machine makes**: `transfer_sim`
with `pays = false`. The typed run's `canPay` is the machine's balance check
and `accepts` (`Sim.funds`, `Sim.oracle`), so the two refuse together and
both revert; the refused-payment outcome does not arise. -/
theorem transfer_paid (r a : Solidity.Val C Γ .uint)
    (hm : Sim C L b F σ m) (hwr : valIn F r = true)
    (hwa : valIn F a = true) :
    StmtOut C L b F false false false (Solidity.TRun.transfer r a σ)
      (run (compileVal b r ++ compileVal b a ++ [.call] ++ assertTop) m) m := by
  simp only [List.append_assoc]
  rcases val_sim r hm hwr with ⟨vr, wr, hvr, hrv, hrunr⟩ | ⟨hvr, hrunr⟩
  · obtain ⟨x, rfl, hx1⟩ := hrv
    rw [run_append_ok hrunr]
    rcases val_sim a (hm.push _) hwa with ⟨va, wa, hva, hra, hruna⟩ | ⟨hva, hruna⟩
    · obtain ⟨y, rfl, hy1⟩ := hra
      rw [run_append_ok hruna]
      have hc : σ.canPay vr va =
          (decide (y.1 ≤ m.bal m.self) && m.accepts x y) := by
        simp only [State.canPay, hm.funds, hy1, Int.ofNat_le]
        exact congrArg (fun z => decide (y.1 ≤ m.bal m.self) && z)
          (hm.oracle vr va x y hx1 hy1)
      obtain ⟨-, -, -, hself⟩ := hm.env
      have hpay : ∀ c : Fin W, netAt (σ.pay vr y.1).net c.1 =
          if x = m.self then netAt σ.net c.1 else if c = x then netAt σ.net x.1 - y.1
          else netAt σ.net c.1 := by
        intro c
        rw [netAt_pay, hx1, hself]
        simp only [Int.ofNat_inj, Fin.val_inj]
      have hns : netAt (σ.pay vr y.1).net m.self.1 = 0 := by
        rw [hpay m.self]
        split
        · exact hm.netSelf
        · rename_i hxs
          rw [if_neg (fun h => hxs h.symm)]
          exact hm.netSelf
      by_cases hrf : m.bal m.self < y.1 ∨ m.accepts x y = false
      · have hn : σ.canPay vr va = false := by
          rw [hc]
          rcases hrf with hrf | hrf
          · simp only [show ¬ y.1 ≤ m.bal m.self by omega, decide_false, Bool.false_and]
          · simp only [hrf, Bool.and_false]
        refine .inr ⟨?_, ?_⟩
        · simp only [Solidity.TRun.transfer, hvr, hva, bind, Except.bind, hn,
            Bool.false_eq_true, ↓reduceIte]
          rfl
        · simp only [run, assertTop, List.cons_append, List.nil_append,
            Machine.push, exec_cons_zero, Instr.step, hrf, ↓reduceIte, Machine.next,
            Out.ok_bind, exec_nil, Out.revert_bind]
      · have hrf' : y.1 ≤ m.bal m.self ∧ m.accepts x y = true := by
          simp only [not_or, Bool.not_eq_false] at hrf
          exact ⟨by omega, hrf.2⟩
        have hn : σ.canPay vr va = true := by
          simp only [hc, hrf'.1, decide_true, hrf'.2, Bool.and_self]
        have hres : Solidity.TRun.transfer r a σ =
            .ok ⟨σ.pay vr y.1, List.prefix_refl _⟩ := by
          simp only [Solidity.TRun.transfer, hvr, hva, bind, Except.bind, hn,
            ↓reduceIte, hy1]
          rfl
        rw [hres]
        have hbal := balance_pay σ vr y.1 (by rw [hm.funds]; exact_mod_cast hrf'.1)
        rw [hx1, hself] at hbal
        simp only [Int.ofNat_inj, Fin.val_inj] at hbal
        by_cases hxe : x = m.self
        · have hb := hm.book _ _ m.bal m.bal₀ (fun c hcs => by
            rw [hpay c, if_pos hxe]; exact hm.net c hcs) hns (by rw [hbal, if_pos hxe, hm.funds])
          refine .inl ⟨⟨σ.pay vr y.1, List.prefix_refl _⟩, m, rfl, ?_, rfl, Keeps.refl m, hb⟩
          subst hxe
          simp only [run, assertTop, List.cons_append, List.nil_append, Machine.push,
              exec_cons_zero, Instr.step, hrf, ↓reduceIte, Machine.next, Out.ok_bind,
              Nat.succ_ne_self, exec_cons_succ, exec_nil]
        · simp only [not_or, Bool.not_eq_false] at hrf
          refine .inl ⟨⟨σ.pay vr y.1, List.prefix_refl _⟩, { m with bal := pay m.bal m.self x y.1 },
            rfl, ?_, rfl, ⟨fun _ _ => rfl, fun _ _ _ => Nat.le_refl _⟩,
            hm.book vr y.1 _ m.bal₀ (fun c hcs => ?_) hns ?_⟩
          · simp only [run, assertTop, List.cons_append, List.nil_append, Machine.push,
              exec_cons_zero, Instr.step, hrf, Bool.true_eq_false, or_self, ↓reduceIte, hxe,
              Out.ok_bind, Nat.succ_ne_self, exec_cons_succ, exec_nil]
          · have h1 := hm.net c hcs
            rw [hpay c]
            simp only [pay, upd, hxe, ↓reduceIte]
            by_cases hcx : c = x
            · subst hcx; simp only [↓reduceIte]; omega
            · simp only [hcx, hcs, ↓reduceIte]; exact h1
          · rw [hbal, if_neg hxe, hm.funds]
            simp only [pay, upd, hxe, if_neg (Ne.symm hxe), ↓reduceIte]
            omega
    · exact .inr ⟨by simp only [Solidity.TRun.transfer, hvr, hva, bind, Except.bind],
        run_append_revert hruna⟩
  · exact .inr ⟨by simp only [Solidity.TRun.transfer, hvr, bind, Except.bind],
      run_append_revert hrunr⟩

/-- `transfer_family` with `pays = false`. -/
theorem transfer_family_paid (r a : Solidity.Val C Γ .uint) {F' : Frag Γ}
    (hm : Sim C L b F σ m) (hw : inFrag F (.transfer r a) = some F') :
    StmtOut C L b F' false false false (Solidity.Stmt.run σ (.transfer r a))
      (run (compileStmt b (.transfer r a)) m) m := by
  simp only [inFrag] at hw
  obtain ⟨hok, rfl⟩ := Frag.guard_some hw
  simp only [Bool.and_eq_true] at hok
  exact transfer_paid r a hm hok.1 hok.2

/-- `stmt_sim_outside` at any flags: vacuous. -/
theorem outside_paid {Γ Γ' : Ctx} (s : Solidity.Stmt C Γ Γ') (h : Stmt.evmOutside s = true)
    {L b : Nat} {F : Frag Γ} {F' : Frag Γ'} {σ : State C Γ} {m : Machine} :
    Sim C L b F σ m → inFrag F s = some F' → L + Stmt.pushes s ≤ Lmax →
      StmtOut C (L + Stmt.pushes s) b F' (Stmt.shrinks s) false (Stmt.asserts s)
        (Solidity.Stmt.run σ s) (run (compileStmt b s) m) m :=
  fun _ hw _ => Option.noConfusion ((inFrag_outside _ _ h).symm.trans hw)

end Generic

mutual

/-- **`stmt_sim` with no refused payment**: the same outcomes, `pays` fixed
at `false`, so the machine reverts only where the typed run reverts or
panics, and faults only where it diverges. -/
theorem stmt_paid : ∀ {Γ Γ' : Ctx} (s : Solidity.Stmt C Γ Γ') {L b : Nat} {F : Frag Γ}
    {F' : Frag Γ'} {σ : State C Γ} {m : Machine},
    Sim C L b F σ m → inFrag F s = some F' → L + Stmt.pushes s ≤ Lmax →
      StmtOut C (L + Stmt.pushes s) b F' (Stmt.shrinks s) false (Stmt.asserts s)
        (Solidity.Stmt.run σ s) (run (compileStmt b s) m) m
  | _, _, .assign l r => fun hm hw _ => assign_family l r hm hw
  | _, _, .rebind i r => fun hm hw _ => rebind_family i r hm hw
  | _, _, .assignLocal i r => fun hm hw _ => assignLocal_family i r hm hw
  | _, _, .declLocal p x init => fun hm hw _ => declLocal_family p x init hm hw
  | _, _, .declStorage R x init => fun hm hw _ =>
    declStorage_family R x init hm hw
  | _, _, .opAssign op hop hp l r => fun hm hw _ =>
    opAssign_family op hop hp l r hm hw
  | _, _, .incDec op hp l => fun hm hw _ => incDec_family op hp l hm hw
  | _, _, .assignIncDec i op hp l hs => fun hm hw _ =>
    assignIncDec_family i op hp l hs hm hw
  | _, _, .push q v hd => fun hm hw hL => push_family q v hd hm hw hL
  | _, _, .pop q => fun hm hw _ => pop_family q hm hw
  | _, _, .transfer r a => fun hm hw _ => transfer_family_paid r a hm hw
  | _, _, .delete l => fun hm hw _ => delete_family l hm hw
  | _, _, .require c => fun hm hw _ => require_family c hm hw
  | _, _, .assert c => fun hm hw _ => assert_family c hm hw
  | _, _, .revert => fun _ _ _ => .inr ⟨rfl, rfl⟩
  | _, _, .assumeFalse => fun _ hw _ => nomatch hw
  | _, _, .ite c t e => fun hm hw hL => by
    obtain ⟨hwc, F₁, F₂, ht, he, rfl⟩ := ite_frag hw
    have hL' : _ + (Prog.pushes t + Prog.pushes e) ≤ Lmax := hL
    have hite : Stmt.pushes (.ite c t e) = Prog.pushes t + Prog.pushes e := rfl
    exact ite_flags (p₁ := false) (p₂ := false) c t e hm hwc
      ((prog_paid t hm ht (by omega)).mono (by omega) hL')
      ((prog_paid e hm he (by omega)).mono (by omega) hL')
  | _, _, .block body => fun hm hw hL => by
    obtain ⟨G, hb, rfl⟩ := block_frag hw
    exact block_sim body (prog_paid body hm hb hL)
  | _, _, .call f args ret body => fun hm hw hL =>
    call_flags f args ret body hm hw fun hb hm₂ => prog_paid body hm₂ hb hL
  | _, _, .send a0 a1 a2 a3 => outside_paid (.send a0 a1 a2 a3) rfl
  | _, _, .declMem a0 a1 a2 a3 a4 => outside_paid (.declMem a0 a1 a2 a3 a4) rfl
  | _, _, .rebindMem a0 a1 => outside_paid (.rebindMem a0 a1) rfl
  | _, _, .assignFromMem a0 a1 => outside_paid (.assignFromMem a0 a1) rfl
  | _, _, .assignMem a0 a1 => outside_paid (.assignMem a0 a1) rfl
  | _, _, .deleteMem a0 a1 => outside_paid (.deleteMem a0 a1) rfl
  | _, _, .assignNew a0 a1 a2 => outside_paid (.assignNew a0 a1 a2) rfl
  | _, _, .tryCall .. => fun _ hw _ => by rw [inFrag_tryCall] at hw; cases hw
  | _, _, .loop a c body => fun hm hw hL => by
    obtain ⟨-, -, hpay, -⟩ := loop_frag hw
    have h := loop_family a c body hm hw hL @fun _ hb hLb _ _ hm' => by
      rw [hpay]; exact prog_paid body hm' hb hLb
    have e₂ : Stmt.pays (Solidity.Stmt.loop a c body) = false := hpay
    rw [e₂] at h
    exact h
  | _, _, .assignLocalPush a0 a1 => outside_paid (.assignLocalPush a0 a1) rfl
  | _, _, .pushOpAssign a0 a1 a2 a3 a4 => outside_paid (.pushOpAssign a0 a1 a2 a3 a4) rfl
  | _, _, .pushIncDec a0 a1 a2 => outside_paid (.pushIncDec a0 a1 a2) rfl
  | _, _, .callReceiver a0 a1 a2 a3 a4 => outside_paid (.callReceiver a0 a1 a2 a3 a4) rfl
  | _, _, .callReceiverPush a0 a1 a2 a3 a4 a5 =>
    outside_paid (.callReceiverPush a0 a1 a2 a3 a4 a5) rfl
  | _, _, .callRec a0 a1 a2 a3 a4 => outside_paid (.callRec a0 a1 a2 a3 a4) rfl
  | _, _, .revertData a0 => outside_paid (.revertData a0) rfl
  | _, _, .catchData c rets sargs sbody self kind x body =>
    outside_paid (.catchData c rets sargs sbody self kind x body) rfl

/-- `prog_sim` with no refused payment. -/
theorem prog_paid : ∀ {Γ Γ' : Ctx} (P : Solidity.Prog C Γ Γ') {L b : Nat} {F : Frag Γ}
    {F' : Frag Γ'} {σ : State C Γ} {m : Machine},
    Sim C L b F σ m → inFragP F P = some F' → L + Prog.pushes P ≤ Lmax →
      StmtOut C (L + Prog.pushes P) b F' (Prog.shrinks P) false (Prog.asserts P)
        (Solidity.Prog.run σ P) (run (compileProg b P) m) m
  | _, _, .nil => fun hm hw _ => by
    simp only [inFragP, Option.some.injEq] at hw
    subst hw
    exact .inl ⟨_, _, rfl, rfl, rfl, Keeps.refl _, hm⟩
  | _, _, .cons s P => fun hm hw hL => by
    simp only [inFragP] at hw
    split at hw
    · rename_i F₁ hs
      have hL' : _ + (Stmt.pushes s + Prog.pushes P) ≤ Lmax := hL
      have he : Prog.pushes (.cons s P) = Stmt.pushes s + Prog.pushes P := rfl
      rw [he] at hL ⊢
      exact seq_sim (p₁ := false) (p₂ := false) s P (stmt_paid s hm hs (by omega))
        fun hm₁ => (prog_paid P hm₁ hw (by omega)).mono (by omega) hL'
    · cases hw

end

section Headline

variable {L b : Nat} {Γ Γ' : Ctx} {F : Frag Γ} {F' : Frag Γ'} {σ : State C Γ}
  {m : Machine}

/-- **The core compiler agrees exactly, payments included** (G43): under
`compile_correct`'s own premises, both succeed in related states, or both
revert (the typed run reverting, or panicking in code that asserts), or the
typed run diverges and the machine faults. Unlike `compile_exact`, no
`Prog.pays P = false` premise: a refused payment is a revert on both sides. -/
theorem compile_paid {P : Solidity.Prog C Γ Γ'} (hP : inFragP F P = some F')
    (hm : Sim C L b F σ m) (hL : L + Prog.pushes P ≤ Lmax) :
    (∃ o m', Solidity.Prog.run σ P = .ok o ∧ run (compileProg b P) m = .ok m' 0 ∧
      m'.stack = m.stack ∧ Sim C (L + Prog.pushes P) b F' o.st m') ∨
    ((Solidity.Prog.run σ P = .error .revert ∨
        (Prog.asserts P = true ∧ Solidity.Prog.run σ P = .error .panic)) ∧
      run (compileProg b P) m = .revert) ∨
    (Solidity.Prog.run σ P = .error .diverge ∧ run (compileProg b P) m = .fault) := by
  rcases prog_paid P hm hP hL with ⟨o, m', h1, h2, h3, -, h5⟩ | ⟨h1, h2⟩ | ⟨ha, h1, h2⟩ |
      ⟨hp, -⟩ | ⟨h1, h2 | ⟨hp, -⟩⟩
  · exact .inl ⟨o, m', h1, h2, h3, h5⟩
  · exact .inr (.inl ⟨.inl h1, h2⟩)
  · exact .inr (.inl ⟨.inr ⟨ha, h1⟩, h2⟩)
  · cases hp
  · exact .inr (.inr ⟨h1, h2⟩)
  · cases hp

/-- **Compiler success** (G43, OBL-SUCCESS): a typed run of a fragment
program that succeeds has a machine run that succeeds, its stack as it was,
in a state representing the typed one. -/
theorem compile_success {P : Solidity.Prog C Γ Γ'} (hP : inFragP F P = some F')
    (hm : Sim C L b F σ m) (hL : L + Prog.pushes P ≤ Lmax)
    {o : Solidity.Out C σ.H Γ'} (ho : Solidity.Prog.run σ P = .ok o) :
    ∃ m', run (compileProg b P) m = .ok m' 0 ∧ m'.stack = m.stack ∧
      Sim C (L + Prog.pushes P) b F' o.st m' := by
  rcases compile_paid hP hm hL with ⟨o', m', h1, h2, h3, h4⟩ | ⟨h1 | ⟨-, h1⟩, -⟩ | ⟨h1, -⟩
  · rw [ho] at h1
    cases h1
    exact ⟨m', h2, h3, h4⟩
  all_goals (rw [ho] at h1; cases h1)

/-- The machine reverts only where the typed run reverts or panics. -/
theorem compile_revert {P : Solidity.Prog C Γ Γ'} (hP : inFragP F P = some F')
    (hm : Sim C L b F σ m) (hL : L + Prog.pushes P ≤ Lmax)
    (hr : run (compileProg b P) m = .revert) :
    Solidity.Prog.run σ P = .error .revert ∨
      (Prog.asserts P = true ∧ Solidity.Prog.run σ P = .error .panic) := by
  rcases compile_paid hP hm hL with ⟨_, _, -, h2, -⟩ | ⟨h1, -⟩ | ⟨-, h2⟩
  · rw [hr] at h2; cases h2
  · exact h1
  · rw [hr] at h2; cases h2

/-- **`compile_storage` with no payment outcome**: from a fresh contract
(`Sim.init`, so `compile_paid`'s premises hold for every balance map and
address, with every payment accepted; refusals then come from the balance check), a fragment
program both runs, the machine holding every live `uint` the typed run reads,
or both revert, or the typed run diverges and the machine faults. -/
theorem compile_storage_paid {P : Solidity.Prog C [] Γ'} (hP : inFragP (Frag.init []) P = some F')
    (hL : Prog.pushes P < Lmax) (balance : Nat) (hb : balance < W) (bal : Fin W → Nat)
    (self : Fin W) (hbalance : balance = bal self) :
    (∃ o m', Solidity.Prog.run (freshT C balance hb self) P = .ok o ∧
        run (compileProg 0 P) (Machine.init bal self) = .ok m' 0 ∧
      ∀ (r : SRef C (.prim .uint)) s (v : PrimTy.uint.Denote),
        PathSlot C false r s →
        o.st.storage.findLive r = some (.prim v) → m'.store s = v.1.toNat) ∨
    ((Solidity.Prog.run (freshT C balance hb self) P = .error .revert ∨
        (Prog.asserts P = true ∧
          Solidity.Prog.run (freshT C balance hb self) P = .error .panic)) ∧
      run (compileProg 0 P) (Machine.init bal self) = .revert) ∨
    (Solidity.Prog.run (freshT C balance hb self) P = .error .diverge ∧
      run (compileProg 0 P) (Machine.init bal self) = .fault) := by
  rcases compile_paid hP (Sim.init C balance hb bal self hbalance) (by omega) with
    ⟨o, m', h1, h2, _, hm⟩ | h | h
  · refine .inl ⟨o, m', h1, h2, fun r s v hp hf => ?_⟩
    rcases find_repr hm.store hp with ⟨sv, hsv, hr⟩ | ⟨_, hsv⟩
    · rw [hf] at hsv; cases hsv
      cases hr with
      | prim h =>
        obtain ⟨a, ha, hv⟩ := h
        cases ha
        rw [hv, Int.toNat_natCast]
        rfl
    · rw [hf] at hsv; cases hsv
  · exact .inr (.inl h)
  · exact .inr (.inr h)

end Headline

end Solidity.Evm.Payments
