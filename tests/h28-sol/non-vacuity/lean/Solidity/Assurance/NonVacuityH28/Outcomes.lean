import Solidity.Assurance.NonVacuityH28.Families

/-! Additional scoped compiler outcomes: panic and actual money movement. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics
variable (C : Contract)

def panicProgram : Prog C [] [] := .cons (.assert (.simple (.bool false))) .nil

theorem panic_source (σ : State C []) :
    Prog.run σ (panicProgram C) = .error .panic := rfl

theorem panic_target (b : Nat) (mc : Evm.Machine) :
    Evm.run (Evm.compileProg b (panicProgram C)) mc = .revert := rfl

theorem panic_fragment :
    Evm.inFragP (Evm.Frag.init []) (panicProgram C) = some (Evm.Frag.init []) := rfl

theorem compiler_panic_application :
    Evm.run (Evm.compileProg 0 (panicProgram C))
      (Evm.Machine.init (fun _ => 0) ⟨0, by decide⟩) = .revert := by
  rcases Main.compiler_correct (panic_fragment C) (closed_simulation C)
    (by change 1 ≤ Evm.Lmax; decide) with
    ⟨_, _, ho, _⟩ | ⟨_, hr⟩ | ⟨hd, _⟩
  · simp only [Main.Runs, panic_source, reduceCtorEq] at ho
  · exact hr
  · rw [panic_source] at hd
    cases hd

def worldBalances (funds : Nat) (a : Fin Evm.W) : Nat := if a.1 = 0 then funds else 0
def paymentProgram : Prog C [] [] :=
  .cons (.transfer (.simple (.lit 9 rfl)) (.simple (.lit 5 rfl))) .nil

def paymentSource : State C [] := Evm.freshT C 10 (by decide) ⟨0, by decide⟩
def paymentMachine : Evm.Machine := Evm.Machine.init (worldBalances 10) ⟨0, by decide⟩
def afterPaymentMachine : Evm.Machine :=
  { paymentMachine with bal := Evm.pay paymentMachine.bal paymentMachine.self ⟨9, by decide⟩ 5 }

theorem payment_fragment :
    Evm.inFragP (Evm.Frag.init []) (paymentProgram C) = some (Evm.Frag.init []) := rfl

theorem payment_simulation :
    Evm.Sim C 1 0 (Evm.Frag.init []) (paymentSource C) paymentMachine :=
  Evm.Sim.init C 10 (by decide) (worldBalances 10) ⟨0, by decide⟩ rfl

theorem payment_source : Prog.run (paymentSource C) (paymentProgram C) =
    .ok ⟨(paymentSource C).pay ⟨9, rfl⟩ 5, List.prefix_refl _⟩ := rfl

/-- The public headline forces success for `transfer(9, 5)` with enough funds. -/
theorem payment_headline_success :
    ∃ o mc', Prog.run (paymentSource C) (paymentProgram C) = .ok o ∧
      Evm.run (Evm.compileProg 0 (paymentProgram C)) paymentMachine = .ok mc' 0 ∧
      Evm.Sim C (1 + Evm.Prog.pushes (paymentProgram C)) 0 (Evm.Frag.init []) o.st mc' := by
  rcases Main.compiler_correct (payment_fragment C) (payment_simulation C)
    (by change 1 ≤ Evm.Lmax; decide) with h | ⟨hr | ⟨_, hr⟩, _⟩ | ⟨hd, _⟩
  · exact h
  · rw [payment_source] at hr
    cases hr
  · rw [payment_source] at hr
    cases hr
  · rw [payment_source] at hd
    cases hd

/-- A reverting or faulting replacement cannot satisfy the headline's exact
three-outcome conclusion for this successful paying source. -/
theorem payment_bad_machine_rejected (code : List Evm.Instr) (mc : Evm.Machine)
    (hbad : Evm.run code mc = .revert ∨ Evm.run code mc = .fault) :
    ¬ ((∃ o mc', Prog.run (paymentSource C) (paymentProgram C) = .ok o ∧
        Evm.run code mc = .ok mc' 0 ∧
        Evm.Sim C (1 + Evm.Prog.pushes (paymentProgram C)) 0 (Evm.Frag.init []) o.st mc') ∨
      ((Prog.run (paymentSource C) (paymentProgram C) = .error .revert ∨
          (Prog.asserts (paymentProgram C) = true ∧
            Prog.run (paymentSource C) (paymentProgram C) = .error .panic)) ∧
        Evm.run code mc = .revert) ∨
      (Prog.run (paymentSource C) (paymentProgram C) = .error .diverge ∧
        Evm.run code mc = .fault)) := by
  rw [payment_source]
  rcases hbad with hbad | hbad <;> simp only [hbad, reduceCtorEq, and_false, false_and,
    or_self, exists_false, not_false_eq_true]

theorem payment_target : Evm.run (Evm.compileProg 0 (paymentProgram C)) paymentMachine =
    .ok afterPaymentMachine 0 := rfl

theorem payment_observations : afterPaymentMachine.bal ⟨0, by decide⟩ = 5 ∧
    afterPaymentMachine.bal ⟨9, by decide⟩ = 5 ∧
    afterPaymentMachine.bal₀ ⟨0, by decide⟩ = 10 ∧
    afterPaymentMachine.bal₀ ⟨9, by decide⟩ = 0 := ⟨rfl, rfl, rfl, rfl⟩

theorem payment_net_application :
    ∃ o, Prog.run (paymentSource C) (paymentProgram C) = .ok o ∧
      (∀ a : Fin Evm.W, a ≠ afterPaymentMachine.self →
        Evm.netAt o.st.net a.1 = (afterPaymentMachine.bal₀ a : Int) - afterPaymentMachine.bal a) ∧
      Evm.netAt o.st.net afterPaymentMachine.self = 0 :=
  Main.compiler_net (payment_fragment C) (payment_simulation C)
    (by change 1 ≤ Evm.Lmax; decide) (payment_target C)

theorem payment_checked_application (frame : Nat) (base : Nat → Fin Evm.W) :
    (Evm.Compiler.Compilation.core (b := 0) _ (payment_fragment C)).Agrees
      1 frame base (paymentSource C) paymentMachine :=
  Main.compiler_checked _ ⟨payment_simulation C, by change 1 ≤ Evm.Lmax; decide⟩

theorem poor_payment_source :
    Prog.run (Evm.freshT C 0 (by decide) ⟨0, by decide⟩) (paymentProgram C) = .error .revert := rfl

theorem poor_payment_target :
    Evm.run (Evm.compileProg 0 (paymentProgram C))
      (Evm.Machine.init (worldBalances 0) ⟨0, by decide⟩) = .revert := rfl

def refusedSource : State C [] :=
  { paymentSource C with
    tx := { (paymentSource C).tx with ext := [(sendKey ⟨9, rfl⟩ ⟨5, rfl⟩, .error [])] } }

def tableAccepts (σ : State C []) (x y : Fin Evm.W) : Bool :=
  match lookupBy (sendKey (Evm.uintT x.1 x.2) (Evm.uintT y.1 y.2)) σ.tx.ext with
  | none | some (.ok _) => true
  | some _ => false

def refusedMachine : Evm.Machine := { paymentMachine with accepts := tableAccepts C (refusedSource C) }

theorem refused_simulation :
    Evm.Sim C 1 0 (Evm.Frag.init []) (refusedSource C) (refusedMachine C) := by
  have h : Evm.Sim C 1 0 (Evm.Frag.init []) (paymentSource C) paymentMachine :=
    payment_simulation C
  refine ⟨h.store, h.vals, h.aliases, h.net, h.netSelf, h.bound, h.fragile, h.env, h.funds, ?_⟩
  intro addr amt x y hx hy
  have haddr : addr = Evm.uintT x.1 x.2 := Subtype.ext hx
  have hamt : amt = Evm.uintT y.1 y.2 := Subtype.ext hy
  rw [haddr, hamt]
  rfl

theorem refused_source : Prog.run (refusedSource C) (paymentProgram C) = .error .revert := rfl

/-- Refused `transfer(9, 5)` forces the public headline's joint revert arm. -/
theorem refused_headline_revert :
    Prog.run (refusedSource C) (paymentProgram C) = .error .revert ∧
      Evm.run (Evm.compileProg 0 (paymentProgram C)) (refusedMachine C) = .revert := by
  rcases Main.compiler_correct (payment_fragment C) (refused_simulation C)
    (by change 1 ≤ Evm.Lmax; decide) with ⟨_, _, ho, _⟩ | ⟨_, hr⟩ | ⟨hd, _⟩
  · simp only [Main.Runs, refused_source, reduceCtorEq] at ho
  · exact ⟨refused_source C, hr⟩
  · rw [refused_source] at hd
    cases hd

theorem refused_target : Evm.run (Evm.compileProg 0 (paymentProgram C)) (refusedMachine C) = .revert := rfl

theorem refused_checked_application (frame : Nat) (base : Nat → Fin Evm.W) :
    (Evm.Compiler.Compilation.core (b := 0) _ (payment_fragment C)).Agrees
      1 frame base (refusedSource C) (refusedMachine C) :=
  Main.compiler_checked _ ⟨refused_simulation C, by change 1 ≤ Evm.Lmax; decide⟩

def divergingProgram : Prog C [] [] :=
  .cons (.loop .auto (.simple (.bool true)) .nil) .nil

theorem identity_loop_diverges {α : Type} (x : α) :
    TLoop.run (fun a : α => .ok a) (fun _ => .ok true) x = .error .diverge := by
  have hi : ∀ (n : Nat) (a : α),
      TLoop.iterN (fun a : α => .ok a) (fun _ => .ok true) n a = .inl a := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih => intro a; exact ih a
  have hex : ¬ ∃ r n,
      TLoop.iterN (fun a : α => .ok a) (fun _ => .ok true) n x = .inr r := by
    rintro ⟨r, n, h⟩
    rw [hi] at h
    cases h
  unfold TLoop.run
  rw [dif_neg hex]

theorem divergence_source (σ : State C []) :
    Prog.run σ (divergingProgram C) = .error .diverge := by
  have hl : Stmt.run σ (.loop .auto (.simple (.bool true)) (.nil : Prog C [] [])) =
      .error .diverge := identity_loop_diverges (⟨σ, List.prefix_refl _⟩ : Out C σ.H [])
  change TRun.seq (Stmt.runR (.loop .auto (.simple (.bool true)) (.nil : Prog C [] [])))
    TRun.nil σ = _
  simp only [TRun.seq, hl]

theorem machine_loop_diverges (mc : Evm.Machine) :
    Evm.loopRun (fun m => .ok (m.push (.val (Evm.bword true))) 0)
      (fun m => .ok m 0) mc = .fault := by
  apply Evm.loopRun_of_forall
  intro n
  refine ⟨mc, ?_⟩
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem divergence_target (b : Nat) (mc : Evm.Machine) :
    Evm.run (Evm.compileProg b (divergingProgram C)) mc = .fault := by
  change (Evm.loopRun (fun m => .ok (m.push (.val (Evm.bword true))) 0)
    (fun m => .ok m 0) mc).bind (fun m k => Evm.exec [] k m) = .fault
  rw [machine_loop_diverges]
  rfl

theorem divergence_fragment :
    Evm.inFragP (Evm.Frag.init []) (divergingProgram C) = some (Evm.Frag.init []) := rfl

theorem compiler_divergence_application :
    Evm.run (Evm.compileProg 0 (divergingProgram C))
      (Evm.Machine.init (fun _ => 0) ⟨0, by decide⟩) = .fault := by
  rcases Main.compiler_correct (divergence_fragment C) (closed_simulation C)
    (by change 1 ≤ Evm.Lmax; decide) with
    ⟨_, _, ho, _⟩ | ⟨hr, _⟩ | ⟨_, ht⟩
  · simp only [Main.Runs, divergence_source, reduceCtorEq] at ho
  · rcases hr with hr | ⟨_, hp⟩
    · rw [divergence_source] at hr
      cases hr
    · rw [divergence_source] at hp
      cases hp
  · exact ht

end Solidity.Assurance.NonVacuityH28
