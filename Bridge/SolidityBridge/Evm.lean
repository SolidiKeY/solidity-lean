import Solidity.Evm.Machine
import Solidity.Evm.Correct
import Cslib.Foundations.Semantics.LTS.Basic

/-!
# The EVM fragment as a labelled transition system

`Evm.exec` (`Evm/Machine.lean`) runs a list of instructions, a pending skip
counted down first (the end of an `if`'s branch).  Here it is a CSLib `LTS`
on configurations — the code still to run, the skip, the machine — whose
labels are the instructions executed (`some i`) or skipped (`none`):

* `Evm.lts_deterministic`: one configuration, one label, one successor;
* `Evm.exec_eq_ok_iff`: code runs to a machine exactly when the LTS reaches
  the end of the code with it;
* `Evm.exec_eq_halt_iff`: code reverts (or faults) exactly when the LTS
  reaches an instruction that does.
-/

namespace Solidity

namespace Evm

/-- A configuration: the code still to run, the instructions still to skip,
the machine. -/
structure Cfg where
  code : List Instr
  skip : Nat
  m : Machine

/-- One transition: an instruction skipped, or one that succeeded. -/
inductive Tr : Cfg → Option Instr → Cfg → Prop where
  | skip {i : Instr} {c : List Instr} {k : Nat} {m : Machine} :
      Tr ⟨i :: c, k + 1, m⟩ none ⟨c, k, m⟩
  | step {i : Instr} {c : List Instr} {m m' : Machine} {k' : Nat} (h : i.step m = .ok m' k') :
      Tr ⟨i :: c, 0, m⟩ (some i) ⟨c, k', m'⟩

/-- **The EVM fragment as a CSLib LTS.** -/
def lts : LTS Cfg (Option Instr) where
  Tr := Tr

/-- What a configuration runs to. -/
def Cfg.exec (s : Cfg) : Out := Evm.exec s.code s.skip s.m

/-- The LTS is deterministic. -/
theorem lts_deterministic : lts.Deterministic := by
  intro s μ s₁ s₂ h₁ h₂
  cases h₁ with
  | skip => cases h₂; rfl
  | step h =>
    cases h₂ with
    | step h' =>
      rw [h] at h'
      cases h'
      rfl

/-- A transition keeps what the configuration runs to. -/
theorem Tr.exec_eq {s s' : Cfg} {μ : Option Instr} (h : lts.Tr s μ s') : s.exec = s'.exec := by
  cases h with
  | skip => rfl
  | step h => simp only [Cfg.exec, Evm.exec, h, Out.ok_bind]

/-- So does a run. -/
theorem MTr.exec_eq {s s' : Cfg} {μs : List (Option Instr)} (h : lts.MTr s μs s') :
    s.exec = s'.exec := by
  induction h with
  | refl => rfl
  | stepL t _ ih => exact (Tr.exec_eq t).trans ih

/-- **Code runs to a machine exactly when the LTS reaches the end of the
code with it.** -/
theorem exec_eq_ok_iff {c : List Instr} {k k' : Nat} {m m' : Machine} :
    Evm.exec c k m = .ok m' k' ↔ ∃ μs, lts.MTr ⟨c, k, m⟩ μs ⟨[], k', m'⟩ := by
  constructor
  · intro h
    induction c generalizing k m with
    | nil =>
      cases h
      exact ⟨[], .refl⟩
    | cons i c ih =>
      cases k with
      | succ k =>
        obtain ⟨μs, hμ⟩ := ih h
        exact ⟨none :: μs, .stepL Tr.skip hμ⟩
      | zero =>
        simp only [Evm.exec] at h
        cases hs : i.step m with
        | ok m₁ k₁ =>
          rw [hs, Out.ok_bind] at h
          obtain ⟨μs, hμ⟩ := ih h
          exact ⟨some i :: μs, .stepL (Tr.step hs) hμ⟩
        | revert => rw [hs, Out.revert_bind] at h; cases h
        | fault => rw [hs, Out.fault_bind] at h; cases h
  · rintro ⟨μs, h⟩
    exact MTr.exec_eq h

/-- **Code halts (reverts or faults) exactly when the LTS reaches an
instruction that does.** -/
theorem exec_eq_halt_iff {c : List Instr} {k : Nat} {m : Machine} {o : Out}
    (ho : ∀ m k, o ≠ .ok m k) :
    Evm.exec c k m = o ↔
      ∃ μs i c' m₁, lts.MTr ⟨c, k, m⟩ μs ⟨i :: c', 0, m₁⟩ ∧ i.step m₁ = o := by
  have hbind : ∀ f, o.bind f = o := by
    intro f
    cases o with
    | ok m k => exact absurd rfl (ho m k)
    | revert => rfl
    | fault => rfl
  constructor
  · intro h
    induction c generalizing k m with
    | nil => exact absurd h.symm (ho m k)
    | cons i c ih =>
      cases k with
      | succ k =>
        obtain ⟨μs, j, c', m₁, hμ, hj⟩ := ih h
        exact ⟨none :: μs, j, c', m₁, .stepL Tr.skip hμ, hj⟩
      | zero =>
        simp only [Evm.exec] at h
        cases hs : i.step m with
        | ok m₁ k₁ =>
          rw [hs, Out.ok_bind] at h
          obtain ⟨μs, j, c', m₂, hμ, hj⟩ := ih h
          exact ⟨some i :: μs, j, c', m₂, .stepL (Tr.step hs) hμ, hj⟩
        | revert =>
          rw [hs, Out.revert_bind] at h
          exact ⟨[], i, c, m, .refl, hs.trans h⟩
        | fault =>
          rw [hs, Out.fault_bind] at h
          exact ⟨[], i, c, m, .refl, hs.trans h⟩
  · rintro ⟨μs, i, c', m₁, h, hi⟩
    rw [show Evm.exec c k m = Cfg.exec ⟨c, k, m⟩ from rfl, MTr.exec_eq h]
    simp only [Cfg.exec, Evm.exec, hi, hbind]

/-! ## Compiler correctness as machine traces -/

section Compiler

variable {C : Contract} {L b : Nat} {Γ Γ' : Ctx} {F : Frag Γ} {F' : Frag Γ'}
  {σ : State C Γ} {m : Machine} {P : Solidity.Prog C Γ Γ'}

/-- Every successful CSLib trace of compiled code has a corresponding typed
source run. This direction permits payments. -/
theorem compile_trace_sound (hP : inFragP F P = some F') (hm : Sim C L b F σ m)
    (hL : L + Prog.pushes P ≤ Lmax) {m' : Machine} {μs : List (Option Instr)}
    (htr : lts.MTr ⟨compileProg b P, 0, m⟩ μs ⟨[], 0, m'⟩) :
    ∃ o, Solidity.Prog.run σ P = .ok o ∧
      Sim C (L + Prog.pushes P) b F' o.st m' :=
  compile_box hP hm hL (exec_eq_ok_iff.mpr ⟨μs, htr⟩)

/-- A successful source run has a successful instruction trace when payments
cannot be refused. Inlined calls are included wherever `inFragP` admits them. -/
theorem compile_trace_complete (hP : inFragP F P = some F') (hm : Sim C L b F σ m)
    (hL : L + Prog.pushes P ≤ Lmax) (hpay : Prog.pays P = false)
    {o : Solidity.Out C σ.H Γ'} (hrun : Solidity.Prog.run σ P = .ok o) :
    ∃ m' μs, lts.MTr ⟨compileProg b P, 0, m⟩ μs ⟨[], 0, m'⟩ ∧
      m'.stack = m.stack ∧ Sim C (L + Prog.pushes P) b F' o.st m' := by
  rcases compile_exact hP hm hL hpay with ⟨o', m', hsrc, htgt, hstk, hsim⟩ | ⟨hbad, _⟩ |
      ⟨hdiv, _⟩
  · have ho : o' = o := Except.ok.inj (hsrc.symm.trans hrun)
    subst o'
    obtain ⟨μs, htr⟩ := exec_eq_ok_iff.mp htgt
    exact ⟨m', μs, htr, hstk, hsim⟩
  · rcases hbad with hr | ⟨_, hr⟩ <;> rw [hrun] at hr <;> cases hr
  · rw [hrun] at hdiv
    cases hdiv

/-- Exact successful termination correspondence, stated using CSLib traces.
This is a trace theorem for the existing compiler, not a bisimulation with
an independently implemented EVM. -/
theorem compile_terminates_iff (hP : inFragP F P = some F') (hm : Sim C L b F σ m)
    (hL : L + Prog.pushes P ≤ Lmax) (hpay : Prog.pays P = false) :
    (∃ m' μs, lts.MTr ⟨compileProg b P, 0, m⟩ μs ⟨[], 0, m'⟩) ↔
      ∃ o, Solidity.Prog.run σ P = .ok o := by
  constructor
  · rintro ⟨m', μs, htr⟩
    obtain ⟨o, ho, _⟩ := compile_trace_sound hP hm hL htr
    exact ⟨o, ho⟩
  · rintro ⟨o, ho⟩
    obtain ⟨m', μs, htr, _, _⟩ := compile_trace_complete hP hm hL hpay ho
    exact ⟨m', μs, htr⟩

end Compiler

end Evm

end Solidity
