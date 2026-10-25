import SolidityBridge.Evm
import Cslib.Foundations.Semantics.LTS.Bisimulation

/-!
Compiler bisimulation at successful program boundaries. A target transition
is an actual finite trace in `Evm.lts`, not a call to the source interpreter.
Labels retain the typed program. Fragment admission, local-space bounds and
payment freedom are checked on both sides. Halting and diverging executions
are not transitions of this successful-execution LTS.
-/
namespace Solidity.Evm.Compiler

variable {C : Contract}

structure Action (C : Contract) where
  src : Ctx
  dst : Ctx
  prog : Solidity.Prog C src dst

inductive Config (C : Contract) where
  | source {Γ : Ctx} (L : Nat) (F : Frag Γ) (σ : State C Γ)
  | target {Γ : Ctx} (L : Nat) (F : Frag Γ) (m : Machine)

inductive Transition (b : Nat) : Config C → Action C → Config C → Prop where
  | source {Γ Δ : Ctx} {L : Nat} {F : Frag Γ} {G : Frag Δ}
      {P : Solidity.Prog C Γ Δ} {σ : State C Γ} {o : Solidity.Out C σ.H Δ}
      (frag : inFragP F P = some G) (space : L + Prog.pushes P ≤ Lmax)
      (pay : Prog.pays P = false) (run : Solidity.Prog.run σ P = .ok o) :
      Transition b (.source L F σ) ⟨Γ, Δ, P⟩ (.source (L + Prog.pushes P) G o.st)
  | target {Γ Δ : Ctx} {L : Nat} {F : Frag Γ} {G : Frag Δ}
      {P : Solidity.Prog C Γ Δ} {m m' : Machine} {es : List (Option Instr)}
      (frag : inFragP F P = some G) (space : L + Prog.pushes P ≤ Lmax)
      (pay : Prog.pays P = false)
      (trace : Evm.lts.MTr ⟨compileProg b P, 0, m⟩ es ⟨[], 0, m'⟩) :
      Transition b (.target L F m) ⟨Γ, Δ, P⟩ (.target (L + Prog.pushes P) G m')

def system (C : Contract) (b : Nat) : LTS (Config C) (Action C) := ⟨Transition b⟩

/-- Relates typed source states to represented machines with the same
context, fragment and allocation counter. -/
inductive Represents (b : Nat) : Config C → Config C → Prop where
  | state {Γ : Ctx} {L : Nat} {F : Frag Γ} {σ : State C Γ} {m : Machine}
      (sim : Sim C L b F σ m) : Represents b (.source L F σ) (.target L F m)

theorem bisimulation (b : Nat) : (system C b).IsBisimulation (Represents b) := by
  intro s t h label
  cases h with
  | state hm =>
    constructor
    · intro s' hs
      cases hs with
      | source hF hL hp hr =>
        obtain ⟨m', es, ht, _, hm'⟩ := compile_trace_complete hF hm hL hp hr
        exact ⟨_, Transition.target hF hL hp ht, Represents.state hm'⟩
    · intro t' ht
      cases ht with
      | target hF hL hp ht =>
        obtain ⟨o, hr, hm'⟩ := compile_trace_sound hF hm hL ht
        exact ⟨_, Transition.source hF hL hp hr, Represents.state hm'⟩

theorem simulation (b : Nat) : Simulation (system C b) (Represents b) := by
  intro s t h label s' hs
  exact (bisimulation b h label).1 s' hs

/-- CSLib supplies trace equivalence, including arbitrarily many composed
program boundaries. `Stmt.call` is included through `inFragP`. -/
theorem trace_equivalence {Γ : Ctx} {L b : Nat} {F : Frag Γ}
    {σ : State C Γ} {m : Machine} (hm : Sim C L b F σ m) :
    TraceEq (system C b) (.source L F σ) (.target L F m) :=
  (bisimulation b).traceEq (Represents.state hm)

end Solidity.Evm.Compiler

/-- info: 'Solidity.Evm.Compiler.bisimulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Compiler.bisimulation
/-- info: 'Solidity.Evm.Compiler.trace_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.Compiler.trace_equivalence
