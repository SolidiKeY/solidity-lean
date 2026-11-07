import Solidity.Backend.AbiWorld.PublicCompilerTotal
import Solidity.Backend.InternalFlow.RuntimeFrameP1LangV2

/-! H68 family 3, P1-REVERT (`docs/feature-work/v13-public-compiler-total.md`):
a `BridgeGoal` over V12's canonical version-2 P1 languages
(`RuntimeFrameP1LangV2`), for the public compiler's own output.

* **Context.** A statement `s` of the totality domain (`StmtOk K s K'`) from a
  fragment matching its alias kinds (`Matches K F`) at base `b`, with no
  `assert` (`Stmt.asserts s = false`; see below). The source family is `s` at
  every depth.
* **Target.** The code `Compiler.compile b F (s; )` emits, lifted to the
  version-2 machine (`lift`). It is compiler output, not a hand-written image.
* **Domain** (`admitted`): the compiler's own core input
  (`Compilation.Input`, whose push bound is `L ≤ Lmax` here since the domain
  pushes nothing): `Sim C L b F caller machine` and `L ≤ Lmax`. It does not
  mention the outcome. It is not the P1 `InterfaceV1.Entry` admission: the
  code is frame-free core output, and `frame`, `base`, `start` are unused.

Every admitted input gives the same prefix on both sides (`agree`), from
`PublicCompilerTotal.compile_agrees`: success with no data on both; a bare
source revert as a version-2 revert with empty data and an unchanged journal;
divergence as a fault (both unfinished). Payment cannot occur (the domain
pays nothing). `Local` is a version-2 analog of
`PendingBareRevertProducer.required_bare_revert` (`bare_revert`: a bare
source revert is a target revert with empty data and the caller's journal)
together with the frame agreement. It is not built from such a producer and
has no `RevertingEntry` field.

Limits it depends on: callee code is never run (the domain makes no external
call, so the version-2 `reply`/`accepts` oracles are not consulted); gas and
depth are not resources (as in `P1LangV2`); data windows play no part (the
core code reverts without data). `assert` is excluded because the source
observes a failing `assert` as `revert(Panic(0x01))` while the core compiler
emits a data-free revert: a real compiler gap, recorded, not hidden. -/
namespace Solidity.Backend.AbiWorld.P1RevertBridge
open Solidity.Evm Solidity.Backend.AbiWorld.PublicCompilerTotal
open Solidity.Backend.InternalFlow.RuntimeFrame.P1LangV2
open Solidity.Roadmap (Event Outcome Prefix Lang Prefixes)
open Solidity.Roadmap.G49Final (BridgeGoal PassCorrect Behaviour)

variable {C : Contract}

/-- The one-statement program the compiler is given. -/
abbrev prog {Γ Δ : Ctx} (s : Solidity.Stmt C Γ Δ) : Solidity.Prog C Γ Δ := .cons s .nil

/-- The public compiler's code for `s` (empty when refused, which the domain
rules out). -/
def code {Γ Δ : Ctx} (b : Nat) (F : Frag Γ) (s : Solidity.Stmt C Γ Δ) : List Instr :=
  match Compiler.compile b F (prog s) with
  | some r => r.code
  | none => []

/-- The admitted inputs: the compiler's own core input. -/
def admitted {Γ : Ctx} (b : Nat) (F : Frag Γ) : Admission C Γ := fun e =>
  Sim C e.L b F e.caller e.machine.base ∧ e.L ≤ Lmax

/-! ## The one-statement program halts as its statement -/

theorem single_halt {Γ Δ : Ctx} (σ : State C Γ) (s : Solidity.Stmt C Γ Δ) :
    (Solidity.Prog.run σ (prog s)).halt? = (s.run σ).halt? := by
  cases h : s.run σ with
  | ok o => rw [Solidity.Prog.run_cons_ok h, Solidity.Prog.run_nil]; rfl
  | error e =>
    show (TRun.seq s.runR (Solidity.Prog.nil : Solidity.Prog C Δ Δ).runR σ).halt? = _
    simp only [TRun.seq, Solidity.Stmt.run] at h ⊢
    rw [h]

theorem sourcePrefix_of_halt {H H' : HTy} {Δ Δ' : Ctx} (r : TRes (Solidity.Out C H Δ))
    (r' : TRes (Solidity.Out C H' Δ')) (h : r.halt? = r'.halt?) :
    sourcePrefix r = sourcePrefix r' := by
  rcases r with e | o <;> rcases r' with e' | o'
  · simp only [TRes.halt?, Option.some.injEq] at h
    subst h
    cases e <;> rfl
  · simp only [TRes.halt?, reduceCtorEq] at h
  · simp only [TRes.halt?, reduceCtorEq] at h
  · rfl

/-! ## Frame agreement -/

theorem code_eq {Γ Δ : Ctx} {b : Nat} {F : Frag Γ} {s : Solidity.Stmt C Γ Δ}
    {result : Compiler.Compilation b F (prog s)} (h : Compiler.compile b F (prog s) = some result) :
    code b F s = result.code := by
  simp only [code, h]

/-- **Frame agreement**: on every admitted input, the lifted compiled code and
the source show the same prefix. -/
theorem agree {Γ Δ : Ctx} {K K' : Kinds} {b : Nat} {F : Frag Γ} {s : Solidity.Stmt C Γ Δ}
    (hF : Matches K F) (hs : StmtOk K s K') (noAssert : Stmt.asserts s = false)
    (e : Input C Γ) (h : admitted b F e) :
    targetSem (lift (code b F s)) e = sourcePrefix (s.run e.caller) := by
  have hP : ProgOk K (prog s) := .cons hs .nil
  obtain ⟨result, hc, ag⟩ := compile_agrees b hF hP
  have q := hP.quiet
  have hasP : Prog.asserts (prog s) = false := by
    simp only [Prog.asserts, noAssert, Bool.or_false]
  rw [code_eq hc, ← sourcePrefix_of_halt _ _ (single_halt e.caller s)]
  rcases ag e.L e.frame e.base e.caller e.machine.base h.1 h.2 with
    ⟨o, m', hr, hrun, _, _⟩ | ⟨hr | ⟨ha, _⟩, hrun⟩ | ⟨hp, _⟩ | ⟨hr, hrun | ⟨hp, _⟩⟩
  · rw [hr]
    simp only [targetSem, run_lift_ok hrun, targetPrefix, eventsAfter, MachineV2.withBase,
      List.drop_length, List.filter_nil, List.map_nil, List.flatten_nil]
    rfl
  · rw [hr]
    simp only [targetSem, run_lift_revert hrun, targetPrefix, eventsAfter, List.drop_length,
      List.filter_nil, List.map_nil, List.flatten_nil]
    rfl
  · rw [hasP] at ha
    exact absurd ha Bool.false_ne_true
  · rw [q.2.1] at hp
    exact absurd hp Bool.false_ne_true
  · rw [hr]
    simp only [targetSem, run_lift, hrun, OutV2.ofOut, targetPrefix]
    rfl
  · rw [q.2.1] at hp
    exact absurd hp Bool.false_ne_true

/-- The failure-only conclusion of `PendingBareRevertProducer`, version 2: a
bare source revert is a target revert with empty data and the caller's
journal. -/
theorem bare_revert {Γ Δ : Ctx} {K K' : Kinds} {b : Nat} {F : Frag Γ} {s : Solidity.Stmt C Γ Δ}
    (hF : Matches K F) (hs : StmtOk K s K') (noAssert : Stmt.asserts s = false)
    (e : Input C Γ) (h : admitted b F e) (reverts : s.run e.caller = .error .revert) :
    runV2 (lift (code b F s)) e.machine = .revert e.machine.calls [] := by
  have hP : ProgOk K (prog s) := .cons hs .nil
  obtain ⟨result, hc, ag⟩ := compile_agrees b hF hP
  have q := hP.quiet
  have hasP : Prog.asserts (prog s) = false := by
    simp only [Prog.asserts, noAssert, Bool.or_false]
  have halt : (Solidity.Prog.run e.caller (prog s)).halt? = some .revert := by
    rw [single_halt, reverts]
    rfl
  rw [code_eq hc]
  rcases ag e.L e.frame e.base e.caller e.machine.base h.1 h.2 with
    ⟨o, m', hr, _, _, _⟩ | ⟨_, hrun⟩ | ⟨hp, _⟩ | ⟨hr, _⟩
  · rw [hr] at halt
    cases halt
  · exact run_lift_revert hrun
  · rw [q.2.1] at hp
    exact absurd hp Bool.false_ne_true
  · rw [hr] at halt
    cases halt

/-! ## Languages and the bridge -/

theorem consistent {Γ Δ : Ctx} (s : Solidity.Stmt C Γ Δ) (e : Input C Γ) :
    Prefixes.Consistent (sourceSem (fun _ => s) e) :=
  fun _ _ _ => Prefix.Le.refl _

/-- The canonical version-2 source language of the context. -/
def A {Γ Δ : Ctx} (b : Nat) (F : Frag Γ) (s : Solidity.Stmt C Γ Δ) : Lang Event Outcome :=
  sourceLang (fun _ => s) (admitted b F) (consistent s)

/-- The canonical version-2 target language of the compiled code. -/
noncomputable def B {Γ Δ : Ctx} (b : Nat) (F : Frag Γ) (s : Solidity.Stmt C Γ Δ) :
    Lang Event Outcome :=
  targetLang (C := C) (lift (code b F s)) (admitted b F)

/-- The entire local conclusion: the version-2 bare-revert claim and the
frame agreement, for every admitted input. -/
def Local {Γ Δ : Ctx} (b : Nat) (F : Frag Γ) (s : Solidity.Stmt C Γ Δ) : Prop :=
  ∀ e : Input C Γ, admitted b F e →
    (s.run e.caller = .error .revert →
      runV2 (lift (code b F s)) e.machine = .revert e.machine.calls []) ∧
    targetSem (lift (code b F s)) e = sourcePrefix (s.run e.caller)

/-- The full refinement between the canonical version-2 languages. -/
noncomputable def pass {Γ Δ : Ctx} {K K' : Kinds} (b : Nat) {F : Frag Γ}
    {s : Solidity.Stmt C Γ Δ} (hF : Matches K F) (hs : StmtOk K s K')
    (noAssert : Stmt.asserts s = false) :
    PassCorrect (Behaviour.ofLang (A b F s) ()) (Behaviour.ofLang (B b F s) ()) where
  envAbs := id
  envSound := fun _ h => h
  envOnto := fun e h => ⟨e, h, rfl⟩
  need := fun _ _ => ()
  need_ok e _ h _ := by
    refine ⟨⟨trivial, trivial, trivial⟩, ?_⟩
    change (sourcePrefix (s.run e.caller)).Le (targetSem (lift (code b F s)) e)
    rw [agree hF hs noAssert e h]
    exact Prefix.Le.refl _
  back e _ h _ _ := by
    refine ⟨(0 : Nat), trivial, trivial, ?_⟩
    change (targetSem (lift (code b F s)) e).Le (sourcePrefix (s.run e.caller))
    rw [agree hF hs noAssert e h]
    exact Prefix.Le.refl _

/-- **`p1_frame_bridge`, P1-REVERT variant**, for every statement of the
public compiler's totality domain without `assert`. -/
noncomputable def p1_revert_bridge {Γ Δ : Ctx} {K K' : Kinds} (b : Nat) {F : Frag Γ}
    {s : Solidity.Stmt C Γ Δ} (hF : Matches K F) (hs : StmtOk K s K')
    (noAssert : Stmt.asserts s = false) :
    BridgeGoal (A b F s) (B b F s) () () id (fun _ _ => ()) (Local b F s) :=
  ⟨pass b hF hs noAssert, rfl, rfl,
    fun e h => ⟨bare_revert hF hs noAssert e h, agree hF hs noAssert e h⟩⟩

end Solidity.Backend.AbiWorld.P1RevertBridge
