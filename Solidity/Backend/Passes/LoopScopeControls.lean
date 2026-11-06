import Solidity.Backend.Passes.LoopBoundary
import Solidity.Backend.Passes.MemoryCallControls

/-! An actual allocating alias-rebinding loop inside a block. Finite source
iteration witnesses use the existing TLoop semantics, never target execution
as substitute Source semantics. The contract and states remain intrinsic. -/
namespace Solidity.Backend.Passes.LoopScopeControls
open Evm Evm.Memory Evm.Compiler MemoryCallControls
abbrev Γ : Ctx := Captured
abbrev Δ : Ctx := .mem A :: Γ
abbrev Ω : Ctx := .val .uint :: Γ

def capture : Prog C Before Γ :=
  .cons (.declMem A (.user "live") (some (.alias (.var (.there .here) rfl))) rfl rfl) .nil

def prepare : Prog C [] Γ := allocate.join capture
def preparation : CompiledProg 1 (Frag.init []) prepare :=
  (Memory.compileProg 1 _ prepare).get (by decide +kernel)
noncomputable def prepared : Solidity.Out C initial.H Γ :=
  (prepare.run initial).toOption.get (by decide +kernel)

private theorem source_get {Γ Δ : Ctx} {σ : State C Γ} {P : Prog C Γ Δ}
    {o : Solidity.Out C σ.H Δ} (hx : some o = (P.run σ).toOption) : P.run σ = .ok o := by
  cases hs : P.run σ with
  | ok value => rw [hs] at hx; exact congrArg Except.ok (Option.some.inj hx).symm
  | error e => rw [hs] at hx; cases hx

theorem prepared_source : prepare.run initial = .ok prepared := source_get (Option.some_get _)

def condition : Val C Γ .bool :=
  .binop .gt rfl rfl (.simple (.local (.there .here))) (.simple (.lit 0 rfl))

def body : Prog C Γ Δ :=
  .cons (.declMem A (.user "fresh") (some (.newArr (.lit 2 rfl) rfl)) rfl rfl)
  (.cons (.rebindMem (.there .here) (.alias (.var .here rfl)))
  (.cons (.assignLocal (.there (.there .here)) (.simple (.lit 0 rfl))) .nil))

def conditionCompiled : CompiledVal 1 preparation.frag condition :=
  (Memory.compileVal 1 _ condition).get (by decide +kernel)
def bodyCompiled : CompiledProg 1 preparation.frag body :=
  (Memory.compileProg 1 _ body).get (by decide +kernel)
noncomputable def bodyResult (σ : State C Γ) : Solidity.Out C σ.H Δ :=
  (body.run σ).toOption.get (by rfl)

theorem body_source (σ : State C Γ) : body.run σ = .ok (bodyResult σ) := source_get (Option.some_get _)

theorem body_stops (σ : State C Γ) (o : Solidity.Out C σ.H Δ)
    (source : body.run σ = .ok o) : condition.evalT (o.st.drop body.ext) = .ok false := by
  have same : bodyResult σ = o := Except.ok.inj ((body_source σ).symm.trans source)
  subst o
  with_unfolding_all rfl

def iteration : Prog C Γ Γ := .cons (.loop .auto condition body) .nil
def loopCompiled : Loops.CompiledProg 1 preparation.frag iteration :=
  (Loops.compileProg 1 _ iteration).get (by decide +kernel)
def wrapped : Prog C Γ Γ := .cons (.block iteration) .nil
def enclosed : LoopScopes.CompiledProg 1 preparation.frag wrapped :=
  (LoopScopes.compileProg 1 wrapped _).get (by decide +kernel)
def checked : Compilation 1 preparation.frag wrapped := .memoryLoopScopes enclosed

noncomputable def loopOut : Solidity.Out C prepared.st.H Γ :=
  ⟨(bodyResult prepared.st).st.drop body.ext,(bodyResult prepared.st).ext⟩

theorem condition_initial : condition.evalT prepared.st = .ok true := by with_unfolding_all rfl
theorem condition_final : condition.evalT loopOut.st = .ok false :=
  body_stops prepared.st _ (body_source prepared.st)

theorem iteration_source : iteration.run prepared.st = .ok loopOut := by
  have one : (Stmt.loop .auto condition body).run prepared.st = .ok loopOut := by
    rw [Stmt.run_loop]
    apply TLoop.run_of_iterN (n := 2)
    simp only [TLoop.iterN,TLoop.step,condition_initial,body_source,Except.map]
    have done := body_stops prepared.st (bodyResult prepared.st) (body_source prepared.st)
    rw [done]
    rfl
  rw [iteration,Prog.run_cons_ok one,Prog.run_nil]
  rfl

theorem wrapped_source : wrapped.run prepared.st = .ok loopOut := by
  change (Prog.cons (.block iteration) .nil).run prepared.st = .ok loopOut
  have hb : (Stmt.block iteration).run prepared.st = .ok loopOut := by
    change (iteration.run prepared.st).map _ = .ok loopOut
    rw [iteration_source]
    rfl
  rw [Prog.run_cons_ok hb,Prog.run_nil]
  rfl

def consume : Prog C Γ Ω :=
  .cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))
    (.val (.binop .add rfl rfl
      (.readMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))) (.simple (.lit 9 rfl)))))
  (.cons (.assignMem (.index .dyn (.var (.there (.there .here)) rfl) (.simple (.lit 0 rfl)))
    (.val (.binop .add rfl rfl
      (.readMem (.index .dyn (.var (.there (.there .here)) rfl) (.simple (.lit 0 rfl))))
      (.simple (.lit 1 rfl)))))
  (.cons (.declLocal .uint (.user "observed")
    (some (.readMem (.index .dyn (.var .here rfl) (.simple (.lit 1 rfl)))))) .nil))
def suffix : CompiledProg 1 enclosed.frag consume := (Memory.compileProg 1 _ consume).get (by decide +kernel)
noncomputable def final : Solidity.Out C loopOut.st.H Ω :=
  (consume.run loopOut.st).toOption.get (by decide +kernel)
theorem final_source : consume.run loopOut.st = .ok final := source_get (Option.some_get _)

theorem costs : preparation.cert.cost initial = 2 ∧ Memory.hasAllocation consume = false := by decide +kernel
theorem body_cost (σ : State C Γ) : allocationCostProg body σ = 3 := by with_unfolding_all rfl

theorem public_recognizer : (Compiler.compile 1 preparation.frag wrapped).map (·.isMemoryLoopScopes) = some true := by
  decide +kernel

theorem frames : 1 + enclosed.cert.need ≤ 128 ∧ 1 + frameNeedProg consume ≤ 128 := by decide +kernel


theorem iteration_stmt_source : (Stmt.loop .auto condition body).run prepared.st = .ok loopOut := by
  simpa only [iteration,LoopScopes.run_singleton] using iteration_source

theorem block_stmt_source : (Stmt.block iteration).run prepared.st = .ok loopOut := by
  simpa only [wrapped,LoopScopes.run_singleton] using wrapped_source

theorem reached_prefix : LoopPrefix condition body prepared.st loopOut 3 := by
  simpa only [body_cost,Nat.zero_add] using
    LoopPrefix.next LoopPrefix.start condition_initial (body_source prepared.st)

/-- The actual nonempty successful scope carries a positive cost certificate,
while the legacy finite projection intentionally cannot measure loop costs. -/
theorem actual_cost : LoopScopes.Cost enclosed.cert prepared.st loopOut 3 := by
  refine .cons (cost := 3) (rest := 0) block_stmt_source (.block iteration_source ?_) (.nil _)
  refine .cons (cost := 3) (rest := 0) iteration_stmt_source (.base ?_) (.nil _)
  refine .cons (cost := 3) (rest := 0) iteration_stmt_source ?_ (.nil _)
  exact reached_prefix

theorem legacy_metric_zero : checked.allocationCost prepared.st = 0 := by with_unfolding_all rfl

end Solidity.Backend.Passes.LoopScopeControls
