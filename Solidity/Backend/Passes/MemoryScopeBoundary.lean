import Solidity.Backend.Passes.MappedTail

/-! Scope exit keeps actual emitted code, reached cost and selected map.
Only the existing block constructor and public memory certificates are used. -/
namespace Solidity.Backend.Passes.MemoryScopeBoundary
open Evm Evm.Memory Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}

def program (P : Prog C Γ Δ) : Prog C Γ Γ := .cons (.block P) .nil

def compiled (body : CompiledProg b F P) : CompiledProg b F (program P) :=
  ⟨body.frag.restrict Γ, body.code ++ [],
    .cons (.block P body.code body.cert) (.nil _)⟩

theorem code (body : CompiledProg b F P) : (compiled body).code = body.code := by
  simp only [compiled, List.append_nil]

theorem cost (body : CompiledProg b F P) (state : State C Γ) :
    (compiled body).cert.cost state = body.cert.cost state := by
  change allocationCostProg (.cons (.block P) .nil) state = allocationCostProg P state
  rw [allocationCostProg_cons, allocationCostStmt_block]
  cases (Stmt.block P).run state <;> rfl

theorem input (body : CompiledProg b F P) {state : State C Γ}
    {base : Nat → Fin W} {machine : Machine}
    (h : (Compilation.memory body).Input L frame base state machine) :
    (Compilation.memory (compiled body)).Input L frame base state machine := by
  refine ⟨h.1, ?_, ?_⟩
  · have locals := h.1.locals
    have peak := h.2.1
    change b + max (max Γ.length (max Γ.length (frameNeedProg P))) Γ.length ≤ frame
    omega
  · rw [cost]
    exact h.2.2

theorem output (body : CompiledProg b F P) {entry : State C Γ}
    {initial middle : Machine} {base selected : Nat → Fin W} {state : State C Δ}
    (h : MappedOutput (.memory body) L frame base entry initial state middle selected) :
    MappedOutput (.memory (compiled body)) L frame base entry initial
      (state.drop P.ext) middle selected := by
  refine ⟨h.1.drop P.ext, h.2.1, ?_⟩
  simpa only [cost] using h.2.2

theorem source_success {state : State C Γ} {out : Solidity.Out C state.H Δ}
    (success : P.run state = .ok out) :
    (program P).run state = .ok ⟨out.st.drop P.ext, out.ext⟩ := by
  have blockRun : (Stmt.block P).run state = .ok (⟨out.st.drop P.ext, out.ext⟩ : Solidity.Out C state.H Γ) := by
    change (P.run state).map (fun o => (⟨o.st.drop P.ext, o.ext⟩ : Solidity.Out C state.H Γ)) = _
    rw [success]
    rfl
  change (Prog.cons (.block P) .nil).run state = _
  rw [Prog.run_cons_ok blockRun]
  rfl

theorem source_error {state : State C Γ} (halt : THalt) :
    (program P).run state = .error halt ↔ P.run state = .error halt := by
  cases hs : P.run state with
  | ok out =>
    rw [source_success hs]
    simp only [reduceCtorEq]
  | error reason =>
    have blockError : (Stmt.block P).run state = .error reason := by
      change (P.run state).map (fun o => (⟨o.st.drop P.ext, o.ext⟩ : Solidity.Out C state.H Γ)) = _
      rw [hs]
      rfl
    have outerError : (program P).run state = .error reason := by
      show TRun.seq (Stmt.block P).runR Prog.nil.runR state = _
      simp only [TRun.seq, Solidity.Stmt.run] at blockError ⊢
      rw [blockError]
    rw [outerError]
    simp only [Except.error.injEq]

theorem target_error (body : CompiledProg b F P) (machine : Machine) (halt : Evm.Out) :
    run (compiled body).code machine = halt ↔ run body.code machine = halt := by
  rw [code]

theorem shared (body : CompiledProg b F P) {entry : State C Γ}
    {machine : Machine} {base : Nat → Fin W}
    (h : (Compilation.memory body).Input L frame base entry machine)
    (noPay : Evm.Prog.pays P = false) {out : Solidity.Out C entry.H Δ}
    (success : P.run entry = .ok out) :
    ∃ (canonical : Machine) (selected : Nat → Fin W), canonical.stack = [] ∧ ∀ tail,
      run body.code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
      run (compiled body).code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
      MappedOutput (.memory (compiled body)) L frame base entry {machine with stack := tail}
        (out.st.drop P.ext) {canonical with stack := tail} selected := by
  obtain ⟨canonical,selected,_,empty,runs⟩ := compilation_success_shared_mapped (.memory body) h noPay success
  refine ⟨canonical,selected,empty,?_⟩
  intro tail
  have represented := (runs tail).2
  rw [body.cert.pushes_zero, Nat.add_zero] at represented
  exact ⟨(runs tail).1, by rw [code]; exact (runs tail).1, output body represented⟩

end Solidity.Backend.Passes.MemoryScopeBoundary
