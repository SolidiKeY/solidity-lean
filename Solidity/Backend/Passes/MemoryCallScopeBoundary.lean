import Solidity.Backend.Passes.MemoryScopeBoundary

/-! Scope transport for the expanded-call compiler branch. Private call need,
actual reached cost, push-free witness and selected heap map are retained. -/
namespace Solidity.Backend.Passes.MemoryCallScopeBoundary
open Evm Evm.Memory Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}

@[irreducible] def compiled (body : Calls.Program b F P) : Calls.Program b F (MemoryScopeBoundary.program P) :=
  Calls.cons (Calls.block body) (Calls.nil b (body.frag.restrict Γ))

theorem frag (body : Calls.Program b F P) : (compiled body).frag = body.frag.restrict Γ := by
  unfold compiled
  rfl

theorem code (body : Calls.Program b F P) : (compiled body).code = body.code := by
  unfold compiled
  exact List.append_nil _

theorem need (body : Calls.Program b F P) : (compiled body).need = max body.need Γ.length := by
  unfold compiled
  rfl

theorem cost (body : Calls.Program b F P) (state : State C Γ) :
    (compiled body).cost state = body.cost state := by
  unfold compiled
  rfl

theorem scope_free (free : Evm.Prog.pushes P = 0) :
    Evm.Prog.pushes (MemoryScopeBoundary.program P) = 0 := by
  change Evm.Prog.pushes P + 0 = 0
  rw [free]

theorem input (body : Calls.Program b F P) (free : Evm.Prog.pushes P = 0)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (h : (Compilation.memoryCalls body free).Input L frame base state machine) :
    (Compilation.memoryCalls (compiled body) (scope_free free)).Input L frame base state machine := by
  refine ⟨h.1, ?_, ?_⟩
  · have locals := h.1.locals
    have privateRoom := h.2.1
    rw [need]
    omega
  · rw [cost]
    exact h.2.2

theorem input_back (body : Calls.Program b F P) (free : Evm.Prog.pushes P = 0)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (h : (Compilation.memoryCalls (compiled body) (scope_free free)).Input L frame base state machine) :
    (Compilation.memoryCalls body free).Input L frame base state machine := by
  refine ⟨h.1, ?_, ?_⟩
  · have room := h.2.1
    rw [need] at room
    omega
  · simpa only [cost] using h.2.2

theorem input_iff (body : Calls.Program b F P) (free : Evm.Prog.pushes P = 0)
    (state : State C Γ) (base : Nat → Fin W) (machine : Machine) :
    (Compilation.memoryCalls (compiled body) (scope_free free)).Input L frame base state machine ↔
      (Compilation.memoryCalls body free).Input L frame base state machine :=
  ⟨input_back body free, input body free⟩

theorem output (body : Calls.Program b F P) (free : Evm.Prog.pushes P = 0)
    {entry : State C Γ} {initial middle : Machine} {base selected : Nat → Fin W} {state : State C Δ}
    (h : MappedOutput (.memoryCalls body free) L frame base entry initial state middle selected) :
    MappedOutput (.memoryCalls (compiled body) (scope_free free)) L frame base entry initial
      (state.drop P.ext) middle selected := by
  change StateRepr L b frame (compiled body).frag (state.drop P.ext) selected middle ∧
    BaseExtends entry.H base selected ∧
    GrowsAllocator b frame ((compiled body).cost entry) entry base initial (state.drop P.ext) selected middle
  rw [frag,cost]
  exact ⟨h.1.drop P.ext,h.2.1,h.2.2⟩

theorem shared (body : Calls.Program b F P) (free : Evm.Prog.pushes P = 0)
    {entry : State C Γ} {machine : Machine} {base : Nat → Fin W}
    (h : (Compilation.memoryCalls body free).Input L frame base entry machine)
    (noPay : Evm.Prog.pays P = false) {out : Solidity.Out C entry.H Δ}
    (success : P.run entry = .ok out) :
    ∃ (canonical : Machine) (selected : Nat → Fin W), canonical.stack = [] ∧ ∀ tail,
      run body.code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
      run (compiled body).code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
      MappedOutput (.memoryCalls (compiled body) (scope_free free)) L frame base entry {machine with stack := tail}
        (out.st.drop P.ext) {canonical with stack := tail} selected := by
  obtain ⟨canonical,selected,_,empty,runs⟩ :=
    compilation_success_shared_mapped (.memoryCalls body free) h noPay success
  refine ⟨canonical,selected,empty,?_⟩
  intro tail
  have represented := (runs tail).2
  rw [free,Nat.add_zero] at represented
  exact ⟨(runs tail).1, by rw [code]; exact (runs tail).1, output body free represented⟩

end Solidity.Backend.Passes.MemoryCallScopeBoundary
