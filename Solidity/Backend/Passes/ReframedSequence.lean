import Solidity.Backend.Passes.Frame
import Solidity.Backend.Passes.Divergence

/-! Frame-sensitive proof adapters over ACTUAL Compilation and Instr.
The prefix and suffix keep different reservation predicates. No frame/state/IR
representation changes; shrinking does not erase local or code capacity. -/
namespace Solidity.Backend.Passes
open Evm Evm.Compiler
variable {C : Contract} {b L beforeFrame afterFrame : Nat} {Γ Δ Ξ : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}

/-- Full existing heap ownership survives a smaller reservation only if ALL
current locals fit. Heap bounds follow from the old separation, not a new map. -/
theorem memory_state_shrink {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (h : Memory.StateRepr L b beforeFrame F σ base m)
    (smaller : afterFrame ≤ beforeFrame) (locals : b + Γ.length ≤ afterFrame) :
    Memory.StateRepr L b afterFrame F σ base m :=
  memory_frame h locals
    (fun r => Nat.le_trans smaller (h.heap.above r))
    (fun r => Nat.le_trans smaller (h.structs.above r))

/-- A physical boundary can reserve a DIFFERENT suffix frame. Both relations
retain their original frame, selected map, source and target successes. -/
def ReframedLink (left : Compilation b F P) (right : Compilation b left.frag Q)
    (L beforeFrame afterFrame : Nat) (base : Nat → Fin W)
    (σ : State C Γ) (m : Machine) : Prop :=
  ∀ (o : Solidity.Out C σ.H Δ) (mid : Machine) (selected : Nat → Fin W),
    P.run σ = .ok o → run left.code m = .ok mid 0 →
    MappedOutput left (L + Evm.Prog.pushes P) beforeFrame base σ m o.st mid selected →
    right.Input (L + Evm.Prog.pushes P) afterFrame selected o.st mid

/-- A published memory output supplies the reached suffix heap and map.
Nonallocation is a real syntactic property, never an assumed preservation. -/
theorem memory_shrinking_link (left : Memory.CompiledProg b F P)
    (right : Memory.CompiledProg b left.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (smaller : afterFrame ≤ beforeFrame) (locals : b + Δ.length ≤ afterFrame)
    (codeRoom : b + Memory.frameNeedProg Q ≤ afterFrame)
    (noAlloc : Memory.hasAllocation Q = false) :
    ReframedLink (.memory left) (.memory right) L beforeFrame afterFrame base σ m := by
  intro o mid selected _ _ output
  exact ⟨memory_state_shrink output.1 smaller locals,codeRoom,
    .inl (Memory.allocationCostProg_zero Q noAlloc o.st)⟩

/-- The expanded call's ACTUAL escaped heap/map survives frame release.
Its original private need/cost/push-free certificate is not changed. -/
theorem memoryCalls_shrinking_link (left : Memory.Calls.Program b F P)
    (pushFree : Evm.Prog.pushes P = 0) (right : Memory.CompiledProg b left.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (smaller : afterFrame ≤ beforeFrame) (locals : b + Δ.length ≤ afterFrame)
    (codeRoom : b + Memory.frameNeedProg Q ≤ afterFrame)
    (noAlloc : Memory.hasAllocation Q = false) :
    ReframedLink (.memoryCalls left pushFree) (.memory right)
      L beforeFrame afterFrame base σ m := by
  intro o mid selected _ _ output
  exact ⟨memory_state_shrink output.1 smaller locals,codeRoom,
    .inl (Memory.allocationCostProg_zero Q noAlloc o.st)⟩

/-- Same-frame links remain usable, with all original obligations. -/
theorem reframed_same (left : Compilation b F P) (right : Compilation b left.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (h : MappedBoundaryLink left right L beforeFrame base σ m) :
    ReframedLink left right L beforeFrame beforeFrame base σ m := h

/-- Exact reached states/maps at DIFFERENT physical frame predicates. Both
maps/machine skeletons precede tails; all Input/run/output facts are PER TAIL. -/
theorem compilation_reframed_shared
    (left : Compilation b F P) (right : Compilation b left.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : left.Input L beforeFrame base σ m) (empty : m.stack = [])
    (link : ReframedLink left right L beforeFrame afterFrame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o)
    {u : Solidity.Out C o.st.H Ξ} (hu : Q.run o.st = .ok u) :
    ∃ (mb nb : Nat → Fin W) (mid final : Machine),
      (P.join Q).run σ = .ok ⟨u.st,o.ext.trans u.ext⟩ ∧
      mid.stack = [] ∧ final.stack = [] ∧ ∀ tail,
      left.Input L beforeFrame base σ {m with stack := tail} ∧
      run left.code {m with stack := tail} = .ok {mid with stack := tail} 0 ∧
      MappedOutput left (L + Evm.Prog.pushes P) beforeFrame base σ
        {m with stack := tail} o.st {mid with stack := tail} mb ∧
      right.Input (L + Evm.Prog.pushes P) afterFrame mb o.st {mid with stack := tail} ∧
      run right.code {mid with stack := tail} = .ok {final with stack := tail} 0 ∧
      MappedOutput right ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q)
        afterFrame mb o.st {mid with stack := tail} u.st {final with stack := tail} nb ∧
      run (left.code ++ right.code) {m with stack := tail} =
        .ok {final with stack := tail} 0 := by
  obtain ⟨mid, hm, sm, ml⟩ := compilation_success left hi hp hs
  obtain ⟨mb, ml⟩ := (mapped_output_iff left _ _ _ _ _ _ _).mp ml
  have ir := link o mid mb hs hm ml
  obtain ⟨final, hf, sf, mr⟩ := compilation_success right ir hq hu
  obtain ⟨nb, mr⟩ := (mapped_output_iff right _ _ _ _ _ _ _).mp mr
  have sm' : mid.stack = [] := sm.trans empty
  have sf' : final.stack = [] := sf.trans sm'
  refine ⟨mb,nb,mid,final,?_,sm',sf',?_⟩
  · rw [DeferredSource.join_run]
    simp only [TRun.seq,hs,hu,Except.map]
  · intro tail
    have transport (code : List Instr) (x y : Machine)
        (hx : x.stack = []) (hy : y.stack = []) (h : run code x = .ok y 0) :
        run code {x with stack := tail} = .ok {y with stack := tail} 0 := by
      have htail := run_tail code x tail (by rw [h]; intro bad; cases bad)
      simpa only [h,appendOut,appendTail,hx,hy,List.nil_append] using htail
    have hleft := transport left.code m mid empty sm' hm
    have hright := transport right.code mid final sm' sf' hf
    exact ⟨compilation_input_stack left hi tail,hleft,
      mapped_output_stack left ml tail tail,compilation_input_stack right ir tail,hright,
      mapped_output_stack right mr tail tail,by rw [run_append_ok hleft];exact hright⟩

/-- Coarse two-sided failure still distinguishes immediate from reached
failure. Suffix Input is demanded only after an actual successful prefix. -/
theorem compilation_reframed_revert_iff
    (left : Compilation b F P) (right : Compilation b left.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : left.Input L beforeFrame base σ m)
    (link : ReframedLink left right L beforeFrame afterFrame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false) :
    run (left.code ++ right.code) m = .revert ↔
      TerminalFailure P σ ∨ ∃ o, P.run σ = .ok o ∧ TerminalFailure Q o.st := by
  constructor
  · intro ht
    rcases compilation_exact left hi hp with
      ⟨o,mid,hs,hm,_,rep⟩ | ⟨hs,_⟩ | ⟨_,hm⟩
    · obtain ⟨mb,out⟩ := (mapped_output_iff left _ _ _ _ _ _ _).mp rep
      rw [run_append_ok hm] at ht
      exact .inr ⟨o,hs,(compilation_revert_iff right (link o mid mb hs hm out) hq).mp ht⟩
    · exact .inl hs
    · have impossible := run_append_fault (c₂ := right.code) hm
      rw [ht] at impossible
      cases impossible
  · rintro (hs | ⟨o,hs,bad⟩)
    · exact run_append_revert ((compilation_revert_iff left hi hp).mpr hs)
    · obtain ⟨mid,hm,_,rep⟩ := compilation_success left hi hp hs
      obtain ⟨mb,out⟩ := (mapped_output_iff left _ _ _ _ _ _ _).mp rep
      rw [run_append_ok hm]
      exact (compilation_revert_iff right (link o mid mb hs hm out) hq).mpr bad

/-- Fault transport uses the typed suffix Input/source divergence, NEVER a
raw run_tail argument for faulting target code. -/
theorem compilation_reframed_fault_iff
    (left : Compilation b F P) (right : Compilation b left.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : left.Input L beforeFrame base σ m)
    (link : ReframedLink left right L beforeFrame afterFrame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false) :
    run (left.code ++ right.code) m = .fault ↔
      P.run σ = .error .diverge ∨ ∃ o, P.run σ = .ok o ∧ Q.run o.st = .error .diverge := by
  constructor
  · intro ht
    rcases compilation_exact left hi hp with
      ⟨o,mid,hs,hm,_,rep⟩ | ⟨_,hm⟩ | ⟨hs,_⟩
    · obtain ⟨mb,out⟩ := (mapped_output_iff left _ _ _ _ _ _ _).mp rep
      rw [run_append_ok hm] at ht
      exact .inr ⟨o,hs,(compilation_fault_iff right (link o mid mb hs hm out) hq).mp ht⟩
    · have impossible := run_append_revert (c₂ := right.code) hm
      rw [ht] at impossible
      cases impossible
    · exact .inl hs
  · rintro (hs | ⟨o,hs,bad⟩)
    · exact run_append_fault ((compilation_fault_iff left hi hp).mpr hs)
    · obtain ⟨mid,hm,_,rep⟩ := compilation_success left hi hp hs
      obtain ⟨mb,out⟩ := (mapped_output_iff left _ _ _ _ _ _ _).mp rep
      rw [run_append_ok hm]
      exact (compilation_fault_iff right (link o mid mb hs hm out) hq).mpr bad
end Solidity.Backend.Passes
