import Solidity.Backend.Passes.ReframedSequence

/-! DRAFT / UNVALIDATED: private source-owner design for independent validation.
Exact successful-prefix witnesses across DIFFERENT original frame predicates.
No public session/resource/ABI adequacy, no post-failure state or map. -/
namespace Solidity.Backend.Passes
open Evm Evm.Compiler
variable {C : Contract} {b L beforeFrame afterFrame : Nat} {Γ Δ Ξ : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}

/-- The immediate alternative requires no suffix execution/Input. A reached
failure exposes the actual typed source output, target machine, selected map,
FULL prefix output, transported suffix Input and actual suffix revert. -/
theorem compilation_reframed_revert_witness_iff
    (left : Compilation b F P) (right : Compilation b left.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : left.Input L beforeFrame base σ m)
    (link : ReframedLink left right L beforeFrame afterFrame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false) :
    run (left.code ++ right.code) m = .revert ↔
      (TerminalFailure P σ ∧ run left.code m = .revert) ∨
      ∃ (o : Solidity.Out C σ.H Δ) (mid : Machine) (selected : Nat → Fin W),
        P.run σ = .ok o ∧ run left.code m = .ok mid 0 ∧
        MappedOutput left (L + Evm.Prog.pushes P) beforeFrame
          base σ m o.st mid selected ∧
        right.Input (L + Evm.Prog.pushes P) afterFrame selected o.st mid ∧
        TerminalFailure Q o.st ∧ run right.code mid = .revert := by
  constructor
  · intro whole
    rcases (compilation_reframed_revert_iff left right hi link hp hq).mp whole with
      immediate | ⟨o,source,bad⟩
    · exact .inl ⟨immediate,(compilation_revert_iff left hi hp).mpr immediate⟩
    · obtain ⟨mid,target,_,rep⟩ := compilation_success left hi hp source
      obtain ⟨selected,output⟩ := (mapped_output_iff left _ _ _ _ _ _ _).mp rep
      have input : right.Input (L + Evm.Prog.pushes P) afterFrame selected o.st mid := link o mid selected source target output
      exact .inr ⟨o,mid,selected,source,target,output,input,bad,
        (compilation_revert_iff right input hq).mpr bad⟩
  · rintro (⟨_,target⟩ | ⟨o,mid,selected,_,target,_,_,_,bad⟩)
    · exact run_append_revert target
    · rw [run_append_ok target]
      exact bad

/-- Reached ordinary revert or guarded panic, with the same chosen prefix map
and machine BEFORE all saved tails. Only successful code uses run_tail. -/
theorem compilation_reframed_reached_revert_shared
    (left : Compilation b F P) (right : Compilation b left.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : left.Input L beforeFrame base σ m) (empty : m.stack = [])
    (link : ReframedLink left right L beforeFrame afterFrame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    {o : Solidity.Out C σ.H Δ} (source : P.run σ = .ok o)
    (bad : TerminalFailure Q o.st) :
    ∃ (mid : Machine) (selected : Nat → Fin W), mid.stack = [] ∧ ∀ tail,
      left.Input L beforeFrame base σ {m with stack := tail} ∧
      run left.code {m with stack := tail} = .ok {mid with stack := tail} 0 ∧
      MappedOutput left (L + Evm.Prog.pushes P) beforeFrame base σ
        {m with stack := tail} o.st {mid with stack := tail} selected ∧
      right.Input (L + Evm.Prog.pushes P) afterFrame selected o.st
        {mid with stack := tail} ∧
      TerminalFailure Q o.st ∧
      run right.code {mid with stack := tail} = .revert ∧
      run (left.code ++ right.code) {m with stack := tail} = .revert := by
  obtain ⟨mid,target,stack,rep⟩ := compilation_success left hi hp source
  obtain ⟨selected,output⟩ := (mapped_output_iff left _ _ _ _ _ _ _).mp rep
  have midEmpty : mid.stack = [] := stack.trans empty
  have input : right.Input (L + Evm.Prog.pushes P) afterFrame selected o.st mid := link o mid selected source target output
  refine ⟨mid,selected,midEmpty,?_⟩
  intro tail
  have prefixRun : run left.code (appendTail m tail) = appendOut tail (run left.code m) := run_tail left.code m tail (by rw [target]; intro h; cases h)
  have prefixTail : run left.code {m with stack := tail} =
      .ok {mid with stack := tail} 0 := by
    simpa only [target,appendOut,appendTail,empty,midEmpty,List.nil_append] using prefixRun
  have inputTail : right.Input (L + Evm.Prog.pushes P) afterFrame selected o.st
      {mid with stack := tail} := compilation_input_stack right input tail
  have suffixTail : run right.code {mid with stack := tail} = .revert := (compilation_revert_iff right inputTail hq).mpr bad
  refine ⟨compilation_input_stack left hi tail,prefixTail,
    mapped_output_stack left output tail tail,inputTail,bad,suffixTail,?_⟩
  rw [run_append_ok prefixTail]
  exact suffixTail

/-- The analogous reached divergence keeps the actual failing-stage Input/run.
No faulting target code is transported by raw run_tail. -/
theorem compilation_reframed_reached_fault_shared
    (left : Compilation b F P) (right : Compilation b left.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : left.Input L beforeFrame base σ m) (empty : m.stack = [])
    (link : ReframedLink left right L beforeFrame afterFrame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    {o : Solidity.Out C σ.H Δ} (source : P.run σ = .ok o)
    (diverges : Q.run o.st = .error .diverge) :
    ∃ (mid : Machine) (selected : Nat → Fin W), mid.stack = [] ∧ ∀ tail,
      run left.code {m with stack := tail} = .ok {mid with stack := tail} 0 ∧
      MappedOutput left (L + Evm.Prog.pushes P) beforeFrame base σ
        {m with stack := tail} o.st {mid with stack := tail} selected ∧
      right.Input (L + Evm.Prog.pushes P) afterFrame selected o.st
        {mid with stack := tail} ∧
      Q.run o.st = .error .diverge ∧
      run right.code {mid with stack := tail} = .fault ∧
      run (left.code ++ right.code) {m with stack := tail} = .fault := by
  obtain ⟨mid,target,stack,rep⟩ := compilation_success left hi hp source
  obtain ⟨selected,output⟩ := (mapped_output_iff left _ _ _ _ _ _ _).mp rep
  have midEmpty : mid.stack = [] := stack.trans empty
  have input : right.Input (L + Evm.Prog.pushes P) afterFrame selected o.st mid := link o mid selected source target output
  refine ⟨mid,selected,midEmpty,?_⟩
  intro tail
  have prefixRun : run left.code (appendTail m tail) = appendOut tail (run left.code m) := run_tail left.code m tail (by rw [target]; intro h; cases h)
  have prefixTail : run left.code {m with stack := tail} =
      .ok {mid with stack := tail} 0 := by
    simpa only [target,appendOut,appendTail,empty,midEmpty,List.nil_append] using prefixRun
  have inputTail : right.Input (L + Evm.Prog.pushes P) afterFrame selected o.st
      {mid with stack := tail} := compilation_input_stack right input tail
  have fault : run right.code {mid with stack := tail} = .fault := (compilation_fault_iff right inputTail hq).mpr diverges
  refine ⟨prefixTail,mapped_output_stack left output tail tail,inputTail,
    diverges,fault,?_⟩
  rw [run_append_ok prefixTail]
  exact fault
end Solidity.Backend.Passes
