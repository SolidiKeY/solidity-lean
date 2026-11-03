import Solidity.Backend.Passes.ReframedSequence
import Solidity.Backend.Passes.SourceTerminalFailure

/-! Three actual typed stages with independently retained physical frames.
This is internal terminal composition, not public Source/world/session adequacy.
No equality of reached machines is inferred merely from representation. -/
namespace Solidity.Backend.Passes
open Evm Evm.Compiler
variable {C : Contract} {b L frameA frameB frameC : Nat} {Γ Δ Ξ Ω : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ} {R : Prog C Ξ Ω}

/-- The third Input consumes the second stage's actual map and state, after
the first actual successful source/target prefix has selected its own map. -/
def ReachedReframedLink (a : Compilation b F P) (d : Compilation b a.frag Q)
    (e : Compilation b d.frag R) (L frameA frameB frameC : Nat)
    (base : Nat → Fin W) (σ : State C Γ) (m : Machine) : Prop :=
  ∀ (o : Solidity.Out C σ.H Δ) (mid : Machine) (mb : Nat → Fin W),
    P.run σ = .ok o → run a.code m = .ok mid 0 →
    MappedOutput a (L + Evm.Prog.pushes P) frameA base σ m o.st mid mb →
    ReframedLink d e (L + Evm.Prog.pushes P) frameB frameC mb o.st mid

/-- All actual maps/machine skeletons precede tails. Every original Input and
full branch output retains its OWN frame, at the correlated reached state. -/
theorem compilation_reframed_triple_shared
    (a : Compilation b F P) (d : Compilation b a.frag Q) (e : Compilation b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (input : a.Input L frameA base σ m) (empty : m.stack = [])
    (first : ReframedLink a d L frameA frameB base σ m)
    (second : ReachedReframedLink a d e L frameA frameB frameC base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    (hr : Evm.Prog.pays R = false)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o)
    {u : Solidity.Out C o.st.H Ξ} (hu : Q.run o.st = .ok u)
    {v : Solidity.Out C u.st.H Ω} (hv : R.run u.st = .ok v) :
    ∃ (mb nb ob : Nat → Fin W) (mid next final : Machine),
      ((P.join Q).join R).run σ = .ok ⟨v.st,(o.ext.trans u.ext).trans v.ext⟩ ∧
      (P.join (Q.join R)).run σ = .ok ⟨v.st,o.ext.trans (u.ext.trans v.ext)⟩ ∧
      mid.stack = [] ∧ next.stack = [] ∧ final.stack = [] ∧ ∀ tail,
      a.Input L frameA base σ {m with stack := tail} ∧
      run a.code {m with stack := tail} = .ok {mid with stack := tail} 0 ∧
      MappedOutput a (L + Evm.Prog.pushes P) frameA base σ
        {m with stack := tail} o.st {mid with stack := tail} mb ∧
      d.Input (L + Evm.Prog.pushes P) frameB mb o.st {mid with stack := tail} ∧
      run d.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
      MappedOutput d ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q) frameB mb o.st
        {mid with stack := tail} u.st {next with stack := tail} nb ∧
      e.Input ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q) frameC nb u.st
        {next with stack := tail} ∧
      run e.code {next with stack := tail} = .ok {final with stack := tail} 0 ∧
      MappedOutput e (((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q) + Evm.Prog.pushes R)
        frameC nb u.st {next with stack := tail} v.st {final with stack := tail} ob ∧
      run ((a.code ++ d.code) ++ e.code) {m with stack := tail} =
        .ok {final with stack := tail} 0 ∧
      run (a.code ++ (d.code ++ e.code)) {m with stack := tail} =
        .ok {final with stack := tail} 0 := by
  obtain ⟨mid,ha,stack,rep⟩ := compilation_success a input hp hs
  obtain ⟨mb,ma⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp rep
  have middleInput := first o mid mb hs ha ma
  have middleEmpty : mid.stack = [] := stack.trans empty
  obtain ⟨nb,ob,next,final,_,nextEmpty,finalEmpty,rest⟩ :=
    compilation_reframed_shared d e middleInput middleEmpty
      (second o mid mb hs ha ma) hq hr hu hv
  refine ⟨mb,nb,ob,mid,next,final,(triple_source_success σ hs hu hv).1,
    (triple_source_success σ hs hu hv).2,middleEmpty,nextEmpty,finalEmpty,?_⟩
  intro tail
  have transported := run_tail a.code m tail (by rw [ha]; intro bad; cases bad)
  have firstRun : run a.code {m with stack := tail} = .ok {mid with stack := tail} 0 := by
    simpa only [ha,appendOut,appendTail,empty,middleEmpty,List.nil_append] using transported
  obtain ⟨id,hd,md,ie,he,me,hde⟩ := rest tail
  have whole : run (a.code ++ (d.code ++ e.code)) {m with stack := tail} =
      .ok {final with stack := tail} 0 := by
    rw [run_append_ok firstRun]
    exact hde
  exact ⟨compilation_input_stack a input tail,firstRun,mapped_output_stack a ma tail tail,
    id,hd,md,ie,he,me,by simpa only [List.append_assoc] using whole,whole⟩

/-- Immediate, middle and third-stage failures require no skipped source
success. The right Input is required only at each actual reached boundary. -/
theorem compilation_reframed_triple_revert_iff
    (a : Compilation b F P) (d : Compilation b a.frag Q) (e : Compilation b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (input : a.Input L frameA base σ m)
    (first : ReframedLink a d L frameA frameB base σ m)
    (second : ReachedReframedLink a d e L frameA frameB frameC base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    (hr : Evm.Prog.pays R = false) :
    run (a.code ++ (d.code ++ e.code)) m = .revert ↔
      TerminalFailure P σ ∨ ∃ o, P.run σ = .ok o ∧
        (TerminalFailure Q o.st ∨ ∃ u, Q.run o.st = .ok u ∧ TerminalFailure R u.st) := by
  constructor
  · intro whole
    rcases compilation_exact a input hp with
      ⟨o,mid,hs,ha,_,rep⟩ | ⟨bad,_⟩ | ⟨_,ha⟩
    · obtain ⟨mb,ma⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp rep
      rw [run_append_ok ha] at whole
      exact .inr ⟨o,hs,(compilation_reframed_revert_iff d e
        (first o mid mb hs ha ma) (second o mid mb hs ha ma) hq hr).mp whole⟩
    · exact .inl bad
    · have impossible := run_append_fault (c₂ := d.code ++ e.code) ha
      rw [whole] at impossible
      cases impossible
  · rintro (bad | ⟨o,hs,bad⟩)
    · exact run_append_revert ((compilation_revert_iff a input hp).mpr bad)
    · obtain ⟨mid,ha,_,rep⟩ := compilation_success a input hp hs
      obtain ⟨mb,ma⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp rep
      rw [run_append_ok ha]
      exact (compilation_reframed_revert_iff d e
        (first o mid mb hs ha ma) (second o mid mb hs ha ma) hq hr).mpr bad

theorem compilation_reframed_triple_fault_iff
    (a : Compilation b F P) (d : Compilation b a.frag Q) (e : Compilation b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (input : a.Input L frameA base σ m)
    (first : ReframedLink a d L frameA frameB base σ m)
    (second : ReachedReframedLink a d e L frameA frameB frameC base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    (hr : Evm.Prog.pays R = false) :
    run (a.code ++ (d.code ++ e.code)) m = .fault ↔
      P.run σ = .error .diverge ∨ ∃ o, P.run σ = .ok o ∧
        (Q.run o.st = .error .diverge ∨ ∃ u,
          Q.run o.st = .ok u ∧ R.run u.st = .error .diverge) := by
  constructor
  · intro whole
    rcases compilation_exact a input hp with
      ⟨o,mid,hs,ha,_,rep⟩ | ⟨_,ha⟩ | ⟨bad,_⟩
    · obtain ⟨mb,ma⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp rep
      rw [run_append_ok ha] at whole
      exact .inr ⟨o,hs,(compilation_reframed_fault_iff d e
        (first o mid mb hs ha ma) (second o mid mb hs ha ma) hq hr).mp whole⟩
    · have impossible := run_append_revert (c₂ := d.code ++ e.code) ha
      rw [whole] at impossible
      cases impossible
    · exact .inl bad
  · rintro (bad | ⟨o,hs,bad⟩)
    · exact run_append_fault ((compilation_fault_iff a input hp).mpr bad)
    · obtain ⟨mid,ha,_,rep⟩ := compilation_success a input hp hs
      obtain ⟨mb,ma⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp rep
      rw [run_append_ok ha]
      exact (compilation_reframed_fault_iff d e
        (first o mid mb hs ha ma) (second o mid mb hs ha ma) hq hr).mpr bad

/-- Actual joined intrinsic programs, not just a reached-case formula. -/
theorem compilation_reframed_triple_join_revert_iff
    (a : Compilation b F P) (d : Compilation b a.frag Q) (e : Compilation b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (input : a.Input L frameA base σ m)
    (first : ReframedLink a d L frameA frameB base σ m)
    (second : ReachedReframedLink a d e L frameA frameB frameC base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    (hr : Evm.Prog.pays R = false) :
    (run (a.code ++ (d.code ++ e.code)) m = .revert ↔
      TerminalFailure (P.join (Q.join R)) σ) ∧
    (run ((a.code ++ d.code) ++ e.code) m = .revert ↔
      TerminalFailure ((P.join Q).join R) σ) := by
  have joined : TerminalFailure (P.join (Q.join R)) σ ↔
      TerminalFailure P σ ∨ ∃ o, P.run σ = .ok o ∧
        (TerminalFailure Q o.st ∨ ∃ u, Q.run o.st = .ok u ∧ TerminalFailure R u.st) := by
    rw [joined_terminal_failure_iff]
    simp only [joined_terminal_failure_iff]
  have result := (compilation_reframed_triple_revert_iff a d e input first second hp hq hr).trans joined.symm
  exact ⟨result,by simpa only [List.append_assoc,typed_sequencing_assoc] using result⟩

theorem compilation_reframed_triple_join_fault_iff
    (a : Compilation b F P) (d : Compilation b a.frag Q) (e : Compilation b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (input : a.Input L frameA base σ m)
    (first : ReframedLink a d L frameA frameB base σ m)
    (second : ReachedReframedLink a d e L frameA frameB frameC base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    (hr : Evm.Prog.pays R = false) :
    (run (a.code ++ (d.code ++ e.code)) m = .fault ↔
      (P.join (Q.join R)).run σ = .error .diverge) ∧
    (run ((a.code ++ d.code) ++ e.code) m = .fault ↔
      ((P.join Q).join R).run σ = .error .diverge) := by
  have joined : (P.join (Q.join R)).run σ = .error .diverge ↔
      P.run σ = .error .diverge ∨ ∃ o, P.run σ = .ok o ∧
        (Q.run o.st = .error .diverge ∨ ∃ u,
          Q.run o.st = .ok u ∧ R.run u.st = .error .diverge) := by
    rw [joined_halt_iff]
    simp only [joined_halt_iff]
  have result := (compilation_reframed_triple_fault_iff a d e input first second hp hq hr).trans joined.symm
  exact ⟨result,by simpa only [List.append_assoc,typed_sequencing_assoc] using result⟩

/-- Exact actual successful-prefix witnesses for each reached revert stage,
with the failing Input and target run exposed at its own original frame. -/
theorem compilation_reframed_triple_revert_witness_iff
    (a : Compilation b F P) (d : Compilation b a.frag Q) (e : Compilation b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (input : a.Input L frameA base σ m)
    (first : ReframedLink a d L frameA frameB base σ m)
    (second : ReachedReframedLink a d e L frameA frameB frameC base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    (hr : Evm.Prog.pays R = false) :
    run (a.code ++ (d.code ++ e.code)) m = .revert ↔
      (TerminalFailure P σ ∧ run a.code m = .revert) ∨
      ∃ (o : Solidity.Out C σ.H Δ) (mid : Machine) (mb : Nat → Fin W),
        P.run σ = .ok o ∧ run a.code m = .ok mid 0 ∧
        MappedOutput a (L + Evm.Prog.pushes P) frameA base σ m o.st mid mb ∧
        d.Input (L + Evm.Prog.pushes P) frameB mb o.st mid ∧
        ((TerminalFailure Q o.st ∧ run d.code mid = .revert) ∨
          ∃ (u : Solidity.Out C o.st.H Ξ) (next : Machine) (nb : Nat → Fin W),
            Q.run o.st = .ok u ∧ run d.code mid = .ok next 0 ∧
            MappedOutput d ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q)
              frameB mb o.st mid u.st next nb ∧
            e.Input ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q) frameC nb u.st next ∧
            TerminalFailure R u.st ∧ run e.code next = .revert) := by
  constructor
  · intro whole
    rcases compilation_exact a input hp with
      ⟨o,mid,hs,ha,_,rep⟩ | ⟨bad,ha⟩ | ⟨_,ha⟩
    · obtain ⟨mb,ma⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp rep
      have middleInput := first o mid mb hs ha ma
      rw [run_append_ok ha] at whole
      rcases compilation_exact d middleInput hq with
        ⟨u,next,hu,hd,_,repd⟩ | ⟨bad,hd⟩ | ⟨_,hd⟩
      · obtain ⟨nb,md⟩ := (mapped_output_iff d _ _ _ _ _ _ _).mp repd
        have finalInput := second o mid mb hs ha ma u next nb hu hd md
        rw [run_append_ok hd] at whole
        exact .inr ⟨o,mid,mb,hs,ha,ma,middleInput,.inr
          ⟨u,next,nb,hu,hd,md,finalInput,
            (compilation_revert_iff e finalInput hr).mp whole,whole⟩⟩
      · exact .inr ⟨o,mid,mb,hs,ha,ma,middleInput,.inl ⟨bad,hd⟩⟩
      · have impossible := run_append_fault (c₂ := e.code) hd
        rw [whole] at impossible
        cases impossible
    · exact .inl ⟨bad,ha⟩
    · have impossible := run_append_fault (c₂ := d.code ++ e.code) ha
      rw [whole] at impossible
      cases impossible
  · rintro (⟨_,ha⟩ | ⟨o,mid,mb,_,ha,_,_,rest⟩)
    · exact run_append_revert ha
    · rw [run_append_ok ha]
      rcases rest with ⟨_,hd⟩ | ⟨u,next,nb,_,hd,_,_,_,he⟩
      · exact run_append_revert hd
      · rw [run_append_ok hd]
        exact he

/-- Divergence is separate from revert/panic. Faulting code is NEVER used
with raw run_tail; each actual fault follows its reached typed Input. -/
theorem compilation_reframed_triple_fault_witness_iff
    (a : Compilation b F P) (d : Compilation b a.frag Q) (e : Compilation b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (input : a.Input L frameA base σ m)
    (first : ReframedLink a d L frameA frameB base σ m)
    (second : ReachedReframedLink a d e L frameA frameB frameC base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false)
    (hr : Evm.Prog.pays R = false) :
    run (a.code ++ (d.code ++ e.code)) m = .fault ↔
      (P.run σ = .error .diverge ∧ run a.code m = .fault) ∨
      ∃ (o : Solidity.Out C σ.H Δ) (mid : Machine) (mb : Nat → Fin W),
        P.run σ = .ok o ∧ run a.code m = .ok mid 0 ∧
        MappedOutput a (L + Evm.Prog.pushes P) frameA base σ m o.st mid mb ∧
        d.Input (L + Evm.Prog.pushes P) frameB mb o.st mid ∧
        ((Q.run o.st = .error .diverge ∧ run d.code mid = .fault) ∨
          ∃ (u : Solidity.Out C o.st.H Ξ) (next : Machine) (nb : Nat → Fin W),
            Q.run o.st = .ok u ∧ run d.code mid = .ok next 0 ∧
            MappedOutput d ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q)
              frameB mb o.st mid u.st next nb ∧
            e.Input ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q) frameC nb u.st next ∧
            R.run u.st = .error .diverge ∧ run e.code next = .fault) := by
  constructor
  · intro whole
    rcases compilation_exact a input hp with
      ⟨o,mid,hs,ha,_,rep⟩ | ⟨_,ha⟩ | ⟨bad,ha⟩
    · obtain ⟨mb,ma⟩ := (mapped_output_iff a _ _ _ _ _ _ _).mp rep
      have middleInput := first o mid mb hs ha ma
      rw [run_append_ok ha] at whole
      rcases compilation_exact d middleInput hq with
        ⟨u,next,hu,hd,_,repd⟩ | ⟨_,hd⟩ | ⟨bad,hd⟩
      · obtain ⟨nb,md⟩ := (mapped_output_iff d _ _ _ _ _ _ _).mp repd
        have finalInput := second o mid mb hs ha ma u next nb hu hd md
        rw [run_append_ok hd] at whole
        exact .inr ⟨o,mid,mb,hs,ha,ma,middleInput,.inr
          ⟨u,next,nb,hu,hd,md,finalInput,
            (compilation_fault_iff e finalInput hr).mp whole,whole⟩⟩
      · have impossible := run_append_revert (c₂ := e.code) hd
        rw [whole] at impossible
        cases impossible
      · exact .inr ⟨o,mid,mb,hs,ha,ma,middleInput,.inl ⟨bad,hd⟩⟩
    · have impossible := run_append_revert (c₂ := d.code ++ e.code) ha
      rw [whole] at impossible
      cases impossible
    · exact .inl ⟨bad,ha⟩
  · rintro (⟨_,ha⟩ | ⟨o,mid,mb,_,ha,_,_,rest⟩)
    · exact run_append_fault ha
    · rw [run_append_ok ha]
      rcases rest with ⟨_,hd⟩ | ⟨u,next,nb,_,hd,_,_,_,he⟩
      · exact run_append_fault hd
      · rw [run_append_ok hd]
        exact he

end Solidity.Backend.Passes
