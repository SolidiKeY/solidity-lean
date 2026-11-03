import Solidity.Backend.Passes.LoopCallControls

/-! Actual selected maps, expanded-call frame/cost and eleven-cell growth
through both physical boundaries. Internal intrinsic/symbolic execution only. -/
namespace Solidity.Backend.Passes.LoopCallApplication
open Evm Evm.Memory Evm.Compiler
open MemoryCallControls (C A initial base machine)
open LoopScopeControls
open LoopScopeTrace (preparedTarget loopTarget)
open LoopCallControls
attribute [local irreducible] producer result preparation enclosed prepared loopOut preparedTarget loopTarget

/-- A concrete reached link derives the call Input from the full ACTUAL output,
retaining its chosen map/cost/growth. No desired preservation is a premise. -/
theorem after_scope : ReachedMappedLink (.memory preparation) LoopScopeControls.checked checkedCall
    1 128 base initial machine := by
  intro o mid mb hs ht ha
  have same : prepared = o := Except.ok.inj (prepared_source.symm.trans hs)
  subst o
  have machines : mid = preparedTarget :=
    (Evm.Out.ok.inj (ht.symm.trans LoopScopeTrace.preparation_target)).1
  subst mid
  intro u next nb hsu htu hb
  have same : loopOut = u := Except.ok.inj (wrapped_source.symm.trans hsu)
  subst u
  have machines : next = loopTarget :=
    (Evm.Out.ok.inj (htu.symm.trans LoopScopeTrace.loop_target)).1
  subst next
  exact receiving ha hb

/-- Original full three-stage composition law, with the independently inhabited
receiving link, actual three typed source successes and all pays=false guards. -/
theorem correlated : ∃ (mb nb ob : Nat → Fin W) (mid next out : Machine) (amount : Nat)
      (ext : prepared.st.H <+: loopOut.st.H),
    LoopScopes.Cost enclosed.cert prepared.st ⟨loopOut.st,ext⟩ amount ∧
    mid.stack = [] ∧ next.stack = [] ∧ out.stack = [] ∧ ∀ tail,
    run preparation.code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
    run enclosed.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
    run producer.code {next with stack := tail} = .ok {out with stack := tail} 0 ∧
    run ((preparation.code ++ enclosed.code) ++ producer.code) {machine with stack := tail} =
      .ok {out with stack := tail} 0 ∧
    run (preparation.code ++ (enclosed.code ++ producer.code)) {machine with stack := tail} =
      .ok {out with stack := tail} 0 ∧
    MappedOutput (.memory preparation) 1 128 base initial {machine with stack := tail}
      prepared.st {mid with stack := tail} mb ∧
    MappedOutput checked 1 128 mb prepared.st {mid with stack := tail}
      loopOut.st {next with stack := tail} nb ∧
    MappedOutput checkedCall 1 128 nb loopOut.st {next with stack := tail}
      result.st {out with stack := tail} ob := by
  simpa only [show Evm.Prog.pushes prepare = 0 by decide +kernel,
    enclosed.cert.pushes_zero,free,Nat.add_zero] using
    loop_scopes_triple_shared (.memory preparation) enclosed checkedCall
      LoopScopeApplication.preparation_input (by rfl) LoopScopeApplication.into_scope after_scope
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      prepared_source wrapped_source source

theorem shared : ∃ (mb nb ob : Nat → Fin W) (out : Machine) (ext : prepared.st.H <+: loopOut.st.H),
    LoopScopes.Cost enclosed.cert prepared.st ⟨loopOut.st,ext⟩ 3 ∧
    BaseExtends prepared.st.H mb nb ∧ BaseExtends loopOut.st.H nb ob ∧
    ∀ tail,
      run producer.code {loopTarget with stack := tail} = .ok {out with stack := tail} 0 ∧
      run (preparation.code ++ (enclosed.code ++ producer.code)) {machine with stack := tail} =
        .ok {out with stack := tail} 0 ∧
      run ((preparation.code ++ enclosed.code) ++ producer.code) {machine with stack := tail} =
        .ok {out with stack := tail} 0 ∧
      MappedOutput (.memory preparation) 1 128 base initial {machine with stack := tail}
        prepared.st {preparedTarget with stack := tail} mb ∧
      MappedOutput checked 1 128 mb prepared.st {preparedTarget with stack := tail}
        loopOut.st {loopTarget with stack := tail} nb ∧
      MappedOutput checkedCall 1 128 nb loopOut.st {loopTarget with stack := tail}
        result.st {out with stack := tail} ob ∧
      GrowsAllocator 1 128 11 initial base {machine with stack := tail} result.st ob {out with stack := tail} := by
  obtain ⟨mb,nb,ha,hb⟩ := LoopScopeTerminal.prefix_relations
  obtain ⟨out,ob,ht,empty,all⟩ := compilation_success_shared_mapped checkedCall
    (receiving ha hb) (by decide +kernel) source
  have loopgrowth := (LoopAllocatingSuffix.actual_resources ha hb).2.2
  have hbase : BaseExtends prepared.st.H mb nb := by
    rcases hb with ⟨_,_,_,_,h,_⟩; exact h
  have outrel := (all []).2
  have outbase : BaseExtends loopOut.st.H nb ob := outrel.2.1
  obtain ⟨ext,hcost⟩ := (LoopAllocatingSuffix.actual_resources ha hb).1
  refine ⟨mb,nb,ob,out,ext,hcost,hbase,outbase,?_⟩
  obtain ⟨mb2,nb2,prefixes⟩ := LoopScopeTerminal.prefix_tails
  intro tail
  obtain ⟨hpre,hloop,_,_⟩ := prefixes tail
  -- Execution is deterministic; the representation and growth below use mb/nb above.
  have hp : run preparation.code {machine with stack := tail} = .ok {preparedTarget with stack := tail} 0 :=
    hpre
  have hl : run enclosed.code {preparedTarget with stack := tail} = .ok {loopTarget with stack := tail} 0 := hloop
  have hc := (all tail).1
  change run producer.code {loopTarget with stack := tail} = .ok {out with stack := tail} 0 at hc
  have whole : run (preparation.code ++ (enclosed.code ++ producer.code)) {machine with stack := tail} =
      .ok {out with stack := tail} 0 := by rw [run_append_ok hp,run_append_ok hl,hc]
  have suffixgrowth : GrowsAllocator 1 128 6 loopOut.st nb loopTarget result.st ob {out with stack := []} := by
    intro cursor hb hr fit
    have fit' : cursor.val + producer.cost loopOut.st < W := by rw [cost]; exact fit
    simpa only [cost] using outrel.2.2 cursor hb (hr.mem_eq rfl) fit'
  have total := ha.2.2.comp (loopgrowth.comp suffixgrowth)
  have total11 : GrowsAllocator 1 128 11 initial base machine result.st ob {out with stack := []} := by
    simpa only [LoopScopeControls.costs.1,cost] using total
  refine ⟨hc,whole,by simpa only [List.append_assoc] using whole,
    mapped_output_stack (.memory preparation) ha tail tail,
    mapped_output_stack checked hb tail tail,?_,?_⟩
  · simpa only [free,Nat.add_zero] using (all tail).2
  · intro cursor hb hr fit
    exact (total11 cursor hb (hr.mem_eq rfl) fit).mem_eq rfl

end Solidity.Backend.Passes.LoopCallApplication
