import Solidity.Backend.Passes.LoopScopeTerminal

/-! An actual allocating suffix consumes the allocator and selected map reached
by the enclosing allocating block-loop. The legacy metric is never its budget. -/
namespace Solidity.Backend.Passes.LoopAllocatingSuffix
open Evm Evm.Memory Evm.Compiler
open MemoryCallControls (C A initial base machine initial_repr)
open LoopScopeControls
open LoopScopeTrace (preparedTarget loopTarget)

/-- The compiler's actual selected cost is determined by the original Room,
allocator growth and independently checked cursor of the reached physical run. -/
theorem actual_resources {mb nb : Nat → Fin W}
    (ha : MappedOutput (.memory preparation) 1 128 base initial machine prepared.st preparedTarget mb)
    (hb : MappedOutput checked 1 128 mb prepared.st preparedTarget loopOut.st loopTarget nb) :
    (∃ ext : prepared.st.H <+: loopOut.st.H, LoopScopes.Cost enclosed.cert prepared.st ⟨loopOut.st,ext⟩ 3) ∧
    StructAllocatorRepr loopOut.st.heap nb 128 (wmod 261) loopTarget ∧
    GrowsAllocator 1 128 3 prepared.st mb preparedTarget loopOut.st nb loopTarget := by
  have first : StructAllocatorRepr prepared.st.heap mb 128 (wmod 258) preparedTarget := by
    simpa only [LoopScopeControls.costs.1] using
      ha.2.2 (wmod 256) (by decide) initial_repr.2 (by rw [LoopScopeControls.costs.1]; decide +kernel)
  have hi := LoopScopeApplication.into_scope prepared preparedTarget mb prepared_source
    LoopScopeTrace.preparation_target ha
  rcases hb with ⟨amount,ext,cost,state,extension,growth⟩
  have capacity := scope_cost_allocation_input hi.2.2 cost
  have fit : 258 + amount < W := by
    rcases capacity with hz | ⟨_,cursor,repr,fit⟩
    · rw [hz]; decide +kernel
    · have same : cursor = wmod 258 := Word.val.inj
        (repr.arrays.free.cell.symm.trans first.arrays.free.cell)
      subst cursor
      exact fit
  have reached := growth (wmod 258) (by decide) first fit
  have actual : loopTarget.mem 0 = .val (wmod 261) := by decide +kernel
  have values := congrArg Fin.val (Word.val.inj (reached.arrays.free.cell.symm.trans actual))
  change 258 + amount = 261 at values
  have amount_eq : amount = 3 := by omega
  subst amount
  exact ⟨⟨ext,cost⟩,reached,growth⟩

def fresh : Prog C LoopScopeControls.Γ (.mem A :: LoopScopeControls.Γ) :=
  .cons (.declMem A (.user "afterLoop") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl)
  (.cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))
    (.val (.simple (.lit 5 rfl)))) .nil)
def compiled : CompiledProg 1 enclosed.frag fresh := (Memory.compileProg 1 _ fresh).get (by decide +kernel)
noncomputable def result : Solidity.Out C loopOut.st.H (.mem A :: LoopScopeControls.Γ) :=
  (fresh.run loopOut.st).toOption.get (by decide +kernel)

theorem source : fresh.run loopOut.st = .ok result := by
  have h : some result = (fresh.run loopOut.st).toOption := Option.some_get _
  cases hs : fresh.run loopOut.st with
  | ok o => rw [hs] at h; exact congrArg Except.ok (Option.some.inj h).symm
  | error e => rw [hs] at h; cases h

theorem cost : compiled.cert.cost loopOut.st = 2 := by decide +kernel

-- Keep proof-carrying recognizer terms opaque to elaboration; all finite
-- observations and equality checks still reduce in the kernel.
attribute [local irreducible] compiled result preparation enclosed prepared loopOut preparedTarget loopTarget

/-- The suffix Input is obtained from the exact reached allocator, so it uses
nb (including the loop's fresh object), never the stale initial map. -/
theorem receiving {mb nb : Nat → Fin W}
    (ha : MappedOutput (.memory preparation) 1 128 base initial machine prepared.st preparedTarget mb)
    (hb : MappedOutput checked 1 128 mb prepared.st preparedTarget loopOut.st loopTarget nb) :
    (Compilation.memory compiled).Input 1 128 nb loopOut.st loopTarget := by
  refine ⟨?_,by decide +kernel,?_⟩
  · rcases hb with ⟨amount,ext,cost,state,extension,growth⟩
    exact state
  · exact .inr ⟨by decide,wmod 261,(actual_resources ha hb).2.1,by rw [cost]; decide +kernel⟩

/-- All three selected maps and machines are outside the saved-tail quantifier;
the loop's exact cost3 and total7-cell growth retain all original identities. -/
theorem shared : ∃ (mb nb ob : Nat → Fin W) (out : Machine) (ext : prepared.st.H <+: loopOut.st.H),
    LoopScopes.Cost enclosed.cert prepared.st ⟨loopOut.st,ext⟩ 3 ∧
    BaseExtends prepared.st.H mb nb ∧ BaseExtends loopOut.st.H nb ob ∧
    ∀ tail,
      run compiled.code {loopTarget with stack := tail} = .ok {out with stack := tail} 0 ∧
      run (preparation.code ++ (enclosed.code ++ compiled.code)) {machine with stack := tail} =
        .ok {out with stack := tail} 0 ∧
      run ((preparation.code ++ enclosed.code) ++ compiled.code) {machine with stack := tail} =
        .ok {out with stack := tail} 0 ∧
      MappedOutput (.memory preparation) 1 128 base initial {machine with stack := tail}
        prepared.st {preparedTarget with stack := tail} mb ∧
      MappedOutput checked 1 128 mb prepared.st {preparedTarget with stack := tail}
        loopOut.st {loopTarget with stack := tail} nb ∧
      MappedOutput (.memory compiled) 1 128 nb loopOut.st {loopTarget with stack := tail}
        result.st {out with stack := tail} ob ∧
      GrowsAllocator 1 128 7 initial base {machine with stack := tail} result.st ob {out with stack := tail} := by
  obtain ⟨mb,nb,ha,hb⟩ := LoopScopeTerminal.prefix_relations
  obtain ⟨out,ob,ht,empty,all⟩ := compilation_success_shared_mapped (.memory compiled)
    (receiving ha hb) (by decide +kernel) source
  have loopgrowth := (actual_resources ha hb).2.2
  have hbase : BaseExtends prepared.st.H mb nb := by
    rcases hb with ⟨_,_,_,_,h,_⟩; exact h
  have outrel := (all []).2
  have outbase : BaseExtends loopOut.st.H nb ob := outrel.2.1
  obtain ⟨ext,hcost⟩ := (actual_resources ha hb).1
  refine ⟨mb,nb,ob,out,ext,hcost,hbase,outbase,?_⟩
  obtain ⟨mb2,nb2,prefixes⟩ := LoopScopeTerminal.prefix_tails
  intro tail
  obtain ⟨hpre,hloop,_,_⟩ := prefixes tail
  -- Execution is deterministic; the representation and growth below use mb/nb above.
  have hp : run preparation.code {machine with stack := tail} = .ok {preparedTarget with stack := tail} 0 :=
    hpre
  have hl : run enclosed.code {preparedTarget with stack := tail} = .ok {loopTarget with stack := tail} 0 := hloop
  have hc := (all tail).1
  change run compiled.code {loopTarget with stack := tail} = .ok {out with stack := tail} 0 at hc
  have whole : run (preparation.code ++ (enclosed.code ++ compiled.code)) {machine with stack := tail} =
      .ok {out with stack := tail} 0 := by rw [run_append_ok hp,run_append_ok hl,hc]
  have suffixgrowth : GrowsAllocator 1 128 2 loopOut.st nb loopTarget result.st ob {out with stack := []} := by
    intro cursor hb hr fit
    have fit' : cursor.val + compiled.cert.cost loopOut.st < W := by rw [cost]; exact fit
    exact outrel.2.2 cursor hb (hr.mem_eq rfl) fit'
  have total := ha.2.2.comp (loopgrowth.comp suffixgrowth)
  have total7 : GrowsAllocator 1 128 7 initial base machine result.st ob {out with stack := []} := by
    simpa only [LoopScopeControls.costs.1,cost] using total
  refine ⟨hc,whole,by simpa only [List.append_assoc] using whole,
    mapped_output_stack (.memory preparation) ha tail tail,
    mapped_output_stack checked hb tail tail,?_,?_⟩
  · simpa only [compiled.cert.pushes_zero,Nat.add_zero] using (all tail).2
  · intro cursor hb hr fit
    exact (total7 cursor hb (hr.mem_eq rfl) fit).mem_eq rfl

private def okMachine : Evm.Out → Option Machine
  | .ok m 0 => some m | _ => none
noncomputable def target : Machine :=
  (okMachine (run compiled.code loopTarget)).get (by decide +kernel)
theorem target_run : run compiled.code loopTarget = .ok target 0 := by
  have h : some target = okMachine (run compiled.code loopTarget) := Option.some_get _
  generalize run compiled.code loopTarget = value at h ⊢
  cases value with
  | ok m skip =>
    cases skip with
    | zero => exact congrArg (fun m => Evm.Out.ok m 0) (Option.some.inj h).symm
    | succ n => cases h
  | revert => cases h
  | fault => cases h

private def words (m : Machine) : Option (List Nat) :=
  (m.stack ++ (LoopScopeTrace.addresses ++ [261,262]).map m.mem).mapM fun w => match w with
    | .val n => some n.val | .slot _ => none

theorem complete_target_vector : words {target with stack := [w[77],w[88]]} =
    some [77,88,263,99,256,0,258,261,1,7,2,0,0,1,5] := by decide +kernel

theorem skipped_allocation : words {loopTarget with stack := [w[77],w[88]]} ≠
    some [77,88,263,99,256,0,258,261,1,7,2,0,0,1,5] := by decide +kernel

private noncomputable def sourceVector : Option (List Int) := do
  let old ← TEnv.get (.there (.there (.there .here))) result.st.env
  let live ← TEnv.get (.there .here) result.st.env
  let fresh ← TEnv.get .here result.st.env
  let flag := TEnv.get (.there (.there .here)) result.st.env
  let oldRef : HRef result.st.H A := ⟨0,by decide +kernel⟩
  let liveRef : HRef result.st.H A := ⟨1,by decide +kernel⟩
  let freshRef : HRef result.st.H A := ⟨2,by decide +kernel⟩
  let oldVal ← result.st.heap.index oldRef .dyn (indexValue (wmod 0))
  let liveFirst ← result.st.heap.index liveRef .dyn (indexValue (wmod 0))
  let liveSecond ← result.st.heap.index liveRef .dyn (indexValue (wmod 1))
  let freshVal ← result.st.heap.index freshRef .dyn (indexValue (wmod 0))
  pure [result.st.H.length,old.id,live.id,fresh.id,flag.val,result.st.heap.len oldRef .dyn,oldVal.val,
    result.st.heap.len liveRef .dyn,liveFirst.val,liveSecond.val,result.st.heap.len freshRef .dyn,freshVal.val]

theorem complete_source_vector : sourceVector = some [3,0,1,2,0,1,7,2,0,0,1,5] := by decide +kernel

end Solidity.Backend.Passes.LoopAllocatingSuffix
