import Solidity.Backend.Passes.MemoryCallScopeBoundary
import Solidity.Backend.Passes.MemoryCallApplication

namespace Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls
open Evm Evm.Memory Evm.Compiler MemoryCallControls

def scopeProgram : Prog C Before Before := MemoryScopeBoundary.program call
def scopeProducer := MemoryCallScopeBoundary.compiled producer
def scopeChecked : Compilation 1 allocation.frag scopeProgram :=
  .memoryCalls scopeProducer (scope_free push_free)
noncomputable def post : State C Before := second.st.drop call.ext

theorem scope_source : scopeProgram.run first.st =
    .ok (⟨post,second.ext⟩ : Solidity.Out C first.st.H Before) :=
  MemoryScopeBoundary.source_success second_source

def suffix : Prog C Before Before :=
  .cons (.assignMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 0 rfl)))
    (.val (.binop .add rfl rfl
      (.readMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 0 rfl))))
      (.simple (.lit 1 rfl))))) .nil

@[irreducible] def right : CompiledProg 1 scopeProducer.frag suffix :=
  (Memory.compileProg 1 scopeProducer.frag suffix).get (by decide +kernel)
private theorem final_some : (suffix.run post).toOption.isSome = true := by decide +kernel
noncomputable def final : Solidity.Out C post.H Before := (suffix.run post).toOption.get final_some

theorem suffix_source : suffix.run post = .ok final := by
  have h : some final = (suffix.run post).toOption := Option.some_get _
  generalize suffix.run post = result at h ⊢
  cases result with
  | ok out => exact congrArg Except.ok (Option.some.inj h).symm
  | error halt => cases h

theorem joined_source :
    ((allocate.join scopeProgram).join suffix).run initial =
      .ok ⟨final.st,(first.ext.trans second.ext).trans final.ext⟩ ∧
    (allocate.join (scopeProgram.join suffix)).run initial =
      .ok ⟨final.st,first.ext.trans (second.ext.trans final.ext)⟩ :=
  triple_source_success initial first_source scope_source suffix_source

theorem shared : ∃ (mb nb ob : Nat → Fin W) (mid next out : Machine),
    mid.stack = [] ∧ next.stack = [] ∧ out.stack = [] ∧ ∀ tail,
    run allocation.code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
    run scopeProducer.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
    run right.code {next with stack := tail} = .ok {out with stack := tail} 0 ∧
    run ((allocation.code ++ scopeProducer.code) ++ right.code) {machine with stack := tail} =
      .ok {out with stack := tail} 0 ∧
    run (allocation.code ++ (scopeProducer.code ++ right.code)) {machine with stack := tail} =
      .ok {out with stack := tail} 0 ∧
    MappedOutput (.memory allocation) 1 128 base initial {machine with stack := tail}
      first.st {mid with stack := tail} mb ∧
    MappedOutput scopeChecked 1 128 mb first.st {mid with stack := tail}
      post {next with stack := tail} nb ∧
    (Compilation.memory right).Input 1 128 nb post {next with stack := tail} ∧
    MappedOutput (.memory right) 1 128 nb post {next with stack := tail}
      final.st {out with stack := tail} ob := by
  obtain ⟨mb,nb,_,mid,next,_,me,ne,_,firstRuns⟩ := MemoryCallApplication.shared
  have callOutput := (firstRuns []).2.2.2.2.2.2.1
  have scopedOutput := MemoryCallScopeBoundary.output producer push_free callOutput
  have inputRight : (Compilation.memory right).Input 1 128 nb post {next with stack := []} :=
    ⟨scopedOutput.1,by decide +kernel,.inl (allocationCostProg_zero suffix rfl post)⟩
  obtain ⟨out,ob,_,oe,runs⟩ := compilation_success_shared_mapped (.memory right) inputRight rfl suffix_source
  refine ⟨mb,nb,ob,mid,next,out,me,ne,oe,?_⟩
  intro tail
  rcases firstRuns tail with ⟨ha,hb,_,_,_,ma,mc,_⟩
  have hs : run scopeProducer.code {mid with stack := tail} = .ok {next with stack := tail} 0 := by
    simp only [scopeProducer, MemoryCallScopeBoundary.code]
    exact hb
  have mo := MemoryCallScopeBoundary.output producer push_free mc
  have ir : (Compilation.memory right).Input 1 128 nb post {next with stack := tail} :=
    ⟨mo.1,by decide +kernel,.inl (allocationCostProg_zero suffix rfl post)⟩
  have last := (runs tail).2
  rw [right.cert.pushes_zero,Nat.add_zero] at last
  refine ⟨ha,hs,(runs tail).1,?_,?_,ma,mo,ir,last⟩
  · exact (run_append_ok (c₂ := right.code) ((run_append_ok (c₂ := scopeProducer.code) ha).trans hs)).trans (runs tail).1
  · exact (run_append_ok (c₂ := scopeProducer.code ++ right.code) ha).trans
      ((run_append_ok (c₂ := right.code) hs).trans (runs tail).1)

theorem reached_cost : scopeProducer.cost first.st = 6 := by
  unfold scopeProducer
  rw [MemoryCallScopeBoundary.cost]
  exact MemoryCallControls.costs.2.1

theorem suffix_cost : right.cert.cost post = 0 :=
  allocationCostProg_zero suffix rfl post

theorem costs : scopeProducer.cost first.st = 6 ∧ right.cert.cost post = 0 :=
  ⟨reached_cost,suffix_cost⟩

theorem private_frame_refused {selected : Nat → Fin W} {state : State C Before} {m : Machine} :
    ¬ scopeChecked.Input 1 (1 + frameNeedProg call) selected state m := by
  intro h
  exact MemoryCallApplication.source_frame_refused
    (MemoryCallScopeBoundary.input_back producer push_free h)

end Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls
