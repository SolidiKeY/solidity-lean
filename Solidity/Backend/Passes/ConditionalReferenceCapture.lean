import Solidity.Backend.Passes.MappedTail

/-! An actual conditional reference rebind followed by a fresh alias capture.
The existing scoped branch certificate retains its full fragment meet. -/
namespace Solidity.Backend.Passes.ConditionalReferenceCapture
open Evm Evm.Memory Evm.Compiler
variable {C : Contract} {Γ : Ctx} {R : RefTy}
def arm (dst src : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true) : Prog C Γ Γ :=
  .cons (.rebindMem dst (.alias (.var src hm))) .nil
def program (name : Var) (condition : Val C Γ .bool)
    (dst yes no : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true) :
    Prog C Γ (.mem R :: Γ) :=
  .cons (.ite condition (arm dst yes hm) (arm dst no hm))
    (.cons (.declMem R name (some (.alias (.var dst hm))) rfl hm) .nil)
def branchFrag (F : Frag Γ) : Frag Γ := (F.restrict Γ).meet (F.restrict Γ)
def compiled {b : Nat} {F : Frag Γ} (name : Var) (condition : Val C Γ .bool)
    (cc : CompiledVal b F condition) (dst yes no : Idx Γ (.mem R))
    (hm : (Ty.ref R).mapFree = true) :
    Compilation b F (program (C := C) name condition dst yes no hm) :=
  .memory ⟨(branchFrag F).push (.mem R) .ok,
    conditionalCode cc.code (aliasLocalCode b dst yes ++ []) (aliasLocalCode b dst no ++ []) ++
      (declareAliasCode b dst ++ []),
    .cons (.ite condition (arm dst yes hm) (arm dst no hm) _ _ _ cc.cert
      (.cons (.rebind F dst yes hm) (.nil _)) (.cons (.rebind F dst no hm) (.nil _)))
      (.cons (.declareAlias _ name dst hm) (.nil _))⟩

theorem source (name : Var) (condition : Val C Γ .bool)
    (dst yes no : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (state : State C Γ) (a : Bool) (evaluated : condition.evalT state = .ok a)
    (yr nr : HRef state.H R) (hy : TEnv.get yes state.env = some yr)
    (hn : TEnv.get no state.env = some nr) :
    (program name condition dst yes no hm).run state =
      .ok ⟨(state.setLocal dst (some (if a then yr else nr))).push
        (t := .mem R) (some (if a then yr else nr)),List.prefix_refl _⟩ := by
  have rebind (src : Idx Γ (.mem R)) (r : HRef state.H R)
      (get : TEnv.get src state.env = some r) :
      (arm dst src hm).run state = .ok ⟨state.setLocal dst (some r),List.prefix_refl _⟩ := by
    have step : (Stmt.rebindMem dst (.alias (.var src hm))).run state =
        .ok ⟨state.setLocal dst (some r),List.prefix_refl _⟩ := by
      change TRun.rebindMem dst (.alias (.var src hm)) state = _
      simp only [TRun.rebindMem,MRhs.evalT,MPath.mvalT,get,bind,Except.bind,pure,Except.pure]
    rw [arm,Prog.run_cons_ok step]
    rfl
  have branch : (Stmt.ite condition (arm dst yes hm) (arm dst no hm)).run state =
      .ok ⟨state.setLocal dst (some (if a then yr else nr)),List.prefix_refl _⟩ := by
    change TRun.ite condition _ (arm dst yes hm).run _ (arm dst no hm).run state = _
    cases a <;> simp only [TRun.ite,evaluated,boolT,Bool.false_eq_true,ite_false,ite_true,
      bind,Except.bind]
    · rw [rebind no nr hn]
      rfl
    · rw [rebind yes yr hy]
      rfl
  have capture : (Stmt.declMem R name (some (.alias (.var dst hm))) rfl hm).run
      (state.setLocal dst (some (if a then yr else nr))) =
      .ok ⟨(state.setLocal dst (some (if a then yr else nr))).push
        (t := .mem R) (some (if a then yr else nr)),List.prefix_refl _⟩ := by
    change TRun.declMem R (some (.alias (.var dst hm))) hm _ = _
    simp only [TRun.declMem,MRhs.evalT,MPath.mvalT,State.setLocal,
      TEnv.get_set,bind,Except.bind,pure,Except.pure]
  rw [program,Prog.run_cons_ok branch,Prog.run_cons_ok capture]
  rfl

theorem execution {b L frame : Nat} {F : Frag Γ}
    (name : Var) (condition : Val C Γ .bool) (cc : CompiledVal b F condition)
    (dst yes no : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (input : (compiled name condition cc dst yes no hm).Input L frame base state machine)
    (a : Bool) (evaluated : condition.evalT state = .ok a) :
    ∃ yr nr : HRef state.H R,
      TEnv.get yes state.env = some yr ∧ TEnv.get no state.env = some nr ∧
      (program name condition dst yes no hm).run state =
        .ok ⟨(state.setLocal dst (some (if a then yr else nr))).push
          (t := .mem R) (some (if a then yr else nr)),List.prefix_refl _⟩ ∧
      ∃ (canonical : Machine) (outBase : Nat → Fin W), canonical.stack = [] ∧ ∀ tail,
        (compiled name condition cc dst yes no hm).Input L frame base state {machine with stack := tail} ∧
        run (compiled name condition cc dst yes no hm).code {machine with stack := tail} =
          .ok {canonical with stack := tail} 0 ∧
        MappedOutput (compiled name condition cc dst yes no hm) L frame base state
          {machine with stack := tail}
          ((state.setLocal dst (some (if a then yr else nr))).push
            (t := .mem R) (some (if a then yr else nr))) {canonical with stack := tail} outBase ∧
        outBase yr.id = base yr.id ∧ outBase nr.id = base nr.id ∧
        canonical.mem (cell (b+Γ.length)) = .val (base (if a then yr else nr).id) := by
  have represented : StateRepr L b frame F state base machine := input.1
  obtain ⟨yr,hy,_⟩ := represented.pointers yes
  obtain ⟨nr,hn,_⟩ := represented.pointers no
  have sourceRun := source name condition dst yes no hm state a evaluated yr nr hy hn
  obtain ⟨canonical,outBase,_,emptyStack,all⟩ :=
    compilation_success_shared_mapped (compiled name condition cc dst yes no hm) input rfl sourceRun
  refine ⟨yr,nr,hy,hn,sourceRun,canonical,outBase,emptyStack,?_⟩
  intro tail
  obtain ⟨target,rawMapped⟩ := all tail
  have mapped : MappedOutput (compiled name condition cc dst yes no hm) L frame base state
      {machine with stack := tail}
      ((state.setLocal dst (some (if a then yr else nr))).push
        (t := .mem R) (some (if a then yr else nr))) {canonical with stack := tail} outBase := by
    simpa only [show Evm.Prog.pushes (program name condition dst yes no hm) = 0 from rfl,
      Nat.add_zero] using rawMapped
  refine ⟨compilation_input_stack _ input tail,target,mapped,
    mapped.2.1 yr,mapped.2.1 nr,?_⟩
  obtain ⟨actual,get,word⟩ := mapped.1.pointers (.here : Idx (.mem R :: Γ) (.mem R))
  have same : (if a then yr else nr) = actual := Option.some.inj get
  rw [← same] at word
  change canonical.mem (cell (b+Γ.length)) = .val (outBase (if a then yr else nr).id) at word
  rw [mapped.2.1 (if a then yr else nr)] at word
  exact word

end Solidity.Backend.Passes.ConditionalReferenceCapture
/-- info: 'Solidity.Backend.Passes.ConditionalReferenceCapture.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ConditionalReferenceCapture.source
/-- info: 'Solidity.Backend.Passes.ConditionalReferenceCapture.execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ConditionalReferenceCapture.execution
