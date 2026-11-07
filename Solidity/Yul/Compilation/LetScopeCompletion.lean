import Solidity.Yul.Compilation.CompletionControls
import Solidity.Yul.Compilation.LetScopeCompilation
/-! Reflection of actual selected single-word let execution. The initializer
has its actual concrete compiler law; body target success derives original
source completion before forward transport is reused for exact exit framing. -/
namespace Solidity.Yul.Compilation.LetScopeCompletion
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

/-- Whole model success derives an actual original let completion and exact
caller/nonstack frame. No source horizon or desired body/exit run is assumed. -/
theorem model_to_source {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : LetScopeCompilation.Artifact fuel stmt) (locals : Vector Scalar.Word n)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} := by
 have forward := artifact.source_to_model
 rcases artifact with ⟨compiled,code,lowered⟩
 cases compiled with
 | scope initializer body =>
   obtain ⟨entry,emitted,rest⟩ := Option.bind_eq_some_iff.mp lowered
   obtain ⟨begin,beginSelected,rest⟩ := Option.bind_eq_some_iff.mp rest
   obtain ⟨finish,finishSelected,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   have initScalar : Scalar.run entry locals.toList = some (initializer.value locals :: locals.toList) := by
     simpa only [Vector.toList_empty,List.nil_append,List.append_nil] using
       initializer.lowered.correct 0 entry emitted locals #v[] []
   have entering := WordExecution.run entry begin beginSelected locals.toList
     (initializer.value locals :: locals.toList) initScalar m caller
   change Evm.run (begin ++ body.code ++ finish) {m with stack := locals.toList.map coreWord++caller} = .ok final skip at ran
   have original := ran
   rw [List.append_assoc,Evm.run_append_ok entering] at ran
   have whole : (Evm.run body.code {m with stack := (initializer.value locals :: locals.toList).map coreWord++caller}).bind
     (fun mid pending => Evm.exec finish pending mid) = .ok final skip := by
     simpa only [Evm.run,Evm.exec_append] using ran
   cases actual : Evm.run body.code
     {m with stack := (initializer.value locals :: locals.toList).map coreWord++caller} with
   | revert => rw [actual] at whole; cases whole
   | fault => rw [actual] at whole; cases whole
   | ok middle pending =>
     have bodyRun : Evm.run body.code
       {m with stack := (#v[initializer.value locals] ++ locals).toList.map coreWord++caller} = .ok middle pending := by
       simpa only [Vector.toList_append,Vector.toList_singleton,List.singleton_append] using actual
     obtain ⟨horizon,out,source,_,_⟩ := LoopControlCompletion.artifact_reflected body
       (#v[initializer.value locals] ++ locals) #v[] m middle caller pending bodyRun
     have scopeSource := LetScopeCompilation.scope_source initializer body horizon locals out source
     obtain ⟨outer,same,computed⟩ := forward (max fuel horizon+1) locals
       ⟨sourceLocals (outerLocals out),.normal⟩ scopeSource m caller
     have equal : outerLocals out = outer :=
       SourceLoopCompletion.sourceLocals_injective (congrArg Outcome.vars same)
     subst outer
     have parts := Evm.Out.ok.inj (computed.symm.trans original)
     exact ⟨max fuel horizon+1,outerLocals out,scopeSource,parts.2.symm,parts.1.symm⟩

/-- Exact normal-success equivalence for actual let compiler artifacts.
Source horizon is existential; scalar/model success does not assert native
capacity, gas or logical Core Source/G24 adequacy. -/
theorem completion_iff {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : LetScopeCompilation.Artifact fuel stmt) (locals out : Vector Scalar.Word n)
 (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 exact CompletionControls.completion_iff_zero stmt artifact.compiled.profile artifact.code
   artifact.normal_to_model (model_to_source artifact) locals out m caller

/-- info: 'Solidity.Yul.Compilation.LetScopeCompletion.model_to_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model_to_source
/-- info: 'Solidity.Yul.Compilation.LetScopeCompletion.completion_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms completion_iff
end Solidity.Yul.Compilation.LetScopeCompletion
