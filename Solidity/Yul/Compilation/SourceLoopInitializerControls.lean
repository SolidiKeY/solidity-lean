import Solidity.Yul.Compilation.SourceLoopInitializer
import Solidity.Yul.Compilation.SourceLoopControls
/-! A non-skip initializer overwrites an arbitrary old counter before two real
body/post iterations. The full dirty second local and symbolic tail survive. -/
namespace Solidity.Yul.Compilation.SourceLoopInitializer.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls

def pre : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 :=
 .assign (fun _ : Fin 1 => .local 0) (.literal 2)
def initial := (ScopedStatements.compile 2 pre).get (by rfl)
def source : Solidity.Yul.Stmt [] [] root 2 := .for_ pre test step work
def profile : StmtWordP source := ⟨initial.profile,condition.profile,post.profile,body.profile⟩
def block := (SourceLoopInitializer.emit (c := root) initial condition post body 0).get (by rfl)
def code := (WordControl.blockCode block).get (by rfl)

theorem initialized (a b : Scalar.Word) : initial.update #v[a,b] = #v[2,b] := rfl

/-- Actual source success from ANY old counter, not just the loop's required
input counter. Iterations use the initializer output and preserve dirty bits. -/
theorem source_done (a b : Scalar.Word) :
 evalStmt 9 .nil True.intro source profile (sourceLocals #v[a,b]) =
 some ⟨sourceLocals #v[0,~~~(~~~b+3)+3],.normal⟩ := by
 have done := SourceLoopInitializer.finite (c := root) initial condition post body 2 #v[a,b]
   (guards_two b) (stopped_two b)
 simpa only [initialized,repeat_two] using done

/-- Whole emitted initializer+loop success with arbitrary untouched caller
words and non-stack machine fields; no caller-frame run is assumed. -/
theorem target_done (a b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run code {m with stack := [coreWord a,coreWord b]++caller} =
 .ok {m with stack := [coreWord 0,coreWord (~~~(~~~b+3)+3)]++caller} 0 := by
 obtain ⟨out,same,ran⟩ := SourceLoopInitializer.source_to_model (c := root)
   initial condition post body 0 block code (Option.some_get (by rfl)).symm
   (Option.some_get (by rfl)).symm 9 #v[a,b] _ (source_done a b) #v[] m caller
 have values := congrArg Outcome.vars same
 have equal : #v[0,~~~(~~~b+3)+3] = out := SourceLoopCompletion.sourceLocals_injective values
 subst out
 simpa only [Vector.toList_empty,List.nil_append,List.map_cons,List.map_nil] using ran

#guard (evalStmt 0 .nil True.intro source profile (sourceLocals #v[99,dirty])).isNone
#guard (evalStmt 1 .nil True.intro source profile (sourceLocals #v[99,dirty])).isNone
#guard initial.update #v[99,dirty] = #v[2,dirty]
#guard (SourceLoopInitializer.emit (c := root) initial condition post body 15).isNone
/-- info: 'Solidity.Yul.Compilation.SourceLoopInitializer.Controls.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms initialized
/-- info: 'Solidity.Yul.Compilation.SourceLoopInitializer.Controls.source_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_done
/-- info: 'Solidity.Yul.Compilation.SourceLoopInitializer.Controls.target_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_done
end Solidity.Yul.Compilation.SourceLoopInitializer.Controls
