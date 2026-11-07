import Solidity.Yul.RawNoGuardSource
import Solidity.Yul.Checks.RawNoGuardFailure
/-! Actual Source noncompletion instantiations, completing-break/early-timeout
controls and explicit dirty-input refusal. Clean Source facts never imply
arbitrary dirty readback. H30 shared registration remains external. -/
namespace Solidity.Yul.Checks.RawNoGuardSource
namespace Old
export Solidity.Yul.Checks.RawNoGuardFailure
 (ctx env dirty initial skipProof writeFalse continuation repeatedStmt repeated breakStmt)
export Solidity.Yul.Checks.RawControlledWhileHorizon (mutatingContinue)
export Solidity.Yul.Checks.RawStatementHorizon (dirtyInput)
end Old
export Old (ctx env dirty initial skipProof writeFalse continuation)
def witness : Nonempty (RawSourceAdapter.Adapter ctx [] false false Old.repeatedStmt) := ⟨Old.repeated⟩
theorem iterationFamily : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawNoGuardSource.env) (frame : Solidity.Source.Fr) (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawNoGuardSource.env)) (next : Solidity.Source.Locals Solidity.Yul.Checks.RawNoGuardSource.env.layout Solidity.Yul.Checks.RawNoGuardSource.ctx.tys) (finalWorld : Solidity.Source.St Solidity.Yul.Checks.RawNoGuardSource.env), (Solidity.Source.forIter glob frame fuel nps ph .none (.some (.assign (.local .here) (.bool false))) (.cont : Solidity.Source.RStmt Solidity.Yul.Checks.RawNoGuardSource.env [] false ⟨true,false⟩ Solidity.Yul.Checks.RawNoGuardSource.ctx.tys Solidity.Yul.Checks.RawNoGuardSource.ctx.tys) Solidity.Yul.Checks.RawNoGuardSource.initial.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawNoGuardSource.env,Solidity.Yul.Checks.RawNoGuardSource.initial.world) ≠ (.ok (.normal next),(Solidity.Source.L0 Solidity.Yul.Checks.RawNoGuardSource.env,finalWorld)) := by
  intro glob frame fuel nps ph next finalWorld
  exact Solidity.Yul.RawNoGuardSource.source_iter_no_normal Solidity.Yul.Checks.RawNoGuardSource.ctx [] false false _ Solidity.Yul.Checks.RawNoGuardSource.continuation (by rfl) _ Solidity.Yul.Checks.RawNoGuardSource.writeFalse glob frame fuel nps ph Solidity.Yul.Checks.RawNoGuardSource.initial (Solidity.Yul.RawCoherent.coherent_ofClean _ _) next finalWorld

theorem initializedFamily : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawNoGuardSource.env) (frame : Solidity.Source.Fr) (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawNoGuardSource.env)) (l : Bool) (next : Solidity.Source.Locals Solidity.Yul.Checks.RawNoGuardSource.env.layout Solidity.Yul.Checks.RawNoGuardSource.ctx.tys) (finalWorld : Solidity.Source.St Solidity.Yul.Checks.RawNoGuardSource.env), (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.forLoop (l := l) (.skip : Solidity.Source.RStmt Solidity.Yul.Checks.RawNoGuardSource.env [] false ⟨true,false⟩ Solidity.Yul.Checks.RawNoGuardSource.ctx.tys Solidity.Yul.Checks.RawNoGuardSource.ctx.tys) .none (.some (.assign (.local .here) (.bool false))) (.cont : Solidity.Source.RStmt Solidity.Yul.Checks.RawNoGuardSource.env [] false ⟨true,false⟩ Solidity.Yul.Checks.RawNoGuardSource.ctx.tys Solidity.Yul.Checks.RawNoGuardSource.ctx.tys)) Solidity.Yul.Checks.RawNoGuardSource.initial.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawNoGuardSource.env,Solidity.Yul.Checks.RawNoGuardSource.initial.world) ≠ (.ok (.normal next),(Solidity.Source.L0 Solidity.Yul.Checks.RawNoGuardSource.env,finalWorld)) := by
  intro glob frame fuel nps ph l next finalWorld
  exact Solidity.Yul.RawNoGuardSource.source_initialized_no_normal Solidity.Yul.Checks.RawNoGuardSource.ctx [] false false _ Solidity.Yul.Checks.RawNoGuardSource.continuation (by rfl) _ Solidity.Yul.Checks.RawNoGuardSource.writeFalse l _ (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawNoGuardSource.skipProof) glob frame fuel nps ph Solidity.Yul.Checks.RawNoGuardSource.initial (Solidity.Yul.RawCoherent.coherent_ofClean _ _) next finalWorld

theorem cleanFamily : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawNoGuardSource.env) (frame : Solidity.Source.Fr) (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawNoGuardSource.env)) (l : Bool) (locals next : Solidity.Source.Locals Solidity.Yul.Checks.RawNoGuardSource.env.layout Solidity.Yul.Checks.RawNoGuardSource.ctx.tys) (world finalWorld : Solidity.Source.St Solidity.Yul.Checks.RawNoGuardSource.env), (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.forLoop (l := l) (.skip : Solidity.Source.RStmt Solidity.Yul.Checks.RawNoGuardSource.env [] false ⟨true,false⟩ Solidity.Yul.Checks.RawNoGuardSource.ctx.tys Solidity.Yul.Checks.RawNoGuardSource.ctx.tys) .none (.some (.assign (.local .here) (.bool false))) (.cont : Solidity.Source.RStmt Solidity.Yul.Checks.RawNoGuardSource.env [] false ⟨true,false⟩ Solidity.Yul.Checks.RawNoGuardSource.ctx.tys Solidity.Yul.Checks.RawNoGuardSource.ctx.tys)) locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawNoGuardSource.env,world) ≠ (.ok (.normal next),(Solidity.Source.L0 Solidity.Yul.Checks.RawNoGuardSource.env,finalWorld)) := by
  intro glob frame fuel nps ph l locals next world finalWorld
  exact Solidity.Yul.RawNoGuardSource.source_clean_no_normal Solidity.Yul.Checks.RawNoGuardSource.ctx [] false false _ Solidity.Yul.Checks.RawNoGuardSource.continuation (by rfl) _ Solidity.Yul.Checks.RawNoGuardSource.writeFalse l _ (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawNoGuardSource.skipProof) glob frame fuel nps ph locals next world finalWorld

theorem conditionalFamily : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawNoGuardSource.env) (frame : Solidity.Source.Fr) (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawNoGuardSource.env)) (l : Bool) (locals next : Solidity.Source.Locals Solidity.Yul.Checks.RawNoGuardSource.env.layout Solidity.Yul.Checks.RawNoGuardSource.ctx.tys) (world finalWorld : Solidity.Source.St Solidity.Yul.Checks.RawNoGuardSource.env), (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.forLoop (l := l) (.skip : Solidity.Source.RStmt Solidity.Yul.Checks.RawNoGuardSource.env [] false ⟨true,false⟩ Solidity.Yul.Checks.RawNoGuardSource.ctx.tys Solidity.Yul.Checks.RawNoGuardSource.ctx.tys) .none (.some (.assign (.local .here) (.bool false))) (.ifThen (.unary .not (.assign (.local .here) (.bool false))) .cont)) locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawNoGuardSource.env,world) ≠ (.ok (.normal next),(Solidity.Source.L0 Solidity.Yul.Checks.RawNoGuardSource.env,finalWorld)) := by
  intro glob frame fuel nps ph l locals next world finalWorld
  exact Solidity.Yul.RawNoGuardSource.source_clean_no_normal Solidity.Yul.Checks.RawNoGuardSource.ctx [] false false _ Solidity.Yul.Checks.RawNoGuardSource.Old.mutatingContinue (by rfl) _ Solidity.Yul.Checks.RawNoGuardSource.writeFalse l _ (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawNoGuardSource.skipProof) glob frame fuel nps ph locals next world finalWorld

theorem sourceBreakCounterexample : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawNoGuardSource.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawNoGuardSource.env)), (Solidity.Source.execS glob frame 3 nps ph Solidity.Yul.Checks.RawNoGuardSource.Old.breakStmt Solidity.Yul.Checks.RawNoGuardSource.initial.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawNoGuardSource.env,Solidity.Yul.Checks.RawNoGuardSource.initial.world) = (.ok (.normal Solidity.Yul.Checks.RawNoGuardSource.initial.clean),(Solidity.Source.L0 Solidity.Yul.Checks.RawNoGuardSource.env,Solidity.Yul.Checks.RawNoGuardSource.initial.world)) := by
  intro glob frame nps ph
  rfl

theorem sourceEarlyTimeout : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawNoGuardSource.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawNoGuardSource.env)), ((Solidity.Source.execS glob frame 2 nps ph Solidity.Yul.Checks.RawNoGuardSource.Old.repeatedStmt Solidity.Yul.Checks.RawNoGuardSource.initial.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawNoGuardSource.env,Solidity.Yul.Checks.RawNoGuardSource.initial.world)).1 = .error .timeout := by
  intro glob frame nps ph
  rfl

theorem dirtyRefusal : Solidity.Yul.RawCoherent.coherent Solidity.Yul.Checks.RawNoGuardSource.dirty = false := by
  exact Solidity.Yul.Checks.RawNoGuardSource.Old.dirtyInput.1

theorem coherentFamily : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawNoGuardSource.env) (frame : Solidity.Source.Fr) (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawNoGuardSource.env)) (l : Bool) (state : Solidity.Yul.RawFrame.State Solidity.Yul.Checks.RawNoGuardSource.ctx) (_same : Solidity.Yul.RawCoherent.coherent state = true) (next : Solidity.Source.Locals Solidity.Yul.Checks.RawNoGuardSource.env.layout Solidity.Yul.Checks.RawNoGuardSource.ctx.tys) (finalWorld : Solidity.Source.St Solidity.Yul.Checks.RawNoGuardSource.env), (Solidity.Source.execS glob frame fuel nps ph (Solidity.Source.RStmt.forLoop (l := l) (.skip : Solidity.Source.RStmt Solidity.Yul.Checks.RawNoGuardSource.env [] false ⟨true,false⟩ Solidity.Yul.Checks.RawNoGuardSource.ctx.tys Solidity.Yul.Checks.RawNoGuardSource.ctx.tys) .none (.some (.assign (.local .here) (.bool false))) (.cont : Solidity.Source.RStmt Solidity.Yul.Checks.RawNoGuardSource.env [] false ⟨true,false⟩ Solidity.Yul.Checks.RawNoGuardSource.ctx.tys Solidity.Yul.Checks.RawNoGuardSource.ctx.tys)) state.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawNoGuardSource.env,state.world) ≠ (.ok (.normal next),(Solidity.Source.L0 Solidity.Yul.Checks.RawNoGuardSource.env,finalWorld)) := by
  intro glob frame fuel nps ph l state same next finalWorld
  exact Solidity.Yul.RawNoGuardSource.source_initialized_no_normal Solidity.Yul.Checks.RawNoGuardSource.ctx [] false false _ Solidity.Yul.Checks.RawNoGuardSource.continuation (by rfl) _ Solidity.Yul.Checks.RawNoGuardSource.writeFalse l _ (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawNoGuardSource.skipProof) glob frame fuel nps ph state same next finalWorld

#print axioms Solidity.Yul.RawNoGuardSource.source_iter_no_normal
#print axioms Solidity.Yul.RawNoGuardSource.source_initialized_no_normal
#print axioms Solidity.Yul.RawNoGuardSource.source_clean_no_normal
#print axioms iterationFamily
#print axioms initializedFamily
#print axioms cleanFamily
#print axioms conditionalFamily
#print axioms sourceBreakCounterexample
#print axioms sourceEarlyTimeout
#print axioms dirtyRefusal
#print axioms coherentFamily
end Solidity.Yul.Checks.RawNoGuardSource
