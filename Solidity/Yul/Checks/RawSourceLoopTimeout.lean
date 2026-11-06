import Solidity.Yul.RawSourceLoopTimeout
import Solidity.Yul.Checks.RawNoGuardFailure
/-! Exact Source timeout/world and firstDone controls. Completing break and
initialized-stuck examples keep sufficient premises and iteration scope honest.
Dirty refusal concerns coherence only. H30 shared registration remains external. -/
namespace Solidity.Yul.Checks.RawSourceLoopTimeout
namespace Old
export Solidity.Yul.Checks.RawNoGuardFailure
 (ctx env dirty initial skipProof breakProof writeFalse continuation)
export Solidity.Yul.Checks.RawControlledWhileHorizon (mutatingContinue)
export Solidity.Yul.Checks.RawStatementHorizon (dirtyInput)
end Old
export Old (ctx env dirty initial writeFalse continuation)
def simpleBody : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys := .cont
def conditionalBody : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .ifThen (.unary .not (.assign (.local .here) (.bool false))) .cont
def breakBody : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys := .brk
def invalidInitialized : Solidity.Source.RStmt env [] false ⟨true,false⟩ ctx.tys ctx.tys :=
 .forLoop .brk .none .none .skip
def witness : Nonempty (RawLoopBody.Supported ctx [] false false conditionalBody) := ⟨Old.mutatingContinue⟩
theorem postWorld : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawSourceLoopTimeout.env) (frame : Solidity.Source.Fr) (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawSourceLoopTimeout.env)), (Solidity.Source.forIter glob frame fuel nps ph .none (.some (.assign (.local .here) (.bool false))) Solidity.Yul.Checks.RawSourceLoopTimeout.simpleBody Solidity.Yul.Checks.RawSourceLoopTimeout.initial.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawSourceLoopTimeout.env,Solidity.Yul.Checks.RawSourceLoopTimeout.initial.world) = (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.RawSourceLoopTimeout.env,(Solidity.Yul.RawSourceForPost.run (.base (.literal true)) Solidity.Yul.Checks.RawSourceLoopTimeout.writeFalse (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawSourceLoopTimeout.continuation) fuel Solidity.Yul.Checks.RawSourceLoopTimeout.initial).2.world)) := by
  intro glob frame fuel nps ph
  exact Solidity.Yul.RawSourceLoopTimeout.post_timeout Solidity.Yul.Checks.RawSourceLoopTimeout.ctx [] false false _ Solidity.Yul.Checks.RawSourceLoopTimeout.continuation (by rfl) _ Solidity.Yul.Checks.RawSourceLoopTimeout.writeFalse glob frame fuel nps ph Solidity.Yul.Checks.RawSourceLoopTimeout.initial (Solidity.Yul.RawCoherent.coherent_ofClean _ _)

theorem noPostWorld : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawSourceLoopTimeout.env) (frame : Solidity.Source.Fr) (fuel nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawSourceLoopTimeout.env)), (Solidity.Source.forIter glob frame fuel nps ph .none .none Solidity.Yul.Checks.RawSourceLoopTimeout.simpleBody Solidity.Yul.Checks.RawSourceLoopTimeout.initial.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawSourceLoopTimeout.env,Solidity.Yul.Checks.RawSourceLoopTimeout.initial.world) = (.error .timeout,(Solidity.Source.L0 Solidity.Yul.Checks.RawSourceLoopTimeout.env,(Solidity.Yul.RawSourceAdapterLoop.run (.base (.literal true)) (Solidity.Yul.RawSourceAdapter.body Solidity.Yul.Checks.RawSourceLoopTimeout.continuation) fuel Solidity.Yul.Checks.RawSourceLoopTimeout.initial).2.world)) := by
  intro glob frame fuel nps ph
  exact Solidity.Yul.RawSourceLoopTimeout.no_post_timeout Solidity.Yul.Checks.RawSourceLoopTimeout.ctx [] false false _ Solidity.Yul.Checks.RawSourceLoopTimeout.continuation (by rfl) glob frame fuel nps ph Solidity.Yul.Checks.RawSourceLoopTimeout.initial (Solidity.Yul.RawCoherent.coherent_ofClean _ _)

theorem postBounds : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawSourceLoopTimeout.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawSourceLoopTimeout.env)) (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawSourceLoopTimeout.env.layout Solidity.Yul.Checks.RawSourceLoopTimeout.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawSourceLoopTimeout.env), ∀ bound, Solidity.Source.firstDone (fun fuel => (Solidity.Source.forIter glob frame fuel nps ph .none (.some (.assign (.local .here) (.bool false))) Solidity.Yul.Checks.RawSourceLoopTimeout.simpleBody locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawSourceLoopTimeout.env,world)) bound = none := by
  intro glob frame nps ph locals world bound
  exact Solidity.Yul.RawSourceLoopTimeout.post_firstDone Solidity.Yul.Checks.RawSourceLoopTimeout.ctx [] false false _ Solidity.Yul.Checks.RawSourceLoopTimeout.continuation (by rfl) _ Solidity.Yul.Checks.RawSourceLoopTimeout.writeFalse glob frame nps ph locals world bound

theorem noPostBounds : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawSourceLoopTimeout.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawSourceLoopTimeout.env)) (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawSourceLoopTimeout.env.layout Solidity.Yul.Checks.RawSourceLoopTimeout.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawSourceLoopTimeout.env), ∀ bound, Solidity.Source.firstDone (fun fuel => (Solidity.Source.forIter glob frame fuel nps ph .none .none Solidity.Yul.Checks.RawSourceLoopTimeout.simpleBody locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawSourceLoopTimeout.env,world)) bound = none := by
  intro glob frame nps ph locals world bound
  exact Solidity.Yul.RawSourceLoopTimeout.no_post_firstDone Solidity.Yul.Checks.RawSourceLoopTimeout.ctx [] false false _ Solidity.Yul.Checks.RawSourceLoopTimeout.continuation (by rfl) glob frame nps ph locals world bound

theorem conditionalPostBounds : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawSourceLoopTimeout.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawSourceLoopTimeout.env)) (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawSourceLoopTimeout.env.layout Solidity.Yul.Checks.RawSourceLoopTimeout.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawSourceLoopTimeout.env), ∀ bound, Solidity.Source.firstDone (fun fuel => (Solidity.Source.forIter glob frame fuel nps ph .none (.some (.assign (.local .here) (.bool false))) Solidity.Yul.Checks.RawSourceLoopTimeout.conditionalBody locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawSourceLoopTimeout.env,world)) bound = none := by
  intro glob frame nps ph locals world bound
  exact Solidity.Yul.RawSourceLoopTimeout.post_firstDone Solidity.Yul.Checks.RawSourceLoopTimeout.ctx [] false false _ Solidity.Yul.Checks.RawSourceLoopTimeout.Old.mutatingContinue (by rfl) _ Solidity.Yul.Checks.RawSourceLoopTimeout.writeFalse glob frame nps ph locals world bound

theorem conditionalNoPostBounds : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawSourceLoopTimeout.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawSourceLoopTimeout.env)) (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawSourceLoopTimeout.env.layout Solidity.Yul.Checks.RawSourceLoopTimeout.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawSourceLoopTimeout.env), ∀ bound, Solidity.Source.firstDone (fun fuel => (Solidity.Source.forIter glob frame fuel nps ph .none .none Solidity.Yul.Checks.RawSourceLoopTimeout.conditionalBody locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawSourceLoopTimeout.env,world)) bound = none := by
  intro glob frame nps ph locals world bound
  exact Solidity.Yul.RawSourceLoopTimeout.no_post_firstDone Solidity.Yul.Checks.RawSourceLoopTimeout.ctx [] false false _ Solidity.Yul.Checks.RawSourceLoopTimeout.Old.mutatingContinue (by rfl) glob frame nps ph locals world bound

theorem breakFirstDone : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawSourceLoopTimeout.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawSourceLoopTimeout.env)), Solidity.Source.firstDone (fun fuel => (Solidity.Source.forIter glob frame fuel nps ph .none .none Solidity.Yul.Checks.RawSourceLoopTimeout.breakBody Solidity.Yul.Checks.RawSourceLoopTimeout.initial.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawSourceLoopTimeout.env,Solidity.Yul.Checks.RawSourceLoopTimeout.initial.world)) 2 = some (2,(.ok (.normal Solidity.Yul.Checks.RawSourceLoopTimeout.initial.clean),(Solidity.Source.L0 Solidity.Yul.Checks.RawSourceLoopTimeout.env,Solidity.Yul.Checks.RawSourceLoopTimeout.initial.world))) := by
  intro glob frame nps ph
  rfl

theorem initializedCounterexample : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawSourceLoopTimeout.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawSourceLoopTimeout.env)), Solidity.Source.firstDone (fun fuel => (Solidity.Source.execS glob frame fuel nps ph Solidity.Yul.Checks.RawSourceLoopTimeout.invalidInitialized Solidity.Yul.Checks.RawSourceLoopTimeout.initial.clean).run (Solidity.Source.L0 Solidity.Yul.Checks.RawSourceLoopTimeout.env,Solidity.Yul.Checks.RawSourceLoopTimeout.initial.world)) 2 ≠ none := by
  intro glob frame nps ph bad
  cases bad

theorem dirtyRefusal : Solidity.Yul.RawCoherent.coherent Solidity.Yul.Checks.RawSourceLoopTimeout.dirty = false := by
  exact Solidity.Yul.Checks.RawSourceLoopTimeout.Old.dirtyInput.1

theorem zeroBound : ∀ (glob : Solidity.Source.Glob Solidity.Yul.Checks.RawSourceLoopTimeout.env) (frame : Solidity.Source.Fr) (nps : Nat) (ph : Option (Solidity.Source.Ph Solidity.Yul.Checks.RawSourceLoopTimeout.env)) (locals : Solidity.Source.Locals Solidity.Yul.Checks.RawSourceLoopTimeout.env.layout Solidity.Yul.Checks.RawSourceLoopTimeout.ctx.tys) (world : Solidity.Source.St Solidity.Yul.Checks.RawSourceLoopTimeout.env), Solidity.Source.firstDone (fun fuel => (Solidity.Source.forIter glob frame fuel nps ph .none (.some (.assign (.local .here) (.bool false))) Solidity.Yul.Checks.RawSourceLoopTimeout.simpleBody locals).run (Solidity.Source.L0 Solidity.Yul.Checks.RawSourceLoopTimeout.env,world)) 0 = none := by
  intro glob frame nps ph locals world
  rfl

#print axioms Solidity.Yul.RawSourceLoopTimeout.post_timeout
#print axioms Solidity.Yul.RawSourceLoopTimeout.no_post_timeout
#print axioms Solidity.Yul.RawSourceLoopTimeout.post_firstDone
#print axioms Solidity.Yul.RawSourceLoopTimeout.no_post_firstDone
#print axioms postWorld
#print axioms noPostWorld
#print axioms postBounds
#print axioms noPostBounds
#print axioms conditionalPostBounds
#print axioms conditionalNoPostBounds
#print axioms breakFirstDone
#print axioms initializedCounterexample
#print axioms dirtyRefusal
#print axioms zeroBound
end Solidity.Yul.Checks.RawSourceLoopTimeout
