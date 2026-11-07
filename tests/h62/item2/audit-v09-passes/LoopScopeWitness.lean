import Solidity.Backend.Passes.LoopScopeControls
import Solidity.Backend.Passes.LoopScopeApplication

/-! Guard empty loop-scope admission, substituting target execution for finite
source iteration, or treating the zero legacy metric as a positive-cost budget.
Reuse actual preparation, alias rebinding and source TLoop witnesses. -/
namespace Solidity.Backend.Passes.AuditLoopScope
open Evm Evm.Memory Evm.Compiler
open Solidity.Backend.Passes
open LoopScopeControls

theorem joint :
    (Compilation.memory preparation).Input 1 128 MemoryCallControls.base
      MemoryCallControls.initial MemoryCallControls.machine ∧
    (Compiler.compile 1 preparation.frag wrapped).map (·.isMemoryLoopScopes) = some true ∧
    body.run prepared.st = .ok (bodyResult prepared.st) ∧
    wrapped.run prepared.st = .ok loopOut ∧
    LoopScopes.Cost enclosed.cert prepared.st loopOut 3 ∧
    checked.allocationCost prepared.st = 0 :=
  ⟨LoopScopeApplication.preparation_input,public_recognizer,body_source prepared.st,
    wrapped_source,actual_cost,legacy_metric_zero⟩
def prepared_source := @Solidity.Backend.Passes.LoopScopeControls.prepared_source
def body_source := @Solidity.Backend.Passes.LoopScopeControls.body_source
def body_stops := @Solidity.Backend.Passes.LoopScopeControls.body_stops
def condition_initial := @Solidity.Backend.Passes.LoopScopeControls.condition_initial
def condition_final := @Solidity.Backend.Passes.LoopScopeControls.condition_final
def iteration_source := @Solidity.Backend.Passes.LoopScopeControls.iteration_source
def wrapped_source := @Solidity.Backend.Passes.LoopScopeControls.wrapped_source
def final_source := @Solidity.Backend.Passes.LoopScopeControls.final_source
def costs := @Solidity.Backend.Passes.LoopScopeControls.costs
def body_cost := @Solidity.Backend.Passes.LoopScopeControls.body_cost
def public_recognizer := @Solidity.Backend.Passes.LoopScopeControls.public_recognizer
def frames := @Solidity.Backend.Passes.LoopScopeControls.frames
def iteration_stmt_source := @Solidity.Backend.Passes.LoopScopeControls.iteration_stmt_source
def block_stmt_source := @Solidity.Backend.Passes.LoopScopeControls.block_stmt_source
def reached_prefix := @Solidity.Backend.Passes.LoopScopeControls.reached_prefix
def actual_cost := @Solidity.Backend.Passes.LoopScopeControls.actual_cost
def legacy_metric_zero := @Solidity.Backend.Passes.LoopScopeControls.legacy_metric_zero

macro "loopScopePrivate%" n:ident : term =>
  pure (Lean.mkIdentFrom n ((Lean.Name.num `_private.Solidity.Backend.Passes.LoopScopeControls 0) ++
    `Solidity.Backend.Passes.LoopScopeControls ++ n.getId))
example {Γ Δ : Ctx} {σ : State MemoryCallControls.C Γ}
    {P : Prog MemoryCallControls.C Γ Δ} {o : Solidity.Out MemoryCallControls.C σ.H Δ}
    (hx : some o = (P.run σ).toOption) : P.run σ = .ok o :=
  (loopScopePrivate% source_get) hx

theorem extraction_premise :
    some prepared = (prepare.run MemoryCallControls.initial).toOption := by
  rw [LoopScopeControls.prepared_source]
  rfl

/-- info: 'Solidity.Backend.Passes.AuditLoopScope.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopScope.joint

/-- info: 'Solidity.Backend.Passes.AuditLoopScope.extraction_premise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopScope.extraction_premise

/-- info: 'Solidity.Backend.Passes.AuditLoopScope.prepared_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopScope.prepared_source

/-- info: 'Solidity.Backend.Passes.AuditLoopScope.body_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopScope.body_source

/-- info: 'Solidity.Backend.Passes.AuditLoopScope.body_stops' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopScope.body_stops

/-- info: 'Solidity.Backend.Passes.AuditLoopScope.condition_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopScope.condition_initial

/-- info: 'Solidity.Backend.Passes.AuditLoopScope.condition_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopScope.condition_final

/-- info: 'Solidity.Backend.Passes.AuditLoopScope.iteration_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopScope.iteration_source

/-- info: 'Solidity.Backend.Passes.AuditLoopScope.wrapped_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopScope.wrapped_source

/-- info: 'Solidity.Backend.Passes.AuditLoopScope.final_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopScope.final_source

/-- info: 'Solidity.Backend.Passes.AuditLoopScope.costs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopScope.costs

/-- info: 'Solidity.Backend.Passes.AuditLoopScope.body_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopScope.body_cost

/-- info: 'Solidity.Backend.Passes.AuditLoopScope.public_recognizer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopScope.public_recognizer

/-- info: 'Solidity.Backend.Passes.AuditLoopScope.frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopScope.frames

/-- info: 'Solidity.Backend.Passes.AuditLoopScope.iteration_stmt_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopScope.iteration_stmt_source

/-- info: 'Solidity.Backend.Passes.AuditLoopScope.block_stmt_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopScope.block_stmt_source

/-- info: 'Solidity.Backend.Passes.AuditLoopScope.reached_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopScope.reached_prefix

/-- info: 'Solidity.Backend.Passes.AuditLoopScope.actual_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopScope.actual_cost

/-- info: 'Solidity.Backend.Passes.AuditLoopScope.legacy_metric_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditLoopScope.legacy_metric_zero

/-- info: _private.Solidity.Backend.Passes.LoopScopeControls.0.Solidity.Backend.Passes.LoopScopeControls.source_get: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
run_cmd do
  let name := (Lean.Name.num `_private.Solidity.Backend.Passes.LoopScopeControls 0) ++
    `Solidity.Backend.Passes.LoopScopeControls.source_get
  let axes ← Lean.collectAxioms name
  Lean.logInfo m!"{name}: {axes}"
end Solidity.Backend.Passes.AuditLoopScope
