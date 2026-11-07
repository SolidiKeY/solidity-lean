import Solidity.Backend.Passes.MemoryCallScopeControls
import Solidity.Backend.Passes.MemoryCallControls

/-! Guard empty public memory-call admission, lost caller alias/escaped return
semantics, or replacing the call frame demand by legacy memory frame demand.
Instantiate actual expanded-memory-call selections; no external CALL or
independent Source lowering/world semantics is asserted. -/
namespace Solidity.Backend.Passes.AuditMemoryCall
open Evm Evm.Memory Evm.Compiler
open Solidity.Backend.Passes
open MemoryCallControls

theorem joint :
    (Compilation.memory allocation).Input 1 128 base initial machine ∧
    Evm.Prog.pushes call = 0 ∧
    Compiler.compile 1 allocation.frag call = some checked ∧
    allocate.run initial = .ok first ∧
    call.run first.st = .ok second ∧
    consume.run second.st = .ok final ∧
    Memory.frameNeedProg call < producer.need ∧ 1 + producer.need ≤ 128 :=
  ⟨MemoryCallControls.input,MemoryCallControls.push_free,MemoryCallControls.actual_public,
    MemoryCallControls.first_source,MemoryCallControls.second_source,
    MemoryCallControls.final_source,MemoryCallControls.frame_difference⟩
def push_free := @Solidity.Backend.Passes.MemoryCallControls.push_free
def public_recognizer := @Solidity.Backend.Passes.MemoryCallControls.public_recognizer
def actual_public := @Solidity.Backend.Passes.MemoryCallControls.actual_public
def initial_repr := @Solidity.Backend.Passes.MemoryCallControls.initial_repr
def first_source := @Solidity.Backend.Passes.MemoryCallControls.first_source
def second_source := @Solidity.Backend.Passes.MemoryCallControls.second_source
def final_source := @Solidity.Backend.Passes.MemoryCallControls.final_source
def costs := @Solidity.Backend.Passes.MemoryCallControls.costs
def frame_difference := @Solidity.Backend.Passes.MemoryCallControls.frame_difference
def input := @Solidity.Backend.Passes.MemoryCallControls.input

/-- info: 'Solidity.Backend.Passes.AuditMemoryCall.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditMemoryCall.joint

/-- info: 'Solidity.Backend.Passes.AuditMemoryCall.push_free' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditMemoryCall.push_free

/-- info: 'Solidity.Backend.Passes.AuditMemoryCall.public_recognizer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditMemoryCall.public_recognizer

/-- info: 'Solidity.Backend.Passes.AuditMemoryCall.actual_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditMemoryCall.actual_public

/-- info: 'Solidity.Backend.Passes.AuditMemoryCall.initial_repr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditMemoryCall.initial_repr

/-- info: 'Solidity.Backend.Passes.AuditMemoryCall.first_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditMemoryCall.first_source

/-- info: 'Solidity.Backend.Passes.AuditMemoryCall.second_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditMemoryCall.second_source

/-- info: 'Solidity.Backend.Passes.AuditMemoryCall.final_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditMemoryCall.final_source

/-- info: 'Solidity.Backend.Passes.AuditMemoryCall.costs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditMemoryCall.costs

/-- info: 'Solidity.Backend.Passes.AuditMemoryCall.frame_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditMemoryCall.frame_difference

/-- info: 'Solidity.Backend.Passes.AuditMemoryCall.input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditMemoryCall.input

-- Resolve original private success declarations without re-exporting them.
macro "memoryCallPrivate%" n:ident : term =>
  pure (Lean.mkIdentFrom n ((Lean.Name.num `_private.Solidity.Backend.Passes.MemoryCallControls 0) ++
    `Solidity.Backend.Passes.MemoryCallControls ++ n.getId))

example : (allocate.run initial).toOption.isSome = true := memoryCallPrivate% first_some
example : (call.run first.st).toOption.isSome = true := memoryCallPrivate% second_some
example : (consume.run second.st).toOption.isSome = true := memoryCallPrivate% final_some
example {Γ Δ : Ctx} {σ : State C Γ} {P : Prog C Γ Δ}
    {o : Solidity.Out C σ.H Δ} (hx : some o = (P.run σ).toOption) : P.run σ = .ok o :=
  (memoryCallPrivate% source_get) hx

/-- The private extraction premise is inhabited by the actual nontrivial allocation. -/
theorem source_get_joint :
    ∃ (σ : State C []) (P : Prog C [] Before) (o : Solidity.Out C σ.H Before),
      some o = (P.run σ).toOption :=
  ⟨initial,allocate,first,Option.some_get (memoryCallPrivate% first_some)⟩

/-- info: 'Solidity.Backend.Passes.AuditMemoryCall.source_get_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditMemoryCall.source_get_joint
/-- info: first_some: [propext, Classical.choice, Quot.sound]
---
info: second_some: [propext, Classical.choice, Quot.sound]
---
info: final_some: [propext, Classical.choice, Quot.sound]
---
info: source_get: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
run_cmd do
  for short in [`first_some, `second_some, `final_some, `source_get] do
    let name := (Lean.Name.num `_private.Solidity.Backend.Passes.MemoryCallControls 0) ++
      `Solidity.Backend.Passes.MemoryCallControls ++ short
    let axes ← Lean.collectAxioms name
    Lean.logInfo m!"{short}: {axes}"

namespace Scope
/-! Guard losing caller aliases on scope exit, dropping the private call frame,
or choosing stage maps only after a caller tail is supplied. -/
theorem joint :
    (Compilation.memory allocation).Input 1 128 base initial machine ∧
    MemoryCallScopeBoundary.Controls.scopeProgram.run first.st =
      .ok (⟨MemoryCallScopeBoundary.Controls.post,second.ext⟩ : Solidity.Out C first.st.H Before) ∧
    MemoryCallScopeBoundary.Controls.suffix.run MemoryCallScopeBoundary.Controls.post =
      .ok MemoryCallScopeBoundary.Controls.final ∧
    Memory.frameNeedProg call < producer.need ∧ 1 + producer.need ≤ 128 :=
  ⟨MemoryCallControls.input,MemoryCallScopeBoundary.Controls.scope_source,
    MemoryCallScopeBoundary.Controls.suffix_source,MemoryCallControls.frame_difference⟩
def scope_source := @Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.scope_source
def suffix_source := @Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.suffix_source
def joined_source := @Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.joined_source
def shared := @Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.shared
def reached_cost := @Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.reached_cost
def suffix_cost := @Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.suffix_cost
def costs := @Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.costs
def private_frame_refused := @Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.private_frame_refused

/-- info: 'Solidity.Backend.Passes.AuditMemoryCall.Scope.joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditMemoryCall.Scope.joint

/-- info: 'Solidity.Backend.Passes.AuditMemoryCall.Scope.scope_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditMemoryCall.Scope.scope_source

/-- info: 'Solidity.Backend.Passes.AuditMemoryCall.Scope.suffix_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditMemoryCall.Scope.suffix_source

/-- info: 'Solidity.Backend.Passes.AuditMemoryCall.Scope.joined_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditMemoryCall.Scope.joined_source

/-- info: 'Solidity.Backend.Passes.AuditMemoryCall.Scope.shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditMemoryCall.Scope.shared

/-- info: 'Solidity.Backend.Passes.AuditMemoryCall.Scope.reached_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditMemoryCall.Scope.reached_cost

/-- info: 'Solidity.Backend.Passes.AuditMemoryCall.Scope.suffix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditMemoryCall.Scope.suffix_cost

/-- info: 'Solidity.Backend.Passes.AuditMemoryCall.Scope.costs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditMemoryCall.Scope.costs

/-- info: 'Solidity.Backend.Passes.AuditMemoryCall.Scope.private_frame_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditMemoryCall.Scope.private_frame_refused

-- Guard a private success selector being mapped only by source spelling.
macro "scopeCallPrivate%" n:ident : term =>
  pure (Lean.mkIdentFrom n ((Lean.Name.num `_private.Solidity.Backend.Passes.MemoryCallScopeControls 0) ++
    `Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls ++ n.getId))
example : (MemoryCallScopeBoundary.Controls.suffix.run
    MemoryCallScopeBoundary.Controls.post).toOption.isSome = true :=
  scopeCallPrivate% final_some

/-- info: _private.Solidity.Backend.Passes.MemoryCallScopeControls.0.Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.final_some: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
run_cmd do
  let name := (Lean.Name.num `_private.Solidity.Backend.Passes.MemoryCallScopeControls 0) ++
    `Solidity.Backend.Passes.MemoryCallScopeBoundary.Controls.final_some
  let axes ← Lean.collectAxioms name
  Lean.logInfo m!"{name}: {axes}"
end Scope

-- Guard counting an intentional empty-heap refutation as an inhabited witness.
example {R : RefTy} (r : HRef initial.H R) : False := (memoryCallPrivate% noRefs) r

theorem noRefs_premises_impossible (R : RefTy) : ¬ Nonempty (HRef initial.H R) := by
  rintro ⟨r⟩
  exact (memoryCallPrivate% noRefs) r

/-- info: 'Solidity.Backend.Passes.AuditMemoryCall.noRefs_premises_impossible' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Backend.Passes.AuditMemoryCall.noRefs_premises_impossible
/-- info: _private.Solidity.Backend.Passes.MemoryCallControls.0.Solidity.Backend.Passes.MemoryCallControls.noRefs: [propext] -/
#guard_msgs in
run_cmd do
  let name := (Lean.Name.num `_private.Solidity.Backend.Passes.MemoryCallControls 0) ++
    `Solidity.Backend.Passes.MemoryCallControls.noRefs
  let axes ← Lean.collectAxioms name
  Lean.logInfo m!"{name}: {axes}"
end Solidity.Backend.Passes.AuditMemoryCall
