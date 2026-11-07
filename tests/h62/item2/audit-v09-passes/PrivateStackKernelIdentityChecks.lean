import Solidity.Backend.Passes.Stack

/-! Regression: frozen private source identities must not be mistaken for
resolved kernel constants. These anonymous type checks pin the actual imported
private constants against their original premise/conclusion types, without
changing their visibility or exporting public aliases. This resolves three
specific identities only; full census elaboration remains open. -/
namespace Solidity.Backend.Passes.AuditPrivateStackIdentity
open Evm Evm.Compiler

-- Numeric kernel Name components cannot be written as dotted source identifiers.
macro "privateStack%" n:ident : term =>
  pure (Lean.mkIdentFrom n ((Lean.Name.num `_private.Solidity.Backend.Passes.Stack 0) ++
    `Solidity.Backend.Passes ++ n.getId))

example {C : Contract} {Γ : Ctx} {b frame cost : Nat} {σ : State C Γ}
    {base : Nat → Fin W} {m : Machine}
    (h : Memory.AllocationInput b frame cost σ base m) (tail : List Word) :
    Memory.AllocationInput b frame cost σ base {m with stack := tail} :=
  (privateStack% allocation_stack) h tail

example {C : Contract} {Γ : Ctx} {b frame cost : Nat} {σ : State C Γ}
    {base : Nat → Fin W} {m : Machine}
    (h : Memory.Objects.AllocationInput b frame cost σ base m) (tail : List Word) :
    Memory.Objects.AllocationInput b frame cost σ base {m with stack := tail} :=
  (privateStack% object_allocation_stack) h tail

example {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ} {σ : State C Γ}
    {base : Nat → Fin W} {m : Machine}
    (h : Memory.Objects.StateRepr L b frame F σ base m) (tail : List Word) :
    Memory.Objects.StateRepr L b frame F σ base {m with stack := tail} :=
  (privateStack% object_state_stack) h tail

/-- info: _private.Solidity.Backend.Passes.Stack.0.Solidity.Backend.Passes.allocation_stack: [propext, Quot.sound] -/
#guard_msgs in
run_cmd do
  let name := (Lean.Name.num `_private.Solidity.Backend.Passes.Stack 0) ++
    `Solidity.Backend.Passes.allocation_stack
  let axes ← Lean.collectAxioms name
  Lean.logInfo m!"{name}: {axes}"

/-- info: _private.Solidity.Backend.Passes.Stack.0.Solidity.Backend.Passes.object_allocation_stack: [propext, Quot.sound] -/
#guard_msgs in
run_cmd do
  let name := (Lean.Name.num `_private.Solidity.Backend.Passes.Stack 0) ++
    `Solidity.Backend.Passes.object_allocation_stack
  let axes ← Lean.collectAxioms name
  Lean.logInfo m!"{name}: {axes}"

/-- info: _private.Solidity.Backend.Passes.Stack.0.Solidity.Backend.Passes.object_state_stack: [propext, Quot.sound] -/
#guard_msgs in
run_cmd do
  let name := (Lean.Name.num `_private.Solidity.Backend.Passes.Stack 0) ++
    `Solidity.Backend.Passes.object_state_stack
  let axes ← Lean.collectAxioms name
  Lean.logInfo m!"{name}: {axes}"

end Solidity.Backend.Passes.AuditPrivateStackIdentity
