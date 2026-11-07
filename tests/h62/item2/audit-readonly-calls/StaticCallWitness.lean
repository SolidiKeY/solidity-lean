import Solidity.Lowering.Readonly.SourceDispatchInterfaceV2Controls

/-! Static-mode premise inhabitation and storage-law specialization.
`jointly_satisfiable` supplies values for the single mode equation: choosing
`requested = true` reduces it to `true || F.static = true`. It establishes no
execution feasibility beyond that flag condition. `client` separately applies
the existing versioned storage law. Neither result proves compiler success,
gas/fork behavior or source-to-target callee correspondence; V1 stays unchanged.
-/
namespace Solidity.H62.ReadonlyAudit.StaticCallWitness
open Solidity.Source Solidity.Source.SemanticsExamples Solidity.Roadmap
open Solidity.Lowering.Readonly

theorem jointly_satisfiable :
    ∃ (G : Glob EB) (F : Fr) (n : Nat) (receiver : Address) (value : Word)
      (input : Bytes) (requested : Bool) (state : St EB),
      (requested || F.static) = true :=
  ⟨SourceDispatchV2.Controls.global, FC, 3, addr 0, word 0, SourceDispatchControls.cb, true, sB, rfl⟩

theorem client : StaticJournal.SameStorage
    ((callAddr SourceDispatchV2.Controls.global FC 3 (addr 0) (word 0) SourceDispatchControls.cb true).run
      (L0 EB, sB)).2.2.ex sB.ex :=
  SourceDispatchV2.static_call_storage SourceDispatchV2.Controls.global FC 3 (addr 0) (word 0) SourceDispatchControls.cb true sB rfl

#print axioms jointly_satisfiable
#print axioms client
end Solidity.H62.ReadonlyAudit.StaticCallWitness
