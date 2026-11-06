import Solidity.Backend.Scalar.Axioms
import Solidity.Backend.Environment.CompositionChecks

/-! Shared concrete data for simultaneous witnesses, never new premises.
All certificates and source/target relations remain the original interfaces. -/
namespace Solidity.Backend.Scalar.H62Audit.Fixtures
open Solidity
open Solidity.Backend.Environment (represented represented_ok sample)

abbrev u0 : PrimTy.uint.Denote := ⟨0, by decide⟩
abbrev u1 : PrimTy.uint.Denote := ⟨1, by decide⟩
abbrev u3 : PrimTy.uint.Denote := ⟨3, by decide⟩
abbrev u7 : PrimTy.uint.Denote := ⟨7, by decide⟩
abbrev u9 : PrimTy.uint.Denote := ⟨9, by decide⟩
abbrev u99 : PrimTy.uint.Denote := ⟨99, by decide⟩
abbrev u255 : PrimTy.uint.Denote := ⟨255, by decide⟩
abbrev i0 : PrimTy.int.Denote := ⟨0, by decide⟩
abbrev i1 : PrimTy.int.Denote := ⟨1, by decide⟩
abbrev ineg1 : PrimTy.int.Denote := ⟨-1, by decide⟩
abbrev state0 : State default [] := State.init default
abbrev representedState : State default [] := Solidity.Backend.Environment.represented state0 Solidity.Backend.Environment.sample
abbrev representedProof : Solidity.Backend.Environment.Represents Solidity.Backend.Environment.sample representedState := Solidity.Backend.Environment.represented_ok state0 Solidity.Backend.Environment.sample
abbrev emptyMemory : Solidity.Backend.Environment.Memory := fun _ => 0
abbrev targetSlice : Solidity.Backend.Environment.Slice := ⟨[u99], emptyMemory⟩
abbrev stableSample : Solidity.Backend.Environment.Stable Solidity.Backend.Environment.sample Solidity.Backend.Environment.sample := ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩

abbrev bytesR : RefTy := .array (.prim .uint)
abbrev bytesΓ : Ctx := [.mem bytesR]
def bytesState : State default bytesΓ :=
  { storage := Storage.init default
    H := [bytesR]
    heap := (⟨[], by decide⟩, ())
    env := (some ⟨0, rfl⟩, ()) }
abbrev bytesPath : MPath default bytesΓ (.ref bytesR) := .var .here rfl
abbrev bytesRef : HRef bytesState.H bytesR := ⟨0, rfl⟩
def unsetBytesState : State default bytesΓ := { bytesState with env := (none, ()) }

abbrev emptyHashInput : Solidity.Backend.Environment.HashInput targetSlice ⟨0, by decide⟩ ⟨0, by decide⟩ [] :=
  ⟨by decide, rfl⟩
abbrev heapHashInput : Solidity.Backend.Environment.HashInput targetSlice ⟨0, by decide⟩ ⟨0, by decide⟩
    (MObj.words bytesR (bytesState.heap.get bytesRef)) := ⟨by decide, rfl⟩
abbrev emptyNamespaceInput : Solidity.Backend.Environment.NamespaceInput targetSlice ⟨0, by decide⟩
    ⟨0, by decide⟩ ⟨0, by decide⟩ [] := ⟨by decide, by decide, rfl⟩

abbrev sampleWorld : ContractWorld.World (fun _ : Unit => default) :=
  ContractWorld.World.empty (fun _ : Unit => default) Solidity.Backend.Environment.sample.funds
abbrev resolvedDecl : SourceFunction :=
  { callable := .abi .externalFn .selected (some ⟨0, by decide⟩) }
abbrev localState : State default [.val .uint] :=
  { storage := Storage.init default, H := [], heap := (), env := (u0, ()) }
abbrev identityStep : TStep default [] [] := fun σ => .ok ⟨σ, List.prefix_refl _⟩
abbrev failedStep : TStep default [] [] := fun _ => .error .revert
abbrev initialOut : Out default state0.H [] := ⟨state0, List.prefix_refl _⟩

end Solidity.Backend.Scalar.H62Audit.Fixtures
