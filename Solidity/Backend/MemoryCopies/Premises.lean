import Solidity.Backend.MemoryCopies.Interface
import Solidity.Source.Eval
import Solidity.Source.Hoare

/-! Explicit external obligations. No instance is postulated. A consumer must
supply the producing item's actual theorem at the specified types. These are
local boundaries; they are not substitutes for the producers' frozen APIs. -/
namespace Solidity.Backend.MemoryCopies

/-- S03-PANIC41: a supplied actual
Source allocation operation, at an actual state, fails with alloc panic.
The producer must also establish which size predicate selects this branch. -/
structure Panic41Premise {E : Source.Env} {Γ : Source.RCtx} {α : Type}
    (operation : Source.EM E Γ α) (before after : Source.EMState E Γ) : Prop where
  failure : operation.run before = (Source.panic .alloc, after)

/-- V11 G34: the compiled alias branch has the existing typed identity and
heap. The actual path-resolution and rebinding certificates must be supplied. -/
structure AliasPremise {H : HTy} {R : RefTy} (hp : Heap H)
    (input output : HRef H R) (after : Heap H) : Prop where
  agreement : AliasCertificate hp input output after

/-- V10 G27.05, V11 G35.02/.03: reached machines at a composition boundary.
These are exact execution equations, not an assumed universal compiler theorem.
Each use must name its producing item, resolved operands and observations. -/
structure LocationStepPremise (code : List Evm.Instr)
    (before after : Evm.Machine) : Prop where
  execution : Evm.run code before = .ok after 0

/-- G34 resolved-path/rebinding boundary at existing intrinsic types. Unlike
AliasPremise, this fixes the actual path evaluator and rebind operation. It is
a local success premise, not the missing physical path/compiler certificate. -/
structure AliasPathPremise {C : Contract} {Γ : Ctx} {R : RefTy}
    (before : State C Γ) (path : MPath C Γ (.ref R))
    (destination : Idx Γ (.mem R)) (reference : HRef before.H R) : Prop where
  resolution : path.mvalT before = .ok reference
  rebinding : TRun.rebindMem destination (.alias path) before =
    .ok ⟨before.setLocal destination (some reference), List.prefix_refl _⟩

/-- Concrete existing Source newArray length-panic boundary. Length evaluation
and conversion are explicit at the reached state; their side effects are not
rolled back. This covers the published 2^64 branch only. S03-PANIC41's missing
finalize-allocation/cursor-overflow semantics is NOT supplied by this record.
The existing length-panic equation is derived in SourceSize, not an input field. -/
structure NewArrayLengthPanicPremise {E : Source.Env} {Γ : Source.RCtx}
    {τ σ : Source.STy} (global : Source.Glob E) (frame : Source.Fr)
    (fuel : Nat) (newable : τ.newable = true) (length : Source.RExpr E Γ σ)
    (index : σ.isIndex = true) (value : Source.RVal E.layout σ) (count : Nat)
    (before reached : Source.EMState E Γ) : Prop where
  evaluation : (Source.evalE global frame fuel length).run before = (.ok value, reached)
  conversion : (Source.indexNat (E := E) (Γ := Γ) value).run reached = (.ok count, reached)
  oversized : 2 ^ 64 ≤ count

end Solidity.Backend.MemoryCopies
