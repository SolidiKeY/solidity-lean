import Solidity.Semantics.RunFuel
import Solidity.Roadmap.Contracts

/-!
# How the existing typed run reads as a resourced family

The fuelled typed run (`Prog.runF`, `Semantics/RunFuel.lean`) is a family
indexed by loop fuel: its `diverge` at fuel `n` ends the prefix unfinished,
and every other result completes it.  This only shows the plug for G01's
contracts (`Solidity/Roadmap/Contracts.lean`): the intrinsic language of
contract 2 still needs events, the transaction boundary and a call semantics
without the fixed recursion unrolling (`recDepth`).  It is kept apart from
the contracts so that a source semantics importing them for `Artifact` does
not reach the intrinsic run; so is the evaluation order of each pipeline,
which reads the raw syntax's `EvalOrder`.
-/

namespace Solidity.Roadmap

/-- The evaluation order of a pipeline. -/
def Pipeline.order : Pipeline → EvalOrder
  | .legacy => {}
  | .viaIR => EvalOrder.viaIR

/-- The evaluation order of an input: its pipeline's. -/
def SourceSpec.order (S : SourceSpec) (i : S.Input) : EvalOrder := (S.pipeline i).order

/-- One typed run as a resourced family with no events, completing with the
typed result. -/
def typedRunPrefixes {C : Contract} {Γ Γ' : Ctx} (P : Prog C Γ Γ') (σ : State C Γ) :
    Prefixes Nat Unit (TRes (State C Γ')) := fun n =>
  match Prog.runF n P σ with
  | .error .diverge => ⟨[], none⟩
  | .error e => ⟨[], some (.error e)⟩
  | .ok o => ⟨[], some (.ok o.st)⟩

end Solidity.Roadmap
