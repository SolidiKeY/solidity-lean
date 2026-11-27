import Solidity.Correctness.Lowering.Sim.Match
import Solidity.Correctness.Lowering.Total.Versions.CalleeBinding.Frame

/-!
# P3 association contract, pending semantic review

Advances `Solidity.Goals.loweringBySimulation` additively. These are definitions
of obligations, not proofs of them. No frozen diagram or association changes.
The callee branch binds the original declared body using P2's actual producer;
it does not use plain spelling. Ordinary here means non-constructor, as in P2.

The proposed relation extends frozen `Assoc`; it agrees with it on loops.
The converse is intentionally only a loop statement. Separate existential
coverage obligations require actual callee and recursive witnesses, including
successful P2 production. They do not assert successful lowering: `Production`
remains separate, as in frozen `Assoc`. No totality over all production runs,
execution simulation, modifier execution or recursive-frame provenance is
claimed. In particular `Reads` observes items, not `RBody.mods`. P2 preserves
the complete body but does not prove storage or local alignment; those remain
explicit requirements here. Recursive scope must be linked separately before
using P2's recursive endpoint in a simulation proof.
-/
namespace Solidity.Correctness.Lowering.Sim.AssociationV2

open Solidity.Goals.Shrink.Lowering
open Solidity.Lowering.V07 (ContextMap)

abbrev BindingSite := Total.Version.CalleeBinding.Site
abbrev BindingOutput := Total.Version.CalleeBinding.Output

/-- The fixed P2 producer, not an arbitrary output relation. -/
def produce (site : BindingSite) (r : Total.Request) : Option BindingOutput :=
  Total.Version.CalleeBinding.fromFunctions site.tables site.registry site.settings
    site.scope site.leadingParts r.contract.funs site.index

/-- The exact items program of P2's bound body. Modifiers are retained in the
binding output, not asserted to execute by frozen `Reads`. -/
def program (s : BindingOutput) : Total.SourceProgram :=
  ⟨s.source.res.env, s.body.rs, s.body.inModifier, .body,
    s.body.locals, s.body.out, s.body.items⟩

/-- New branch: selected first-match alias, original raw input, successful
fixed producer, exact P2 binding, exact resolved items and storage typing.
No `Total.Spells` hypothesis appears in this branch. -/
def Callee (b : Body) (u : Emitted) : Prop :=
  ∃ (site : BindingSite) (c : Total.CalleeRequest) (s : BindingOutput) (alias : Name),
    produce site (request b u) = some s ∧
    Total.Version.CalleeBinding.AliasBound site (request b u) c s alias ∧
    b.input.raw = c.declaration.body ∧
    Reads b (program s) ∧ StorageTyped b.E u.C

/-- Proposed additive association. Both branches retain context/name alignment
and total local liftability. The old branch is preserved verbatim. -/
def AssocV2 (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ) : Prop :=
  u.Γ = (request b u).context.ctx ∧
  u.output.names = (request b u).context.names ∧ Aligned m ∧
    ((∃ s, Total.Spells (request b u) s ∧ Reads b s) ∨ Callee b u)

/-- Unproved direction and exact loop coverage of the compatibility contract. -/
def Compatibility : Prop :=
  (∀ b u m, Assoc b u m → AssocV2 b u m) ∧
  (∀ b u m, b.site = .loop → (AssocV2 b u m ↔ Assoc b u m))

/-- Total initial matching uses exactly the frozen value/global relations and
quantifies over every Source state; no initial-state premise is added. -/
def InitialMatching : Prop :=
  ∀ (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ), AssocV2 b u m →
    ∀ src : Source.EMState b.E b.ctx, ∃ tgt : State u.C u.Γ,
      m.Related (fun τ v => valRel τ v) src.1 tgt.env ∧ globRel src.2 tgt

/-- Genuine association inhabitants at both non-loop site constructors.
Existentials require producer success through `Callee`; a conditional theorem
from an assumed binding is insufficient. This is not production totality. -/
def Coverage : Prop :=
  (∃ (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ),
    (∃ d ρ ctor selfFrame Γf funs k₀,
      b.site = .callee d ρ ctor selfFrame Γf funs k₀) ∧ AssocV2 b u m ∧ Callee b u) ∧
  (∃ (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ),
    (∃ d ρ ctor selfFrame Γf funs k₀ outer rf,
      b.site = .recursive d ρ ctor selfFrame Γf funs k₀ outer rf) ∧
    AssocV2 b u m ∧ Callee b u)

/-- Reviewable obligations; no inhabitant is asserted before approval. -/
def Contract : Prop := Compatibility ∧ InitialMatching ∧ Coverage

end Solidity.Correctness.Lowering.Sim.AssociationV2
