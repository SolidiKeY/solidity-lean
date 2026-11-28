import Solidity.Correctness.Lowering.Sim.Match
import Solidity.Correctness.Lowering.Total.Versions.CalleeBinding.Frame

/-!
# Association contract with callee binding, pending semantic review

Advances `Solidity.Goals.loweringBySimulation` additively. These are definitions
of obligations, not proofs of them. No frozen diagram or association changes.
The callee branch binds the original declared body using the actual callee-binding producer;
it does not use plain spelling. Ordinary here means non-constructor, as in `CalleeBinding`.

The proposed relation extends frozen `Assoc`; it agrees with it on loops.
The converse is intentionally only a loop statement. Coverage requires witnesses
with successful production and actual recursive caller provenance. It
retains `Production` and `Accepted`; its recursive witness also retains the
full caller success equation and canonical first-frame protocol. The witness
has no parameters or returns; this does not restrict the association itself.

No obligation is proved here. The public `elabCallRet` and `elabStmtP` remain
partial; their closed success equations need upstream kernel bridges, not
axioms or external execution relabelled as proof. `Reads` still observes items,
not `RBody.mods`; no execution simulation is claimed. The callee binding retains the complete
body but storage and local alignment remain explicit requirements.

-/
namespace Solidity.Correctness.Lowering.Sim.AssociationV2

open Solidity.Goals.Shrink.Lowering
open Solidity.Lowering.V07 (ContextMap)

abbrev BindingSite := Total.Version.CalleeBinding.Site
abbrev BindingOutput := Total.Version.CalleeBinding.Output

/-- The fixed callee-binding producer, not an arbitrary output relation. -/
def produce (site : BindingSite) (r : Total.Request) : Option BindingOutput :=
  Total.Version.CalleeBinding.fromFunctions site.tables site.registry site.settings
    site.scope site.leadingParts r.contract.funs site.index

/-- The exact items program of the bound callee body. Modifiers are retained in the
binding output, not asserted to execute by frozen `Reads`. -/
def program (s : BindingOutput) : Total.SourceProgram :=
  ⟨s.source.res.env, s.body.rs, s.body.inModifier, .body,
    s.body.locals, s.body.out, s.body.items⟩

/-- New branch: selected first-match alias, original raw input, successful
fixed producer, exact callee binding, exact resolved items and storage typing.
No `Total.Spells` hypothesis appears in this branch. -/
def CalleeAt (b : Body) (u : Emitted) (alias : Name) : Prop :=
  ∃ (site : BindingSite) (c : Total.CalleeRequest) (s : BindingOutput),
    produce site (request b u) = some s ∧
    Total.Version.CalleeBinding.AliasBound site (request b u) c s alias ∧
    b.input.raw = c.declaration.body ∧
    Reads b (program s) ∧ StorageTyped b.E u.C

/-- Forget only the alias; recursive provenance retains it via `CalleeAt`. -/
def Callee (b : Body) (u : Emitted) : Prop := ∃ alias, CalleeAt b u alias

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

/-- A no-argument/no-return recursive witness retains an actual successful
caller on the body's full input snapshot. First-match selection, recursive
classification and absence of an older frame identify the new-frame branch.
No header slots are allocated, so k₀ is the initial counter. The frame is the
first checked frame of `elabCallRetCore`, over `Prog.recBase`, with the same
alias, contract and empty context. These equations remain proof obligations;
field shape alone or an unrelated successful caller would not suffice. -/
def RecursiveOrigin (b : Body) (u : Emitted) (alias : Name) : Prop :=
  letI : FreshNames := productionNames
  ∃ (d : FunDecl) (i : Nat),
    b.input.scope.funs.findIdx? (fun entry => entry.1 == alias) = some i ∧
    b.input.scope.funs[i]? = some (alias, d) ∧
    d.params = [] ∧ d.rets = [] ∧
    isRecursiveC (C := u.C) alias = true ∧
    b.input.scope.recs.find? (fun frame => frame.name == alias) = none ∧
    u.Γ = [] ∧ u.output.names = [] ∧
    b.site = .recursive d [] false b.input.scope.selfFrame []
      (u.C.funs.take ((u.C.funs.findIdx? (fun entry => entry.1 == alias)).getD 0) ++
        (u.C.funs.drop ((u.C.funs.findIdx? (fun entry => entry.1 == alias)).getD 0)).filter
          (fun entry => (recPartnersC (C := u.C) alias).contains entry.1))
      b.input.before.locals.2 b.input.scope
      { name := alias, params := [], rets := [], depth := recDepth - 1,
        below := ⟨u.C, [], fun _ => Prog.recBase⟩ } ∧
    ∃ (after : Solidity.Correctness.Lowering.Checker.Snapshot), ∃ result,
      (((elabCallRet (C := u.C) alias [] none).run b.input.scope).run
        b.input.before.locals).run b.input.before.memo =
        .ok ((result, after.locals), after.memo)

/-- Actual successful accepted production at both non-loop sites. Recursive
coverage retains the same alias's actual caller and canonical first frame.
These are existential obligations, not assumed production receipts. -/
def Coverage : Prop :=
  letI : FreshNames := productionNames
  (∃ (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ),
    (∃ d ρ ctor selfFrame Γf funs k₀,
      b.site = .callee d ρ ctor selfFrame Γf funs k₀) ∧
    AssocV2 b u m ∧ Callee b u ∧ Production b u ∧ Accepted u) ∧
  (∃ (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ) (alias : Name),
    AssocV2 b u m ∧ CalleeAt b u alias ∧ Production b u ∧ Accepted u ∧
      RecursiveOrigin b u alias)

/-- Draft obligations, not the final delivery contract. In addition
to these same-input caller and canonical-frame conditions, the exact bridge
from the caller result/state to the checked frame output must be stated and
proved against the upstream producer interface. No inhabitant here alone
completes that missing provenance obligation or the association contract. -/
def Contract : Prop := Compatibility ∧ InitialMatching ∧ Coverage

end Solidity.Correctness.Lowering.Sim.AssociationV2
