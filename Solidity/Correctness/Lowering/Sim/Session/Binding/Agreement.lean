import Solidity.Goals.LoweringSession
import Solidity.Correctness.Lowering.Sim.Match

/-!
# Storage and event agreement from `globRel` (ls2s, lane binding)

What `Shrink.Lowering.Agrees` (`Goals/LoweringSession.lean`) is for
`Sim.diagram.globRel`, and what a frame matched by `Diagram.Final` gives.

* `globRel_congr`: `globRel` reads the model state's own address, storage and
  funds, nothing else.
* `boundaryAt`, `globRel_committed`: a related final state committed by
  `World.finish` leaves at its address an account whose boundary state, with
  the frame's address and funds, is related.
* `globRel_boundaryState`, `agrees_iff`: at the goal's `boundaryState` (the
  zero address and funds of `State.init`) the relation is about Source
  address zero, and so is `Agrees Sim.diagram`.

**What the goal lacks (reported, not worked around).** `globRel` identifies
the Source instance by `tx.selfAddress`, and `boundaryState` keeps
`State.init`'s. So `Agrees` compares the deployed storage with Source address
zero, not the deployed instance; `globRel_committed` gives `boundaryAt`, which
is `boundaryState` only at address zero without funds (`boundaryAt_dflt`).
Closing this needs `boundaryState` to carry the address and the world's funds.
-/
namespace Solidity.Correctness.Lowering.Sim.Session

open Solidity.Goals.Shrink.Lowering
open Solidity.Correctness.Lowering.Sim
open Solidity.ContractWorld (World Account)
open Solidity.Roadmap (SessionEnv Outcome)
open Solidity.Roadmap.G49Final (Behaviour)
open Solidity.Semantics.IntrinsicSession (Start spec runOf)

/-- `globRel` reads the model state's own address, storage and funds only. -/
theorem globRel_congr {E : Source.Env} {C : Contract} {Γ Γ' : Ctx} {st : Source.St E}
    {σ : State C Γ} {σ' : State C Γ'} (h : diagram.globRel st σ) (storage : σ'.storage = σ.storage)
    (address : σ'.tx.selfAddress = σ.tx.selfAddress) (funds : σ'.selfBalance = σ.selfBalance) :
    diagram.globRel st σ' := by
  obtain ⟨self, at_self, fields, balance⟩ := h
  exact ⟨self, address ▸ at_self, storage ▸ fields, funds ▸ balance⟩

/-- The boundary state of an instance with its own address and funds. -/
def boundaryAt {K : Type} {contracts : K → Contract} (a : Account contracts)
    (self funds : PrimTy.uint.Denote) : State (contracts a.1) [] :=
  { boundaryState a with selfBalance := funds, tx := { selfAddress := self } }

/-- The goal's boundary state is the one at address zero without funds. -/
theorem boundaryAt_dflt {K : Type} {contracts : K → Contract} (a : Account contracts) :
    boundaryAt a (PrimTy.dflt .uint) (PrimTy.dflt .uint) = boundaryState a := rfl

/-- **Storage agreement of a committed frame**: a related final state leaves at
its address an account related at the frame's address and funds. -/
theorem globRel_committed {E : Source.Env} {K : Type} [DecidableEq K] {contracts : K → Contract}
    {w t : World contracts} {k : K} {Γ : Ctx} {self : ContractWorld.Address}
    {σ : State (contracts k) Γ} {st : Source.St E} (h : diagram.globRel st σ)
    (commit : w.finish self σ = .ok t) :
    ∃ a, t.accounts self = some a ∧
      diagram.globRel st (boundaryAt a σ.tx.selfAddress σ.selfBalance) :=
  ⟨⟨k, σ.storage⟩, by rw [World.finish_accounts commit]; exact if_pos rfl,
    globRel_congr (σ' := boundaryAt ⟨k, σ.storage⟩ σ.tx.selfAddress σ.selfBalance) h rfl rfl rfl⟩

/-- **At the goal's boundary state `globRel` is about address zero**: the
account's storage is related to the cells of Source address zero, whose balance
is zero when it is a word. -/
theorem globRel_boundaryState {E : Source.Env} {K : Type} {contracts : K → Contract}
    (st : Source.St E) (a : Account contracts) :
    diagram.globRel st (boundaryState a) ↔
      Total.Relation.fields (cell st Roadmap.Address.zero) a.2 ∧
      (Source.Monetary.Fits (st.ex.world.accounts Roadmap.Address.zero).balance →
        (st.ex.world.accounts Roadmap.Address.zero).balance = 0) := by
  constructor
  · rintro ⟨self, address, fields, balance⟩
    have zero : self = Roadmap.Address.zero := Fin.ext (Int.ofNat.inj address)
    subst zero
    exact ⟨fields, fun fits => (Int.ofNat.inj (balance fits)).symm⟩
  · rintro ⟨fields, balance⟩
    exact ⟨Roadmap.Address.zero, rfl, fields, fun fits => by rw [balance fits]; rfl⟩

/-- **The agreement conjunct for the diagram**, unfolded: the Source history
is a prefix of the lowered run's, and the deployed account of the `i`th
boundary world holds storage related to the cells of Source address zero. -/
theorem agrees_iff (F : Roadmap.Fixed) {E : Source.Env} (P : Source.SrcProg E) (x : Start) :
    Agrees diagram F P x ↔
      ∀ (e : SessionEnv) (n k i : Nat) (s : Source.St E) (last : Outcome), e.Allowed →
        (Behaviour.ofLang (spec F).lang ((spec F).ofWorld x)).Ready e (transport diagram n) →
        (sourceMachine P e).Reachable (SourceState.run n k i s last) →
          s.events <+: ((spec F).lang.sem x e (transport diagram n)).events ∧
          ∀ w, (runOf F x e (transport diagram n)).worlds[i]? = some w →
            ∀ a, w.accounts (Solidity.Lowering.V08.EnvironmentProjection.liftAddress
              (P.fixed.createAddress e.deployer e.deployNonce)) = some a →
              Total.Relation.fields (cell s Roadmap.Address.zero) a.2 ∧
              (Source.Monetary.Fits (s.ex.world.accounts Roadmap.Address.zero).balance →
                (s.ex.world.accounts Roadmap.Address.zero).balance = 0) := by
  constructor <;> intro h e n k i s last allowed ready reach <;>
    obtain ⟨events, storage⟩ := h e n k i s last allowed ready reach
  · exact ⟨events, fun w hw a ha => (globRel_boundaryState s a).1 (storage w hw a ha)⟩
  · exact ⟨events, fun w hw a ha => (globRel_boundaryState s a).2 (storage w hw a ha)⟩

end Solidity.Correctness.Lowering.Sim.Session
