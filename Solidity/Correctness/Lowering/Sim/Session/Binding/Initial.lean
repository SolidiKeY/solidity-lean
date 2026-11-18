import Solidity.Goals.LoweringSession
import Solidity.Correctness.Lowering.Sim.Match

/-!
# Initial matching of a session under `globRel` (ls2s, lane binding)

An unwritten Source instance and a model frame at `Storage.init` are related
(`fields_fresh`, `globRel_fresh`); so are the Source state before the session
(`initial_globRel`) and the state the deployment's frame of a lowered world
enters (`enter_fresh`, `deploy_initial`).

**What the relation lacks (reported, not worked around).** `World.enter` gives
the frame `funds self + value`, `funds` the session's opening balances; the
Source deployment opens the account at `0 + value` (`Source.deploy`: opening
balances stay in `Glob.balance0`, read only at addresses without code). So the
balance clause of `globRel` fails at a deployed address with a nonzero opening
balance: `deploy_initial` needs `unfunded`.
-/
namespace Solidity.Correctness.Lowering.Sim.Session

open Solidity.Goals.Shrink.Lowering
open Solidity.Correctness.Lowering.Sim
open Solidity.Source.Agreement (sourceTy PrimitiveRel)
open Solidity.ContractWorld (World Context)
open Solidity.Lowering.V08.EnvironmentProjection (liftAddress liftWord lower_lift_address)

/-- An unwritten primitive cell reads the value related to the model default. -/
theorem read_empty_prim {D : Source.Layout} {L : Source.SPath → Source.STy} (path : Source.SPath)
    (p : PrimTy) (h : L path = sourceTy p) :
    ∃ v : Source.Val D (sourceTy p),
      (((Source.Storage.empty : Source.Storage D L).read path).map fun v =>
        (⟨_, v⟩ : (τ : Source.STy) × Source.Val D τ)) = some ⟨sourceTy p, v⟩ ∧
      PrimitiveRel D p v (PrimTy.dflt p) := by
  have key : ∀ (τ : Source.STy), τ = sourceTy p → ∃ v : Source.Val D (sourceTy p),
      ((Source.Val.default D τ).map fun v => (⟨τ, v⟩ : (τ : Source.STy) × Source.Val D τ)) =
        some ⟨sourceTy p, v⟩ ∧ PrimitiveRel D p v (PrimTy.dflt p) := by
    intro τ e
    subst e
    cases p
    · exact ⟨_, rfl, .bool false⟩
    · exact ⟨_, rfl, .uint (PrimTy.dflt .uint) _⟩
    · exact ⟨_, rfl, .int (PrimTy.dflt .int) _⟩
  exact key _ h

/-- Default model fields are related to a reader of such values. -/
theorem fields_dflt {D : Source.Layout}
    (read : Source.SPath → Option ((τ : Source.STy) × Source.Val D τ)) :
    (fs : List (Name × Ty)) →
    (∀ x T, (x, T) ∈ fs → ∃ p, T = .prim p ∧ ∃ v : Source.Val D (sourceTy p),
      read ⟨⟨some Total.Decode.contractName, x⟩, []⟩ = some ⟨sourceTy p, v⟩ ∧
        PrimitiveRel D p v (PrimTy.dflt p)) →
    Total.Relation.fields read (SFields.dflt fs)
  | [], _ => trivial
  | (x, T) :: fs, h => by
    obtain ⟨p, rfl, v, hv, rel⟩ := h x T (List.mem_cons_self ..)
    exact ⟨⟨v, hv, rel⟩, fields_dflt read fs fun y U m => h y U (List.mem_cons_of_mem _ m)⟩

variable {E : Source.Env} {C : Contract} {Γ : Ctx}

/-- **Fresh storage is related**: an instance nothing was written to holds
cells related to the model's initial storage. -/
theorem fields_fresh (typed : StorageTyped E C) {st : Source.St E} {self : Roadmap.Address}
    (storage : (st.ex.world.accounts self).storage = Source.Storage.empty)
    (transient : st.ex.transient.cells self = Source.Storage.empty) :
    Total.Relation.fields (cell st self) (Storage.init C) := by
  refine fields_dflt _ C.vars fun x T mem => ?_
  obtain ⟨p, rfl, ty⟩ := typed x T mem
  refine ⟨p, rfl, ?_⟩
  simp only [cell, storage, transient, ite_self]
  exact read_empty_prim _ p ty

/-- **A fresh instance and a model frame at its address**, with equal balances. -/
theorem globRel_fresh (typed : StorageTyped E C) {st : Source.St E} {σ : State C Γ}
    (self : Roadmap.Address) (address : (self.val : Int) = σ.tx.selfAddress.1)
    (storage : (st.ex.world.accounts self).storage = Source.Storage.empty)
    (transient : st.ex.transient.cells self = Source.Storage.empty)
    (initial : σ.storage = Storage.init C)
    (balance : Source.Monetary.Fits (st.ex.world.accounts self).balance →
      σ.selfBalance.1 = ((st.ex.world.accounts self).balance : Int)) :
    diagram.globRel st σ :=
  ⟨self, address, initial ▸ fields_fresh typed storage transient, balance⟩

/-- **Initial matching**: the Source state before the session is related to
every model state at the initial storage, at any address, without funds. -/
theorem initial_globRel (typed : StorageTyped E C) {σ : State C Γ} (self : Roadmap.Address)
    (address : (self.val : Int) = σ.tx.selfAddress.1) (initial : σ.storage = Storage.init C)
    (unfunded : σ.selfBalance.1 = 0) : diagram.globRel (Source.St.init E) σ :=
  globRel_fresh typed self address rfl rfl initial fun _ => unfunded

/-- A range-checked `uint` is the integer it was made from. -/
theorem ofInt?_uint_val {n : Int} {b : PrimTy.uint.Denote} (h : PrimTy.ofInt? .uint n = some b) :
    b.1 = n := by
  simp only [PrimTy.ofInt?] at h
  split at h
  · cases h; rfl
  · cases h

/-- A frame's entry state: the storage, its address, its funds plus the value. -/
theorem enter_fresh {K : Type} {contracts : K → Contract} {w : World contracts} {k : K}
    {self : ContractWorld.Address} {ctx : Context} {st : Storage (contracts k)} {payable : Bool}
    {σ : State (contracts k) []} (entered : w.enter self ctx st payable = .ok σ) :
    σ.storage = st ∧ σ.tx.selfAddress = self.1 ∧
      σ.selfBalance.1 = (w.funds self).1 + if ctx.sender = self then 0 else ctx.value.1 := by
  unfold World.enter at entered
  split at entered
  · cases entered
  · split at entered
    · cases entered
    · cases sum : PrimTy.ofInt? .uint
          ((w.funds self).1 + if ctx.sender = self then 0 else ctx.value.1) with
      | none => simp only [sum, TRes.ofOpt, bind, Except.bind] at entered; cases entered
      | some balance =>
        simp only [sum, TRes.ofOpt, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at entered
        subst entered
        exact ⟨rfl, rfl, ofInt?_uint_val sum⟩

/-- **Initial matching of a lowered world**: the state the deployment's frame
enters is related to the Source state before the session, at an address
without opening balance and a deployment without value. -/
theorem deploy_initial [FreshNames] (c : Compilation) (typed : StorageTyped E c.C)
    (F : Roadmap.Fixed) (e : Roadmap.SessionEnv) {payable : Bool} {σ : State c.C []}
    (entered : (Semantics.IntrinsicSession.initial (loweredCode c).roles e).enter
      (k := ⟨0, Nat.zero_lt_one⟩) (liftAddress (F.createAddress e.deployer e.deployNonce))
      (Semantics.IntrinsicSession.deployContext Semantics.IntrinsicSession.wire e)
      (Storage.init c.C) payable = .ok σ)
    (unfunded : (e.balance (F.createAddress e.deployer e.deployNonce)).val = 0)
    (free : e.deployValue.val = 0) : diagram.globRel (Source.St.init E) σ := by
  obtain ⟨initial, address, funds⟩ := enter_fresh entered
  refine initial_globRel typed _ (by rw [address]; rfl) initial ?_
  rw [funds]
  have opening : ((Semantics.IntrinsicSession.initial (loweredCode c).roles e).funds
      (liftAddress (F.createAddress e.deployer e.deployNonce))).1 = 0 := by
    show (liftWord (e.balance _)).1 = 0
    rw [lower_lift_address]
    exact congrArg Int.ofNat unfunded
  have value : (Semantics.IntrinsicSession.deployContext Semantics.IntrinsicSession.wire e).value.1
      = 0 := congrArg Int.ofNat free
  rw [opening, value]
  split <;> rfl

end Solidity.Correctness.Lowering.Sim.Session
