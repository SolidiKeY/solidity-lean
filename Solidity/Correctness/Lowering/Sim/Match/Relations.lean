import Solidity.Goals.LoweringDiagram
import Solidity.Correctness.Lowering.Total.Boundary

/-!
# Source-to-Intrinsic match relations (plan step `ls1-sim-diagrams`)

The value relation, the global relation and the context alignment of the one
lowering diagram (`Sim.diagram`, `Sim/Match.lean`), with the laws that mention
no producer. Frozen once landed: later steps prove against it.

* `valRel`: a Source Boolean and the same model Boolean; a Source integer of
  any width and the model integer of the same sign with the same number
  (`IntValueRel`). No other pair of types is related: addresses, enums, fixed
  bytes, references and formula locals are gaps, as in the landed decoder
  (`Total.Decode.localTy`).
* `globRel`: at the instance whose address is the model's `tx.selfAddress`,
  every primitive state variable holds related values, read as the Source
  machine reads a cell (transient roots from transient storage, the rest from
  the account's storage; `Total.Relation.fields`), and the model's own funds
  are the account's balance when that is a word.
* `frameRel`: what `globRel` cannot say, because its type sees no call frame.
  `Diagram.Simulates` quantifies over every frame, so the forward diagram is
  provable only under it (reported with this step).

Not related: memory heaps, the model ledger `net` and other accounts'
balances (they need the frame's opening funds), external-call answers
(`tx.ext`), and events and logs: the intrinsic `State` has no event component
(a session's events are built per frame, `IntrinsicSession/Step.lean`), so
event agreement is a session-level obligation.
-/
namespace Solidity.Correctness.Lowering.Sim

open Solidity.Lowering.V07 (ContextMap IntValueRel integerPrim integerValue integer_observe)
open Solidity.Source.Agreement (sourceTy PrimitiveRel)

/-! ## Values -/

/-- **The value relation.** Booleans agree; integers agree as numbers at the
model primitive of the Source sign. -/
def valRel {D : Source.Layout} {C : Contract} {H : HTy} :
    (τ : Source.STy) → (u : LTy) → Source.Val D τ → u.TDenote C H → Prop
  | .bool, .val .bool, v, x => v = .bool x
  | .int t, .val p, v, x => p = integerPrim t ∧ v.key = PrimTy.num? (p := p) x
  | _, _, _, _ => False

/-- Boolean reflection. -/
theorem valRel_bool {D : Source.Layout} {C : Contract} {H : HTy} (v : Source.Val D .bool)
    (b : Bool) (h : valRel (C := C) (H := H) .bool (.val .bool) v b) : v = .bool b := h

/-- Integer reflection (`IntValueRel`). -/
theorem valRel_int {D : Source.Layout} {C : Contract} {H : HTy} (t : Source.IntTy)
    (v : Source.Val D (.int t)) (x : (integerPrim t).Denote)
    (h : valRel (C := C) (H := H) (.int t) (.val (integerPrim t)) v x) : IntValueRel t v x := h.2

/-- Every Source value of type `τ` has a related model value of type `u`, at
every heap typing. -/
def Liftable (τ : Source.STy) (u : LTy) : Prop :=
  ∀ (D : Source.Layout) (C : Contract) (H : HTy) (v : Source.Val D τ),
    ∃ x : u.TDenote C H, valRel τ u v x

theorem liftable_bool : Liftable .bool (.val .bool) := fun _ _ _ v => by
  cases v with
  | bool b => exact ⟨b, rfl⟩
  | memRef h | storRef h | cdRef h => cases h

theorem liftable_int (t : Source.IntTy) : Liftable (.int t) (.val (integerPrim t)) :=
  fun _ _ _ v => by
    cases v with
    | int n h => exact ⟨integerValue t n h, rfl, (integer_observe t n h).symm⟩
    | memRef h | storRef h | cdRef h => cases h

/-- The primitive pairs of the landed boundary relation are liftable. -/
theorem liftable_prim : (p : PrimTy) → Liftable (sourceTy p) (.val p)
  | .bool => liftable_bool
  | .uint => liftable_int Source.IntTy.u256
  | .int => liftable_int { Source.IntTy.u256 with signed := true }

/-- The landed primitive correspondence is contained in `valRel`. -/
theorem valRel_of_primitive {D : Source.Layout} {C : Contract} {H : HTy} {p : PrimTy}
    {v : Source.Val D (sourceTy p)} {x : p.Denote} (h : PrimitiveRel D p v x) :
    valRel (C := C) (H := H) (sourceTy p) (.val p) v x := by
  cases h with
  | bool b => rfl
  | uint x h => exact ⟨rfl, rfl⟩
  | int x h => exact ⟨rfl, rfl⟩

/-- The landed boundary value relation (`Total.Relation.val`) is contained in
`valRel`. -/
theorem valRel_of_boundary {E : Source.Env} {C : Contract} {H : HTy} {τ : Source.STy} {u : LTy}
    {v : Source.Val E.layout τ} {x : u.TDenote C H} (h : Total.Relation.val E C H τ u v x) :
    valRel τ u v x := by
  cases u with
  | val p =>
    obtain ⟨rfl, r⟩ := h
    exact valRel_of_primitive r
  | _ => exact h.elim

/-! ## Context alignment -/

/-- A context map built binding by binding from liftable pairs: the Source
and model contexts have the same length and every Source local has a related
model local at its position. -/
inductive Aligned : {srcΓ : Source.RCtx} → {Γ : Ctx} → ContextMap srcΓ Γ → Prop
  | nil : Aligned .empty
  | cons {srcΓ : Source.RCtx} {Γ : Ctx} {m : ContextMap srcΓ Γ} (τ : Source.STy) (u : LTy) :
      Aligned m → Liftable τ u → Aligned (m.cons τ u)

/-- An aligned map is the positional map of the landed boundary. -/
theorem Aligned.positional {srcΓ : Source.RCtx} {Γ : Ctx} {m : ContextMap srcΓ Γ}
    (a : Aligned m) : Total.Simulation.Positional m := by
  induction a with
  | nil => exact fun i => nomatch i
  | cons τ u _ _ ih =>
    intro σ i
    cases i with
    | here => rfl
    | there j => exact congrArg (· + 1) (ih j)

/-- The positional map of primitive locals is aligned. -/
theorem aligned_primitiveMap : (ps : List PrimTy) → Aligned (Total.Simulation.primitiveMap ps)
  | [] => .nil
  | p :: ps => .cons _ _ (aligned_primitiveMap ps) (liftable_prim p)

/-- **Locals half of total initial matching**: under an aligned map every
Source locals has related model locals, at every heap typing. -/
theorem Aligned.locals {srcΓ : Source.RCtx} {Γ : Ctx} {m : ContextMap srcΓ Γ} (a : Aligned m)
    (D : Source.Layout) (C : Contract) (H : HTy) (ls : Source.Locals D srcΓ) :
    ∃ env : TEnv C H Γ, m.Related (fun τ u => valRel τ u) ls env := by
  induction a with
  | nil => exact ⟨(), fun i => nomatch i⟩
  | cons τ u _ lift ih =>
    cases ls with
    | cons v rest =>
      obtain ⟨x, hx⟩ := lift D C H v
      obtain ⟨env, henv⟩ := ih rest
      exact ⟨(x, env), ContextMap.related_cons _ _ _ _ henv _ _ _ _ hx⟩

/-! ## Globals -/

/-- The cell of the instance `self` at a path, read as the Source machine
reads it (`Source.readCell`): a transient root from transient storage, any
other path from the account's storage. -/
def cell {E : Source.Env} (st : Source.St E) (self : Roadmap.Address) (p : Source.SPath) :
    Option ((τ : Source.STy) × Source.Val E.layout τ) :=
  ((if E.transientRoot p then st.ex.transient.cells self
    else (st.ex.world.accounts self).storage).read p).map fun v => ⟨_, v⟩

/-- **The global relation.** Some Source instance has the model's own address;
its storage and transient storage hold values related to the model's state
variables; the model's own funds are its balance whenever the balance is a
word (a Source balance is an unbounded natural number). -/
def globRel {E : Source.Env} {C : Contract} {Γ : Ctx} (st : Source.St E) (σ : State C Γ) : Prop :=
  ∃ self : Roadmap.Address, (self.val : Int) = σ.tx.selfAddress.1 ∧
    Total.Relation.fields (cell st self) σ.storage ∧
    (Source.Monetary.Fits (st.ex.world.accounts self).balance →
      σ.selfBalance.1 = ((st.ex.world.accounts self).balance : Int))

/-- **The frame relation**: the Source frame is the model's transaction. It is
not part of `globRel`, whose type has no frame. -/
def frameRel {E : Source.Env} {C : Contract} {Γ : Ctx} (G : Source.Glob E) (F : Source.Fr)
    (σ : State C Γ) : Prop :=
  (F.this.val : Int) = σ.tx.selfAddress.1 ∧ (F.sender.val : Int) = σ.tx.msgSender.1 ∧
  σ.tx.msgValue.1 = (F.value.val : Int) ∧ σ.tx.timestamp.1 = (G.timestamp.val : Int) ∧
  F.static = false ∧ F.checked = true

/-- Under the frame relation the instance of `globRel` is the frame's. -/
theorem globRel.at_frame {E : Source.Env} {C : Contract} {Γ : Ctx} {st : Source.St E}
    {σ : State C Γ} (h : globRel st σ) {G : Source.Glob E} {F : Source.Fr}
    (frame : frameRel G F σ) :
    Total.Relation.fields (cell st F.this) σ.storage ∧
    (Source.Monetary.Fits (st.ex.world.accounts F.this).balance →
      σ.selfBalance.1 = ((st.ex.world.accounts F.this).balance : Int)) := by
  obtain ⟨self, address, rest⟩ := h
  have same : self = F.this := Fin.ext (Int.ofNat.inj (address.trans frame.1.symm))
  exact same ▸ rest

/-- **Compatibility with the landed boundary**: where no path is transient,
`globRel` and `frameRel` give the stage-1 global relation `Total.Relation.glob`. -/
theorem globRel.boundary {E : Source.Env} {C : Contract} {Γ : Ctx} {st : Source.St E}
    {σ : State C Γ} (h : globRel st σ) {G : Source.Glob E} {F : Source.Fr}
    (frame : frameRel G F σ) (persistent : ∀ p, E.transientRoot p = false) :
    Total.Relation.glob E C G F st σ.glob := by
  have same : cell st F.this = fun p =>
      ((st.ex.world.accounts F.this).storage.read p).map fun v => ⟨_, v⟩ := by
    funext p
    simp only [cell, persistent p, Bool.false_eq_true, if_false]
  exact ⟨same ▸ (h.at_frame frame).1, frame.2.2.1, frame.2.2.2.1, frame.2.2.2.2⟩

/-- What total matching of globals needs of a Source environment and a model
contract: every state variable is primitive and its cell in the canonical
unit's contract has the primitive's Source type (`Total.Decode.unit_cellTy`). -/
def StorageTyped (E : Source.Env) (C : Contract) : Prop :=
  ∀ x T, (x, T) ∈ C.vars → ∃ p, T = .prim p ∧
    E.cellTy ⟨⟨some Total.Decode.contractName, x⟩, []⟩ = sourceTy p

/-- **Globals half of total initial matching**: every Source state has a
related model state, with any locals over the empty heap. -/
theorem globRel_total {E : Source.Env} {C : Contract} {Γ : Ctx} (typed : StorageTyped E C)
    (st : Source.St E) (env : TEnv C [] Γ) :
    ∃ (storage : Storage C) (funds : PrimTy.uint.Denote),
      globRel st ({ storage, H := [], heap := Heap.empty, env, selfBalance := funds } : State C Γ) := by
  obtain ⟨storage, related⟩ := Total.Simulation.fields_onto (cell st Roadmap.Address.zero) C.vars
    fun x T mem => by
      obtain ⟨p, rfl, ty⟩ := typed x T mem
      exact ⟨p, rfl, Total.Simulation.read_prim _ _ p ty⟩
  by_cases fits : Source.Monetary.Fits (st.ex.world.accounts Roadmap.Address.zero).balance
  · exact ⟨storage, Total.Simulation.wordDenote ⟨_, fits⟩, Roadmap.Address.zero, rfl, related,
      fun _ => rfl⟩
  · exact ⟨storage, PrimTy.dflt .uint, Roadmap.Address.zero, rfl, related, fun h => absurd h fits⟩

end Solidity.Correctness.Lowering.Sim
