import Solidity.Lowering.V07.DoubleAssignmentFamily
import tests.h62.item2.«audit-v07-lowering».IntegerLocalFamilyWitness

/-!
Guarded regression: the pair-family audit must preserve operand-order effects
and the first-destination/second-RHS separation premise. Aliasing destinations
remains permitted. A nonempty three-slot family jointly inhabits the complete
assign_pair telescope for both pipelines; unequal reads distinguish the actual
ordered local writes. These are local-carrier results, not whole-program
termination, gas, global producer feasibility or a complete interface audit.
-/
namespace Solidity.H62.AuditV07.IntegerPairFamilyWitness
open Solidity.Lowering.V07
open IntegerLocalFamilyWitness (witnessLayout witnessContract)

inductive Slot where
  | first | middle | last

def sourceIndex (t : Source.IntTy) :
    Slot → Source.Idx [.int t, .int t, .int t] (.int t)
  | .first => .here
  | .middle => .there .here
  | .last => .there (.there .here)

def targetIndex (t : Source.IntTy) :
    Slot → Idx [.val (integerPrim t), .val (integerPrim t), .val (integerPrim t)]
      (.val (integerPrim t))
  | .first => .here
  | .middle => .there .here
  | .last => .there (.there .here)

def sourceLocals (D : Source.Layout) (t : Source.IntTy) (u x z : Int)
    (hu : t.lo ≤ u ∧ u ≤ t.hi) (hx : t.lo ≤ x ∧ x ≤ t.hi)
    (hz : t.lo ≤ z ∧ z ≤ t.hi) : Source.Locals D [.int t, .int t, .int t] :=
  .cons (.int u hu) (.cons (.int x hx) (.cons (.int z hz) .nil))

def targetLocals (C : Contract) (H : HTy) (t : Source.IntTy) (u x z : Int)
    (hu : t.lo ≤ u ∧ u ≤ t.hi) (hx : t.lo ≤ x ∧ x ≤ t.hi)
    (hz : t.lo ≤ z ∧ z ≤ t.hi) :
    TEnv C H [.val (integerPrim t), .val (integerPrim t), .val (integerPrim t)] :=
  (integerValue t u hu, (integerValue t x hx, (integerValue t z hz, ())))

theorem related_family (D : Source.Layout) (C : Contract) (H : HTy)
    (t : Source.IntTy) (u x z : Int) (hu : t.lo ≤ u ∧ u ≤ t.hi)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi) :
    IntegerLocalFamily t (sourceIndex t) (targetIndex t)
      (sourceLocals D t u x z hu hx hz) (targetLocals C H t u x z hu hx hz) := by
  constructor
  · intro k
    cases k with
    | first => exact integer_related t u hu
    | middle => exact integer_related t x hx
    | last => exact integer_related t z hz
  · intro k l
    cases k <;> cases l <;> exact Iff.rfl

def sourcePost (p : Roadmap.Pipeline) (i : Slot) (D : Source.Layout)
    (t : Source.IntTy) (u x z : Int) (hu : t.lo ≤ u ∧ u ≤ t.hi)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi) :=
  if p = .legacy then
    ((sourceLocals D t u x z hu hx hz).set (sourceIndex t .middle) (.int z hz)).set
      (sourceIndex t i) (.int z hz)
  else ((sourceLocals D t u x z hu hx hz).set (sourceIndex t i) (.int x hx)).set
      (sourceIndex t .middle) (.int z hz)

def targetPost (p : Roadmap.Pipeline) (i : Slot) (C : Contract) (H : HTy)
    (t : Source.IntTy) (u x z : Int) (hu : t.lo ≤ u ∧ u ≤ t.hi)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi) :=
  if p = .legacy then
    TEnv.set (targetIndex t i) (integerValue t z hz)
      (TEnv.set (targetIndex t .middle) (integerValue t z hz)
        (targetLocals C H t u x z hu hx hz))
  else TEnv.set (targetIndex t .middle) (integerValue t z hz)
    (TEnv.set (targetIndex t i) (integerValue t x hx) (targetLocals C H t u x z hu hx hz))

/-- The imported theorem derives the postfamily from the same initial inputs. -/
theorem related_after_pair (D : Source.Layout) (C : Contract) (H : HTy)
    (t : Source.IntTy) (u x z : Int) (hu : t.lo ≤ u ∧ u ≤ t.hi)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi)
    (p : Roadmap.Pipeline) (i : Slot)
    (different : (sourceIndex t i).toNat ≠ (sourceIndex t .last).toNat) :
    IntegerLocalFamily t (sourceIndex t) (targetIndex t)
      (sourcePost p i D t u x z hu hx hz) (targetPost p i C H t u x z hu hx hz) :=
  (related_family D C H t u x z hu hx hz).assign_pair p i .middle .last x z hx hz
    rfl rfl different

/-- The two destinations can coincide; only separation from the last RHS is needed. -/
theorem aliased_destinations_permitted (D : Source.Layout) (C : Contract) (H : HTy)
    (t : Source.IntTy) (u x z : Int) (hu : t.lo ≤ u ∧ u ≤ t.hi)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi) (p : Roadmap.Pipeline) :
    IntegerLocalFamily t (sourceIndex t) (targetIndex t)
      (sourcePost p .middle D t u x z hu hx hz)
      (targetPost p .middle C H t u x z hu hx hz) :=
  related_after_pair D C H t u x z hu hx hz p .middle (by change (1 : Nat) ≠ 2; decide)

/-- The head gets z in legacy order and x in viaIR, in both existing carriers. -/
theorem pipeline_head_reads (D : Source.Layout) (C : Contract) (H : HTy)
    (t : Source.IntTy) (u x z : Int) (hu : t.lo ≤ u ∧ u ≤ t.hi)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi) :
    (sourcePost .legacy .first D t u x z hu hx hz).get (sourceIndex t .first) = .int z hz ∧
    (sourcePost .viaIR .first D t u x z hu hx hz).get (sourceIndex t .first) = .int x hx ∧
    TEnv.get (targetIndex t .first) (targetPost .legacy .first C H t u x z hu hx hz) =
      integerValue t z hz ∧
    TEnv.get (targetIndex t .first) (targetPost .viaIR .first C H t u x z hu hx hz) =
      integerValue t x hx := ⟨rfl, rfl, rfl, rfl⟩

/-- Unequal operand reads make the source local effects distinguishable. -/
theorem source_orders_differ (D : Source.Layout) (t : Source.IntTy) (u x z : Int)
    (hu : t.lo ≤ u ∧ u ≤ t.hi) (hx : t.lo ≤ x ∧ x ≤ t.hi)
    (hz : t.lo ≤ z ∧ z ≤ t.hi) (different : x ≠ z) :
    sourcePost .legacy .first D t u x z hu hx hz ≠
      sourcePost .viaIR .first D t u x z hu hx hz := by
  intro same
  have read := congrArg (fun locals => (locals.get (sourceIndex t .first)).key) same
  change some z = some x at read
  exact different (Option.some.inj read).symm

/-- The native carrier exposes the same order distinction at every legal width/sign. -/
theorem target_orders_differ (C : Contract) (H : HTy) (t : Source.IntTy) (u x z : Int)
    (hu : t.lo ≤ u ∧ u ≤ t.hi) (hx : t.lo ≤ x ∧ x ≤ t.hi)
    (hz : t.lo ≤ z ∧ z ≤ t.hi) (different : x ≠ z) :
    targetPost .legacy .first C H t u x z hu hx hz ≠
      targetPost .viaIR .first C H t u x z hu hx hz := by
  intro same
  have read := congrArg (TEnv.get (targetIndex t .first)) same
  change integerValue t z hz = integerValue t x hx at read
  exact different (integer_injective t z x hz hx read).symm

/-- Fail if the imported pair telescope gains, loses or changes a premise. -/
private def checkedPairSignature :
    ∀ {D : Source.Layout} {srcΓ : Source.RCtx} {C : Contract} {H : HTy}
      {Γ : Ctx} {ι : Type} {t : Source.IntTy}
      {si : ι → Source.Idx srcΓ (.int t)} {ti : ι → Idx Γ (.val (integerPrim t))}
      {source : Source.Locals D srcΓ} {target : TEnv C H Γ},
      IntegerLocalFamily t si ti source target →
      ∀ (pipeline : Roadmap.Pipeline) (i a b : ι) (x z : Int)
        (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi),
        source.get (si a) = .int x hx → source.get (si b) = .int z hz →
        (si i).toNat ≠ (si b).toNat →
        IntegerLocalFamily t si ti
          (if pipeline = .legacy then (source.set (si a) (.int z hz)).set (si i) (.int z hz)
            else (source.set (si i) (.int x hx)).set (si a) (.int z hz))
          (if pipeline = .legacy then
            TEnv.set (ti i) (integerValue t z hz) (TEnv.set (ti a) (integerValue t z hz) target)
            else TEnv.set (ti a) (integerValue t z hz) (TEnv.set (ti i) (integerValue t x hx) target)) :=
  @IntegerLocalFamily.assign_pair

/-- All 23 entries coexist with the actual postfamily, for either pipeline. -/
theorem complete_pair_hypotheses (pipeline : Roadmap.Pipeline) :
    ∃ (D : Source.Layout) (srcΓ : Source.RCtx) (C : Contract) (H : HTy)
      (Γ : Ctx) (ι : Type) (t : Source.IntTy)
      (si : ι → Source.Idx srcΓ (.int t))
      (ti : ι → Idx Γ (.val (integerPrim t)))
      (source : Source.Locals D srcΓ) (target : TEnv C H Γ)
      (_family : IntegerLocalFamily t si ti source target)
      (i a b : ι) (x z : Int) (hx : t.lo ≤ x ∧ x ≤ t.hi) (hz : t.lo ≤ z ∧ z ≤ t.hi)
      (_readA : source.get (si a) = .int x hx) (_readB : source.get (si b) = .int z hz)
      (_different : (si i).toNat ≠ (si b).toNat),
      IntegerLocalFamily t si ti
        (if pipeline = .legacy then (source.set (si a) (.int z hz)).set (si i) (.int z hz)
          else (source.set (si i) (.int x hx)).set (si a) (.int z hz))
        (if pipeline = .legacy then
          TEnv.set (ti i) (integerValue t z hz) (TEnv.set (ti a) (integerValue t z hz) target)
          else TEnv.set (ti a) (integerValue t z hz) (TEnv.set (ti i) (integerValue t x hx) target)) := by
  let hu : Source.IntTy.u8.lo ≤ 5 ∧ 5 ≤ Source.IntTy.u8.hi := by decide
  let hx : Source.IntTy.u8.lo ≤ 7 ∧ 7 ≤ Source.IntTy.u8.hi := by decide
  let hz : Source.IntTy.u8.lo ≤ 9 ∧ 9 ≤ Source.IntTy.u8.hi := by decide
  exact ⟨witnessLayout, _, witnessContract, [], _, Slot, Source.IntTy.u8,
    sourceIndex _, targetIndex _, sourceLocals witnessLayout _ 5 7 9 hu hx hz,
    targetLocals witnessContract [] _ 5 7 9 hu hx hz,
    related_family witnessLayout witnessContract [] _ 5 7 9 hu hx hz,
    .first, .middle, .last, 7, 9, hx, hz, rfl, rfl, by decide,
    related_after_pair witnessLayout witnessContract [] _ 5 7 9 hu hx hz pipeline .first
      (by change (0 : Nat) ≠ 2; decide)⟩

#check @IntegerLocalFamily.assign_pair
#print axioms related_family
#print axioms related_after_pair
#print axioms aliased_destinations_permitted
#print axioms pipeline_head_reads
#print axioms source_orders_differ
#print axioms target_orders_differ
#print axioms complete_pair_hypotheses
end Solidity.H62.AuditV07.IntegerPairFamilyWitness
