import Solidity.Lowering.V07.WrappedMultiplicationPair
import Solidity.Lowering.V07.WrappedPairControls
import Solidity.Lowering.V07.UnsignedNarrowingControls
namespace Solidity.Lowering.V07.WrappedMultiplicationControls
open Source.SemanticsExamples
open UnsignedNarrowingControls (SrcCtx TgtCtx Keys si ti)
abbrev U8 := UnsignedNarrowing.ty 8 (by decide)
def source : Source.EMState MixedAssignmentControls.E SrcCtx :=
  (((MixedAssignmentControls.source.1.set .here (.int 200 (by decide))).set
    (.there .here) (.int 250 (by decide))),MixedAssignmentControls.source.2)
def target : State MixedAssignmentControls.C TgtCtx :=
  (MixedAssignmentControls.target.setLocal .here (integerValue .u8 200 (by decide))).setLocal
    (.there .here) (integerValue .u8 250 (by decide))
theorem initial : IntegerLocalFamily U8 si ti source.1 target.env := by
  constructor
  · intro k; rcases k with ⟨a,b⟩; cases a <;> cases b <;> rfl
  · intro k l; rcases k with ⟨a,b⟩; rcases l with ⟨c,d⟩
    cases a <;> cases b <;> cases c <;> cases d <;> decide

open WrappedMultiplicationPair (operand product)
open WrappedAssignmentPair (sourcePost targetPost)
def value (k : Keys) : Int := if k.1 then 250 else 200
def range (k : Keys) : U8.lo ≤ value k ∧ value k ≤ U8.hi := by
  unfold value
  split <;> decide

def witness (p : Roadmap.Pipeline) (fuel : Nat) (i a b : Keys) :=
  WrappedMultiplicationPair.transport (MixedAssignmentControls.globals p) F0 fuel source target 8
    (by decide) si ti initial i a b (value a) (value b) (range a) (range b)
    (by rcases a with ⟨a,b⟩; cases a <;> rfl)
    (by rcases b with ⟨a,b⟩; cases a <;> rfl)
def sf (p : Roadmap.Pipeline) (i a b : Keys) :=
  sourcePost p source 8 (by decide) (si i) (si a) (si b) (value a) (value b) (range a) (range b)
def tf (p : Roadmap.Pipeline) (i a b : Keys) :=
  targetPost p target 8 (by decide) (ti i) (ti a) (ti b) (value a) (value b) (range a) (range b)
-- Arbitrary selected keys include repeated aliases and distinct caller identities.
example (p : Roadmap.Pipeline) (fuel : Nat) (i a b : Keys) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} (fuel+4)
      (.binary .mul (.assign (.local (si i)) (.local (si a)))
        (.assign (.local (si a)) (.local (si b))))).run source =
      (.ok (.val (Source.intWrap U8
        (product p (decide ((si i).toNat = (si b).toNat)) (value a) (value b)))),sf p i a b) :=
  (witness p fuel i a b).1
example (p : Roadmap.Pipeline) (i a b : Keys) :
    IntegerLocalFamily U8 si ti (sf p i a b).1 (tf p i a b).env :=
  (witness p 0 i a b).2.2.2
example (p : Roadmap.Pipeline) (i a b : Keys) : (sf p i a b).2 = source.2 :=
  WrappedAssignmentPair.source_state_frame p source 8 (by decide) _ _ _ _ _ _ _
example (p : Roadmap.Pipeline) (i a b : Keys) : (tf p i a b).glob = target.glob :=
  WrappedAssignmentPair.target_glob_frame p target 8 (by decide) _ _ _ _ _ _ _

-- A genuinely different fresh caller binder, with the actual multiplication effect prefix transported.
example (p : Roadmap.Pipeline) :
    ((operand p 8 .here .here (.there .here)).wk
      (Thin.drop (t := .val .bool) .refl)).run (target.lift (Thin.drop .refl) (true,target.env)) =
      liftedT₂ (Thin.drop (t := .val .bool) .refl) (true,target.env)
        (.ok ((⟨tf p (false,false) (false,false) (true,false),
          by cases p <;> exact List.prefix_refl _⟩ : Out MixedAssignmentControls.C target.H TgtCtx),
          SVal.prim (integerValue .u8 (if p = .legacy then 36 else 80) (by cases p <;> decide)))) := by
  have h := WrappedMultiplicationPair.extension p target 8 (by decide) .here .here (.there .here)
    200 250 (by decide) (by decide) rfl rfl (Thin.drop (t := .val .bool) .refl) (true,target.env)
  cases p <;> exact h

example (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) {F0 with checked := false} (fuel+4)
      (.binary .mul (.assign (.local .here) (.local .here))
        (.assign (.local .here) (.local (.there .here))))).run
          (UnsignedNarrowingControls.pureSource bits valid) =
      (.ok (.val (Source.intWrap (UnsignedNarrowing.ty bits valid) (product p false 0 1))),
        sourcePost p (UnsignedNarrowingControls.pureSource bits valid) bits valid
          .here .here (.there .here) 0 1 (integer_zero_range _) (UnsignedNarrowingControls.one_range bits valid)) ∧
    (operand p bits .here .here (.there .here)).run (UnsignedNarrowingControls.pureTarget bits valid) =
      .ok (⟨targetPost p (UnsignedNarrowingControls.pureTarget bits valid) bits valid
        .here .here (.there .here) 0 1 (integer_zero_range _) (UnsignedNarrowingControls.one_range bits valid),
        by cases p <;> exact List.prefix_refl _⟩,
        .prim (integerValue (UnsignedNarrowing.ty bits valid)
          ((UnsignedNarrowing.ty bits valid).wrap (product p false 0 1))
          ((UnsignedNarrowing.ty bits valid).wrap_mem _))) :=
  ⟨WrappedMultiplicationPair.source_run (G0 p) F0 fuel _ bits valid .here .here (.there .here) 0 1
      (integer_zero_range _) (UnsignedNarrowingControls.one_range bits valid) rfl rfl,
   WrappedMultiplicationPair.operand_run p _ bits valid .here .here (.there .here) 0 1
      (integer_zero_range _) (UnsignedNarrowingControls.one_range bits valid) rfl rfl⟩

-- Existing mixed state with THREE distinct scalar identities, including initial destination17.
def tripleWitness (p : Roadmap.Pipeline) (fuel : Nat) :=
  WrappedMultiplicationPair.transport (MixedAssignmentControls.globals p) F0 fuel
    WrappedPairControls.tripleSource WrappedPairControls.tripleTarget 8 (by decide)
    WrappedPairControls.tsi WrappedPairControls.tti WrappedPairControls.triple_initial
    none (some (false,false)) (some (true,false)) 0 1 (by decide) (by decide) rfl rfl
example (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} (fuel+4)
      (.binary .mul (.assign (.local .here) (.local (.there .here)))
        (.assign (.local (.there .here)) (.local (.there (.there .here)))))).run
          WrappedPairControls.tripleSource =
      (.ok (.val (.int (if p = .legacy then 1 else 0) (by cases p <;> decide))),
        WrappedPairControls.tripleSourceFinal p) := by
  have h := tripleWitness p fuel
  cases p <;> exact h.1

-- Full ordered observations (result plus both final caller locals) and real captures.
def sourceObs (p : Roadmap.Pipeline) (i a b : Keys) : List Int :=
  match (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} 4
      (.binary .mul (.assign (.local (si i)) (.local (si a)))
        (.assign (.local (si a)) (.local (si b))))).run source with
  | (.ok (.val (.int z _)),s) => [z,(s.1.get .here).key.getD (-1),(s.1.get (.there .here)).key.getD (-1)]
  | _ => []
def targetObs (p : Roadmap.Pipeline) (i a b : Keys) : List Int :=
  match (operand p 8 (ti i) (ti a) (ti b)).run target with
  | .ok (s,.prim z) => [(PrimTy.num? z).getD (-1),
      (PrimTy.num? (TEnv.get .here s.st.env)).getD (-1),
      (PrimTy.num? (TEnv.get (.there .here) s.st.env)).getD (-1)]
  | _ => []
def captures (p : Roadmap.Pipeline) (i a b : Keys) : List Int :=
  match (assignAssignPrefix p (ti i) (ti a) (ti b)).run target with
  | .ok s => [(PrimTy.num? (TEnv.get .here s.st.env)).getD (-1),
      (PrimTy.num? (TEnv.get (.there .here) s.st.env)).getD (-1)]
  | _ => []
-- This Boolean observes one dropped caller slot; the exact operand_run frames the whole caller.
def dropCorrect (p : Roadmap.Pipeline) (i a b : Keys) : Bool :=
  match (assignAssignPrefix p (ti i) (ti a) (ti b)).run target with
  | .ok s => (TEnv.get .here (s.st.drop (.push (.push .refl))).env).val ==
      (TEnv.get .here (tf p i a b).env).val
  | _ => false
/-- info: [[36, 250, 250],
 [80, 250, 250],
 [64, 200, 200],
 [36, 250, 250],
 [64, 200, 200],
 [64, 200, 200],
 [64, 200, 250],
 [64, 200, 250]] -/
#guard_msgs in
#eval IO.println (reprStr [
  sourceObs .legacy (false,false) (false,true) (true,false),
  sourceObs .viaIR (false,false) (false,true) (true,false),
  sourceObs .legacy (false,false) (true,false) (false,true),
  sourceObs .viaIR (false,false) (true,false) (false,true),
  sourceObs .legacy (true,false) (false,false) (false,true),
  sourceObs .viaIR (true,false) (false,false) (false,true),
  sourceObs .legacy (false,false) (false,true) (false,false),
  sourceObs .viaIR (false,false) (false,true) (false,false)])
/-- info: [[250, 250], [250, 200], [200, 200], [250, 250]] -/
#guard_msgs in
#eval IO.println (reprStr [captures .legacy (false,false) (false,true) (true,false),
  captures .viaIR (false,false) (false,true) (true,false),
  captures .legacy (false,false) (true,false) (false,true),
  captures .viaIR (false,false) (true,false) (false,true)])
-- Every physical selection, using distinct keys for repeated aliases.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p =>
  [false,true].all fun i => [false,true].all fun a => [false,true].all fun b =>
    sourceObs p (i,false) (a,true) (b,false) == targetObs p (i,false) (a,true) (b,false) &&
    dropCorrect p (i,false) (a,true) (b,false)))
-- Actual wrong arithmetic after both writes (uncaptured) loses the original left in IR.
def wrongDeferred : Option Int :=
  match (UnsignedMultiplication.mulValue 8 (.simple (.local .here)) (.simple (.local .here))).evalT
    (tf .viaIR (false,false) (false,true) (true,false)) with
  | .ok z => PrimTy.num? z | _ => none
/-- info: [some 36, some 80, some 80] -/
#guard_msgs in
#eval IO.println (reprStr [wrongDeferred,
  match (UnsignedMultiplication.mulValue 8 (.simple (.local .here))
      (.simple (.local (.there .here)))).evalT target with
    | .ok z => PrimTy.num? z | _ => none,
  -- Stale read when i=b would yield250*200 modulo256=80, instead of the reached250*250 modulo256=36.
  match (UnsignedMultiplication.mulValue 8 (.simple (.local (.there .here)))
      (.simple (.local .here))).evalT target with
    | .ok z => PrimTy.num? z | _ => none])

-- Live locations are framed by the exact callers, independent of the numeric products.
example (p : Roadmap.Pipeline) :
    (sf p (false,false) (false,true) (true,false)).1.get (.there (.there .here)) = .memRef rfl 0 ∧
    (sf p (false,false) (false,true) (true,false)).1.get (.there (.there (.there .here))) =
      .storRef rfl MixedAssignmentControls.path ∧
    (∃ r : HRef (tf p (false,false) (false,true) (true,false)).H bytesR,
      TEnv.get (.there (.there .here)) (tf p (false,false) (false,true) (true,false)).env = some r ∧
      (tf p (false,false) (false,true) (true,false)).heap.len r .dyn = 2) ∧
    TEnv.get (.there (.there (.there .here)))
      (tf p (false,false) (false,true) (true,false)).env = some MixedAssignmentControls.storageRef := by
  cases p <;> exact ⟨rfl,rfl,MixedAssignmentControls.live_memory,rfl⟩

-- Three distinct destinations/donor roles with overflow, on the same live mixed caller.
def bigSource : Source.EMState MixedAssignmentControls.E (.int .u8 :: SrcCtx) :=
  (.cons (.int 17 (by decide)) source.1,source.2)
def bigTarget : State MixedAssignmentControls.C (.val .uint :: TgtCtx) :=
  target.push (t := .val .uint) (integerValue .u8 17 (by decide))
def bigExpr : Source.RExpr MixedAssignmentControls.E (.int .u8 :: SrcCtx) (.int .u8) :=
  .binary .mul (.assign (.local .here) (.local (.there .here)))
    (.assign (.local (.there .here)) (.local (.there (.there .here))))
example (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} (fuel+4)
      bigExpr).run bigSource =
      (.ok (.val (Source.intWrap U8 (product p false 200 250))),
        sourcePost p bigSource 8 (by decide) .here (.there .here) (.there (.there .here))
          200 250 (by decide) (by decide)) := by
  have h := WrappedMultiplicationPair.source_run (MixedAssignmentControls.globals p) F0 fuel bigSource
    8 (by decide) .here (.there .here) (.there (.there .here)) 200 250 (by decide) (by decide) rfl rfl
  cases p <;> exact h
example (p : Roadmap.Pipeline) :
    (operand p 8 .here (.there .here) (.there (.there .here))).run bigTarget =
      .ok (⟨targetPost p bigTarget 8 (by decide) .here (.there .here) (.there (.there .here))
        200 250 (by decide) (by decide),by cases p <;> exact List.prefix_refl _⟩,
        .prim (integerValue U8 (U8.wrap (product p false 200 250)) (U8.wrap_mem _))) :=
  WrappedMultiplicationPair.operand_run p bigTarget 8 (by decide) .here (.there .here)
    (.there (.there .here)) 200 250 (by decide) (by decide) rfl rfl

def bigSourceObs (p : Roadmap.Pipeline) : List Int :=
  match (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} 4 bigExpr).run bigSource with
  | (.ok (.val (.int z _)),s) => [z,(s.1.get .here).key.getD (-1),
      (s.1.get (.there .here)).key.getD (-1),(s.1.get (.there (.there .here))).key.getD (-1)]
  | _ => []
def bigTargetObs (p : Roadmap.Pipeline) : List Int :=
  match (operand p 8 .here (.there .here) (.there (.there .here))).run bigTarget with
  | .ok (s,.prim z) => [(PrimTy.num? z).getD (-1),
      (PrimTy.num? (TEnv.get .here s.st.env)).getD (-1),
      (PrimTy.num? (TEnv.get (.there .here) s.st.env)).getD (-1),
      (PrimTy.num? (TEnv.get (.there (.there .here)) s.st.env)).getD (-1)]
  | _ => []
/-- info: [[36, 250, 250, 250], [80, 200, 250, 250], [36, 250, 250, 250], [80, 200, 250, 250]] -/
#guard_msgs in
#eval IO.println (reprStr [bigSourceObs .legacy,bigSourceObs .viaIR,
  bigTargetObs .legacy,bigTargetObs .viaIR])

-- Actual zero versus max-squared in the two-effect schedule; all32 widths including256.
def edgeSource (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    Source.EMState E0 [.int (UnsignedNarrowing.ty bits valid),.int (UnsignedNarrowing.ty bits valid)] :=
  ((UnsignedNarrowingControls.pureSource bits valid).1.set (.there .here)
    (.int (UnsignedNarrowing.ty bits valid).hi
      ⟨Int.le_trans (integer_zero_range _).1 (integer_zero_range _).2,Int.le_refl _⟩),s0)
def edgeTarget (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :=
  (UnsignedNarrowingControls.pureTarget bits valid).setLocal (.there .here)
    (integerValue (UnsignedNarrowing.ty bits valid) (UnsignedNarrowing.ty bits valid).hi
      ⟨Int.le_trans (integer_zero_range _).1 (integer_zero_range _).2,Int.le_refl _⟩)
def edgeSourceObs (p : Roadmap.Pipeline) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) : Option Int :=
  match (Source.evalE (G0 p) {F0 with checked := false} 4
      (.binary .mul (.assign (.local .here) (.local .here))
        (.assign (.local .here) (.local (.there .here))))).run (edgeSource bits valid) with
  | (.ok (.val v),_) => v.key | _ => none
def edgeTargetObs (p : Roadmap.Pipeline) (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) : Option Int :=
  match (operand p bits .here .here (.there .here)).run (edgeTarget bits valid) with
  | .ok (_, .prim v) => PrimTy.num? v | _ => none
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ((List.finRange 32).all fun i =>
  edgeSourceObs .viaIR (8*(i.val+1)) (by omega) == some 0 &&
  edgeTargetObs .viaIR (8*(i.val+1)) (by omega) == some 0 &&
  edgeSourceObs .legacy (8*(i.val+1)) (by omega) == some 1 &&
  edgeTargetObs .legacy (8*(i.val+1)) (by omega) == some 1))
def source_client (p : Roadmap.Pipeline) (fuel : Nat) :=
  WrappedMultiplicationPair.source_run (MixedAssignmentControls.globals p) F0 fuel source
    8 (by decide) .here .here (.there .here) 200 250 (by decide) (by decide) rfl rfl
def operand_client (p : Roadmap.Pipeline) :=
  WrappedMultiplicationPair.operand_run p target 8 (by decide) .here .here (.there .here)
    200 250 (by decide) (by decide) rfl rfl
def transport_client (p : Roadmap.Pipeline) (fuel : Nat) :=
  witness p fuel (false,false) (false,true) (true,false)
def extension_client (p : Roadmap.Pipeline) :=
  WrappedMultiplicationPair.extension p target 8 (by decide) .here .here (.there .here)
    200 250 (by decide) (by decide) rfl rfl (Thin.drop (t := .val .bool) .refl) (true,target.env)

end Solidity.Lowering.V07.WrappedMultiplicationControls
