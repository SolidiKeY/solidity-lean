import Solidity.Lowering.V07.UnsignedMultiplication
import Solidity.Lowering.V07.UnsignedNarrowingControls
namespace Solidity.Lowering.V07.UnsignedMultiplicationChecks
open Source.SemanticsExamples
open UnsignedNarrowingControls (SrcCtx TgtCtx Keys si ti)
abbrev U8 := UnsignedNarrowing.ty 8 (by decide)
def source : Source.EMState MixedAssignmentControls.E SrcCtx :=
  (((MixedAssignmentControls.source.1.set .here (.int 200 (by decide))).set
    (.there .here) (.int 250 (by decide))),MixedAssignmentControls.source.2)
def target : State MixedAssignmentControls.C TgtCtx :=
  (MixedAssignmentControls.target.setLocal .here (integerValue .u8 200 (by decide))).setLocal
    (.there .here) (integerValue .u8 250 (by decide))
def sourcePost : Source.EMState MixedAssignmentControls.E SrcCtx :=
  (source.1.set (.there .here) (.int 200 (by decide)),source.2)
def targetPost : State MixedAssignmentControls.C TgtCtx :=
  target.setLocal (.there .here) (integerValue .u8 200 (by decide))
def result (p : Roadmap.Pipeline) : Int := if p = .legacy then 80 else 64
theorem initial : IntegerLocalFamily U8 si ti source.1 target.env := by
  constructor
  · intro k; rcases k with ⟨a,b⟩; cases a <;> cases b <;> rfl
  · intro k l; rcases k with ⟨a,b⟩; rcases l with ⟨c,d⟩
    cases a <;> cases b <;> cases c <;> cases d <;> decide

def witness (p : Roadmap.Pipeline) (fuel : Nat) :=
  UnsignedMultiplication.assignment_transport (MixedAssignmentControls.globals p) F0 fuel
    source target 8 (by decide) si ti initial (true,false) (false,false) 200 250
    (by decide) (by decide) rfl rfl

-- Full actual expression, target capture/drop, and post-family from initial alignment.
example (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} (fuel+4)
      (.binary .mul (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run source =
      (.ok (.val (.int (result p) (by cases p <;> decide))),sourcePost) ∧
    (UnsignedMultiplication.assignReadOperand p 8 (.there .here) .here).run target =
      .ok (⟨targetPost,List.prefix_refl _⟩,.prim (integerValue .u8 (result p) (by cases p <;> decide))) ∧
    IntegerLocalFamily U8 si ti sourcePost.1 targetPost.env := by
  have h := witness p fuel
  cases p <;> exact ⟨h.1,h.2.1,h.2.2.2⟩

-- Runtime positions retain semantic arguments while the pipeline changes the captured right value.
def reached (p : Roadmap.Pipeline) : State MixedAssignmentControls.C (.val .uint :: .val .uint :: TgtCtx) :=
  (targetPost.push (integerValue .u8 (if p = .legacy then 250 else 200)
    (by cases p <;> decide))).push (integerValue .u8 200 (by decide))
example (p : Roadmap.Pipeline) : (assignReadPrefix p (.there .here) .here).run target =
    .ok (⟨reached p,List.prefix_refl _⟩) := by
  have h := assign_read_prefix_run p target (.there .here) .here
    (integerValue .u8 200 (by decide)) (integerValue .u8 250 (by decide)) rfl rfl
  cases p <;> exact h
example (p : Roadmap.Pipeline) : (reached p).drop (.push (.push .refl)) = targetPost := rfl
example : sourcePost.2 = source.2 ∧ targetPost.glob = target.glob ∧
    sourcePost.1.get (.there (.there .here)) = .memRef rfl 0 ∧
    sourcePost.1.get (.there (.there (.there .here))) = .storRef rfl MixedAssignmentControls.path ∧
    (∃ r : HRef targetPost.H bytesR, TEnv.get (.there (.there .here)) targetPost.env = some r ∧
      targetPost.heap.len r .dyn = 2) ∧
    TEnv.get (.there (.there (.there .here))) targetPost.env = some MixedAssignmentControls.storageRef :=
  ⟨rfl,rfl,rfl,rfl,MixedAssignmentControls.live_memory,rfl⟩
example (p : Roadmap.Pipeline) :
    ((UnsignedMultiplication.assignReadOperand p 8 (.there .here) .here).wk
      (Thin.drop (t := .val .bool) .refl)).run (target.lift (Thin.drop .refl) (true,target.env)) =
      liftedT₂ (Thin.drop (t := .val .bool) .refl) (true,target.env)
        (.ok ((⟨targetPost,List.prefix_refl _⟩ : Out MixedAssignmentControls.C target.H TgtCtx),
          SVal.prim (integerValue .u8 (result p) (by cases p <;> decide)))) := by
  have h := UnsignedMultiplication.assignment_extension p target 8 (by decide) (.there .here) .here
    200 250 (by decide) (by decide) rfl rfl (Thin.drop (t := .val .bool) .refl) (true,target.env)
  cases p <;> exact h

-- Every approved width, including the full-word branch: max squared wraps to one.
def boundaryTarget (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    State (default : Contract) [.val .uint,.val .uint] :=
  ((State.init (default : Contract)).push (t := .val .uint) (integerValue (UnsignedNarrowing.ty bits valid) (UnsignedNarrowing.ty bits valid).hi
    ⟨Int.le_trans (integer_zero_range _).1 (integer_zero_range _).2,Int.le_refl _⟩)).push
    (integerValue (UnsignedNarrowing.ty bits valid) (UnsignedNarrowing.ty bits valid).hi
      ⟨Int.le_trans (integer_zero_range _).1 (integer_zero_range _).2,Int.le_refl _⟩)
def boundarySource (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    Source.EMState E0 [.int (UnsignedNarrowing.ty bits valid),.int (UnsignedNarrowing.ty bits valid)] :=
  (.cons (.int (UnsignedNarrowing.ty bits valid).hi
      ⟨Int.le_trans (integer_zero_range _).1 (integer_zero_range _).2,Int.le_refl _⟩)
    (.cons (.int (UnsignedNarrowing.ty bits valid).hi ⟨Int.le_trans (integer_zero_range _).1 (integer_zero_range _).2,Int.le_refl _⟩) .nil),s0)
example (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) {F0 with checked := false} (fuel+3)
      (.binary .mul (.local .here) (.local (.there .here)))).run (boundarySource bits valid) =
      (.ok (.val (Source.intWrap (UnsignedNarrowing.ty bits valid)
        ((UnsignedNarrowing.ty bits valid).hi*(UnsignedNarrowing.ty bits valid).hi))),boundarySource bits valid) ∧
    (UnsignedMultiplication.mulValue bits (.simple (.local .here)) (.simple (.local (.there .here)))).evalT
      (boundaryTarget bits valid) =
      .ok (integerValue (UnsignedNarrowing.ty bits valid)
        ((UnsignedNarrowing.ty bits valid).wrap ((UnsignedNarrowing.ty bits valid).hi*(UnsignedNarrowing.ty bits valid).hi))
        ((UnsignedNarrowing.ty bits valid).wrap_mem _)) :=
  ⟨UnsignedMultiplication.source_locals_run (G0 p) F0 fuel _ bits valid .here (.there .here) _ _
    ⟨Int.le_trans (integer_zero_range _).1 (integer_zero_range _).2,Int.le_refl _⟩
    ⟨Int.le_trans (integer_zero_range _).1 (integer_zero_range _).2,Int.le_refl _⟩ rfl rfl,
   UnsignedMultiplication.mul_value_run _ bits valid _ _ _ _
    ⟨Int.le_trans (integer_zero_range _).1 (integer_zero_range _).2,Int.le_refl _⟩
    ⟨Int.le_trans (integer_zero_range _).1 (integer_zero_range _).2,Int.le_refl _⟩ rfl rfl⟩

-- Actual ordered observations, including intermediate captures, not just a final product.
def sourceObs (p : Roadmap.Pipeline) : List Int :=
  match (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} 4
      (.binary .mul (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run source with
  | (.ok (.val (.int z _)),s) => [z,(s.1.get .here).key.getD (-1),(s.1.get (.there .here)).key.getD (-1)]
  | _ => []
def targetObs (p : Roadmap.Pipeline) : List Int :=
  match (UnsignedMultiplication.assignReadOperand p 8 (.there .here) .here).run target with
  | .ok (s,.prim z) => [(PrimTy.num? z).getD (-1),
      (PrimTy.num? (TEnv.get .here s.st.env)).getD (-1),
      (PrimTy.num? (TEnv.get (.there .here) s.st.env)).getD (-1)]
  | _ => []
def captures (p : Roadmap.Pipeline) : List Int :=
  match (assignReadPrefix p (.there .here) .here).run target with
  | .ok s => [(PrimTy.num? (TEnv.get .here s.st.env)).getD (-1),
      (PrimTy.num? (TEnv.get (.there .here) s.st.env)).getD (-1)]
  | _ => []
def boundaryObs (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) : Option Int :=
  match (UnsignedMultiplication.mulValue bits (.simple (.local .here)) (.simple (.local (.there .here)))).evalT
      (boundaryTarget bits valid) with
  | .ok z => PrimTy.num? z
  | _ => none
/-- info: [[80, 200, 200], [64, 200, 200], [80, 200, 200], [64, 200, 200], [200, 250], [200, 200]] -/
#guard_msgs in
#eval IO.println (reprStr [sourceObs .legacy,sourceObs .viaIR,targetObs .legacy,targetObs .viaIR,
  captures .legacy,captures .viaIR])
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ((List.finRange 32).all fun i =>
  boundaryObs (8*(i.val+1)) (by omega) == some 1))
-- Unnarrowed uint256 50000, stale initial-state right 250 in viaIR, and uncaptured reached right
-- 200 in legacy are all distinguishable. Checked uint256 mul alone fails to narrow too.
/-- info: [true, true, true, true, true, true] -/
#guard_msgs in
#eval IO.println (reprStr [result .legacy != 50000,result .viaIR != 50000,
  result .viaIR != result .legacy,result .legacy != 64,
  Source.IntTy.u8.wrap (255*255) == 1,Source.IntTy.u256.wrap (255*255) != 1])
-- Same local may be both assignment destination and RHS; no hidden separation.
example (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} (fuel+4)
      (.binary .mul (.assign (.local .here) (.local .here)) (.local .here))).run source =
      (.ok (.val (.int 64 (by decide))),source) ∧
    (UnsignedMultiplication.assignReadOperand p 8 .here .here).run target =
      .ok (⟨target,List.prefix_refl _⟩,.prim (integerValue .u8 64 (by decide))) := by
  have h := UnsignedMultiplication.assignment_transport (MixedAssignmentControls.globals p) F0 fuel
    source target 8 (by decide) si ti initial (false,false) (false,false) 200 200
    (by decide) (by decide) rfl rfl
  cases p <;> exact ⟨h.1,h.2.1⟩
example (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) {F0 with checked := false} (fuel+3)
      (.binary .mul (.local .here) (.local (.there .here)))).run ReadControls.source =
      (.ok (.val (.int 21 (by decide))),ReadControls.source) ∧
    (UnsignedMultiplication.mulValue 8 (.simple (.local .here)) (.simple (.local (.there .here)))).evalT
      ReadControls.target = .ok (integerValue .u8 21 (by decide)) :=
  ⟨UnsignedMultiplication.source_locals_run (G0 p) F0 fuel _ 8 (by decide)
    .here (.there .here) 7 3 (by decide) (by decide) rfl rfl,
   UnsignedMultiplication.mul_value_run _ 8 (by decide) _ _ 7 3 (by decide) (by decide) rfl rfl⟩

def valObs {Γ : Ctx} (v : Val MixedAssignmentControls.C Γ .uint)
    (s : State MixedAssignmentControls.C Γ) : Option Int :=
  match v.evalT s with | .ok z => PrimTy.num? z | _ => none
-- Actually execute wrong lowerings, rather than comparing expected-result literals.
/-- info: [some 50000, some 64, some 80, some 64, some 21] -/
#guard_msgs in
#eval IO.println (reprStr [
  valObs (.binop .mulW rfl rfl (.simple (.local .here))
    (.simple (.local (.there .here)))) target,
  valObs (UnsignedMultiplication.mulValue 8 (.simple (.local (.there .here)))
    (.simple (.local (.there .here)))) targetPost,
  -- Stale initial read in viaIR wrongly obtains the legacy product.
  valObs (UnsignedMultiplication.mulValue 8 (.simple (.local .here))
    (.simple (.local (.there .here)))) target,
  match (UnsignedMultiplication.assignReadOperand .legacy 8 .here .here).run target with
    | .ok (_, .prim z) => PrimTy.num? z | _ => none,
  match (UnsignedMultiplication.mulValue 8 (.simple (.local .here))
      (.simple (.local (.there .here)))).evalT ReadControls.target with
    | .ok z => PrimTy.num? z | _ => none])
-- Checked Source max squared is a panic in both pipelines; this is no target payload proof.
/-- info: [true, true] -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].map fun p =>
  revertOf ((Source.evalE (G0 p) F0 3
    (.binary .mul (.local .here) (.local (.there .here)))).run
      (boundarySource 8 (by decide))) == some (Source.panicData .arithmetic)))

-- Actual Source max squared at every width and both pipeline choices, not only target arithmetic.
def boundarySourceObs (p : Roadmap.Pipeline) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) : Option Int :=
  match (Source.evalE (G0 p) {F0 with checked := false} 3
      (.binary .mul (.local .here) (.local (.there .here)))).run (boundarySource bits valid) with
  | (.ok (.val v),_) => v.key | _ => none
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ((List.finRange 32).all fun i =>
  boundarySourceObs .legacy (8*(i.val+1)) (by omega) == some 1 &&
  boundarySourceObs .viaIR (8*(i.val+1)) (by omega) == some 1))
example (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) {F0 with checked := false} (fuel+3)
      (.binary .mul (.local .here) (.local (.there .here)))).run
        (UnsignedNarrowingControls.pureSource bits valid) =
      (.ok (.val (.int 0 (integer_zero_range _))),UnsignedNarrowingControls.pureSource bits valid) ∧
    (UnsignedMultiplication.mulValue bits (.simple (.local .here))
      (.simple (.local (.there .here)))).evalT (UnsignedNarrowingControls.pureTarget bits valid) =
      .ok (integerValue (UnsignedNarrowing.ty bits valid) 0 (integer_zero_range _)) := by
  have h := UnsignedMultiplication.source_locals_run (G0 p) F0 fuel
    (UnsignedNarrowingControls.pureSource bits valid) bits valid .here (.there .here) 0 1
    (integer_zero_range _) (UnsignedNarrowingControls.one_range bits valid) rfl rfl
  have t := UnsignedMultiplication.mul_value_run (UnsignedNarrowingControls.pureTarget bits valid)
    bits valid (.simple (.local .here)) (.simple (.local (.there .here))) 0 1
    (integer_zero_range _) (UnsignedNarrowingControls.one_range bits valid) rfl rfl
  have zero := UnsignedNarrowing.wrap_of_range bits valid 0 (integer_zero_range _)
  simp only [Int.zero_mul,Source.intWrap,zero] at h t
  exact ⟨h,t⟩

example {C : Contract} {Γ : Ctx} (a b : Val C Γ .uint) :
    UnsignedMultiplication.mulValue 256 a b = .binop .mulW rfl rfl a b := rfl
-- Bare checked word multiplication rejects max² at256; the actual unchecked result is1.
def checkedWordRejects : Bool :=
  match (Val.binop .mul rfl rfl (.simple (.local .here)) (.simple (.local (.there .here))) :
    Val (default : Contract) [.val .uint,.val .uint] .uint).evalT
      (boundaryTarget 256 (by decide)) with
  | .error _ => true
  | .ok _ => false
/-- info: [true, true] -/
#guard_msgs in
#eval IO.println (reprStr [checkedWordRejects,boundaryObs 256 (by decide) == some 1])
end Solidity.Lowering.V07.UnsignedMultiplicationChecks
