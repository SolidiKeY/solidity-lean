import Solidity.Lowering.V07.UnsignedAddition
import Solidity.Lowering.V07.UnsignedNarrowingControls
namespace Solidity.Lowering.V07.UnsignedAdditionChecks
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
def result (p : Roadmap.Pipeline) : Int := if p = .legacy then 194 else 144
theorem initial : IntegerLocalFamily U8 si ti source.1 target.env := by
  constructor
  · intro k; rcases k with ⟨a,b⟩; cases a <;> cases b <;> rfl
  · intro k l; rcases k with ⟨a,b⟩; rcases l with ⟨c,d⟩
    cases a <;> cases b <;> cases c <;> cases d <;> decide

def witness (p : Roadmap.Pipeline) (fuel : Nat) :=
  UnsignedAddition.assignment_transport (MixedAssignmentControls.globals p) F0 fuel
    source target 8 (by decide) si ti initial (true,false) (false,false) 200 250
    (by decide) (by decide) rfl rfl

-- Full actual expression, target capture/drop, and post-family from initial alignment.
example (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} (fuel+4)
      (.binary .add (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run source =
      (.ok (.val (.int (result p) (by cases p <;> decide))),sourcePost) ∧
    (UnsignedAddition.assignReadOperand p 8 (.there .here) .here).run target =
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
    ((UnsignedAddition.assignReadOperand p 8 (.there .here) .here).wk
      (Thin.drop (t := .val .bool) .refl)).run (target.lift (Thin.drop .refl) (true,target.env)) =
      liftedT₂ (Thin.drop (t := .val .bool) .refl) (true,target.env)
        (.ok ((⟨targetPost,List.prefix_refl _⟩ : Out MixedAssignmentControls.C target.H TgtCtx),
          SVal.prim (integerValue .u8 (result p) (by cases p <;> decide)))) := by
  have h := UnsignedAddition.assignment_extension p target 8 (by decide) (.there .here) .here
    200 250 (by decide) (by decide) rfl rfl (Thin.drop (t := .val .bool) .refl) (true,target.env)
  cases p <;> exact h

-- Every approved width, including the full-word branch: max + 1 wraps to zero.
def boundaryTarget (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    State (default : Contract) [.val .uint,.val .uint] :=
  ((State.init (default : Contract)).push (t := .val .uint) (integerValue (UnsignedNarrowing.ty bits valid) 1
    (UnsignedNarrowingControls.one_range bits valid))).push
    (integerValue (UnsignedNarrowing.ty bits valid) (UnsignedNarrowing.ty bits valid).hi
      ⟨Int.le_trans (integer_zero_range _).1 (integer_zero_range _).2,Int.le_refl _⟩)
def boundarySource (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    Source.EMState E0 [.int (UnsignedNarrowing.ty bits valid),.int (UnsignedNarrowing.ty bits valid)] :=
  (.cons (.int (UnsignedNarrowing.ty bits valid).hi
      ⟨Int.le_trans (integer_zero_range _).1 (integer_zero_range _).2,Int.le_refl _⟩)
    (.cons (.int 1 (UnsignedNarrowingControls.one_range bits valid)) .nil),s0)
example (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) {F0 with checked := false} (fuel+3)
      (.binary .add (.local .here) (.local (.there .here)))).run (boundarySource bits valid) =
      (.ok (.val (Source.intWrap (UnsignedNarrowing.ty bits valid)
        ((UnsignedNarrowing.ty bits valid).hi+1))),boundarySource bits valid) ∧
    (UnsignedAddition.addValue bits (.simple (.local .here)) (.simple (.local (.there .here)))).evalT
      (boundaryTarget bits valid) =
      .ok (integerValue (UnsignedNarrowing.ty bits valid)
        ((UnsignedNarrowing.ty bits valid).wrap ((UnsignedNarrowing.ty bits valid).hi+1))
        ((UnsignedNarrowing.ty bits valid).wrap_mem _)) :=
  ⟨UnsignedAddition.source_locals_run (G0 p) F0 fuel _ bits valid .here (.there .here) _ _
    ⟨Int.le_trans (integer_zero_range _).1 (integer_zero_range _).2,Int.le_refl _⟩
    (UnsignedNarrowingControls.one_range bits valid) rfl rfl,
   UnsignedAddition.add_value_run _ bits valid _ _ _ _
    ⟨Int.le_trans (integer_zero_range _).1 (integer_zero_range _).2,Int.le_refl _⟩
    (UnsignedNarrowingControls.one_range bits valid) rfl rfl⟩

-- Actual ordered observations, including intermediate captures, not just a final sum.
def sourceObs (p : Roadmap.Pipeline) : List Int :=
  match (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} 4
      (.binary .add (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run source with
  | (.ok (.val (.int z _)),s) => [z,(s.1.get .here).key.getD (-1),(s.1.get (.there .here)).key.getD (-1)]
  | _ => []
def targetObs (p : Roadmap.Pipeline) : List Int :=
  match (UnsignedAddition.assignReadOperand p 8 (.there .here) .here).run target with
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
  match (UnsignedAddition.addValue bits (.simple (.local .here)) (.simple (.local (.there .here)))).evalT
      (boundaryTarget bits valid) with
  | .ok z => PrimTy.num? z
  | _ => none
/-- info: [[194, 200, 200], [144, 200, 200], [194, 200, 200], [144, 200, 200], [200, 250], [200, 200]] -/
#guard_msgs in
#eval IO.println (reprStr [sourceObs .legacy,sourceObs .viaIR,targetObs .legacy,targetObs .viaIR,
  captures .legacy,captures .viaIR])
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ((List.finRange 32).all fun i =>
  boundaryObs (8*(i.val+1)) (by omega) == some 0))
-- Unnarrowed uint256 450, stale initial-state right 250 in viaIR, and uncaptured reached right
-- 200 in legacy are all distinguishable. Checked uint256 add alone fails to narrow too.
/-- info: [true, true, true, true, true, true] -/
#guard_msgs in
#eval IO.println (reprStr [result .legacy != 450,result .viaIR != 450,
  result .viaIR != result .legacy,result .legacy != 144,
  Source.IntTy.u8.wrap (255+1) == 0,Source.IntTy.u256.wrap (255+1) != 0])
-- Same local may be both assignment destination and RHS; no hidden separation.
example (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (MixedAssignmentControls.globals p) {F0 with checked := false} (fuel+4)
      (.binary .add (.assign (.local .here) (.local .here)) (.local .here))).run source =
      (.ok (.val (.int 144 (by decide))),source) ∧
    (UnsignedAddition.assignReadOperand p 8 .here .here).run target =
      .ok (⟨target,List.prefix_refl _⟩,.prim (integerValue .u8 144 (by decide))) := by
  have h := UnsignedAddition.assignment_transport (MixedAssignmentControls.globals p) F0 fuel
    source target 8 (by decide) si ti initial (false,false) (false,false) 200 200
    (by decide) (by decide) rfl rfl
  cases p <;> exact ⟨h.1,h.2.1⟩
example (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) {F0 with checked := false} (fuel+3)
      (.binary .add (.local .here) (.local (.there .here)))).run ReadControls.source =
      (.ok (.val (.int 10 (by decide))),ReadControls.source) ∧
    (UnsignedAddition.addValue 8 (.simple (.local .here)) (.simple (.local (.there .here)))).evalT
      ReadControls.target = .ok (integerValue .u8 10 (by decide)) :=
  ⟨UnsignedAddition.source_locals_run (G0 p) F0 fuel _ 8 (by decide)
    .here (.there .here) 7 3 (by decide) (by decide) rfl rfl,
   UnsignedAddition.add_value_run _ 8 (by decide) _ _ 7 3 (by decide) (by decide) rfl rfl⟩

def valObs {Γ : Ctx} (v : Val MixedAssignmentControls.C Γ .uint)
    (s : State MixedAssignmentControls.C Γ) : Option Int :=
  match v.evalT s with | .ok z => PrimTy.num? z | _ => none
-- Actually execute wrong lowerings, rather than comparing expected-result literals.
/-- info: [some 450, some 144, some 194, some 144, some 10] -/
#guard_msgs in
#eval IO.println (reprStr [
  valObs (.binop .addW rfl rfl (.simple (.local .here))
    (.simple (.local (.there .here)))) target,
  valObs (UnsignedAddition.addValue 8 (.simple (.local (.there .here)))
    (.simple (.local (.there .here)))) targetPost,
  -- Stale initial read in viaIR wrongly obtains the legacy sum.
  valObs (UnsignedAddition.addValue 8 (.simple (.local .here))
    (.simple (.local (.there .here)))) target,
  match (UnsignedAddition.assignReadOperand .legacy 8 .here .here).run target with
    | .ok (_, .prim z) => PrimTy.num? z | _ => none,
  match (UnsignedAddition.addValue 8 (.simple (.local .here))
      (.simple (.local (.there .here)))).evalT ReadControls.target with
    | .ok z => PrimTy.num? z | _ => none])
-- Checked Source max+1 is a panic in both pipelines; this is no target payload proof.
/-- info: [true, true] -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].map fun p =>
  revertOf ((Source.evalE (G0 p) F0 3
    (.binary .add (.local .here) (.local (.there .here)))).run
      (boundarySource 8 (by decide))) == some (Source.panicData .arithmetic)))
end Solidity.Lowering.V07.UnsignedAdditionChecks
