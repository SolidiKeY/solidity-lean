import Solidity.Lowering.V07.SignedWordSubtraction
import Solidity.Lowering.V07.WordCastControls

namespace Solidity.Lowering.V07.SignedSubtractionControls
open SignedWordSubtraction Source.SemanticsExamples
open MixedAssignmentControls (C E globals storageRef)
def maximum : Int := Semantics.intBound-1
def minimum : Int := -Semantics.intBound
def source := WordCastControls.source ty maximum (-1) (by decide) (by decide)
def target := WordCastControls.target ty maximum (-1) (by decide) (by decide)
abbrev si := WordCastControls.si ty
abbrev ti := WordCastControls.ti ty

-- Every generic headline has an inhabited registered client.
def signed_wrap_range := wrap_of_range (-1) (by decide)
def signed_wrap_word := wrap_word (-1)
def signed_mod_sub := unsigned_sub_wrap minimum 1
def signed_source_value := source_sub_unchecked (D := E.layout) maximum (-1) (by decide) (by decide)
def signed_target_value := sub_value_run target (.simple (.local .here)) (.simple (.local (.there .here)))
  maximum (-1) (by decide) (by decide) rfl rfl
def signed_pair (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_from_pair (globals p) F0 (fuel+2) source source (.local .here) (.local (.there .here))
    maximum (-1) (by decide) (by decide)
    (source_local_pair (globals p) {F0 with checked := false} fuel source ty .here (.there .here)
      maximum (-1) (by decide) (by decide) rfl rfl)
def signed_source_locals (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_locals_run (globals p) F0 fuel source .here (.there .here) maximum (-1) (by decide) (by decide) rfl rfl
def signed_locals (p : Roadmap.Pipeline) (fuel : Nat) :=
  locals_transport (globals p) F0 fuel source target si ti
    (WordCastControls.initial ty maximum (-1) (by decide) (by decide)) true false
    maximum (-1) (by decide) (by decide) rfl rfl
def signed_source_assignment (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_assign_read_run (globals p) F0 fuel source (.there .here) .here maximum (-1) (by decide) (by decide) rfl rfl
def signed_target_assignment (p : Roadmap.Pipeline) :=
  assign_read_operand_run p target (.there .here) .here maximum (-1) (by decide) (by decide) rfl rfl
def signed_assignment (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport (globals p) F0 fuel source target si ti
    (WordCastControls.initial ty maximum (-1) (by decide) (by decide)) false true
    maximum (-1) (by decide) (by decide) rfl rfl
def signed_extension (p : Roadmap.Pipeline) :=
  assignment_extension p target (.there .here) .here maximum (-1) (by decide) (by decide) rfl rfl
    (Thin.drop (t := .val .bool) .refl) (true,target.env)

-- Boundaries run the actual independent Source evaluator and actual target Val.
def check (p : Roadmap.Pipeline) (x y expected : Int)
    (hx : ty.lo ≤ x ∧ x ≤ ty.hi) (hy : ty.lo ≤ y ∧ y ≤ ty.hi) : Bool :=
  let src := WordCastControls.source ty x y hx hy
  let tgt := WordCastControls.target ty x y hx hy
  let sr := match (Source.evalE (globals p) {F0 with checked := false} 5
    (.binary .sub (.local .here) (.local (.there .here)))).run src with
    | (.ok (.val v),_) => v.key | _ => none
  let tr := match (subValue (.simple (.local .here)) (.simple (.local (.there .here)))).evalT tgt with
    | .ok v => some v.val | _ => none
  sr == some expected && tr == some expected
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p =>
  check p minimum 1 maximum (by decide) (by decide) &&
  check p maximum (-1) minimum (by decide) (by decide) &&
  check p minimum maximum 1 (by decide) (by decide) &&
  check p maximum minimum (-1) (by decide) (by decide) &&
  check p 0 minimum minimum (by decide) (by decide) &&
  check p (-1) 1 (-2) (by decide) (by decide) &&
  check p 0 1 (-1) (by decide) (by decide) &&
  check p minimum minimum 0 (by decide) (by decide) &&
  check p maximum maximum 0 (by decide) (by decide)))

-- Tags are only a readable observation of complete numeric capture/caller vectors.
def tag (n : Int) : String :=
  if n = maximum then "MAX" else if n = minimum then "MIN" else toString n
def stag {τ : Source.STy} (v : Source.Val E.layout τ) : String :=
  match v.key with | some n => tag n | none => "non-numeric"
def sourcePairObs (p : Roadmap.Pipeline) : List String :=
  match (Source.evalPair (globals p) {F0 with checked := false} 5
    (.assign (.local (.there .here)) (.local .here)) (.local (.there .here))).run source with
  | (.ok (.val x,.val y),post) => [stag x,stag y,stag (post.1.get .here),stag (post.1.get (.there .here))]
  | _ => []
def targetPairObs (p : Roadmap.Pipeline) : List String :=
  match (assignReadPrefix p (.there .here) .here).run target with
  | .ok post =>
    let left : Idx [.val .int,.val .int,.val .int,.val .int,.mem bytesR,.alias bytesR] (.val .int) :=
      if p = .legacy then .here else .there .here
    let right : Idx [.val .int,.val .int,.val .int,.val .int,.mem bytesR,.alias bytesR] (.val .int) :=
      if p = .legacy then .there .here else .here
    [tag (TEnv.get left post.st.env).val,tag (TEnv.get right post.st.env).val,
      tag (TEnv.get (.there (.there .here)) post.st.env).val,
      tag (TEnv.get (.there (.there (.there .here))) post.st.env).val]
  | _ => []
/-- info: [["MAX", "-1", "MAX", "MAX"], ["MAX", "MAX", "MAX", "MAX"], ["MAX", "-1", "MAX", "MAX"], ["MAX", "MAX", "MAX", "MAX"]] -/
#guard_msgs in
#eval IO.println (reprStr [sourcePairObs .legacy,sourcePairObs .viaIR,targetPairObs .legacy,targetPairObs .viaIR])

def sourceObs (p : Roadmap.Pipeline) (same : Bool) : List String :=
  let i : Source.Idx [.int ty,.int ty,.bytes .memory,.bytes .storage] (.int ty) :=
    if same then .here else .there .here
  match (Source.evalE (globals p) {F0 with checked := false} 6
    (.binary .sub (.assign (.local i) (.local .here)) (.local i))).run source with
  | (.ok (.val v),post) => [stag v,stag (post.1.get .here),stag (post.1.get (.there .here))]
  | _ => []
def targetObs (p : Roadmap.Pipeline) (same : Bool) : List String :=
  let i : Idx [.val .int,.val .int,.mem bytesR,.alias bytesR] (.val .int) :=
    if same then .here else .there .here
  match (assignReadOperand p i .here).run target with
  | .ok (post,.prim v) => [tag v.val,tag (TEnv.get .here post.st.env).val,tag (TEnv.get (.there .here) post.st.env).val]
  | _ => []
/-- info: [["MIN", "MAX", "MAX"], ["0", "MAX", "MAX"], ["MIN", "MAX", "MAX"], ["0", "MAX", "MAX"]] -/
#guard_msgs in
#eval IO.println (reprStr [sourceObs .legacy false,sourceObs .viaIR false,targetObs .legacy false,targetObs .viaIR false])
/-- info: [["0", "MAX", "-1"], ["0", "MAX", "-1"], ["0", "MAX", "-1"], ["0", "MAX", "-1"]] -/
#guard_msgs in
#eval IO.println (reprStr [sourceObs .legacy true,sourceObs .viaIR true,targetObs .legacy true,targetObs .viaIR true])
example (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport (globals p) F0 fuel source target si ti
    (WordCastControls.initial ty maximum (-1) (by decide) (by decide)) true true
    maximum maximum (by decide) (by decide) rfl rfl

-- Reversed semantic subtraction arguments differ at ordinary negative inputs.
def ordinary := WordCastControls.target ty (-1) 1 (by decide) (by decide)
def normal : Val C [.val .int,.val .int,.mem bytesR,.alias bytesR] .int :=
  subValue (.simple (.local .here)) (.simple (.local (.there .here)))
def reversed : Val C [.val .int,.val .int,.mem bytesR,.alias bytesR] .int :=
  subValue (.simple (.local (.there .here))) (.simple (.local .here))
example : (normal.evalT ordinary).toOption.map (·.val) = some (-2) := by decide
example : (reversed.evalT ordinary).toOption.map (·.val) = some 2 := by decide

-- A bare unsigned word has the wrong observation when the result sign bit is set.
def raw : Val C [.val .int,.val .int,.mem bytesR,.alias bytesR] .uint :=
  UnsignedNarrowing.subValue 256 (.unop .toUint rfl rfl (.simple (.local .here)))
    (.unop .toUint rfl rfl (.simple (.local (.there .here))))
/-- info: [true, false, true] -/
#guard_msgs in
#eval IO.println (reprStr [((raw.evalT target).toOption.map (·.val)) == some Semantics.intBound,
  ((raw.evalT target).toOption.map (·.val)) == some minimum,
  ((normal.evalT target).toOption.map (·.val)) == some minimum])

-- Deferred caller re-reads lose the legacy capture; initial reads lose the IR capture.
def post := target.setLocal (.there .here) (integerValue ty maximum (by decide))
def deferred : Val C [.val .int,.val .int,.mem bytesR,.alias bytesR] .int :=
  subValue (.simple (.local (.there .here))) (.simple (.local (.there .here)))
/-- info: [true, false, true, false] -/
#guard_msgs in
#eval IO.println (reprStr [((deferred.evalT post).toOption.map (·.val)) == some 0,
  ((deferred.evalT post).toOption.map (·.val)) == some minimum,
  ((normal.evalT target).toOption.map (·.val)) == some minimum,
  ((normal.evalT target).toOption.map (·.val)) == some 0])

-- Actual checked operations reject the overflow; no failure-payload agreement claimed.
def sourceSuccess (p : Roadmap.Pipeline) (checked : Bool) : Bool :=
  match (Source.evalE (globals p) {F0 with checked := checked} 5
    (.binary .sub (.local .here) (.local (.there .here)))).run source with
  | (.ok _,_) => true | _ => false
def checkedValue : Val C [.val .int,.val .int,.mem bytesR,.alias bytesR] .int :=
  .binop .sub (integer_sub_accepts ty) rfl (.simple (.local .here)) (.simple (.local (.there .here)))
/-- info: [[true, false], [true, false], [true, false]] -/
#guard_msgs in
#eval IO.println (reprStr [[sourceSuccess .legacy false,sourceSuccess .legacy true],
  [sourceSuccess .viaIR false,sourceSuccess .viaIR true],
  [match normal.evalT target with | .ok _ => true | _ => false,
   match checkedValue.evalT target with | .ok _ => true | _ => false]])

-- Entire callers retain live memory/storage and the independent Source world.
example : source.2.heap.get 0 = some ⟨.bytes .memory,.bytes [0,0]⟩ ∧
    E.pathTy MixedAssignmentControls.path = some (.bytes .storage) := ⟨rfl,rfl⟩
example : ∃ r : HRef target.H bytesR,
    TEnv.get (.there (.there .here)) target.env = some r ∧ target.heap.len r .dyn = 2 :=
  MixedAssignmentControls.live_memory
example : post.heap = target.heap ∧ post.storage = target.storage ∧ post.glob = target.glob ∧
    TEnv.get (.there (.there .here)) post.env = TEnv.get (.there (.there .here)) target.env ∧
    TEnv.get (.there (.there (.there .here))) post.env = some storageRef := ⟨rfl,rfl,rfl,rfl,rfl⟩

end Solidity.Lowering.V07.SignedSubtractionControls
