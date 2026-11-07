import Solidity.Lowering.V07.SignedWordAddition
import Solidity.Lowering.V07.SignedWordMultiplication
import Solidity.Lowering.V07.SignedSubtractionControls

namespace Solidity.Lowering.V07.SignedArithmeticControls
open Source.SemanticsExamples
open SignedWordSubtraction (ty)
open SignedSubtractionControls (maximum minimum source target si ti)
open MixedAssignmentControls (C E globals storageRef)

namespace Addition
open SignedWordAddition
def mod_word := unsigned_add_wrap minimum 1
def source_value := source_add_unchecked (D := E.layout) maximum (-1) (by decide) (by decide)
def target_value := add_value_run target (.simple (.local .here)) (.simple (.local (.there .here)))
  maximum (-1) (by decide) (by decide) rfl rfl
def pair (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_from_pair (globals p) F0 (fuel+2) source source (.local .here) (.local (.there .here))
    maximum (-1) (by decide) (by decide)
    (source_local_pair (globals p) {F0 with checked := false} fuel source ty .here (.there .here)
      maximum (-1) (by decide) (by decide) rfl rfl)
def source_locals (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_locals_run (globals p) F0 fuel source .here (.there .here) maximum (-1) (by decide) (by decide) rfl rfl
def locals (p : Roadmap.Pipeline) (fuel : Nat) :=
  locals_transport (globals p) F0 fuel source target si ti
    (WordCastControls.initial ty maximum (-1) (by decide) (by decide)) true false
    maximum (-1) (by decide) (by decide) rfl rfl
def source_assignment (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_assign_read_run (globals p) F0 fuel source (.there .here) .here maximum (-1) (by decide) (by decide) rfl rfl
def target_assignment (p : Roadmap.Pipeline) :=
  assign_read_operand_run p target (.there .here) .here maximum (-1) (by decide) (by decide) rfl rfl
def assignment (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport (globals p) F0 fuel source target si ti
    (WordCastControls.initial ty maximum (-1) (by decide) (by decide)) false true
    maximum (-1) (by decide) (by decide) rfl rfl
def extension (p : Roadmap.Pipeline) :=
  assignment_extension p target (.there .here) .here maximum (-1) (by decide) (by decide) rfl rfl
    (Thin.drop (t := .val .bool) .refl) (true,target.env)

end Addition

namespace Multiplication
open SignedWordMultiplication
def mod_word := unsigned_mul_wrap minimum 1
def source_value := source_mul_unchecked (D := E.layout) maximum (-1) (by decide) (by decide)
def target_value := mul_value_run target (.simple (.local .here)) (.simple (.local (.there .here)))
  maximum (-1) (by decide) (by decide) rfl rfl
def pair (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_from_pair (globals p) F0 (fuel+2) source source (.local .here) (.local (.there .here))
    maximum (-1) (by decide) (by decide)
    (source_local_pair (globals p) {F0 with checked := false} fuel source ty .here (.there .here)
      maximum (-1) (by decide) (by decide) rfl rfl)
def source_locals (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_locals_run (globals p) F0 fuel source .here (.there .here) maximum (-1) (by decide) (by decide) rfl rfl
def locals (p : Roadmap.Pipeline) (fuel : Nat) :=
  locals_transport (globals p) F0 fuel source target si ti
    (WordCastControls.initial ty maximum (-1) (by decide) (by decide)) true false
    maximum (-1) (by decide) (by decide) rfl rfl
def source_assignment (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_assign_read_run (globals p) F0 fuel source (.there .here) .here maximum (-1) (by decide) (by decide) rfl rfl
def target_assignment (p : Roadmap.Pipeline) :=
  assign_read_operand_run p target (.there .here) .here maximum (-1) (by decide) (by decide) rfl rfl
def assignment (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport (globals p) F0 fuel source target si ti
    (WordCastControls.initial ty maximum (-1) (by decide) (by decide)) false true
    maximum (-1) (by decide) (by decide) rfl rfl
def extension (p : Roadmap.Pipeline) :=
  assignment_extension p target (.there .here) .here maximum (-1) (by decide) (by decide) rfl rfl
    (Thin.drop (t := .val .bool) .refl) (true,target.env)

end Multiplication

-- Both Source pipelines and actual typed target arithmetic at signed boundaries.
def checkAdd (p : Roadmap.Pipeline) (x y expected : Int)
    (hx : ty.lo ≤ x ∧ x ≤ ty.hi) (hy : ty.lo ≤ y ∧ y ≤ ty.hi) : Bool :=
  let src := WordCastControls.source ty x y hx hy
  let tgt := WordCastControls.target ty x y hx hy
  let sr := match (Source.evalE (globals p) {F0 with checked := false} 5
    (.binary .add (.local .here) (.local (.there .here)))).run src with
    | (.ok (.val v),_) => v.key | _ => none
  let tr := match (SignedWordAddition.addValue (.simple (.local .here))
    (.simple (.local (.there .here)))).evalT tgt with | .ok v => some v.val | _ => none
  sr == some expected && tr == some expected

def checkMul (p : Roadmap.Pipeline) (x y expected : Int)
    (hx : ty.lo ≤ x ∧ x ≤ ty.hi) (hy : ty.lo ≤ y ∧ y ≤ ty.hi) : Bool :=
  let src := WordCastControls.source ty x y hx hy
  let tgt := WordCastControls.target ty x y hx hy
  let sr := match (Source.evalE (globals p) {F0 with checked := false} 5
    (.binary .mul (.local .here) (.local (.there .here)))).run src with
    | (.ok (.val v),_) => v.key | _ => none
  let tr := match (SignedWordMultiplication.mulValue (.simple (.local .here))
    (.simple (.local (.there .here)))).evalT tgt with | .ok v => some v.val | _ => none
  sr == some expected && tr == some expected
/-- info: [true, true] -/
#guard_msgs in
#eval IO.println (reprStr [
 [Roadmap.Pipeline.legacy,.viaIR].all (fun p =>
   checkAdd p maximum 1 minimum (by decide) (by decide) &&
   checkAdd p minimum (-1) maximum (by decide) (by decide) &&
   checkAdd p minimum minimum 0 (by decide) (by decide) &&
   checkAdd p maximum maximum (-2) (by decide) (by decide) &&
   checkAdd p minimum maximum (-1) (by decide) (by decide) &&
   checkAdd p (-1) 1 0 (by decide) (by decide) &&
   checkAdd p 0 0 0 (by decide) (by decide) &&
   checkAdd p 0 maximum maximum (by decide) (by decide) &&
   checkAdd p (-1) (-1) (-2) (by decide) (by decide)),
 [Roadmap.Pipeline.legacy,.viaIR].all (fun p =>
   checkMul p minimum (-1) minimum (by decide) (by decide) &&
   checkMul p maximum 2 (-2) (by decide) (by decide) &&
   checkMul p minimum 2 0 (by decide) (by decide) &&
   checkMul p maximum maximum 1 (by decide) (by decide) &&
   checkMul p (-1) maximum (minimum+1) (by decide) (by decide) &&
   checkMul p (-1) (-1) 1 (by decide) (by decide) &&
   checkMul p (-7) 3 (-21) (by decide) (by decide) &&
   checkMul p 0 minimum 0 (by decide) (by decide) &&
   checkMul p minimum maximum minimum (by decide) (by decide))])

-- Tags distinguish exact numeric observations, not a replacement evaluator.
def tag (n : Int) : String :=
  if n = maximum-1 then "MAX-1" else if n = minimum+1 then "MIN+1" else SignedSubtractionControls.tag n
def stag {τ : Source.STy} (v : Source.Val E.layout τ) : String :=
  match v.key with | some n => tag n | none => "non-numeric"
def sourceAddObs (p : Roadmap.Pipeline) : List String :=
  match (Source.evalE (globals p) {F0 with checked := false} 6
    (.binary .add (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run source with
  | (.ok (.val v),out) => [stag v,stag (out.1.get .here),stag (out.1.get (.there .here))] | _ => []
def sourceMulObs (p : Roadmap.Pipeline) : List String :=
  match (Source.evalE (globals p) {F0 with checked := false} 6
    (.binary .mul (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run source with
  | (.ok (.val v),out) => [stag v,stag (out.1.get .here),stag (out.1.get (.there .here))] | _ => []
def targetAddObs (p : Roadmap.Pipeline) : List String :=
  match (SignedWordAddition.assignReadOperand p (.there .here) .here).run target with
  | .ok (out,.prim v) => [tag v.val,tag (TEnv.get .here out.st.env).val,tag (TEnv.get (.there .here) out.st.env).val] | _ => []
def targetMulObs (p : Roadmap.Pipeline) : List String :=
  match (SignedWordMultiplication.assignReadOperand p (.there .here) .here).run target with
  | .ok (out,.prim v) => [tag v.val,tag (TEnv.get .here out.st.env).val,tag (TEnv.get (.there .here) out.st.env).val] | _ => []
/-- info: [["MAX-1", "MAX", "MAX"], ["-2", "MAX", "MAX"], ["MAX-1", "MAX", "MAX"], ["-2", "MAX", "MAX"]] -/
#guard_msgs in
#eval IO.println (reprStr [sourceAddObs .legacy,sourceAddObs .viaIR,targetAddObs .legacy,targetAddObs .viaIR])
/-- info: [["MIN+1", "MAX", "MAX"], ["1", "MAX", "MAX"], ["MIN+1", "MAX", "MAX"], ["1", "MAX", "MAX"]] -/
#guard_msgs in
#eval IO.println (reprStr [sourceMulObs .legacy,sourceMulObs .viaIR,targetMulObs .legacy,targetMulObs .viaIR])

-- Real same-slot and equal-content/distinct-identity family applications.
example (p : Roadmap.Pipeline) (fuel : Nat) :=
  SignedWordAddition.assignment_transport (globals p) F0 fuel source target si ti
    (WordCastControls.initial ty maximum (-1) (by decide) (by decide)) true true
    maximum maximum (by decide) (by decide) rfl rfl
example (p : Roadmap.Pipeline) (fuel : Nat) :=
  SignedWordMultiplication.assignment_transport (globals p) F0 fuel source target si ti
    (WordCastControls.initial ty maximum (-1) (by decide) (by decide)) true true
    maximum maximum (by decide) (by decide) rfl rfl
example (p : Roadmap.Pipeline) (fuel : Nat) :=
  SignedWordAddition.locals_transport (globals p) F0 fuel
    (WordCastControls.source ty minimum minimum (by decide) (by decide))
    (WordCastControls.target ty minimum minimum (by decide) (by decide)) si ti
    (WordCastControls.initial ty minimum minimum (by decide) (by decide)) true false
    minimum minimum (by decide) (by decide) rfl rfl
example (p : Roadmap.Pipeline) (fuel : Nat) :=
  SignedWordMultiplication.locals_transport (globals p) F0 fuel
    (WordCastControls.source ty maximum maximum (by decide) (by decide))
    (WordCastControls.target ty maximum maximum (by decide) (by decide)) si ti
    (WordCastControls.initial ty maximum maximum (by decide) (by decide)) true false
    maximum maximum (by decide) (by decide) rfl rfl

-- Actual missing sign readback at overflowing pure input pairs.
def edgeAdd := WordCastControls.target ty maximum 1 (by decide) (by decide)
def edgeMul := WordCastControls.target ty maximum 2 (by decide) (by decide)
def rawAdd : Val C [.val .int,.val .int,.mem bytesR,.alias bytesR] .uint :=
  UnsignedAddition.addValue 256 (.unop .toUint rfl rfl (.simple (.local .here)))
    (.unop .toUint rfl rfl (.simple (.local (.there .here))))
def rawMul : Val C [.val .int,.val .int,.mem bytesR,.alias bytesR] .uint :=
  UnsignedMultiplication.mulValue 256 (.unop .toUint rfl rfl (.simple (.local .here)))
    (.unop .toUint rfl rfl (.simple (.local (.there .here))))
def normalAdd : Val C [.val .int,.val .int,.mem bytesR,.alias bytesR] .int :=
  SignedWordAddition.addValue (.simple (.local .here)) (.simple (.local (.there .here)))
def normalMul : Val C [.val .int,.val .int,.mem bytesR,.alias bytesR] .int :=
  SignedWordMultiplication.mulValue (.simple (.local .here)) (.simple (.local (.there .here)))
/-- info: [true, false, true, true, false, true] -/
#guard_msgs in
#eval IO.println (reprStr [((rawAdd.evalT edgeAdd).toOption.map (·.val)) == some Semantics.intBound,
  ((rawAdd.evalT edgeAdd).toOption.map (·.val)) == some minimum,
  ((normalAdd.evalT edgeAdd).toOption.map (·.val)) == some minimum,
  ((rawMul.evalT edgeMul).toOption.map (·.val)) == some (Semantics.uintBound-2),
  ((rawMul.evalT edgeMul).toOption.map (·.val)) == some (-2),
  ((normalMul.evalT edgeMul).toOption.map (·.val)) == some (-2)])

-- Actual wrong deferred reads and stale initial reads, not reversed commutative arguments.
def post := SignedSubtractionControls.post
def deferredAdd : Val C [.val .int,.val .int,.mem bytesR,.alias bytesR] .int :=
  SignedWordAddition.addValue (.simple (.local (.there .here))) (.simple (.local (.there .here)))
def deferredMul : Val C [.val .int,.val .int,.mem bytesR,.alias bytesR] .int :=
  SignedWordMultiplication.mulValue (.simple (.local (.there .here))) (.simple (.local (.there .here)))
/-- info: [true, false, true, false, true, false, true, false] -/
#guard_msgs in
#eval IO.println (reprStr [((deferredAdd.evalT post).toOption.map (·.val)) == some (-2),
  ((deferredAdd.evalT post).toOption.map (·.val)) == some (maximum-1),
  ((normalAdd.evalT target).toOption.map (·.val)) == some (maximum-1),
  ((normalAdd.evalT target).toOption.map (·.val)) == some (-2),
  ((deferredMul.evalT post).toOption.map (·.val)) == some 1,
  ((deferredMul.evalT post).toOption.map (·.val)) == some (minimum+1),
  ((normalMul.evalT target).toOption.map (·.val)) == some (minimum+1),
  ((normalMul.evalT target).toOption.map (·.val)) == some 1])

-- Checked versus unchecked SUCCESS only; panic/revert payload transport stays open.
def sourceAddSuccess (p : Roadmap.Pipeline) (checked : Bool) : Bool :=
  match (Source.evalE (globals p) {F0 with checked := checked} 5
    (.binary .add (.local .here) (.local (.there .here)))).run
      (WordCastControls.source ty maximum 1 (by decide) (by decide)) with
  | (.ok _,_) => true | _ => false
def sourceMulSuccess (p : Roadmap.Pipeline) (checked : Bool) : Bool :=
  match (Source.evalE (globals p) {F0 with checked := checked} 5
    (.binary .mul (.local .here) (.local (.there .here)))).run
      (WordCastControls.source ty minimum (-1) (by decide) (by decide)) with
  | (.ok _,_) => true | _ => false
def checkedAdd : Val C [.val .int,.val .int,.mem bytesR,.alias bytesR] .int :=
  .binop .add rfl rfl (.simple (.local .here)) (.simple (.local (.there .here)))
def checkedMul : Val C [.val .int,.val .int,.mem bytesR,.alias bytesR] .int :=
  .binop .mul rfl rfl (.simple (.local .here)) (.simple (.local (.there .here)))
def minTarget := WordCastControls.target ty minimum (-1) (by decide) (by decide)
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (([Roadmap.Pipeline.legacy,.viaIR].all fun p =>
  sourceAddSuccess p false && !sourceAddSuccess p true && sourceMulSuccess p false && !sourceMulSuccess p true) &&
  (match normalAdd.evalT edgeAdd with | .ok _ => true | _ => false) &&
  !(match checkedAdd.evalT edgeAdd with | .ok _ => true | _ => false) &&
  (match normalMul.evalT minTarget with | .ok _ => true | _ => false) &&
  !(match checkedMul.evalT minTarget with | .ok _ => true | _ => false)))

-- The exact updated callers frame live references and the independent world.
example : source.2.heap.get 0 = some ⟨.bytes .memory,.bytes [0,0]⟩ ∧
    E.pathTy MixedAssignmentControls.path = some (.bytes .storage) := ⟨rfl,rfl⟩
example : ∃ r : HRef target.H bytesR,
    TEnv.get (.there (.there .here)) target.env = some r ∧ target.heap.len r .dyn = 2 :=
  MixedAssignmentControls.live_memory
example : post.heap = target.heap ∧ post.storage = target.storage ∧ post.glob = target.glob ∧
    TEnv.get (.there (.there .here)) post.env = TEnv.get (.there (.there .here)) target.env ∧
    TEnv.get (.there (.there (.there .here))) post.env = some storageRef := ⟨rfl,rfl,rfl,rfl,rfl⟩

end Solidity.Lowering.V07.SignedArithmeticControls
