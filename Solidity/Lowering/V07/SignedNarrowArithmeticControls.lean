import Solidity.Lowering.V07.SignedNarrowAddition
import Solidity.Lowering.V07.SignedNarrowSubtraction
import Solidity.Lowering.V07.SignedNarrowMultiplication
import Solidity.Lowering.V07.WordCastControls

namespace Solidity.Lowering.V07.SignedNarrowArithmeticControls
open Source.SemanticsExamples
open SignedWidthCasts (ty)
open MixedAssignmentControls (C E globals storageRef)

def source := WordCastControls.source (ty 8 (by decide)) 127 (-1) (by decide) (by decide)
def target := WordCastControls.target (ty 8 (by decide)) 127 (-1) (by decide) (by decide)
def si := WordCastControls.si (ty 8 (by decide))
def ti := WordCastControls.ti (ty 8 (by decide))
def initial := WordCastControls.initial (ty 8 (by decide)) 127 (-1) (by decide) (by decide)
def narrow_canonical := SignedNarrowing.wrap_of_range 8 (by decide) (-128) (by decide)
def narrow_word := SignedNarrowing.wrap_word 8 (by decide) (Semantics.uintBound+128)

namespace Addition
open SignedNarrowAddition
def source_value := source_add_unchecked 8 (by decide) (D := E.layout) 127 (-1) (by decide) (by decide)
def target_value := add_value_run 8 (by decide) target (.simple (.local .here)) (.simple (.local (.there .here)))
  127 (-1) (by decide) (by decide) rfl rfl
def pair (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_from_pair 8 (by decide) (globals p) F0 (fuel+2) source source (.local .here) (.local (.there .here))
    127 (-1) (by decide) (by decide)
    (source_local_pair (globals p) {F0 with checked := false} fuel source (ty 8 (by decide)) .here (.there .here)
      127 (-1) (by decide) (by decide) rfl rfl)
def source_locals (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_locals_run 8 (by decide) (globals p) F0 fuel source .here (.there .here)
    127 (-1) (by decide) (by decide) rfl rfl
def locals (p : Roadmap.Pipeline) (fuel : Nat) :=
  locals_transport 8 (by decide) (globals p) F0 fuel source target si ti initial true false
    127 (-1) (by decide) (by decide) rfl rfl
def source_assignment (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_assign_read_run 8 (by decide) (globals p) F0 fuel source (.there .here) .here
    127 (-1) (by decide) (by decide) rfl rfl
def target_assignment (p : Roadmap.Pipeline) :=
  assign_read_operand_run 8 (by decide) p target (.there .here) .here
    127 (-1) (by decide) (by decide) rfl rfl
def assignment (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport 8 (by decide) (globals p) F0 fuel source target si ti initial false true
    127 (-1) (by decide) (by decide) rfl rfl
def extension (p : Roadmap.Pipeline) :=
  assignment_extension 8 (by decide) p target (.there .here) .here
    127 (-1) (by decide) (by decide) rfl rfl (Thin.drop (t := .val .bool) .refl) (true,target.env)

-- Same-slot/repeated selected aliases and distinct equal-content locals.
example (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport 8 (by decide) (globals p) F0 fuel source target
    (fun _ : Bool => si true) (fun _ : Bool => ti true) (initial.reindex (fun _ : Bool => true))
    false true 127 127 (by decide) (by decide) rfl rfl
example (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport 8 (by decide) (globals p) F0 fuel
    (WordCastControls.source (ty 8 (by decide)) 127 127 (by decide) (by decide))
    (WordCastControls.target (ty 8 (by decide)) 127 127 (by decide) (by decide)) si ti
    (WordCastControls.initial (ty 8 (by decide)) 127 127 (by decide) (by decide))
    false true 127 127 (by decide) (by decide) rfl rfl
end Addition

def checkAddition (p : Roadmap.Pipeline) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (inputX inputY : Int) : Bool :=
  let x := (ty bits valid).wrap inputX
  let y := (ty bits valid).wrap inputY
  let hx := (ty bits valid).wrap_mem inputX
  let hy := (ty bits valid).wrap_mem inputY
  let src := WordCastControls.source (ty bits valid) x y hx hy
  let tgt := WordCastControls.target (ty bits valid) x y hx hy
  let sr := match (Source.evalE (globals p) {F0 with checked := false} 6
    (.binary .add (.local .here) (.local (.there .here)))).run src with
    | (.ok (.val v),_) => v.key | _ => none
  let tr := match (SignedNarrowAddition.addValue bits (.simple (.local .here)) (.simple (.local (.there .here)))).evalT tgt with
    | .ok v => some v.val | _ => none
  let q := (x+y) % ((2^bits : Nat) : Int)
  let expected := if q < ((2^(bits-1) : Nat) : Int) then q else q-((2^bits : Nat) : Int)
  sr == some expected && tr == sr

def effectAddition (p : Roadmap.Pipeline) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) : Bool :=
  let x := (ty bits valid).wrap (ty bits valid).hi
  let y := (ty bits valid).wrap (-1)
  let hx := (ty bits valid).wrap_mem (ty bits valid).hi
  let hy := (ty bits valid).wrap_mem (-1)
  let src := WordCastControls.source (ty bits valid) x y hx hy
  let tgt := WordCastControls.target (ty bits valid) x y hx hy
  let sr := match (Source.evalE (globals p) {F0 with checked := false} 6
    (.binary .add (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run src with
    | (.ok (.val v),out) => match v.key,(out.1.get (.there .here)).key,(out.1.get .here).key with
      | some v,some i,some a => some (v,i,a) | _,_,_ => none
    | _ => none
  let tr := match (SignedNarrowAddition.assignReadOperand bits p (.there .here) .here).run tgt with
    | .ok (out,.prim v) => some (v.val,(TEnv.get (.there .here) out.st.env).val,(TEnv.get .here out.st.env).val)
    | _ => none
  let q := (x+(if p = .legacy then y else x)) % ((2^bits : Nat) : Int)
  let expected := if q < ((2^(bits-1) : Nat) : Int) then q else q-((2^bits : Nat) : Int)
  sr == some (expected,x,x) && tr == sr

def sourceAddition (p : Roadmap.Pipeline) (checked : Bool := false) : Option (Int × Int × Int) :=
  match (Source.evalE (globals p) {F0 with checked := checked} 6
    (.binary .add (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run source with
  | (.ok (.val v),out) => match v.key,(out.1.get (.there .here)).key,(out.1.get .here).key with
    | some v,some i,some a => some (v,i,a) | _,_,_ => none
  | _ => none

def targetAddition (p : Roadmap.Pipeline) : Option (Int × Int × Int) :=
  match (SignedNarrowAddition.assignReadOperand 8 p (.there .here) .here).run target with
  | .ok (out,.prim v) => some (v.val,(TEnv.get (.there .here) out.st.env).val,(TEnv.get .here out.st.env).val)
  | _ => none

namespace Subtraction
open SignedNarrowSubtraction
def source_value := source_sub_unchecked 8 (by decide) (D := E.layout) 127 (-1) (by decide) (by decide)
def target_value := sub_value_run 8 (by decide) target (.simple (.local .here)) (.simple (.local (.there .here)))
  127 (-1) (by decide) (by decide) rfl rfl
def pair (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_from_pair 8 (by decide) (globals p) F0 (fuel+2) source source (.local .here) (.local (.there .here))
    127 (-1) (by decide) (by decide)
    (source_local_pair (globals p) {F0 with checked := false} fuel source (ty 8 (by decide)) .here (.there .here)
      127 (-1) (by decide) (by decide) rfl rfl)
def source_locals (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_locals_run 8 (by decide) (globals p) F0 fuel source .here (.there .here)
    127 (-1) (by decide) (by decide) rfl rfl
def locals (p : Roadmap.Pipeline) (fuel : Nat) :=
  locals_transport 8 (by decide) (globals p) F0 fuel source target si ti initial true false
    127 (-1) (by decide) (by decide) rfl rfl
def source_assignment (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_assign_read_run 8 (by decide) (globals p) F0 fuel source (.there .here) .here
    127 (-1) (by decide) (by decide) rfl rfl
def target_assignment (p : Roadmap.Pipeline) :=
  assign_read_operand_run 8 (by decide) p target (.there .here) .here
    127 (-1) (by decide) (by decide) rfl rfl
def assignment (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport 8 (by decide) (globals p) F0 fuel source target si ti initial false true
    127 (-1) (by decide) (by decide) rfl rfl
def extension (p : Roadmap.Pipeline) :=
  assignment_extension 8 (by decide) p target (.there .here) .here
    127 (-1) (by decide) (by decide) rfl rfl (Thin.drop (t := .val .bool) .refl) (true,target.env)

-- Same-slot/repeated selected aliases and distinct equal-content locals.
example (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport 8 (by decide) (globals p) F0 fuel source target
    (fun _ : Bool => si true) (fun _ : Bool => ti true) (initial.reindex (fun _ : Bool => true))
    false true 127 127 (by decide) (by decide) rfl rfl
example (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport 8 (by decide) (globals p) F0 fuel
    (WordCastControls.source (ty 8 (by decide)) 127 127 (by decide) (by decide))
    (WordCastControls.target (ty 8 (by decide)) 127 127 (by decide) (by decide)) si ti
    (WordCastControls.initial (ty 8 (by decide)) 127 127 (by decide) (by decide))
    false true 127 127 (by decide) (by decide) rfl rfl
end Subtraction

def checkSubtraction (p : Roadmap.Pipeline) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (inputX inputY : Int) : Bool :=
  let x := (ty bits valid).wrap inputX
  let y := (ty bits valid).wrap inputY
  let hx := (ty bits valid).wrap_mem inputX
  let hy := (ty bits valid).wrap_mem inputY
  let src := WordCastControls.source (ty bits valid) x y hx hy
  let tgt := WordCastControls.target (ty bits valid) x y hx hy
  let sr := match (Source.evalE (globals p) {F0 with checked := false} 6
    (.binary .sub (.local .here) (.local (.there .here)))).run src with
    | (.ok (.val v),_) => v.key | _ => none
  let tr := match (SignedNarrowSubtraction.subValue bits (.simple (.local .here)) (.simple (.local (.there .here)))).evalT tgt with
    | .ok v => some v.val | _ => none
  let q := (x-y) % ((2^bits : Nat) : Int)
  let expected := if q < ((2^(bits-1) : Nat) : Int) then q else q-((2^bits : Nat) : Int)
  sr == some expected && tr == sr

def effectSubtraction (p : Roadmap.Pipeline) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) : Bool :=
  let x := (ty bits valid).wrap (ty bits valid).hi
  let y := (ty bits valid).wrap (-1)
  let hx := (ty bits valid).wrap_mem (ty bits valid).hi
  let hy := (ty bits valid).wrap_mem (-1)
  let src := WordCastControls.source (ty bits valid) x y hx hy
  let tgt := WordCastControls.target (ty bits valid) x y hx hy
  let sr := match (Source.evalE (globals p) {F0 with checked := false} 6
    (.binary .sub (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run src with
    | (.ok (.val v),out) => match v.key,(out.1.get (.there .here)).key,(out.1.get .here).key with
      | some v,some i,some a => some (v,i,a) | _,_,_ => none
    | _ => none
  let tr := match (SignedNarrowSubtraction.assignReadOperand bits p (.there .here) .here).run tgt with
    | .ok (out,.prim v) => some (v.val,(TEnv.get (.there .here) out.st.env).val,(TEnv.get .here out.st.env).val)
    | _ => none
  let q := (x-(if p = .legacy then y else x)) % ((2^bits : Nat) : Int)
  let expected := if q < ((2^(bits-1) : Nat) : Int) then q else q-((2^bits : Nat) : Int)
  sr == some (expected,x,x) && tr == sr

def sourceSubtraction (p : Roadmap.Pipeline) (checked : Bool := false) : Option (Int × Int × Int) :=
  match (Source.evalE (globals p) {F0 with checked := checked} 6
    (.binary .sub (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run source with
  | (.ok (.val v),out) => match v.key,(out.1.get (.there .here)).key,(out.1.get .here).key with
    | some v,some i,some a => some (v,i,a) | _,_,_ => none
  | _ => none

def targetSubtraction (p : Roadmap.Pipeline) : Option (Int × Int × Int) :=
  match (SignedNarrowSubtraction.assignReadOperand 8 p (.there .here) .here).run target with
  | .ok (out,.prim v) => some (v.val,(TEnv.get (.there .here) out.st.env).val,(TEnv.get .here out.st.env).val)
  | _ => none

namespace Multiplication
open SignedNarrowMultiplication
def source_value := source_mul_unchecked 8 (by decide) (D := E.layout) 127 (-1) (by decide) (by decide)
def target_value := mul_value_run 8 (by decide) target (.simple (.local .here)) (.simple (.local (.there .here)))
  127 (-1) (by decide) (by decide) rfl rfl
def pair (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_from_pair 8 (by decide) (globals p) F0 (fuel+2) source source (.local .here) (.local (.there .here))
    127 (-1) (by decide) (by decide)
    (source_local_pair (globals p) {F0 with checked := false} fuel source (ty 8 (by decide)) .here (.there .here)
      127 (-1) (by decide) (by decide) rfl rfl)
def source_locals (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_locals_run 8 (by decide) (globals p) F0 fuel source .here (.there .here)
    127 (-1) (by decide) (by decide) rfl rfl
def locals (p : Roadmap.Pipeline) (fuel : Nat) :=
  locals_transport 8 (by decide) (globals p) F0 fuel source target si ti initial true false
    127 (-1) (by decide) (by decide) rfl rfl
def source_assignment (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_assign_read_run 8 (by decide) (globals p) F0 fuel source (.there .here) .here
    127 (-1) (by decide) (by decide) rfl rfl
def target_assignment (p : Roadmap.Pipeline) :=
  assign_read_operand_run 8 (by decide) p target (.there .here) .here
    127 (-1) (by decide) (by decide) rfl rfl
def assignment (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport 8 (by decide) (globals p) F0 fuel source target si ti initial false true
    127 (-1) (by decide) (by decide) rfl rfl
def extension (p : Roadmap.Pipeline) :=
  assignment_extension 8 (by decide) p target (.there .here) .here
    127 (-1) (by decide) (by decide) rfl rfl (Thin.drop (t := .val .bool) .refl) (true,target.env)

-- Same-slot/repeated selected aliases and distinct equal-content locals.
example (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport 8 (by decide) (globals p) F0 fuel source target
    (fun _ : Bool => si true) (fun _ : Bool => ti true) (initial.reindex (fun _ : Bool => true))
    false true 127 127 (by decide) (by decide) rfl rfl
example (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport 8 (by decide) (globals p) F0 fuel
    (WordCastControls.source (ty 8 (by decide)) 127 127 (by decide) (by decide))
    (WordCastControls.target (ty 8 (by decide)) 127 127 (by decide) (by decide)) si ti
    (WordCastControls.initial (ty 8 (by decide)) 127 127 (by decide) (by decide))
    false true 127 127 (by decide) (by decide) rfl rfl
end Multiplication

def checkMultiplication (p : Roadmap.Pipeline) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (inputX inputY : Int) : Bool :=
  let x := (ty bits valid).wrap inputX
  let y := (ty bits valid).wrap inputY
  let hx := (ty bits valid).wrap_mem inputX
  let hy := (ty bits valid).wrap_mem inputY
  let src := WordCastControls.source (ty bits valid) x y hx hy
  let tgt := WordCastControls.target (ty bits valid) x y hx hy
  let sr := match (Source.evalE (globals p) {F0 with checked := false} 6
    (.binary .mul (.local .here) (.local (.there .here)))).run src with
    | (.ok (.val v),_) => v.key | _ => none
  let tr := match (SignedNarrowMultiplication.mulValue bits (.simple (.local .here)) (.simple (.local (.there .here)))).evalT tgt with
    | .ok v => some v.val | _ => none
  let q := (x*y) % ((2^bits : Nat) : Int)
  let expected := if q < ((2^(bits-1) : Nat) : Int) then q else q-((2^bits : Nat) : Int)
  sr == some expected && tr == sr

def effectMultiplication (p : Roadmap.Pipeline) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) : Bool :=
  let x := (ty bits valid).wrap (ty bits valid).hi
  let y := (ty bits valid).wrap (-1)
  let hx := (ty bits valid).wrap_mem (ty bits valid).hi
  let hy := (ty bits valid).wrap_mem (-1)
  let src := WordCastControls.source (ty bits valid) x y hx hy
  let tgt := WordCastControls.target (ty bits valid) x y hx hy
  let sr := match (Source.evalE (globals p) {F0 with checked := false} 6
    (.binary .mul (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run src with
    | (.ok (.val v),out) => match v.key,(out.1.get (.there .here)).key,(out.1.get .here).key with
      | some v,some i,some a => some (v,i,a) | _,_,_ => none
    | _ => none
  let tr := match (SignedNarrowMultiplication.assignReadOperand bits p (.there .here) .here).run tgt with
    | .ok (out,.prim v) => some (v.val,(TEnv.get (.there .here) out.st.env).val,(TEnv.get .here out.st.env).val)
    | _ => none
  let q := (x*(if p = .legacy then y else x)) % ((2^bits : Nat) : Int)
  let expected := if q < ((2^(bits-1) : Nat) : Int) then q else q-((2^bits : Nat) : Int)
  sr == some (expected,x,x) && tr == sr

def sourceMultiplication (p : Roadmap.Pipeline) (checked : Bool := false) : Option (Int × Int × Int) :=
  match (Source.evalE (globals p) {F0 with checked := checked} 6
    (.binary .mul (.assign (.local (.there .here)) (.local .here)) (.local (.there .here)))).run source with
  | (.ok (.val v),out) => match v.key,(out.1.get (.there .here)).key,(out.1.get .here).key with
    | some v,some i,some a => some (v,i,a) | _,_,_ => none
  | _ => none

def targetMultiplication (p : Roadmap.Pipeline) : Option (Int × Int × Int) :=
  match (SignedNarrowMultiplication.assignReadOperand 8 p (.there .here) .here).run target with
  | .ok (out,.prim v) => some (v.val,(TEnv.get (.there .here) out.st.env).val,(TEnv.get .here out.st.env).val)
  | _ => none

--2pipelines×32widths×12source-wrapped input pairs×3ops=2,304 pure cases;
--2pipelines×32widths×3ops=192 actual effectful cases. Not constant admission.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p => (List.finRange 32).all fun i =>
  let bits := 8*(i.val+1)
  have valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 := by omega
  let lo := (ty bits valid).lo
  let hi := (ty bits valid).hi
  [(hi,1),(lo,1),(lo,-1),(hi,hi),(lo,lo),(-1,-1),(0,0),(127,1),(128,-1),(-129,2),(5,2),(lo,2)].all
    (fun (x,y) => checkAddition p bits valid x y && checkSubtraction p bits valid x y &&
      checkMultiplication p bits valid x y) && effectAddition p bits valid &&
      effectSubtraction p bits valid && effectMultiplication p bits valid))

/-- info: [some (126, 127, 127),
 some (-2, 127, 127),
 some (126, 127, 127),
 some (-2, 127, 127),
 some (-128, 127, 127),
 some (0, 127, 127),
 some (-128, 127, 127),
 some (0, 127, 127),
 some (-127, 127, 127),
 some (1, 127, 127),
 some (-127, 127, 127),
 some (1, 127, 127)] -/
#guard_msgs in
#eval IO.println (reprStr [sourceAddition .legacy,sourceAddition .viaIR,targetAddition .legacy,targetAddition .viaIR,
  sourceSubtraction .legacy,sourceSubtraction .viaIR,targetSubtraction .legacy,targetSubtraction .viaIR,
  sourceMultiplication .legacy,sourceMultiplication .viaIR,targetMultiplication .legacy,targetMultiplication .viaIR])

-- Checked-overflow classification only; these are not failure-payload transports.
/-- info: [true, false, false, true, true, false] -/
#guard_msgs in
#eval IO.println (reprStr [(sourceAddition .legacy true).isSome,(sourceAddition .viaIR true).isSome,
  (sourceSubtraction .legacy true).isSome,(sourceSubtraction .viaIR true).isSome,
  (sourceMultiplication .legacy true).isSome,(sourceMultiplication .viaIR true).isSome])

def sourceCapture (p : Roadmap.Pipeline) : Option (Int × Int × Int) :=
  match (Source.evalPair (globals p) {F0 with checked := false} 6
    (.assign (.local (.there .here)) (.local .here)) (.local (.there .here))).run source with
  | (.ok (.val x,.val y),out) => match x.key,y.key,(out.1.get (.there .here)).key with
    | some x,some y,some i => some (x,y,i) | _,_,_ => none
  | _ => none

def targetCapture (p : Roadmap.Pipeline) : Option (Int × Int × Int) :=
  match (assignReadPrefix p (.there .here) .here).run target with
  | .ok out =>
    let left : Idx [.val .int,.val .int,.val .int,.val .int,.mem bytesR,.alias bytesR] (.val .int) :=
      match p with | .legacy => .here | .viaIR => .there .here
    let right : Idx [.val .int,.val .int,.val .int,.val .int,.mem bytesR,.alias bytesR] (.val .int) :=
      match p with | .legacy => .there .here | .viaIR => .here
    some ((TEnv.get left out.st.env).val,(TEnv.get right out.st.env).val,
      (TEnv.get (.there (.there (.there .here))) out.st.env).val)
  | _ => none
/-- info: [some (127, -1, 127), some (127, 127, 127), some (127, -1, 127), some (127, 127, 127)] -/
#guard_msgs in
#eval IO.println (reprStr [sourceCapture .legacy,sourceCapture .viaIR,targetCapture .legacy,targetCapture .viaIR])

-- Wrong unsigned cleaning loses the destination sign; omitting narrowing loses overflow.
/-- info: [some 128, some (-128), some 254, some (-2), some 16129, some 1] -/
#guard_msgs in
#eval IO.println (reprStr [
  match (Val.unop .toInt rfl rfl (UnsignedCasts.castValue 8 (.unop .toUint rfl rfl
      (SignedWordSubtraction.subValue (.simple (.local .here)) (.simple (.local (.there .here))))))).evalT target with
    | .ok v => some v.val | _ => none,
  match (SignedNarrowSubtraction.subValue 8 (.simple (.local .here)) (.simple (.local (.there .here)))).evalT target with
    | .ok v => some v.val | _ => none,
  match (SignedWordAddition.addValue (.simple (.local .here)) (.simple (.local .here))).evalT target with
    | .ok v => some v.val | _ => none,
  match (SignedNarrowAddition.addValue 8 (.simple (.local .here)) (.simple (.local .here))).evalT target with
    | .ok v => some v.val | _ => none,
  match (SignedWordMultiplication.mulValue (.simple (.local .here)) (.simple (.local .here))).evalT target with
    | .ok v => some v.val | _ => none,
  match (SignedNarrowMultiplication.mulValue 8 (.simple (.local .here)) (.simple (.local .here))).evalT target with
    | .ok v => some v.val | _ => none])

def orderTarget := WordCastControls.target (ty 8 (by decide)) 5 2 (by decide) (by decide)
-- Values avoid the ±128 congruence coincidence: swapping semantic operands must fail.
/-- info: [some (-3), some 0, some 0, some 3] -/
#guard_msgs in
#eval IO.println (reprStr [
  match (assignReadPrefix .legacy (.there .here) .here).run orderTarget with
    | .ok out => match (SignedNarrowSubtraction.subValue 8 (.simple (.local (.there .here)))
        (.simple (.local .here))).evalT out.st with | .ok v => some v.val | _ => none
    | _ => none,
  match (assignReadPrefix .legacy (.there .here) .here).run orderTarget with
    | .ok out => match (SignedNarrowSubtraction.subValue 8 (.simple (.local (.there .here)))
        (.simple (.local (.there .here)))).evalT out.st with | .ok v => some v.val | _ => none
    | _ => none,
  match (assignLocalOperand (.there .here) .here).run orderTarget with
    | .ok (out,_) => match (SignedNarrowSubtraction.subValue 8 (.simple (.local .here))
        (.simple (.local (.there .here)))).evalT out.st with | .ok v => some v.val | _ => none
    | _ => none,
  match (SignedNarrowSubtraction.assignReadOperand 8 .legacy (.there .here) .here).run orderTarget with
    | .ok (_,.prim v) => some v.val | _ => none])

-- Initial-state pure evaluation gets the arithmetic value but misses the write.
/-- info: [some (3, 2), some (3, 5)] -/
#guard_msgs in
#eval IO.println (reprStr [
  match (SignedNarrowSubtraction.subValue 8 (.simple (.local .here)) (.simple (.local (.there .here)))).evalT orderTarget with
    | .ok v => some (v.val,(TEnv.get (.there .here) orderTarget.env).val) | _ => none,
  match (SignedNarrowSubtraction.assignReadOperand 8 .legacy (.there .here) .here).run orderTarget with
    | .ok (out,.prim v) => some (v.val,(TEnv.get (.there .here) out.st.env).val) | _ => none])

-- Equal contents do not justify collapsing distinct selected identities.
example : ¬ IntegerLocalFamily (ty 8 (by decide)) si (fun _ : Bool => ti true)
    (WordCastControls.source (ty 8 (by decide)) 127 127 (by decide) (by decide)).1
    (WordCastControls.target (ty 8 (by decide)) 127 127 (by decide) (by decide)).env := by
  intro h
  have bad : (si true).toNat = (si false).toNat := (h.aliases true false).mpr rfl
  exact (by decide : (si true).toNat ≠ (si false).toNat) bad

def out := target.setLocal (.there .here) (integerValue (ty 8 (by decide)) 127 (by decide))
example : out.heap = target.heap ∧ out.glob = target.glob ∧
    TEnv.get (.there (.there .here)) out.env = TEnv.get (.there (.there .here)) target.env ∧
    TEnv.get (.there (.there (.there .here))) out.env = some storageRef := ⟨rfl,rfl,rfl,rfl⟩
example : ∃ r : HRef target.H bytesR,
    TEnv.get (.there (.there .here)) target.env = some r ∧ target.heap.len r .dyn = 2 :=
  MixedAssignmentControls.live_memory

end Solidity.Lowering.V07.SignedNarrowArithmeticControls
