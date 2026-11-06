import Solidity.Lowering.V07.IntegerConstants
import Solidity.Lowering.V07.P12Controls
import Solidity.Lowering.V07.UnsignedCasts

namespace Solidity.Lowering.V07.IntegerConstantControls
open IntegerConstants Source.SemanticsExamples
open MixedAssignmentControls (C E globals path)
abbrev SrcCtx : Source.RCtx := [.bytes .memory,.bytes .storage]
def source : Source.EMState E SrcCtx :=
  (.cons (.memRef rfl 0) (.cons (.storRef rfl path) .nil),
    {s0 with heap := ((Source.Heap.empty : Source.Heap E.layout).alloc ⟨.bytes .memory,.bytes [0,0]⟩).1})
def target := MixedAssignmentControls.memory

def fits_client (t : Source.IntTy) (z : Int) (h : t.lo ≤ z ∧ z ≤ t.hi) := fits t z h
def allowed_client (t : Source.IntTy) (z : Int) (h : t.lo ≤ z ∧ z ≤ t.hi) := allowed E t z h
def source_value_client (t : Source.IntTy) (z : Int) (h : t.lo ≤ z ∧ z ≤ t.hi) := source_value (D := E.layout) t z h
def source_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat)
    (t : Source.IntTy) (z : Int) (h : t.lo ≤ z ∧ z ≤ t.hi) :=
  source_run (globals p) {F0 with checked := checked} fuel source t z h
def value_client (t : Source.IntTy) (z : Int) (h : t.lo ≤ z ∧ z ≤ t.hi) := value_run target t z h
def code_client (t : Source.IntTy) (z : Int) (h : t.lo ≤ z ∧ z ≤ t.hi) := code_run target t z h
def operand_client (t : Source.IntTy) (z : Int) (h : t.lo ≤ z ∧ z ≤ t.hi) := operand_run target t z h
def transport_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat)
    (t : Source.IntTy) (z : Int) (h : t.lo ≤ z ∧ z ≤ t.hi) :=
  transport (globals p) {F0 with checked := checked} fuel source target t z h
def refused_client := source_refused (D := E.layout) .u8 256 (by decide)
def not_allowed_client := not_allowed E .u8 256 (by decide)
def extension_client := DeferredSource.Operand.run_wk
  (operand .u8 7 (by decide) : DeferredSource.Operand C [.mem bytesR,.alias bytesR] (.prim .uint))
  (Thin.drop (t := .val .bool) Thin.refl) target (true,target.env)
def pass_client : (code (C := C) (Γ := [.mem bytesR,.alias bytesR]) .u8 7 (by decide)).withPanics =
    code .u8 7 (by decide) := by
  rfl

def check (p : Roadmap.Pipeline) (checked : Bool) (t : Source.IntTy) (z : Int) : Bool :=
  if h : t.lo ≤ z ∧ z ≤ t.hi then
    match (Source.evalE (globals p) {F0 with checked := checked} 2
        (.conv (.const (Source.Q.ofInt z)) (.inl (allowed E t z h)))).run source,
        (operand t z h).run target,(code t z h).run target with
    | (.ok (.val v),post),.ok (out,.prim r),.ok cap =>
        v.key == some z && PrimTy.num? r == some z &&
        PrimTy.num? (TEnv.get .here cap.st.env) == some z &&
        (match post.1.get .here with | .memRef _ address => address == 0 | _ => false) &&
        (match post.1.get (.there .here) with | .storRef _ p => p == path | _ => false) &&
        (TEnv.get .here out.st.env).map HRef.id == (TEnv.get .here target.env).map HRef.id &&
        (TEnv.get (.there .here) out.st.env).map (fun r => r.root) ==
          (TEnv.get (.there .here) target.env).map (fun r => r.root) &&
        (TEnv.get (.there .here) cap.st.env).map HRef.id == (TEnv.get .here target.env).map HRef.id &&
        (TEnv.get (.there (.there .here)) cap.st.env).map (fun r => r.root) ==
          (TEnv.get (.there .here) target.env).map (fun r => r.root)
    | _,_,_ => false
  else false

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ((List.range 257).all fun bits =>
  if width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 then [false,true].all fun sign =>
    let t : Source.IntTy := ⟨sign,bits,width⟩
    [Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
      [0,1,t.lo,t.hi].all fun z => check p checked t z
  else true))

-- Implicit literal conversion refuses out-of-range input; wrong unchecked truncation executes to zero.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  match Source.constVal (Source.Q.ofInt 256) (.int .u8) (D := E.layout),
      (UnsignedCasts.castValue 8 (value .u256 256 (by decide))).evalT target with
  | .error (.stuck why),.ok wrong => why == "integer out of range" && wrong.val == 0 &&
      !(Source.STy.rational (Source.Q.ofInt 256)).implicit E.isBase E.mapFree (.int .u8)
  | _,_ => false))

-- Fractional Source constants do not become integer one by silently truncating.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  let q : Source.Q := ⟨3,2,by decide⟩
  match Source.constVal q (.int .u8) (D := E.layout),(operand .u8 1 (by decide)).run target with
  | .error (.stuck why),.ok (_,.prim wrong) => why == "fractional constant at an integer type" && wrong.val == 1 &&
      !(Source.STy.rational q).implicit E.isBase E.mapFree (.int .u8)
  | _,_ => false))

-- Signed literal minus one is not the unsigned bit-pattern literal 255.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  let t : Source.IntTy := ⟨true,8,by decide⟩
  match (operand t (-1) (by decide)).run target,(operand .u8 255 (by decide)).run target with
  | .ok (_,.prim signed),.ok (_,.prim unsigned) => PrimTy.num? signed == some (-1) && unsigned.val == 255
  | _,_ => false))
/-- info: 'Solidity.Lowering.V07.IntegerConstantControls.fits_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantControls.fits_client

/-- info: 'Solidity.Lowering.V07.IntegerConstantControls.allowed_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantControls.allowed_client

/-- info: 'Solidity.Lowering.V07.IntegerConstantControls.source_value_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantControls.source_value_client

/-- info: 'Solidity.Lowering.V07.IntegerConstantControls.source_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantControls.source_client

/-- info: 'Solidity.Lowering.V07.IntegerConstantControls.value_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantControls.value_client

/-- info: 'Solidity.Lowering.V07.IntegerConstantControls.code_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantControls.code_client

/-- info: 'Solidity.Lowering.V07.IntegerConstantControls.operand_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantControls.operand_client

/-- info: 'Solidity.Lowering.V07.IntegerConstantControls.transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantControls.transport_client

/-- info: 'Solidity.Lowering.V07.IntegerConstantControls.refused_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantControls.refused_client

/-- info: 'Solidity.Lowering.V07.IntegerConstantControls.not_allowed_client' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantControls.not_allowed_client

/-- info: 'Solidity.Lowering.V07.IntegerConstantControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantControls.extension_client

/-- info: 'Solidity.Lowering.V07.IntegerConstantControls.pass_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantControls.pass_client

end Solidity.Lowering.V07.IntegerConstantControls
