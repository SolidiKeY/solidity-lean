import Solidity.Lowering.V07.UnsignedQuotRemGuard
import Solidity.Lowering.V07.UnsignedQuotRemControls

namespace Solidity.Lowering.V07.UnsignedQuotRemGuardControls
open UnsignedQuotRemGuard
open UnsignedNarrowing (ty)
open UnsignedQuotRem (calculate sourceOp)
open UnsignedQuotRemControls (t src tgt zeroSrc zeroTgt)
open Source.SemanticsExamples
open MixedAssignmentControls (C E globals)

def metadata_client (rem : Bool) := metadata_condition (C := C) rem
  (.there .here : Idx _ (.val .uint)) (Γ := [.val .uint,.val .uint,.mem bytesR,.alias bytesR])
def condition_client := condition_run tgt (.there .here) (integerValue t 5 (by decide)) rfl
def guard_client := guard_success tgt (.there .here) (integerValue t 5 (by decide)) rfl (by decide)
def guard_zero_client := guard_zero zeroTgt (.there .here) (integerValue t 0 (by decide)) rfl rfl

def code_client (rem : Bool) := code_success 8 (by decide) tgt rem .here (.there .here)
  17 5 (by decide) (by decide) (by decide) rfl rfl
def code_zero_client (rem : Bool) := code_zero zeroTgt rem .here (.there .here)
  (integerValue t 0 (by decide)) rfl rfl
def operand_client (rem : Bool) := operand_success 8 (by decide) tgt rem .here (.there .here)
  17 5 (by decide) (by decide) (by decide) rfl rfl
def operand_zero_client (rem : Bool) := operand_zero zeroTgt rem .here (.there .here)
  (integerValue t 0 (by decide)) rfl rfl

def locals_client (p : Roadmap.Pipeline) (checked rem : Bool) (fuel : Nat) :=
  locals_success 8 (by decide) (globals p) {F0 with checked := checked} fuel src tgt rem
    (WordCastControls.si t) (WordCastControls.ti t)
    (WordCastControls.initial t 17 5 (by decide) (by decide)) true false 17 5
    (by decide) (by decide) (by decide) rfl rfl

def locals_zero_client (p : Roadmap.Pipeline) (checked rem : Bool) (fuel : Nat) :=
  locals_zero 8 (by decide) (globals p) {F0 with checked := checked} fuel zeroSrc zeroTgt rem
    (WordCastControls.si t) (WordCastControls.ti t)
    (WordCastControls.initial t 17 0 (by decide) (by decide)) true false 17 (by decide) rfl rfl

def failure_observation_client (p : Roadmap.Pipeline) (checked rem : Bool) :=
  (locals_zero_client p checked rem 0).2.2

def repeated_client (p : Roadmap.Pipeline) (checked rem : Bool) (fuel : Nat) :=
  locals_success 8 (by decide) (globals p) {F0 with checked := checked} fuel src tgt rem
    (fun _ : Bool => WordCastControls.si t true) (fun _ : Bool => WordCastControls.ti t true)
    ((WordCastControls.initial t 17 5 (by decide) (by decide)).reindex (fun _ : Bool => true))
    true false 17 17 (by decide) (by decide) (by decide) rfl rfl

def equal_content_client (p : Roadmap.Pipeline) (checked rem : Bool) (fuel : Nat) :=
  locals_success 8 (by decide) (globals p) {F0 with checked := checked} fuel
    (WordCastControls.source t 17 17 (by decide) (by decide))
    (WordCastControls.target t 17 17 (by decide) (by decide)) rem
    (WordCastControls.si t) (WordCastControls.ti t)
    (WordCastControls.initial t 17 17 (by decide) (by decide)) true false 17 17
    (by decide) (by decide) (by decide) rfl rfl

def extension_client (rem : Bool) := DeferredSource.Operand.run_wk
  (operand rem .here (.there .here)) (Thin.drop (t := .val .bool) Thin.refl) tgt (true,tgt.env)

def binder_client (p : Roadmap.Pipeline) (checked rem : Bool) (fuel : Nat) :=
  locals_success 8 (by decide) (globals p) {F0 with checked := checked} fuel
    (Source.Locals.cons (.bool true) src.1,src.2) (tgt.push (t := .val .bool) true) rem
    (fun k => .there (WordCastControls.si t k)) (fun k => .there (WordCastControls.ti t k))
    ((WordCastControls.initial t 17 5 (by decide) (by decide)).under_binders (u := .val .bool) (.bool true) true)
    true false 17 5 (by decide) (by decide) (by decide) rfl rfl

def live_caller : ∃ r : HRef tgt.H bytesR,
    TEnv.get (.there (.there .here)) tgt.env = some r ∧ tgt.heap.len r .dyn = 2 :=
  MixedAssignmentControls.live_memory

def source_frame_client (p : Roadmap.Pipeline) (checked rem : Bool) :=
  congrArg (fun result => result.2.2) (locals_client p checked rem 0).1

def check (p : Roadmap.Pipeline) (checked rem : Bool) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (a b : Int) : Bool :=
  let x := (ty bits valid).wrap a
  let y := (ty bits valid).wrap b
  let source := WordCastControls.source (ty bits valid) x y ((ty bits valid).wrap_mem a) ((ty bits valid).wrap_mem b)
  let target := WordCastControls.target (ty bits valid) x y ((ty bits valid).wrap_mem a) ((ty bits valid).wrap_mem b)
  let sr := (Source.evalE (globals p) {F0 with checked := checked} 3
    (.binary (sourceOp rem) (.local .here) (.local (.there .here)))).run source
  let tr := (operand rem .here (.there .here)).run target
  let frame := (sr.2.1.get .here).key == some x && (sr.2.1.get (.there .here)).key == some y
  if y = 0 then
    match sr.1,tr with
    | .error (.revert d),.error err => frame && d == Source.panicData .divZero && err.data == d
    | _,_ => false
  else
    match sr.1,tr with
    | .ok (.val v),.ok (out,.prim w) => frame && v.key == some (calculate rem x y) && w.val == calculate rem x y &&
        (TEnv.get .here out.st.env).val == x && (TEnv.get (.there .here) out.st.env).val == y
    | _,_ => false

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
  [false,true].all fun rem => (List.finRange 32).all fun i =>
  let bits := 8*(i.val+1)
  have valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 := by omega
  let hi := (ty bits valid).hi
  [(0,0),(0,1),(hi,1),(hi,hi),(hi,2),(17,5),(1,hi),(5,17),(hi,0)].all fun (a,b) => check p checked rem bits valid a b))

/-- The fresh result is read before the caller locals are restored. -/
def captured (rem : Bool) : Option (Int × Int × Int × Int × Int) := do
  let out ← (code rem .here (.there .here)).run tgt |>.toOption
  let done ← (operand rem .here (.there .here)).run tgt |>.toOption
  let .prim result := done.2
  pure ((TEnv.get .here out.st.env).val,(TEnv.get (.there .here) out.st.env).val,
    (TEnv.get (.there (.there .here)) out.st.env).val,result.val,(TEnv.get .here done.1.st.env).val)

/-- info: [some (3, 17, 5, 3, 17), some (2, 17, 5, 2, 17)] -/
#guard_msgs in
#eval IO.println (reprStr [captured false,captured true])

-- All three actual error paths are inspected for complete bytes, not just their length.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  (match (operand false .here (.there .here)).run zeroTgt with
    | .error err => err.data == Source.panicData .divZero | _ => false) &&
  (match (panicStmt 0x11 (condition (.there .here))).run zeroTgt with
    | .error err => err.data != Source.panicData .divZero && err.data == Source.panicData .arithmetic | _ => false) &&
  (match (UnsignedQuotRem.value false (.simple (.local .here)) (.simple (.local (.there .here)))).evalT zeroTgt with
    | .error err => err.data != Source.panicData .divZero && err.data == [] | _ => false)))

-- Dropping before reading the result returns numerator17, not quotient3.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  (match (code false .here (.there .here)).run tgt with
    | .ok out => (Val.simple (.local .here) : Val C _ .uint).evalT (out.st.drop (code (C := C) false .here (.there .here)).ext) |>.toOption |>.map (·.val)
    | _ => none) == some 17))

end Solidity.Lowering.V07.UnsignedQuotRemGuardControls

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuardControls.metadata_client' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuardControls.metadata_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuardControls.condition_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuardControls.condition_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuardControls.guard_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuardControls.guard_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuardControls.guard_zero_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuardControls.guard_zero_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuardControls.code_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuardControls.code_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuardControls.code_zero_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuardControls.code_zero_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuardControls.operand_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuardControls.operand_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuardControls.operand_zero_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuardControls.operand_zero_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuardControls.locals_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuardControls.locals_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuardControls.locals_zero_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuardControls.locals_zero_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuardControls.failure_observation_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuardControls.failure_observation_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuardControls.repeated_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuardControls.repeated_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuardControls.equal_content_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuardControls.equal_content_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuardControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuardControls.extension_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuardControls.binder_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuardControls.binder_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuardControls.live_caller' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuardControls.live_caller

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemGuardControls.source_frame_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemGuardControls.source_frame_client
