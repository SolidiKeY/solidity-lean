import Solidity.Lowering.V07.UnsignedQuotRem
import Solidity.Lowering.V07.WordCastControls

namespace Solidity.Lowering.V07.UnsignedQuotRemControls
open UnsignedQuotRem
open UnsignedNarrowing (ty)
open Source.SemanticsExamples
open MixedAssignmentControls (C E globals)

def t := ty 8 (by decide)
def src := WordCastControls.source t 17 5 (by decide) (by decide)
def tgt := WordCastControls.target t 17 5 (by decide) (by decide)
def zeroSrc := WordCastControls.source t 17 0 (by decide) (by decide)
def zeroTgt := WordCastControls.target t 17 0 (by decide) (by decide)

def range_client (rem : Bool) := result_range 8 (by decide) rem 17 5 (by decide) (by decide) (by decide)
def source_value_client (checked rem : Bool) := source_value 8 (by decide) (D := E.layout)
  checked rem 17 5 (by decide) (by decide) (by decide)
def source_zero_client (checked rem : Bool) := source_zero 8 (by decide) (D := E.layout)
  checked rem 17 (by decide)
def value_client (rem : Bool) := value_run 8 (by decide) tgt rem
  (.simple (.local .here)) (.simple (.local (.there .here))) 17 5
  (by decide) (by decide) (by decide) rfl rfl
def zero_value_client (rem : Bool) := value_zero 8 (by decide) zeroTgt rem
  (.simple (.local .here)) (.simple (.local (.there .here))) 17 (by decide) rfl rfl

def pair_client (p : Roadmap.Pipeline) (checked rem : Bool) (fuel : Nat) :=
  source_from_pair 8 (by decide) (globals p) {F0 with checked := checked} (fuel+2) src src rem
    (.local .here) (.local (.there .here)) 17 5 (by decide) (by decide) (by decide)
    (source_local_pair (globals p) {F0 with checked := checked} fuel src t .here (.there .here)
      17 5 (by decide) (by decide) rfl rfl)

def pair_zero_client (p : Roadmap.Pipeline) (checked rem : Bool) (fuel : Nat) :=
  source_pair_zero 8 (by decide) (globals p) {F0 with checked := checked} (fuel+2) zeroSrc zeroSrc rem
    (.local .here) (.local (.there .here)) 17 (by decide)
    (source_local_pair (globals p) {F0 with checked := checked} fuel zeroSrc t .here (.there .here)
      17 0 (by decide) (integer_zero_range t) rfl rfl)

def locals_client (p : Roadmap.Pipeline) (checked rem : Bool) (fuel : Nat) :=
  locals_transport 8 (by decide) (globals p) {F0 with checked := checked} fuel src tgt rem
    (WordCastControls.si t) (WordCastControls.ti t)
    (WordCastControls.initial t 17 5 (by decide) (by decide)) true false 17 5
    (by decide) (by decide) (by decide) rfl rfl

def locals_zero_client (p : Roadmap.Pipeline) (checked rem : Bool) (fuel : Nat) :=
  locals_zero 8 (by decide) (globals p) {F0 with checked := checked} fuel zeroSrc zeroTgt rem
    (WordCastControls.si t) (WordCastControls.ti t)
    (WordCastControls.initial t 17 0 (by decide) (by decide)) true false 17 (by decide) rfl rfl

def repeated_client (p : Roadmap.Pipeline) (checked rem : Bool) (fuel : Nat) :=
  locals_transport 8 (by decide) (globals p) {F0 with checked := checked} fuel src tgt rem
    (fun _ : Bool => WordCastControls.si t true) (fun _ : Bool => WordCastControls.ti t true)
    ((WordCastControls.initial t 17 5 (by decide) (by decide)).reindex (fun _ : Bool => true))
    true false 17 17 (by decide) (by decide) (by decide) rfl rfl

def equal_content_client (p : Roadmap.Pipeline) (checked rem : Bool) (fuel : Nat) :=
  locals_transport 8 (by decide) (globals p) {F0 with checked := checked} fuel
    (WordCastControls.source t 17 17 (by decide) (by decide))
    (WordCastControls.target t 17 17 (by decide) (by decide)) rem
    (WordCastControls.si t) (WordCastControls.ti t)
    (WordCastControls.initial t 17 17 (by decide) (by decide)) true false 17 17
    (by decide) (by decide) (by decide) rfl rfl

def extension_client (rem : Bool) := DeferredSource.Operand.run_wk
  (DeferredSource.Operand.ofSrc (Src.val (value rem (.simple (.local .here)) (.simple (.local (.there .here))))))
  (Thin.drop (t := .val .bool) Thin.refl) tgt (true,tgt.env)

def binder_client (p : Roadmap.Pipeline) (checked rem : Bool) (fuel : Nat) :=
  locals_transport 8 (by decide) (globals p) {F0 with checked := checked} fuel
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
  let tr := (value rem (.simple (.local .here)) (.simple (.local (.there .here)))).evalT target
  let frame := (sr.2.1.get .here).key == some x && (sr.2.1.get (.there .here)).key == some y
  if y = 0 then
    match sr.1,tr with
    | .error (.revert d),.error .revert => frame && d == Source.panicData .divZero
    | _,_ => false
  else
    match sr.1,tr with
    | .ok (.val v),.ok w => frame && v.key == some (calculate rem x y) && w.val == calculate rem x y
    | _,_ => false

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
  [false,true].all fun rem => (List.finRange 32).all fun i =>
  let bits := 8*(i.val+1)
  have valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 := by omega
  let hi := (ty bits valid).hi
  [(0,0),(0,1),(hi,1),(hi,hi),(hi,2),(17,5),(1,hi),(5,17),(hi,0)].all fun (a,b) => check p checked rem bits valid a b))

/-- Noncommutative operand positions are preserved even with right-first Source evaluation. -/
def observed (rem reversed : Bool) : Option Int :=
  let a : Val C _ .uint := .simple (.local .here)
  let b : Val C _ .uint := .simple (.local (.there .here))
  match (if reversed then value rem b a else value rem a b).evalT tgt with
  | .ok v => some v.val | _ => none

/-- info: [some 3, some 0, some 2, some 5] -/
#guard_msgs in
#eval IO.println (reprStr [observed false false,observed false true,observed true false,observed true true])

/-- Raw value failures do not preserve Source's panic payload; the guarded
program layer must supply it explicitly. This is not a failure equivalence. -/
def zero_payloads (p : Roadmap.Pipeline) (checked rem : Bool) : Option (Nat × Nat) :=
  match (Source.evalE (globals p) {F0 with checked := checked} 3
    (.binary (sourceOp rem) (.local .here) (.local (.there .here)))).run zeroSrc,
    (value rem (.simple (.local .here)) (.simple (.local (.there .here)))).evalT zeroTgt with
  | (.error (.revert d),_),.error err => some (d.length,err.data.length)
  | _,_ => none

/-- info: [some (36, 0), some (36, 0), some (36, 0), some (36, 0)] -/
#guard_msgs in
#eval IO.println (reprStr [zero_payloads .legacy false false,zero_payloads .viaIR true false,
  zero_payloads .legacy true true,zero_payloads .viaIR false true])

end Solidity.Lowering.V07.UnsignedQuotRemControls

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemControls.range_client' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemControls.range_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemControls.source_value_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemControls.source_value_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemControls.source_zero_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemControls.source_zero_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemControls.value_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemControls.value_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemControls.zero_value_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemControls.zero_value_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemControls.pair_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemControls.pair_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemControls.pair_zero_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemControls.pair_zero_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemControls.locals_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemControls.locals_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemControls.locals_zero_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemControls.locals_zero_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemControls.repeated_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemControls.repeated_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemControls.equal_content_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemControls.equal_content_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemControls.extension_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemControls.binder_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemControls.binder_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemControls.live_caller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemControls.live_caller

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemControls.source_frame_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemControls.source_frame_client
