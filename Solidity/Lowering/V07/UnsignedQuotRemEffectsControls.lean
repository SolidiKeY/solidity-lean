import Solidity.Lowering.V07.UnsignedQuotRemEffects
import Solidity.Lowering.V07.WordCastControls

namespace Solidity.Lowering.V07.UnsignedQuotRemEffectsControls
open UnsignedQuotRemEffects
open UnsignedQuotRem (calculate sourceOp)
open UnsignedNarrowing (ty)
open Source.SemanticsExamples
open MixedAssignmentControls (C E globals)

def t := ty 8 (by decide)
def src := WordCastControls.source t 5 17 (by decide) (by decide)
def tgt := WordCastControls.target t 5 17 (by decide) (by decide)
def zlSrc := WordCastControls.source t 0 17 (by decide) (by decide)
def zlTgt := WordCastControls.target t 0 17 (by decide) (by decide)
def zvSrc := WordCastControls.source t 5 0 (by decide) (by decide)
def zvTgt := WordCastControls.target t 5 0 (by decide) (by decide)

def range_client (p : Roadmap.Pipeline) := divisor_range p t 17 5 (by decide) (by decide)
def source_client (p : Roadmap.Pipeline) (checked rem : Bool) (fuel : Nat) :=
  source_success 8 (by decide) (globals p) {F0 with checked := checked} fuel src rem .here (.there .here)
    17 5 (by decide) (by decide) (by cases p <;> decide) rfl rfl

def source_zero_legacy_client (checked rem : Bool) (fuel : Nat) :=
  source_zero 8 (by decide) (globals .legacy) {F0 with checked := checked} fuel zlSrc rem .here (.there .here)
    17 0 (by decide) (by decide) rfl rfl rfl

def source_zero_viaIR_client (checked rem : Bool) (fuel : Nat) :=
  source_zero 8 (by decide) (globals .viaIR) {F0 with checked := checked} fuel zvSrc rem .here (.there .here)
    0 5 (by decide) (by decide) rfl rfl rfl

def prefix_client (p : Roadmap.Pipeline) := prefix_run 8 (by decide) tgt p .here (.there .here)
  17 5 (by decide) (by decide) rfl rfl

def code_client (p : Roadmap.Pipeline) (rem : Bool) := code_success 8 (by decide) tgt p rem .here (.there .here)
  17 5 (by decide) (by decide) (by cases p <;> decide) rfl rfl

def code_zero_legacy_client (rem : Bool) := code_zero 8 (by decide) zlTgt .legacy rem .here (.there .here)
  17 0 (by decide) (by decide) rfl rfl rfl

def code_zero_viaIR_client (rem : Bool) := code_zero 8 (by decide) zvTgt .viaIR rem .here (.there .here)
  0 5 (by decide) (by decide) rfl rfl rfl

def operand_client (p : Roadmap.Pipeline) (rem : Bool) := operand_success 8 (by decide) tgt p rem .here (.there .here)
  17 5 (by decide) (by decide) (by cases p <;> decide) rfl rfl

def operand_zero_legacy_client (rem : Bool) := operand_zero 8 (by decide) zlTgt .legacy rem .here (.there .here)
  17 0 (by decide) (by decide) rfl rfl rfl

def operand_zero_viaIR_client (rem : Bool) := operand_zero 8 (by decide) zvTgt .viaIR rem .here (.there .here)
  0 5 (by decide) (by decide) rfl rfl rfl

def transport_client (p : Roadmap.Pipeline) (checked rem : Bool) (fuel : Nat) :=
  transport_success 8 (by decide) (globals p) {F0 with checked := checked} fuel src tgt rem
    (WordCastControls.si t) (WordCastControls.ti t) (WordCastControls.initial t 5 17 (by decide) (by decide))
    true false 17 5 (by decide) (by decide) (by cases p <;> decide) rfl rfl

def zero_legacy_client (checked rem : Bool) (fuel : Nat) :=
  transport_zero 8 (by decide) (globals .legacy) {F0 with checked := checked} fuel zlSrc zlTgt rem
    (WordCastControls.si t) (WordCastControls.ti t) (WordCastControls.initial t 0 17 (by decide) (by decide))
    true false 17 0 (by decide) (by decide) rfl rfl rfl

def zero_viaIR_client (checked rem : Bool) (fuel : Nat) :=
  transport_zero 8 (by decide) (globals .viaIR) {F0 with checked := checked} fuel zvSrc zvTgt rem
    (WordCastControls.si t) (WordCastControls.ti t) (WordCastControls.initial t 5 0 (by decide) (by decide))
    true false 0 5 (by decide) (by decide) rfl rfl rfl

def repeated_client (p : Roadmap.Pipeline) (checked rem : Bool) (fuel : Nat) :=
  transport_success 8 (by decide) (globals p) {F0 with checked := checked} fuel src tgt rem
    (fun k : Fin 3 => WordCastControls.si t (decide (k.val ≠ 1)))
    (fun k : Fin 3 => WordCastControls.ti t (decide (k.val ≠ 1)))
    ((WordCastControls.initial t 5 17 (by decide) (by decide)).reindex (fun k : Fin 3 => decide (k.val ≠ 1)))
    0 1 17 5 (by decide) (by decide) (by cases p <;> decide) rfl rfl

def self_alias_client (p : Roadmap.Pipeline) (checked rem : Bool) (fuel : Nat) :=
  transport_success 8 (by decide) (globals p) {F0 with checked := checked} fuel
    (WordCastControls.source t 17 17 (by decide) (by decide))
    (WordCastControls.target t 17 17 (by decide) (by decide)) rem
    (WordCastControls.si t) (WordCastControls.ti t) (WordCastControls.initial t 17 17 (by decide) (by decide))
    true true 17 17 (by decide) (by decide) (by cases p <;> decide) rfl rfl

def equal_content_client (p : Roadmap.Pipeline) (checked rem : Bool) (fuel : Nat) :=
  transport_success 8 (by decide) (globals p) {F0 with checked := checked} fuel
    (WordCastControls.source t 17 17 (by decide) (by decide))
    (WordCastControls.target t 17 17 (by decide) (by decide)) rem
    (WordCastControls.si t) (WordCastControls.ti t) (WordCastControls.initial t 17 17 (by decide) (by decide))
    true false 17 17 (by decide) (by decide) (by cases p <;> decide) rfl rfl

def extension_client (p : Roadmap.Pipeline) (rem : Bool) := DeferredSource.Operand.run_wk
  (operand p rem .here (.there .here)) (Thin.drop (t := .val .bool) Thin.refl) tgt (true,tgt.env)

def binder_client (p : Roadmap.Pipeline) (checked rem : Bool) (fuel : Nat) :=
  transport_success 8 (by decide) (globals p) {F0 with checked := checked} fuel
    (Source.Locals.cons (.bool true) src.1,src.2) (tgt.push (t := .val .bool) true) rem
    (fun k => .there (WordCastControls.si t k)) (fun k => .there (WordCastControls.ti t k))
    ((WordCastControls.initial t 5 17 (by decide) (by decide)).under_binders (u := .val .bool) (.bool true) true)
    true false 17 5 (by decide) (by decide) (by cases p <;> decide) rfl rfl

def live_caller : ∃ r : HRef tgt.H bytesR,
    TEnv.get (.there (.there .here)) tgt.env = some r ∧ tgt.heap.len r .dyn = 2 :=
  MixedAssignmentControls.live_memory

def source_frame_client (p : Roadmap.Pipeline) (checked rem : Bool) :=
  congrArg (fun result => result.2.2) (transport_client p checked rem 0).1

def check (p : Roadmap.Pipeline) (checked rem : Bool) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (assigned old : Int) : Bool :=
  let x := (ty bits valid).wrap assigned
  let y := (ty bits valid).wrap old
  let source := WordCastControls.source (ty bits valid) y x ((ty bits valid).wrap_mem old) ((ty bits valid).wrap_mem assigned)
  let target := WordCastControls.target (ty bits valid) y x ((ty bits valid).wrap_mem old) ((ty bits valid).wrap_mem assigned)
  let d := divisor p x y
  let sr := (Source.evalE (globals p) {F0 with checked := checked} 4
    (.binary (sourceOp rem) (.assign (.local .here) (.local (.there .here))) (.local .here))).run source
  let tr := (operand p rem .here (.there .here)).run target
  let prefixFrame := match (assignReadPrefix p (.here : Idx _ (.val .uint)) (.there .here)).run target with
    | .ok out => (TEnv.get .here out.st.env).val == x && (TEnv.get (.there .here) out.st.env).val == d &&
        (TEnv.get (.there (.there .here)) out.st.env).val == x &&
        (TEnv.get (.there (.there (.there .here))) out.st.env).val == x
    | _ => false
  let frame := prefixFrame && (sr.2.1.get .here).key == some x && (sr.2.1.get (.there .here)).key == some x
  if d = 0 then
    match sr.1,tr with
    | .error (.revert bytes),.error err => frame && bytes == Source.panicData .divZero && err.data == bytes
    | _,_ => false
  else
    match sr.1,tr with
    | .ok (.val v),.ok (out,.prim w) => frame && v.key == some (calculate rem x d) && w.val == calculate rem x d &&
        (TEnv.get .here out.st.env).val == x && (TEnv.get (.there .here) out.st.env).val == x
    | _,_ => false

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
  [false,true].all fun rem => (List.finRange 32).all fun i =>
  let bits := 8*(i.val+1)
  have valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 := by omega
  let hi := (ty bits valid).hi
  [(0,0),(0,1),(hi,1),(hi,hi),(hi,2),(17,5),(1,hi),(5,17),(hi,0)].all fun (x,y) => check p checked rem bits valid x y))

private instance : BEq (Except (List UInt8) Int) where
  beq a b := match a, b with
    | .ok x, .ok y => x == y
    | .error x, .error y => x == y
    | _, _ => false

-- std Except/tuples here are observations of actual runs, not an execution layer.
def source_observed (p : Roadmap.Pipeline) (checked rem : Bool) (old assigned : Int)
    (hy : t.lo ≤ old ∧ old ≤ t.hi) (hx : t.lo ≤ assigned ∧ assigned ≤ t.hi) :
    Option (Except (List UInt8) Int × Int × Int) :=
  let source := WordCastControls.source t old assigned hy hx
  let (result,out) := (Source.evalE (globals p) {F0 with checked := checked} 4
    (.binary (sourceOp rem) (.assign (.local .here) (.local (.there .here))) (.local .here))).run source
  match result with
  | .ok (.val v) => do pure (.ok (← v.key),← (out.1.get .here).key,← (out.1.get (.there .here)).key)
  | .error (.revert bytes) => do pure (.error bytes,← (out.1.get .here).key,← (out.1.get (.there .here)).key)
  | _ => none

def target_observed (p : Roadmap.Pipeline) (rem : Bool) : Option (Int × Int × Int × Int × Int) := do
  let out ← (code p rem .here (.there .here)).run tgt |>.toOption
  let done ← (operand p rem .here (.there .here)).run tgt |>.toOption
  let .prim result := done.2
  pure ((TEnv.get (.there .here) out.st.env).val,
    (TEnv.get (.there (.there .here)) out.st.env).val,
    (TEnv.get (.there (.there (.there .here))) out.st.env).val,
    result.val,(TEnv.get .here done.1.st.env).val)

/-- info: [some (17, 5, 17, 3, 17), some (17, 17, 17, 1, 17), some (17, 5, 17, 2, 17), some (17, 17, 17, 0, 17)] -/
#guard_msgs in
#eval IO.println (reprStr [target_observed .legacy false,target_observed .viaIR false,
  target_observed .legacy true,target_observed .viaIR true])

-- The same assignment creates a zero denominator only in viaIR order.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  source_observed .legacy true false 5 0 (by decide) (by decide) == some (.ok 0,0,0) &&
  source_observed .viaIR true false 5 0 (by decide) (by decide) == some (.error (Source.panicData .divZero),0,0) &&
  (match (operand .legacy false .here (.there .here)).run zvTgt with | .ok (_, .prim v) => v.val == 0 | _ => false) &&
  (match (operand .viaIR false .here (.there .here)).run zvTgt with | .error err => err.data == Source.panicData .divZero | _ => false)))

-- Using the other actual pipeline is observably wrong, including success vs panic.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  target_observed .legacy false != target_observed .viaIR false &&
  source_observed .legacy false false 5 0 (by decide) (by decide) !=
    source_observed .viaIR false false 5 0 (by decide) (by decide)))

-- A reversed capture mapping is a different actual typed program.
def reversed : DeferredSource.Operand C [.val .uint,.val .uint,.mem bytesR,.alias bytesR] (.prim .uint) :=
  ⟨_,(assignReadPrefix .legacy .here (.there .here)).join
    (UnsignedQuotRemGuard.code false (.there .here) .here),.val (.simple (.local .here))⟩

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  (match reversed.run tgt with | .ok (out,.prim v) => v.val == 0 && (TEnv.get .here out.st.env).val == 17 | _ => false) &&
  (match (code .legacy false .here (.there .here)).run tgt with
    | .ok out => (Val.simple (.local .here) : Val C _ .uint).evalT
        (out.st.drop (code (C := C) .legacy false .here (.there .here)).ext) |>.toOption |>.map (·.val)
    | _ => none) == some 17))

end Solidity.Lowering.V07.UnsignedQuotRemEffectsControls

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.range_client' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.range_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.source_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.source_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.source_zero_legacy_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.source_zero_legacy_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.source_zero_viaIR_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.source_zero_viaIR_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.prefix_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.prefix_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.code_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.code_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.code_zero_legacy_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.code_zero_legacy_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.code_zero_viaIR_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.code_zero_viaIR_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.operand_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.operand_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.operand_zero_legacy_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.operand_zero_legacy_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.operand_zero_viaIR_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.operand_zero_viaIR_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.transport_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.zero_legacy_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.zero_legacy_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.zero_viaIR_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.zero_viaIR_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.repeated_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.repeated_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.self_alias_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.self_alias_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.equal_content_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.equal_content_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.extension_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.binder_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.binder_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.live_caller' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.live_caller

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.source_frame_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemEffectsControls.source_frame_client
