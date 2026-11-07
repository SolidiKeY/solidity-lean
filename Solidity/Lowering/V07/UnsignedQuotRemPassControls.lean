import Solidity.Lowering.V07.UnsignedQuotRemPass
import Solidity.Lowering.V07.UnsignedQuotRemEffectsControls

namespace Solidity.Lowering.V07.UnsignedQuotRemPassControls
open UnsignedQuotRemPass
open UnsignedNarrowing (ty)
open UnsignedQuotRem (calculate sourceOp)
open UnsignedQuotRemEffects (divisor)
open UnsignedQuotRemEffectsControls (t src tgt zlSrc zlTgt zvSrc zvTgt)
open Source.SemanticsExamples
open MixedAssignmentControls (C E globals)

def pure_exact_client (rem : Bool) := pure_exact (C := C) rem
  (.here : Idx [.val .uint,.val .uint,.mem bytesR,.alias bytesR] (.val .uint)) (.there .here)
def effects_exact_client (p : Roadmap.Pipeline) (rem : Bool) := effects_exact (C := C) p rem
  (.here : Idx [.val .uint,.val .uint,.mem bytesR,.alias bytesR] (.val .uint)) (.there .here)
def pure_operand_client (rem : Bool) := pure_operand_exact (C := C) rem
  (.here : Idx [.val .uint,.val .uint,.mem bytesR,.alias bytesR] (.val .uint)) (.there .here)
def effects_operand_client (p : Roadmap.Pipeline) (rem : Bool) := effects_operand_exact (C := C) p rem
  (.here : Idx [.val .uint,.val .uint,.mem bytesR,.alias bytesR] (.val .uint)) (.there .here)
def pure_run_client (rem : Bool) := pure_run tgt rem .here (.there .here)
def effects_run_client (p : Roadmap.Pipeline) (rem : Bool) := effects_run tgt p rem .here (.there .here)

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
  (effectsOperand p rem .here (.there .here)) (Thin.drop (t := .val .bool) Thin.refl) tgt (true,tgt.env)


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
  let tr := (effectsOperand p rem .here (.there .here)).run target
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


def target_observed (p : Roadmap.Pipeline) (rem : Bool) : Option (Int × Int × Int × Int × Int) := do
  let out ← ((rawEffects p rem .here (.there .here)).withPanics).run tgt |>.toOption
  let done ← (effectsOperand p rem .here (.there .here)).run tgt |>.toOption
  let .prim result := done.2
  pure ((TEnv.get (.there .here) out.st.env).val,
    (TEnv.get (.there (.there .here)) out.st.env).val,
    (TEnv.get (.there (.there (.there .here))) out.st.env).val,
    result.val,(TEnv.get .here done.1.st.env).val)

/-- info: [some (17, 5, 17, 3, 17), some (17, 17, 17, 1, 17), some (17, 5, 17, 2, 17), some (17, 17, 17, 0, 17)] -/
#guard_msgs in
#eval IO.println (reprStr [target_observed .legacy false,target_observed .viaIR false,
  target_observed .legacy true,target_observed .viaIR true])


-- Omitting the real panic pass loses the complete panic payload.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  (match (raw (C := C) false .here (.there .here)).run zvTgt with
    | .error err => err.data == []
    | _ => false) &&
  (match (pureOperand false .here (.there .here)).run zvTgt with
    | .error err => err.data == Source.panicData .divZero
    | _ => false)))

-- Assignment makes only the viaIR denominator zero; order is observable.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  (match (effectsOperand .legacy false .here (.there .here)).run zvTgt with
    | .ok (out,.prim v) => v.val == 0 && (TEnv.get .here out.st.env).val == 0
    | _ => false) &&
  (match (effectsOperand .viaIR false .here (.there .here)).run zvTgt with
    | .error err => err.data == Source.panicData .divZero
    | _ => false)))
end Solidity.Lowering.V07.UnsignedQuotRemPassControls

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPassControls.pure_exact_client' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPassControls.pure_exact_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPassControls.effects_exact_client' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPassControls.effects_exact_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPassControls.pure_operand_client' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPassControls.pure_operand_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPassControls.effects_operand_client' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPassControls.effects_operand_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPassControls.pure_run_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPassControls.pure_run_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPassControls.effects_run_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPassControls.effects_run_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPassControls.transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPassControls.transport_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPassControls.zero_legacy_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPassControls.zero_legacy_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPassControls.zero_viaIR_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPassControls.zero_viaIR_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPassControls.repeated_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPassControls.repeated_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPassControls.self_alias_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPassControls.self_alias_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPassControls.equal_content_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPassControls.equal_content_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPassControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPassControls.extension_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPassControls.binder_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPassControls.binder_client

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPassControls.live_caller' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPassControls.live_caller

/-- info: 'Solidity.Lowering.V07.UnsignedQuotRemPassControls.source_frame_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedQuotRemPassControls.source_frame_client
