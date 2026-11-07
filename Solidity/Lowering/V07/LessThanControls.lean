import Solidity.Lowering.V07.LessThan
import Solidity.Lowering.V07.WordCastControls

namespace Solidity.Lowering.V07.LessThanControls
open LessThan
open Source.SemanticsExamples
open MixedAssignmentControls (C E globals)

def t : Source.IntTy := ⟨true,8,by decide⟩
def src := WordCastControls.source t 5 (-7) (by decide) (by decide)
def tgt := WordCastControls.target t 5 (-7) (by decide) (by decide)

def accepts_client := accepts t
def source_value_client := source_value (D := E.layout) t 5 (-7) (by decide) (by decide)
def value_client := value_run tgt t (.simple (.local .here)) (.simple (.local (.there .here)))
  5 (-7) (by decide) (by decide) rfl rfl
def pair_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_from_pair (globals p) {F0 with checked := checked} (fuel+2) src src t
    (.local .here) (.local (.there .here)) 5 (-7) (by decide) (by decide)
    (source_local_pair (globals p) {F0 with checked := checked} fuel src t .here (.there .here)
      5 (-7) (by decide) (by decide) rfl rfl)
def range_client (p : Roadmap.Pipeline) := right_range p t (-7) 5 (by decide) (by decide)
def assignment_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_assignment (globals p) {F0 with checked := checked} fuel src t .here (.there .here)
    (-7) 5 (by decide) (by decide) rfl rfl
def tail_client := tail_run tgt t .here (.there .here) 5 (-7) (by decide) (by decide) rfl rfl
def code_client (p : Roadmap.Pipeline) := code_run tgt t p .here (.there .here)
  (-7) 5 (by decide) (by decide) rfl rfl
def operand_client (p : Roadmap.Pipeline) := operand_run tgt t p .here (.there .here)
  (-7) 5 (by decide) (by decide) rfl rfl
def transport_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel src tgt t
    (WordCastControls.si t) (WordCastControls.ti t) (WordCastControls.initial t 5 (-7) (by decide) (by decide))
    true false (-7) 5 (by decide) (by decide) rfl rfl

def repeated_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel src tgt t
    (fun k : Fin 3 => WordCastControls.si t (decide (k.val ≠ 1)))
    (fun k : Fin 3 => WordCastControls.ti t (decide (k.val ≠ 1)))
    ((WordCastControls.initial t 5 (-7) (by decide) (by decide)).reindex (fun k : Fin 3 => decide (k.val ≠ 1)))
    0 1 (-7) 5 (by decide) (by decide) rfl rfl

def self_alias_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel src tgt t
    (WordCastControls.si t) (WordCastControls.ti t) (WordCastControls.initial t 5 (-7) (by decide) (by decide))
    true true 5 5 (by decide) (by decide) rfl rfl

def equal_content_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel
    (WordCastControls.source t 5 5 (by decide) (by decide))
    (WordCastControls.target t 5 5 (by decide) (by decide)) t
    (WordCastControls.si t) (WordCastControls.ti t) (WordCastControls.initial t 5 5 (by decide) (by decide))
    true false 5 5 (by decide) (by decide) rfl rfl

def extension_client (p : Roadmap.Pipeline) := DeferredSource.Operand.run_wk
  (operand t p .here (.there .here)) (Thin.drop (t := .val .bool) Thin.refl) tgt (true,tgt.env)

def binder_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel
    (Source.Locals.cons (.bool true) src.1,src.2) (tgt.push (t := .val .bool) true) t
    (fun k => .there (WordCastControls.si t k)) (fun k => .there (WordCastControls.ti t k))
    ((WordCastControls.initial t 5 (-7) (by decide) (by decide)).under_binders (u := .val .bool) (.bool true) true)
    true false (-7) 5 (by decide) (by decide) rfl rfl

def live_caller : ∃ r : HRef tgt.H bytesR,
    TEnv.get (.there (.there .here)) tgt.env = some r ∧ tgt.heap.len r .dyn = 2 :=
  MixedAssignmentControls.live_memory

def source_frame_client (p : Roadmap.Pipeline) (checked : Bool) :=
  congrArg (fun result => result.2.2) (transport_client p checked 0).1

def check (p : Roadmap.Pipeline) (checked sign : Bool) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (assigned old : Int) : Bool :=
  let u : Source.IntTy := ⟨sign,bits,valid⟩
  let x := u.wrap assigned
  let y := u.wrap old
  let source := WordCastControls.source u y x (u.wrap_mem old) (u.wrap_mem assigned)
  let target := WordCastControls.target u y x (u.wrap_mem old) (u.wrap_mem assigned)
  let sr := (Source.evalE (globals p) {F0 with checked := checked} 4
    (.compare .lt (.assign (.local .here) (.local (.there .here))) (.local .here))).run source
  let tr := (operand u p .here (.there .here)).run target
  let captures := match (code u p .here (.there .here)).run target with
    | .ok out => (TEnv.get .here out.st.env) == decide (x < rightAt p x y) &&
        PrimTy.num? (TEnv.get (.there .here) out.st.env) == some x &&
        PrimTy.num? (TEnv.get (.there (.there .here)) out.st.env) == some (rightAt p x y)
    | _ => false
  match sr.1,tr with
  | .ok (.val (.bool v)),.ok (out,.prim w) => captures && v == decide (x < rightAt p x y) && w == v &&
      (sr.2.1.get .here).key == some x && (sr.2.1.get (.there .here)).key == some x &&
      PrimTy.num? (TEnv.get .here out.st.env) == some x &&
      PrimTy.num? (TEnv.get (.there .here) out.st.env) == some x
  | _,_ => false

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
  [false,true].all fun sign => (List.finRange 32).all fun i =>
  let bits := 8*(i.val+1)
  have valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 := by omega
  let u : Source.IntTy := ⟨sign,bits,valid⟩
  [(0,0),(u.lo,u.hi),(u.hi,u.lo),(u.lo,u.lo),(u.hi,u.hi),(-7,5),(5,17),(17,5),(1,0)].all
    fun (x,y) => check p checked sign bits valid x y))

def observed (p : Roadmap.Pipeline) : Option (Bool × Int × Int × Bool × Int) := do
  let out ← (code t p .here (.there .here)).run tgt |>.toOption
  let done ← (operand t p .here (.there .here)).run tgt |>.toOption
  let .prim result := done.2
  pure (TEnv.get .here out.st.env,(TEnv.get (.there .here) out.st.env).val,
    (TEnv.get (.there (.there .here)) out.st.env).val,result,(TEnv.get .here done.1.st.env).val)

/-- info: [some (true, -7, 5, true, -7), some (false, -7, -7, false, -7)] -/
#guard_msgs in
#eval IO.println (reprStr [observed .legacy,observed .viaIR])

def reversed : DeferredSource.Operand C [.val .int,.val .int,.mem bytesR,.alias bytesR] (.prim .bool) :=
  ⟨_,(assignReadPrefix .legacy .here (.there .here)).join (tail t (.there .here) .here),
    .val (.simple (.local .here))⟩

def uncaptured : DeferredSource.Operand C [.val .int,.val .int,.mem bytesR,.alias bytesR] (.prim .bool) :=
  ⟨_,(assignReadPrefix .legacy .here (.there .here)).join (tail t .here (.there (.there .here))),
    .val (.simple (.local .here))⟩

-- Wrong initial mapping, reversed captures and an uncaptured reached right read all give false.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  (match (value t (.simple (.local .here)) (.simple (.local (.there .here)))).evalT tgt with
    | .ok false => true
    | _ => false) &&
  (match reversed.run tgt with
    | .ok (out, .prim b) => !b && (TEnv.get .here out.st.env).val == -7
    | _ => false) &&
  (match uncaptured.run tgt with
    | .ok (out, .prim b) => !b && (TEnv.get .here out.st.env).val == -7
    | _ => false) &&
  (match observed .legacy,observed .viaIR with
    | some (true,_,_,_,_),some (false,_,_,_,_) => true
    | _,_ => false)))

-- Dropping captures first exposes a caller scalar, not the captured bool result.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  match (code t .legacy .here (.there .here)).run tgt with
  | .ok out => (TEnv.get .here (out.st.drop (code (C := C) t .legacy .here (.there .here)).ext).env).val == -7
  | _ => false))
end Solidity.Lowering.V07.LessThanControls

/-- info: 'Solidity.Lowering.V07.LessThanControls.accepts_client' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThanControls.accepts_client

/-- info: 'Solidity.Lowering.V07.LessThanControls.source_value_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThanControls.source_value_client

/-- info: 'Solidity.Lowering.V07.LessThanControls.value_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThanControls.value_client

/-- info: 'Solidity.Lowering.V07.LessThanControls.pair_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThanControls.pair_client

/-- info: 'Solidity.Lowering.V07.LessThanControls.range_client' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThanControls.range_client

/-- info: 'Solidity.Lowering.V07.LessThanControls.assignment_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThanControls.assignment_client

/-- info: 'Solidity.Lowering.V07.LessThanControls.tail_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThanControls.tail_client

/-- info: 'Solidity.Lowering.V07.LessThanControls.code_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThanControls.code_client

/-- info: 'Solidity.Lowering.V07.LessThanControls.operand_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThanControls.operand_client

/-- info: 'Solidity.Lowering.V07.LessThanControls.transport_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThanControls.transport_client

/-- info: 'Solidity.Lowering.V07.LessThanControls.repeated_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThanControls.repeated_client

/-- info: 'Solidity.Lowering.V07.LessThanControls.self_alias_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThanControls.self_alias_client

/-- info: 'Solidity.Lowering.V07.LessThanControls.equal_content_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThanControls.equal_content_client

/-- info: 'Solidity.Lowering.V07.LessThanControls.extension_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThanControls.extension_client

/-- info: 'Solidity.Lowering.V07.LessThanControls.binder_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThanControls.binder_client

/-- info: 'Solidity.Lowering.V07.LessThanControls.live_caller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThanControls.live_caller

/-- info: 'Solidity.Lowering.V07.LessThanControls.source_frame_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.LessThanControls.source_frame_client
