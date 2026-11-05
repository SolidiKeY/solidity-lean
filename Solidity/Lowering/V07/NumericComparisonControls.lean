import Solidity.Lowering.V07.NumericComparisons
import Solidity.Lowering.V07.LessThanControls

namespace Solidity.Lowering.V07.NumericComparisonControls
open NumericComparisons
open LessThanControls (t src tgt)
open Source.SemanticsExamples
open MixedAssignmentControls (C E globals)

def operators : List {op : BinOp // op.accepts .uint = true ∧ op.ret .uint = .bool} :=
  [⟨.lt,by decide⟩,⟨.gt,by decide⟩,⟨.le,by decide⟩,⟨.ge,by decide⟩,⟨.eqB,by decide⟩,⟨.neB,by decide⟩]

def classified_client := classified .neB rfl rfl
def metadata_client := metadata .ge rfl rfl t
def value_client := value_run (D := E.layout) tgt t .eqB rfl rfl
  (.simple (.local .here)) (.simple (.local (.there .here))) 5 (-7) (by decide) (by decide) rfl rfl
def pair_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_from_pair (globals p) {F0 with checked := checked} (fuel+2) src src t .gt
    (.local .here) (.local (.there .here)) 5 (-7) (by decide) (by decide) true rfl
    (source_local_pair (globals p) {F0 with checked := checked} fuel src t .here (.there .here)
      5 (-7) (by decide) (by decide) rfl rfl)
def assignment_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_assignment (globals p) {F0 with checked := checked} fuel src t .neB .here (.there .here)
    (-7) 5 (by decide) (by decide) (decide ((-7 : Int) ≠ LessThan.rightAt p (-7) 5))
    (by cases p <;> rfl) rfl rfl
def tail_client := tail_run (D := E.layout) tgt t .ge rfl rfl .here (.there .here)
  5 (-7) (by decide) (by decide) rfl rfl
def pass_client (p : Roadmap.Pipeline) := pass_exact (C := C) t .eqB rfl rfl p
  (.here : Idx [.val .int,.val .int,.mem bytesR,.alias bytesR] (.val .int)) (.there .here)
def code_client (p : Roadmap.Pipeline) := code_run (D := E.layout) tgt t .neB rfl rfl p
  .here (.there .here) (-7) 5 (by decide) (by decide) rfl rfl
def operand_client (p : Roadmap.Pipeline) := operand_run (D := E.layout) tgt t .le rfl rfl p
  .here (.there .here) (-7) 5 (by decide) (by decide) rfl rfl

def transport_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel src tgt t .ge rfl rfl
    (WordCastControls.si t) (WordCastControls.ti t) (WordCastControls.initial t 5 (-7) (by decide) (by decide))
    true false (-7) 5 (by decide) (by decide) rfl rfl
def equality_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel src tgt t .eqB rfl rfl
    (WordCastControls.si t) (WordCastControls.ti t) (WordCastControls.initial t 5 (-7) (by decide) (by decide))
    true false (-7) 5 (by decide) (by decide) rfl rfl
def inequality_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel src tgt t .neB rfl rfl
    (WordCastControls.si t) (WordCastControls.ti t) (WordCastControls.initial t 5 (-7) (by decide) (by decide))
    true false (-7) 5 (by decide) (by decide) rfl rfl

def repeated_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel src tgt t .eqB rfl rfl
    (fun k : Fin 3 => WordCastControls.si t (decide (k.val ≠ 1)))
    (fun k : Fin 3 => WordCastControls.ti t (decide (k.val ≠ 1)))
    ((WordCastControls.initial t 5 (-7) (by decide) (by decide)).reindex (fun k : Fin 3 => decide (k.val ≠ 1)))
    0 1 (-7) 5 (by decide) (by decide) rfl rfl

def self_alias_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel src tgt t .eqB rfl rfl
    (WordCastControls.si t) (WordCastControls.ti t) (WordCastControls.initial t 5 (-7) (by decide) (by decide))
    true true 5 5 (by decide) (by decide) rfl rfl

def equal_content_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel
    (WordCastControls.source t 5 5 (by decide) (by decide))
    (WordCastControls.target t 5 5 (by decide) (by decide)) t .eqB rfl rfl
    (WordCastControls.si t) (WordCastControls.ti t) (WordCastControls.initial t 5 5 (by decide) (by decide))
    true false 5 5 (by decide) (by decide) rfl rfl

def extension_client (p : Roadmap.Pipeline) := DeferredSource.Operand.run_wk
  (operand t .gt rfl rfl p .here (.there .here)) (Thin.drop (t := .val .bool) Thin.refl) tgt (true,tgt.env)

def binder_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel
    (Source.Locals.cons (.bool true) src.1,src.2) (tgt.push (t := .val .bool) true) t .neB rfl rfl
    (fun k => .there (WordCastControls.si t k)) (fun k => .there (WordCastControls.ti t k))
    ((WordCastControls.initial t 5 (-7) (by decide) (by decide)).under_binders (u := .val .bool) (.bool true) true)
    true false (-7) 5 (by decide) (by decide) rfl rfl

def live_caller : ∃ r : HRef tgt.H bytesR,
    TEnv.get (.there (.there .here)) tgt.env = some r ∧ tgt.heap.len r .dyn = 2 :=
  MixedAssignmentControls.live_memory

def check (op : BinOp) (hu : op.accepts .uint = true) (hr : op.ret .uint = .bool)
    (p : Roadmap.Pipeline) (checked sign : Bool) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (assigned old : Int) : Bool :=
  let u : Source.IntTy := ⟨sign,bits,valid⟩
  let x := u.wrap assigned
  let y := u.wrap old
  let source := WordCastControls.source u y x (u.wrap_mem old) (u.wrap_mem assigned)
  let target := WordCastControls.target u y x (u.wrap_mem old) (u.wrap_mem assigned)
  let sr := (Source.evalE (globals p) {F0 with checked := checked} 4
    (.compare (sourceOp op) (.assign (.local .here) (.local (.there .here))) (.local .here))).run source
  let tr := (operand u op hu hr p .here (.there .here)).run target
  match sr.1,tr,(code u op hu hr p .here (.there .here)).run target with
  | .ok (.val (.bool v)),.ok (out,.prim w),.ok captures => v == w && TEnv.get .here captures.st.env == v &&
      PrimTy.num? (TEnv.get (.there .here) captures.st.env) == some x &&
      PrimTy.num? (TEnv.get (.there (.there .here)) captures.st.env) == some (LessThan.rightAt p x y) &&
      (sr.2.1.get .here).key == some x && (sr.2.1.get (.there .here)).key == some x &&
      PrimTy.num? (TEnv.get .here out.st.env) == some x &&
      PrimTy.num? (TEnv.get (.there .here) out.st.env) == some x
  | _,_,_ => false

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (operators.all fun op => [Roadmap.Pipeline.legacy,.viaIR].all fun p =>
  [false,true].all fun checked => [false,true].all fun sign => (List.finRange 32).all fun i =>
  let bits := 8*(i.val+1)
  have valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 := by omega
  let u : Source.IntTy := ⟨sign,bits,valid⟩
  [(0,0),(u.lo,u.hi),(u.hi,u.lo),(u.lo,u.lo),(u.hi,u.hi),(-7,5),(5,17),(17,5),(1,0)].all
    fun (x,y) => check op.val op.property.1 op.property.2 p checked sign bits valid x y))

def observed (op : BinOp) (hu : op.accepts .uint = true) (hr : op.ret .uint = .bool)
    (p : Roadmap.Pipeline) : Option (Bool × Int × Int × Bool × Int) := do
  let out ← (code t op hu hr p .here (.there .here)).run tgt |>.toOption
  let done ← (operand t op hu hr p .here (.there .here)).run tgt |>.toOption
  let .prim result := done.2
  pure (TEnv.get .here out.st.env,(TEnv.get (.there .here) out.st.env).val,
    (TEnv.get (.there (.there .here)) out.st.env).val,result,(TEnv.get .here done.1.st.env).val)

/-- info: [(some (true, -7, 5, true, -7), some (false, -7, -7, false, -7)),
 (some (false, -7, 5, false, -7), some (false, -7, -7, false, -7)),
 (some (true, -7, 5, true, -7), some (true, -7, -7, true, -7)),
 (some (false, -7, 5, false, -7), some (true, -7, -7, true, -7)),
 (some (false, -7, 5, false, -7), some (true, -7, -7, true, -7)),
 (some (true, -7, 5, true, -7), some (false, -7, -7, false, -7))] -/
#guard_msgs in
#eval IO.println (reprStr (operators.map fun op =>
  (observed op.val op.property.1 op.property.2 .legacy,observed op.val op.property.1 op.property.2 .viaIR)))

-- A wrong equality/inequality opcode inverts the actual result.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  observed .eqB rfl rfl .legacy != observed .neB rfl rfl .legacy &&
  observed .eqB rfl rfl .viaIR != observed .eqB rfl rfl .legacy))

-- Actual reversed and uncaptured-right clauses break >= / != respectively.
def reversed : DeferredSource.Operand C [.val .int,.val .int,.mem bytesR,.alias bytesR] (.prim .bool) :=
  ⟨_,(assignReadPrefix .legacy .here (.there .here)).join (tail t .ge rfl rfl (.there .here) .here),
    .val (.simple (.local .here))⟩
def uncaptured : DeferredSource.Operand C [.val .int,.val .int,.mem bytesR,.alias bytesR] (.prim .bool) :=
  ⟨_,(assignReadPrefix .legacy .here (.there .here)).join (tail t .neB rfl rfl .here (.there (.there .here))),
    .val (.simple (.local .here))⟩
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (
  (match reversed.run tgt with | .ok (out,.prim b) => b && (TEnv.get .here out.st.env).val == -7 | _ => false) &&
  (match uncaptured.run tgt with | .ok (out,.prim b) => !b && (TEnv.get .here out.st.env).val == -7 | _ => false)))
end Solidity.Lowering.V07.NumericComparisonControls

/-- info: 'Solidity.Lowering.V07.NumericComparisonControls.classified_client' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisonControls.classified_client

/-- info: 'Solidity.Lowering.V07.NumericComparisonControls.metadata_client' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisonControls.metadata_client

/-- info: 'Solidity.Lowering.V07.NumericComparisonControls.value_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisonControls.value_client

/-- info: 'Solidity.Lowering.V07.NumericComparisonControls.pair_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisonControls.pair_client

/-- info: 'Solidity.Lowering.V07.NumericComparisonControls.assignment_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisonControls.assignment_client

/-- info: 'Solidity.Lowering.V07.NumericComparisonControls.tail_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisonControls.tail_client

/-- info: 'Solidity.Lowering.V07.NumericComparisonControls.pass_client' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisonControls.pass_client

/-- info: 'Solidity.Lowering.V07.NumericComparisonControls.code_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisonControls.code_client

/-- info: 'Solidity.Lowering.V07.NumericComparisonControls.operand_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisonControls.operand_client

/-- info: 'Solidity.Lowering.V07.NumericComparisonControls.transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisonControls.transport_client

/-- info: 'Solidity.Lowering.V07.NumericComparisonControls.equality_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisonControls.equality_client

/-- info: 'Solidity.Lowering.V07.NumericComparisonControls.inequality_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisonControls.inequality_client

/-- info: 'Solidity.Lowering.V07.NumericComparisonControls.repeated_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisonControls.repeated_client

/-- info: 'Solidity.Lowering.V07.NumericComparisonControls.self_alias_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisonControls.self_alias_client

/-- info: 'Solidity.Lowering.V07.NumericComparisonControls.equal_content_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisonControls.equal_content_client

/-- info: 'Solidity.Lowering.V07.NumericComparisonControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisonControls.extension_client

/-- info: 'Solidity.Lowering.V07.NumericComparisonControls.binder_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisonControls.binder_client

/-- info: 'Solidity.Lowering.V07.NumericComparisonControls.live_caller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.NumericComparisonControls.live_caller
