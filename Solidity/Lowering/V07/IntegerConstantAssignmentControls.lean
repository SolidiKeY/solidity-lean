import Solidity.Lowering.V07.IntegerConstantAssignment
import Solidity.Lowering.V07.WordCastControls

namespace Solidity.Lowering.V07.IntegerConstantAssignmentControls
open IntegerConstantAssignment Source.SemanticsExamples
open MixedAssignmentControls (C E globals)
open WordCastControls (si ti)

def src := WordCastControls.source .u8 2 9 (by decide) (by decide)
def tgt := WordCastControls.target .u8 2 9 (by decide) (by decide)
def initial := WordCastControls.initial .u8 2 9 (by decide) (by decide)
def source_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  source_run (globals p) {F0 with checked := checked} fuel src .u8 .here 7 (by decide)
def code_client := code_run tgt .u8 .here 7 (by decide)
def operand_client := operand_run tgt .u8 .here 7 (by decide)
def write_client := family_write .u8 (si .u8) (ti .u8) src.1 tgt.env initial true 7 (by decide)
def transport_client (p : Roadmap.Pipeline) (checked : Bool) (fuel : Nat) :=
  transport (globals p) {F0 with checked := checked} fuel src tgt .u8 (si .u8) (ti .u8)
    initial true 7 (by decide)
def repeated_client (p : Roadmap.Pipeline) (fuel : Nat) :=
  transport (globals p) F0 fuel src tgt .u8
    (fun k : Fin 3 => si .u8 (decide (k.val < 2)))
    (fun k : Fin 3 => ti .u8 (decide (k.val < 2)))
    (initial.reindex (fun k : Fin 3 => decide (k.val < 2))) 0 7 (by decide)
def equal_content_client (p : Roadmap.Pipeline) (fuel : Nat) :=
  transport (globals p) F0 fuel
    (WordCastControls.source .u8 2 2 (by decide) (by decide))
    (WordCastControls.target .u8 2 2 (by decide) (by decide)) .u8 (si .u8) (ti .u8)
    (WordCastControls.initial .u8 2 2 (by decide) (by decide)) true 7 (by decide)
def extension_client := DeferredSource.Operand.run_wk
  (operand .u8 .here 7 (by decide) : DeferredSource.Operand C
    [.val .uint,.val .uint,.mem bytesR,.alias bytesR] (.prim .uint))
  (Thin.drop (t := .val .bool) .refl) tgt (true,tgt.env)
def family_extension_client := write_client.under_binders (σ := .bool) (u := .val .bool) (.bool true) true

theorem collapsed_map_refused : ¬ IntegerLocalFamily .u8 (si .u8) (fun _ : Bool => ti .u8 true)
    (WordCastControls.source .u8 2 2 (by decide) (by decide)).1
    (WordCastControls.target .u8 2 2 (by decide) (by decide)).env := by
  intro h
  have impossible := (h.aliases true false).mpr rfl
  change 0 = 1 at impossible
  exact Nat.zero_ne_one impossible

def observe (p : Roadmap.Pipeline) (checked : Bool) (t : Source.IntTy) (old other z : Int)
    (ho : t.lo ≤ old ∧ old ≤ t.hi) (hn : t.lo ≤ other ∧ other ≤ t.hi)
    (hz : t.lo ≤ z ∧ z ≤ t.hi) : Option (List Int) :=
  let source := WordCastControls.source t old other ho hn
  let target := WordCastControls.target t old other ho hn
  match (Source.evalE (globals p) {F0 with checked := checked} 3
      (.assign (.local .here) (.conv (.const (Source.Q.ofInt z))
        (.inl (IntegerConstants.allowed E t z hz))))).run source,
      (code t .here z hz).run target,(operand t .here z hz).run target with
  | (.ok (.val v),post),.ok captured,.ok (out,.prim result) => do
    let a ← v.key
    let b ← (post.1.get .here).key
    let c ← (post.1.get (.there .here)).key
    let d ← PrimTy.num? (TEnv.get .here captured.st.env)
    let e ← PrimTy.num? (TEnv.get (.there .here) captured.st.env)
    let f ← PrimTy.num? (TEnv.get (.there (.there .here)) captured.st.env)
    let g ← PrimTy.num? result
    let h ← PrimTy.num? (TEnv.get .here out.st.env)
    let i ← PrimTy.num? (TEnv.get (.there .here) out.st.env)
    pure [a,b,c,d,e,f,g,h,i]
  | _,_,_ => none

/-- info: [some [7, 7, 9, 7, 7, 9, 7, 7, 9], some [7, 7, 9, 7, 7, 9, 7, 7, 9]] -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].map fun p =>
  observe p true .u8 2 9 7 (by decide) (by decide) (by decide)))

def check (p : Roadmap.Pipeline) (checked : Bool) (t : Source.IntTy) (z : Int) : Bool :=
  if h : t.lo ≤ z ∧ z ≤ t.hi then
    if h0 : t.lo ≤ 0 ∧ 0 ≤ t.hi then
      if h1 : t.lo ≤ 1 ∧ 1 ≤ t.hi then
        observe p checked t 0 1 z h0 h1 h == some [z,z,1,z,z,1,z,z,1]
      else false
    else false
  else false
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ((List.range 257).all fun bits =>
  if width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 then [false,true].all fun signed =>
    let t : Source.IntTy := ⟨signed,bits,width⟩
    [Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun checked =>
      [0,1,t.lo,t.hi].all fun z => check p checked t z
  else true))

-- Actual wrong code captures the stale caller value before writing the literal.
def stale : DeferredSource.Operand C [.val .uint,.val .uint,.mem bytesR,.alias bytesR] (.prim .uint) :=
  ⟨_,.cons (.declLocal .uint (.user "wrong_stale") (some (.simple (.local .here))))
    (.cons (.assignLocal (.there .here) (IntegerConstants.value .u8 7 (by decide))) .nil),
    .val (.simple (.local .here))⟩
def resultAndCaller (e : DeferredSource.Operand C [.val .uint,.val .uint,.mem bytesR,.alias bytesR] (.prim .uint)) :
    Option (Int × Int) :=
  match e.run tgt with
  | .ok (out,.prim result) => some (result.val,(TEnv.get .here out.st.env).val)
  | _ => none
/-- info: [some (7, 7), some (7, 2), some (2, 7), some (7, 2)] -/
#guard_msgs in
#eval IO.println (reprStr [resultAndCaller (operand .u8 .here 7 (by decide)),
  resultAndCaller (IntegerConstants.operand .u8 7 (by decide)),resultAndCaller stale,
  resultAndCaller (operand .u8 (.there .here) 7 (by decide))])


theorem frame_client :
    (tgt.setLocal .here (integerValue .u8 7 (by decide))).heap = tgt.heap ∧
    (tgt.setLocal .here (integerValue .u8 7 (by decide))).glob = tgt.glob ∧
    TEnv.get (.there (.there .here)) (tgt.setLocal .here (integerValue .u8 7 (by decide))).env =
      TEnv.get (.there (.there .here)) tgt.env ∧
    TEnv.get (.there (.there (.there .here))) (tgt.setLocal .here (integerValue .u8 7 (by decide))).env =
      TEnv.get (.there (.there (.there .here))) tgt.env := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem pass_client : (code (C := C) (Γ := [.val .uint,.val .uint,.mem bytesR,.alias bytesR])
    .u8 .here 7 (by decide)).withPanics = code .u8 .here 7 (by decide) := by
  rfl

/-- info: 'Solidity.Lowering.V07.IntegerConstantAssignmentControls.source_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantAssignmentControls.source_client

/-- info: 'Solidity.Lowering.V07.IntegerConstantAssignmentControls.code_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantAssignmentControls.code_client

/-- info: 'Solidity.Lowering.V07.IntegerConstantAssignmentControls.operand_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantAssignmentControls.operand_client

/-- info: 'Solidity.Lowering.V07.IntegerConstantAssignmentControls.write_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantAssignmentControls.write_client

/-- info: 'Solidity.Lowering.V07.IntegerConstantAssignmentControls.transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantAssignmentControls.transport_client

/-- info: 'Solidity.Lowering.V07.IntegerConstantAssignmentControls.repeated_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantAssignmentControls.repeated_client

/-- info: 'Solidity.Lowering.V07.IntegerConstantAssignmentControls.equal_content_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantAssignmentControls.equal_content_client

/-- info: 'Solidity.Lowering.V07.IntegerConstantAssignmentControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantAssignmentControls.extension_client

/-- info: 'Solidity.Lowering.V07.IntegerConstantAssignmentControls.family_extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantAssignmentControls.family_extension_client

/-- info: 'Solidity.Lowering.V07.IntegerConstantAssignmentControls.collapsed_map_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantAssignmentControls.collapsed_map_refused

/-- info: 'Solidity.Lowering.V07.IntegerConstantAssignmentControls.frame_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantAssignmentControls.frame_client

/-- info: 'Solidity.Lowering.V07.IntegerConstantAssignmentControls.pass_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.IntegerConstantAssignmentControls.pass_client

end Solidity.Lowering.V07.IntegerConstantAssignmentControls
