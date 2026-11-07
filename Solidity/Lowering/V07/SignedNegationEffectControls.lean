import Solidity.Lowering.V07.SignedNegationEffects

namespace Solidity.Lowering.V07.SignedNegationEffectControls
open SignedNegationEffects SignedNegation
open SignedWidthCasts (ty)
open Source.SemanticsExamples
open MixedAssignmentControls (C E globals storageRef path)

def t := ty 8 (by decide)
def src := WordCastControls.source t 5 7 (by decide) (by decide)
def tgt := WordCastControls.target t 5 7 (by decide) (by decide)
def si := WordCastControls.si t
def ti := WordCastControls.ti t
def srcPost := (src.1.set (si false) (.int 5 (by decide)),src.2)
def tgtPost := tgt.setLocal (ti false) (integerValue t 5 (by decide))

def source_client (p : Roadmap.Pipeline) (fuel : Nat) :=
  source_assignment_run 8 (by decide) (globals p) F0 fuel src (si false) (si true) 5 (by decide) rfl
def prefix_client := code_run 8 (by decide) tgt (ti false) (ti true) 5 (by decide) rfl
def transport_client (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport 8 (by decide) (globals p) F0 fuel src tgt si ti
    (WordCastControls.initial t 5 7 (by decide) (by decide)) false true 5 (by decide) rfl

def repeated_client (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport 8 (by decide) (globals p) F0 fuel src tgt
    (fun k : Fin 3 => si (decide (k.val = 1))) (fun k : Fin 3 => ti (decide (k.val = 1)))
    ((WordCastControls.initial t 5 7 (by decide) (by decide)).reindex
      (fun k : Fin 3 => decide (k.val = 1))) 0 1 5 (by decide) rfl

def self_client (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport 8 (by decide) (globals p) F0 fuel src tgt
    (fun _ : Bool => si true) (fun _ : Bool => ti true)
    ((WordCastControls.initial t 5 7 (by decide) (by decide)).reindex (fun _ : Bool => true))
    false true 5 (by decide) rfl

def equal_content_client (p : Roadmap.Pipeline) (fuel : Nat) :=
  assignment_transport 8 (by decide) (globals p) F0 fuel
    (WordCastControls.source t 5 5 (by decide) (by decide))
    (WordCastControls.target t 5 5 (by decide) (by decide)) si ti
    (WordCastControls.initial t 5 5 (by decide) (by decide)) false true 5 (by decide) rfl

def extension_client := DeferredSource.Operand.run_wk (operand 8 (ti false) (ti true))
  (Thin.drop (t := .val .bool) .refl) tgt (true,tgt.env)

def source_frame : srcPost.2 = src.2 ∧
    srcPost.1.get (.there (.there .here)) = .memRef rfl 0 ∧
    srcPost.1.get (.there (.there (.there .here))) = .storRef rfl path ∧
    srcPost.2.heap.get 0 = some ⟨.bytes .memory,.bytes [0,0]⟩ := ⟨rfl,rfl,rfl,rfl⟩

def target_frame : tgtPost.heap = tgt.heap ∧ tgtPost.glob = tgt.glob ∧
    TEnv.get (.there (.there .here)) tgtPost.env = TEnv.get (.there (.there .here)) tgt.env ∧
    TEnv.get (.there (.there (.there .here))) tgtPost.env = some storageRef ∧
    ∃ r : HRef tgtPost.H bytesR,
      TEnv.get (.there (.there .here)) tgtPost.env = some r ∧ tgtPost.heap.len r .dyn = 2 :=
  ⟨rfl,rfl,rfl,rfl,MixedAssignmentControls.live_memory⟩

def sourceReturned (p : Roadmap.Pipeline) : Option (Int × Int × Int) :=
  match (Source.evalE (globals p) {F0 with checked := false} 3
    (.unary .neg (.assign (.local (si false)) (.local (si true))))).run src with
  | (.ok (.val v),out) => match v.key,(out.1.get (si false)).key,(out.1.get (si true)).key with
    | some v,some i,some a => some (v,i,a) | _,_,_ => none
  | _ => none

def targetReturned : Option (Int × Int × Int) :=
  match (operand 8 (ti false) (ti true)).run tgt with
  | .ok (out,.prim v) => some (v.val,(TEnv.get (ti false) out.st.env).val,
      (TEnv.get (ti true) out.st.env).val)
  | _ => none

def sourceAssigned (p : Roadmap.Pipeline) : Option (Int × Int × Int) :=
  match (Source.evalE (globals p) F0 2 (.assign (.local (si false)) (.local (si true)))).run src with
  | (.ok (.val v),out) => match v.key,(out.1.get (si false)).key,(out.1.get (si true)).key with
    | some v,some i,some a => some (v,i,a) | _,_,_ => none
  | _ => none

def targetAssigned : Option (Int × Int) :=
  match (Stmt.assignLocal (ti false) (.simple (.local (ti true)))).run tgt with
  | .ok out => some ((TEnv.get (ti false) out.st.env).val,(TEnv.get (ti true) out.st.env).val)
  | _ => none

def targetCaptured : Option (Int × Int × Int) :=
  match (code 8 (ti false) (ti true)).run tgt with
  | .ok out => some ((TEnv.get .here out.st.env).val,
      (TEnv.get (.there (ti false)) out.st.env).val,(TEnv.get (.there (ti true)) out.st.env).val)
  | _ => none

def observations (p : Roadmap.Pipeline) :=
  (((src.1.get (si false)).key,(src.1.get (si true)).key),sourceAssigned p,sourceReturned p,
    ((TEnv.get (ti false) tgt.env).val,(TEnv.get (ti true) tgt.env).val),
    targetAssigned,targetCaptured,targetReturned)

/-- Actual wrong implementations, kept separate from the transport theorem. -/
def wrongStore : DeferredSource.Operand C [.val .int,.val .int,.mem bytesR,.alias bytesR] (.prim .int) :=
  ⟨.val .int :: _,
    .cons (.assignLocal (ti false) (negValue 8 (.simple (.local (ti true)))))
      (.cons (.declLocal .int (.user "wrong_store") (some (.simple (.local (ti false))))) .nil),
    .val (.simple (.local .here))⟩
def omittedWrite : DeferredSource.Operand C [.val .int,.val .int,.mem bytesR,.alias bytesR] (.prim .int) :=
  DeferredSource.Operand.ofSrc
  (Src.val (negValue 8 (.simple (.local (ti true)))))
def wrongDropped : TRes (Int × Int × Int) := do
  let out ← (code 8 (ti false) (ti true)).run tgt
  let dropped := out.st.drop (code (C := C) 8 (ti false) (ti true)).ext
  let value ← (Val.simple (.local .here) : Val C [.val .int,.val .int,.mem bytesR,.alias bytesR] .int).evalT dropped
  pure (value.val,(TEnv.get (ti false) dropped.env).val,(TEnv.get (ti true) dropped.env).val)

def check (p : Roadmap.Pipeline) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (n : Int) : Bool :=
  let x := (ty bits valid).wrap n
  let hx := (ty bits valid).wrap_mem n
  let y := (ty bits valid).wrap 7
  let hy := (ty bits valid).wrap_mem 7
  let source := WordCastControls.source (ty bits valid) x y hx hy
  let target := WordCastControls.target (ty bits valid) x y hx hy
  let sr := match (Source.evalE (globals p) {F0 with checked := false} 3
    (.unary .neg (.assign (.local (.there .here)) (.local .here)))).run source with
    | (.ok (.val v),out) => match v.key,(out.1.get (.there .here)).key,(out.1.get .here).key with
      | some v,some i,some a => some (v,i,a) | _,_,_ => none
    | _ => none
  let tr := match (operand bits (.there .here) .here).run target with
    | .ok (out,.prim v) => some (v.val,(TEnv.get (.there .here) out.st.env).val,(TEnv.get .here out.st.env).val)
    | _ => none
  sr == some ((ty bits valid).wrap (-x),x,x) && tr == sr

def source_extension_client :=
  (WordCastControls.initial t 5 7 (by decide) (by decide)).under_binders
    (σ := .bool) (u := .val .bool) (.bool true) true

def extendedReturned : Option (Bool × Int × Int × Int) :=
  let h := Thin.drop (t := .val .bool) Thin.refl
  match ((operand 8 (ti false) (ti true)).wk h).run (tgt.lift h (true,tgt.env)) with
  | .ok (out,.prim v) => some (TEnv.get .here out.st.env,v.val,
      (TEnv.get (.there (ti false)) out.st.env).val,(TEnv.get (.there (ti true)) out.st.env).val)
  | _ => none

def wrongNarrow : DeferredSource.Operand C [.val .int,.val .int,.mem bytesR,.alias bytesR] (.prim .int) :=
  ⟨.val .int :: _,
    .cons (.assignLocal (ti false) (.simple (.local (ti true))))
      (.cons (.declLocal .int (.user "wrong_narrow")
        (some (.unop .neg rfl rfl (.simple (.local (ti false)))))) .nil),
    .val (.simple (.local .here))⟩
def minTarget := WordCastControls.target t (-128) 7 (by decide) (by decide)
def narrowComparison :=
  [match (operand 8 (ti false) (ti true)).run minTarget with
    | .ok (_,.prim v) => some v.val | _ => none,
   match wrongNarrow.run minTarget with | .ok (_,.prim v) => some v.val | _ => none]

def collapsedMap :=
  let source := WordCastControls.source t 5 5 (by decide) (by decide)
  let target := WordCastControls.target t 5 5 (by decide) (by decide)
  ([false,true].all (fun k => (source.1.get (si k)).key == some (TEnv.get (ti true) target.env).val),
    (si false).toNat == (si true).toNat,(ti true).toNat == (ti true).toNat)

/-- info: [((some 7, some 5), some (5, 5, 5), some (-5, 5, 5), (7, 5), some (5, 5), some (-5, 5, 5), some (-5, 5, 5)),
 ((some 7, some 5), some (5, 5, 5), some (-5, 5, 5), (7, 5), some (5, 5), some (-5, 5, 5), some (-5, 5, 5))] -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].map observations))
/-- info: (Except.ok (-7), Except.ok (-5, 7), Except.ok (-5, -5), Except.ok (5, 5, 5)) -/
#guard_msgs in
#eval IO.println (reprStr (
  (negValue 8 (.simple (.local (ti false)))).evalT tgt |>.map (·.val),
  omittedWrite.run tgt |>.map (fun (out,v) => ((match v with | .prim n => n.val),(TEnv.get (ti false) out.st.env).val)),
  wrongStore.run tgt |>.map (fun (out,v) => ((match v with | .prim n => n.val),(TEnv.get (ti false) out.st.env).val)),
  wrongDropped))
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p => (List.finRange 32).all fun i =>
  let bits := 8*(i.val+1)
  have valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 := by omega
  [(ty bits valid).lo,(ty bits valid).hi,-1,0,1,5].all (check p bits valid)))
/-- info: some (true, -5, 5, 5) -/
#guard_msgs in
#eval IO.println (reprStr extendedReturned)
/-- info: [some (-128), some 128] -/
#guard_msgs in
#eval IO.println (reprStr narrowComparison)
/-- info: (true, false, true) -/
#guard_msgs in
#eval IO.println (reprStr collapsedMap)
end Solidity.Lowering.V07.SignedNegationEffectControls

/-- info: 'Solidity.Lowering.V07.SignedNegationEffectControls.source_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedNegationEffectControls.source_client

/-- info: 'Solidity.Lowering.V07.SignedNegationEffectControls.prefix_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedNegationEffectControls.prefix_client

/-- info: 'Solidity.Lowering.V07.SignedNegationEffectControls.transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedNegationEffectControls.transport_client

/-- info: 'Solidity.Lowering.V07.SignedNegationEffectControls.repeated_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedNegationEffectControls.repeated_client

/-- info: 'Solidity.Lowering.V07.SignedNegationEffectControls.self_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedNegationEffectControls.self_client

/-- info: 'Solidity.Lowering.V07.SignedNegationEffectControls.equal_content_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedNegationEffectControls.equal_content_client

/-- info: 'Solidity.Lowering.V07.SignedNegationEffectControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedNegationEffectControls.extension_client

/-- info: 'Solidity.Lowering.V07.SignedNegationEffectControls.source_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedNegationEffectControls.source_frame

/-- info: 'Solidity.Lowering.V07.SignedNegationEffectControls.target_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedNegationEffectControls.target_frame

/-- info: 'Solidity.Lowering.V07.SignedNegationEffectControls.source_extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedNegationEffectControls.source_extension_client
