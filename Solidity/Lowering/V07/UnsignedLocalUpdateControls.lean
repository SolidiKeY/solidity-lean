import Solidity.Lowering.V07.UnsignedLocalUpdate
import Solidity.Lowering.V07.WordCastControls

namespace Solidity.Lowering.V07.UnsignedLocalUpdateControls
open UnsignedLocalUpdate
open UnsignedNarrowing (ty)
open Source.SemanticsExamples
open MixedAssignmentControls (C E globals)

def t := ty 8 (by decide)
def src := WordCastControls.source t 255 7 (by decide) (by decide)
def tgt := WordCastControls.target t 255 7 (by decide) (by decide)
def value_source_client (inc : Bool) := source_value 8 (by decide) (D := E.layout) inc 255 (by decide)
def source_client (p : Roadmap.Pipeline) (inc pre : Bool) (fuel : Nat) :=
  source_run 8 (by decide) (globals p) F0 fuel src inc pre .here 255 (by decide) rfl

def value_target_client (inc : Bool) := value_run 8 (by decide) tgt inc
  (.simple (.local .here)) 255 (by decide) rfl

def code_client (inc pre : Bool) := code_run 8 (by decide) tgt inc pre .here 255 (by decide) rfl

def operand_client (inc pre : Bool) := operand_run 8 (by decide) tgt inc pre .here 255 (by decide) rfl

def transport_client (p : Roadmap.Pipeline) (inc pre : Bool) (fuel : Nat) :=
  transport 8 (by decide) (globals p) F0 fuel src tgt inc pre
    (WordCastControls.si t) (WordCastControls.ti t)
    (WordCastControls.initial t 255 7 (by decide) (by decide)) true 255 (by decide) rfl

def repeated_client (p : Roadmap.Pipeline) (inc pre : Bool) (fuel : Nat) :=
  transport 8 (by decide) (globals p) F0 fuel src tgt inc pre
    (fun k : Fin 3 => WordCastControls.si t (decide (k.val < 2)))
    (fun k : Fin 3 => WordCastControls.ti t (decide (k.val < 2)))
    ((WordCastControls.initial t 255 7 (by decide) (by decide)).reindex
      (fun k : Fin 3 => decide (k.val < 2))) 0 255 (by decide) rfl

def equal_content_client (p : Roadmap.Pipeline) (inc pre : Bool) (fuel : Nat) :=
  transport 8 (by decide) (globals p) F0 fuel
    (WordCastControls.source t 7 7 (by decide) (by decide))
    (WordCastControls.target t 7 7 (by decide) (by decide)) inc pre
    (WordCastControls.si t) (WordCastControls.ti t)
    (WordCastControls.initial t 7 7 (by decide) (by decide)) true 7 (by decide) rfl

def extension_client (inc pre : Bool) := DeferredSource.Operand.run_wk
  (operand 8 inc pre (.here : Idx _ (.val .uint)))
  (Thin.drop (t := .val .bool) Thin.refl) tgt (true,tgt.env)

def binder_client (p : Roadmap.Pipeline) (inc pre : Bool) (fuel : Nat) :=
  transport 8 (by decide) (globals p) F0 fuel
    (Source.Locals.cons (.bool true) src.1,src.2) (tgt.push (t := .val .bool) true) inc pre
    (fun k => .there (WordCastControls.si t k)) (fun k => .there (WordCastControls.ti t k))
    ((WordCastControls.initial t 255 7 (by decide) (by decide)).under_binders (u := .val .bool) (.bool true) true)
    true 255 (by decide) rfl

def live_caller : ∃ r : HRef tgt.H bytesR,
    TEnv.get (.there (.there .here)) tgt.env = some r ∧ tgt.heap.len r .dyn = 2 :=
  MixedAssignmentControls.live_memory

def source_frame_client (p : Roadmap.Pipeline) (inc pre : Bool) :=
  congrArg (fun result => result.2.2) (source_run 8 (by decide) (globals p) F0 0 src inc pre .here 255 (by decide) rfl)

/-- The result and all selected postlocals are observed, not merely the returned scalar. -/
def check (p : Roadmap.Pipeline) (inc pre : Bool) (bits : Nat)
    (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (n : Int) : Bool :=
  let x := (ty bits valid).wrap n
  let hx := (ty bits valid).wrap_mem n
  let y := (ty bits valid).wrap 7
  let hy := (ty bits valid).wrap_mem 7
  let source := WordCastControls.source (ty bits valid) x y hx hy
  let target := WordCastControls.target (ty bits valid) x y hx hy
  let sr := match (Source.evalE (globals p) {F0 with checked := false} 2
    (.incDec inc pre (.local .here))).run source with
    | (.ok (.val v),out) => match v.key,(out.1.get .here).key,(out.1.get (.there .here)).key with
      | some v,some x,some y => some (v,x,y) | _,_,_ => none
    | _ => none
  let tr := match (operand bits inc pre .here).run target with
    | .ok (out,.prim v) => some (v.val,(TEnv.get .here out.st.env).val,(TEnv.get (.there .here) out.st.env).val)
    | _ => none
  let new := (ty bits valid).wrap (changed inc x)
  sr == some ((if pre then new else x),new,y) && tr == sr

/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p => [false,true].all fun inc =>
  [false,true].all fun pre => (List.finRange 32).all fun i =>
  let bits := 8*(i.val+1)
  have valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 := by omega
  [(ty bits valid).lo,(ty bits valid).hi,-1,0,1,5].all (check p inc pre bits valid)))

/-- Complete old-capture, write and returned-result observations for uint8 overflow. -/
def observe (inc pre : Bool) : Option (Int × Int × Int × Int × Int) := do
  let captured ← (code 8 inc pre .here).run tgt |>.toOption
  let done ← (operand 8 inc pre .here).run tgt |>.toOption
  let .prim result := done.2
  pure ((TEnv.get .here tgt.env).val,
    (TEnv.get (.there .here) captured.st.env).val,
    (TEnv.get (.there (.there .here)) captured.st.env).val,
    result.val,(TEnv.get .here done.1.st.env).val)

/-- info: [some (255, 255, 0, 255, 0), some (255, 255, 0, 0, 0), some (255, 255, 254, 255, 254), some (255, 255, 254, 254, 254)] -/
#guard_msgs in
#eval IO.println (reprStr [observe true false,observe true true,observe false false,observe false true])

-- Actual incorrect programs: uncaptured postfix read, skipped write, wrong update.
/-- info: [some (255, 255, 0, 255, 0), some (255, 255, 0, 0, 0), some (255, 255, 255, 255, 255), some (255, 255, 254, 255, 254)] -/
#guard_msgs in
#eval IO.println (reprStr [
  observe true false,
  match (code 8 true false .here).run tgt with
    | .ok out => match (Val.simple (.local (.there (.there .here))) : Val C _ .uint).evalT out.st with
      | .ok wrong => some (255,255,wrong.val,wrong.val,wrong.val)
      | _ => none
    | _ => none,
  match (DeferredSource.Operand.ofSrc (Src.val (.simple (.local .here)))).run tgt with
    | .ok (out,.prim v) => some (255,255,(TEnv.get .here out.st.env).val,v.val,(TEnv.get .here out.st.env).val)
    | _ => none,
  observe false false])

-- This closed combination control does not claim a general argument compiler.
def pair_source (p : Roadmap.Pipeline) : Option (Int × Int × Int × Int) :=
  match (Source.evalPair (globals p) {F0 with checked := false} 3
    (.incDec true false (.local .here)) (.local .here)).run src with
  | (.ok (.val left,.val right),out) => do
    pure (← left.key,← right.key,← (out.1.get .here).key,← (out.1.get (.there .here)).key)
  | _ => none

def pair_target (p : Roadmap.Pipeline) : Option (Int × Int × Int × Int) := do
  match p with
  | .legacy =>
    let right ← (Val.simple (.local .here) : Val C _ .uint).evalT tgt |>.toOption
    let (out,.prim left) ← (operand 8 true false .here).run tgt |>.toOption
    pure (left.val,right.val,(TEnv.get .here out.st.env).val,(TEnv.get (.there .here) out.st.env).val)
  | .viaIR =>
    let (out,.prim left) ← (operand 8 true false .here).run tgt |>.toOption
    let right ← (Val.simple (.local .here) : Val C _ .uint).evalT out.st |>.toOption
    pure (left.val,right.val,(TEnv.get .here out.st.env).val,(TEnv.get (.there .here) out.st.env).val)

/-- info: [some (255, 255, 0, 7), some (255, 0, 0, 7), some (255, 255, 0, 7), some (255, 0, 0, 7)] -/
#guard_msgs in
#eval IO.println (reprStr [pair_source .legacy,pair_source .viaIR,pair_target .legacy,pair_target .viaIR])

-- Choosing the other pipeline's operand order is observably incorrect.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr (pair_source .viaIR != pair_target .legacy && pair_source .legacy != pair_target .viaIR))

-- The unchecked premise matters: checked overflow reverts before any write.
/-- info: true -/
#guard_msgs in
#eval IO.println (reprStr ([Roadmap.Pipeline.legacy,.viaIR].all fun p =>
  match (Source.evalE (globals p) {F0 with checked := true} 2 (.incDec true false (.local .here))).run src with
  | (.error (.revert data),out) => data == Source.panicData .arithmetic && (out.1.get .here).key == some 255
  | _ => false))

end Solidity.Lowering.V07.UnsignedLocalUpdateControls

/-- info: 'Solidity.Lowering.V07.UnsignedLocalUpdateControls.value_source_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedLocalUpdateControls.value_source_client

/-- info: 'Solidity.Lowering.V07.UnsignedLocalUpdateControls.source_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedLocalUpdateControls.source_client

/-- info: 'Solidity.Lowering.V07.UnsignedLocalUpdateControls.value_target_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedLocalUpdateControls.value_target_client

/-- info: 'Solidity.Lowering.V07.UnsignedLocalUpdateControls.code_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedLocalUpdateControls.code_client

/-- info: 'Solidity.Lowering.V07.UnsignedLocalUpdateControls.operand_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedLocalUpdateControls.operand_client

/-- info: 'Solidity.Lowering.V07.UnsignedLocalUpdateControls.transport_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedLocalUpdateControls.transport_client

/-- info: 'Solidity.Lowering.V07.UnsignedLocalUpdateControls.repeated_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedLocalUpdateControls.repeated_client

/-- info: 'Solidity.Lowering.V07.UnsignedLocalUpdateControls.equal_content_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedLocalUpdateControls.equal_content_client

/-- info: 'Solidity.Lowering.V07.UnsignedLocalUpdateControls.extension_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedLocalUpdateControls.extension_client

/-- info: 'Solidity.Lowering.V07.UnsignedLocalUpdateControls.binder_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedLocalUpdateControls.binder_client

/-- info: 'Solidity.Lowering.V07.UnsignedLocalUpdateControls.live_caller' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedLocalUpdateControls.live_caller

/-- info: 'Solidity.Lowering.V07.UnsignedLocalUpdateControls.source_frame_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedLocalUpdateControls.source_frame_client
