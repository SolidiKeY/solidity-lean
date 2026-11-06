import Solidity.Yul.Adapters.PhysicalObject
import Solidity.Source.Semantics

namespace Solidity.Yul.Adapters.PhysicalObject.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Views
private def C : Contract := {vars:=[]}
private def E : Source.Env := ⟨[]⟩
private def initial : Source.EMState E [] := (.nil,Source.St.init E)
private def old (text : Bool) : Σ τ, Source.Data E.layout τ :=
  if text then ⟨.string .memory,.string [1,2]⟩ else ⟨.bytes .memory,.bytes [1,2]⟩
private def y (text : Bool) : Source.EMState E [] := ((Source.allocRef (old text).2).run initial).2
private def residual : ByteView := mstore
  (fun k=>if k=170 then 77 else if k=223 then 170 else 0) 64 ⟨192,by decide⟩
private def raw : ByteView := bytesObjectView [255,0,9] (by decide) residual 128
private def image (p : Pipeline) : FrameMem C [] :=
  {st:=State.init C,key:=⟨9,1,p,3,lenU 1 (by decide),lenU 2 (by decide),lenU 0 (by decide)⟩
   scalar:=by intro R i;cases i
   capacity:=256,aligned:=⟨8,rfl⟩,data:=fun i=>raw i.val
   highWaterWords:=8,resident:=by decide,zeroAbove:=by intro i hi;have h:=i.isLt;omega}
private theorem image_raw (p : Pipeline) : frameBytes (image p)=raw := by
  funext k
  change (if h : k<256 then raw k else 0)=raw k
  by_cases inside : k<256
  · exact dif_pos inside
  · rw [dif_neg inside]
    rw [raw,bytesObject_residual _ _ _ _ _ (by right;change 128+32+3≤k;omega)]
    rw [residual,mstore_outside _ _ _ _ (by omega)]
    rw [if_neg (by omega),if_neg (by omega)]

theorem initial_MemOK (text : Bool) : Source.MemOK E (y text).2.heap.ty (y text) := by
  have top : (old text).2.Top := by cases text <;> trivial
  have inner : (old text).2.Inner := by cases text <;> trivial
  have data : Source.DataOK E initial.2.heap.ty (old text).2 := by
    cases text
    · exact .bytes _
    · exact .string _
  have start : Source.MemOK E initial.2.heap.ty initial :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have keep:=Source.allocRef_mem' (E:=E) (Γ:=[]) (H:=initial.2.heap.ty) (old text).2 top inner initial ⟨start,data⟩
  have final : Source.MemOK E initial.2.heap.ty (y text) := by
    cases text <;> exact keep.1
  exact final.self

theorem real_span (p : Pipeline) : Within (image p) 128 := by
  rw [Within,image_raw,raw,bytesObject_header]
  change 128+32+3≤256
  decide

theorem changed_source (text : Bool) (p : Pipeline) : ∃ z,
    (commit (image p) text 0 128).run (y text)=(.ok (),z) ∧
    Source.MemOK E (y text).2.heap.ty z ∧
    (Source.heapBytes (E:=E) (Γ:=[]) 0).run z=(.ok [255,0,9],z) := by
  have decoded : packet E.layout text (frameBytes (image p)) 128=
      (if text then ⟨.string .memory,.string [255,0,9]⟩ else ⟨.bytes .memory,.bytes [255,0,9]⟩) := by
    rw [image_raw]
    exact packet_encode _ _ _ _ _ _
  obtain ⟨z,run,found,other,mem,reconstruct,types,next,locals,state⟩:=
    commit_agreement (image p) text 0 128 (y text) (by rw [decoded];cases text <;> rfl)
  refine ⟨z,run,mem _ (initial_MemOK text),?_⟩
  rw [decoded] at found
  rw [Source.heapBytes,Source.Hoare.run_bind,Solidity.Backend.MemoryOps.source_heapObj_run z 0 _ found]
  cases text <;> rfl

theorem whole_frame_identity (p : Pipeline) :
    MemoryAgreement.writeback (image p)
      (bytesObjectView (payload (frameBytes (image p)) 128) (payload_bound _ _) (frameBytes (image p)) 128)
      (by rw [reconstruct];exact MemoryAgreement.fits_view _)=image p := unchanged_frame _ _

private def observed (p : Pipeline) : List Nat :=
  [ (mload (frameBytes (image p)) 128).val,
    (frameBytes (image p) 160).toNat,(frameBytes (image p) 162).toNat,
    (frameBytes (image p) 170).toNat,(frameBytes (image p) 223).toNat,
    (mload (frameBytes (image p)) 64).val,(mload (frameBytes (image p)) 96).val]
/-- info: [3, 255, 9, 77, 170, 192, 0] -/
#guard_msgs in #eval observed .legacy
/-- info: [3, 255, 9, 77, 170, 192, 0] -/
#guard_msgs in #eval observed .viaIR
/-- info: false -/
#guard_msgs in #eval decide (observed .legacy=[3,255,9,0,170,192,0])
private def yBoth : Source.EMState E [] :=
  ((Source.allocRef (Source.Data.string (D:=E.layout) (l:=.memory) [3,4])).run (y false)).2
private def rawBoth : ByteView := bytesObjectView [128,255] (by decide)
  (bytesObjectView [255,0,9] (by decide) (mstore residual 64 ⟨256,by decide⟩) 128) 192
private def imageBoth (p : Pipeline) : FrameMem C [] :=
  {image p with
    capacity:=320
    aligned:=⟨10,rfl⟩
    data:=fun i=>rawBoth i.val
    highWaterWords:=10
    resident:=by decide
    zeroAbove:=by intro i hi;have h:=i.isLt;omega}
private def specs : List (Bool × Nat × Nat) := [(false,0,128),(true,1,192)]
private theorem readyBoth (p : Pipeline) : ∀ spec∈specs,
    yBoth.2.heap.ty spec.2.1=some (packet E.layout spec.1 (frameBytes (imageBoth p)) spec.2.2).1 := by
  intro spec hs
  simp only [specs,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl <;> rfl
private theorem both_MemOK : Source.MemOK E yBoth.2.heap.ty yBoth := by
  have keep:=Source.allocRef_mem' (E:=E) (Γ:=[]) (H:=(y false).2.heap.ty)
    (Source.Data.string (l:=.memory) [3,4]) trivial trivial (y false)
    ⟨initial_MemOK false,.string _⟩
  exact keep.1.self

theorem mixed_snapshot (p : Pipeline) : ∃ z,
    (ObjectWriteback.putAll (packets (E:=E) (imageBoth p) specs)).run yBoth=(.ok (),z) ∧
    Source.MemOK E yBoth.2.heap.ty z := by
  obtain ⟨z,run,types,next,locals,state,other,mem⟩:=commit_many (imageBoth p) specs yBoth (readyBoth p)
  exact ⟨z,run,mem _ both_MemOK⟩

private def observedBoth (p : Pipeline) (reverse : Bool) : List Nat :=
  let requests:=packets (E:=E) (imageBoth p) (if reverse then specs.reverse else specs)
  let z:=((ObjectWriteback.putAll requests).run yBoth).2
  let read (a : Nat) : List Nat := match ((Source.heapBytes (E:=E) (Γ:=[]) a).run z).1 with
    | .ok bs=>bs.map UInt8.toNat | _=>[]
  read 0++read 1++[(frameBytes (imageBoth p) 170).toNat,
    (mload (frameBytes (imageBoth p)) 64).val,(mload (frameBytes (imageBoth p)) 96).val]
/-- info: [255, 0, 9, 128, 255, 77, 256, 0] -/
#guard_msgs in #eval observedBoth .legacy false
/-- info: [255, 0, 9, 128, 255, 77, 256, 0] -/
#guard_msgs in #eval observedBoth .viaIR true
/-- info: false -/
#guard_msgs in #eval decide (observedBoth .legacy false=[255,0,9,128,255,0,256,0])
private def checkedSpecs (text : Bool) : List (Bool × Nat × Nat) :=
  [(text,0,128),(!text,0,128),(text,0,0)]

/-- Both bytes/string and pipeline tags retain the first decoded payload on a
real Source mismatch; the later header0 request is never executed. -/
theorem checked_snapshot (text : Bool) (p : Pipeline) : ∃ z,
    (ObjectWriteback.putAll (packets (E:=E) (image p) (checkedSpecs text))).run (y text)=
      (.error (.stuck "memory write type"),z) ∧
    Source.MemOK E (y text).2.heap.ty z ∧
    (Source.heapBytes (E:=E) (Γ:=[]) 0).run z=(.ok [255,0,9],z) := by
  let requests := packets (E:=E) (image p) (checkedSpecs text)
  let good := fun request : ObjectWriteback.Request E=>decide ((y text).2.heap.ty request.1=some request.2.1)
  obtain ⟨z,run,complete,types,next,locals,state,other,mem,raw⟩ :=
    commit_many_checked (image p) (checkedSpecs text) (y text)
  have head : (ObjectWriteback.putAll (requests.takeWhile good)).run (y text)=
      (commit (image p) text 0 128).run (y text) := by cases text <;> rfl
  have stop : (requests.dropWhile good).isEmpty=false := by cases text <;> rfl
  change (ObjectWriteback.putAll (requests.takeWhile good)).run (y text)=(.ok (),z) at run
  rw [head] at run
  change (ObjectWriteback.putAll requests).run (y text)=
    ((if (requests.dropWhile good).isEmpty then .ok () else .error (.stuck "memory write type")),z) at complete
  simp only [stop,Bool.false_eq_true,if_false] at complete
  obtain ⟨out,first,ok,read⟩ := changed_source text p
  have same : z=out := congrArg Prod.snd (run.symm.trans first)
  refine ⟨z,complete,mem _ (initial_MemOK text),?_⟩
  rw [same]
  exact read

private def checkedObserved (text : Bool) (p : Pipeline) : List Nat :=
  let result := (ObjectWriteback.putAll (packets (E:=E) (image p) (checkedSpecs text))).run (y text)
  let status := match result.1 with | .error (.stuck "memory write type")=>1 | _=>0
  let value := ((Source.heapBytes (E:=E) (Γ:=[]) 0).run result.2).1.toOption.getD []
  status::value.map UInt8.toNat
/-- info: [1, 255, 0, 9] -/
#guard_msgs in #eval checkedObserved false .legacy
/-- info: [1, 255, 0, 9] -/
#guard_msgs in #eval checkedObserved true .viaIR
/-- info: (false, false) -/
#guard_msgs in #eval
  (checkedObserved false .viaIR==[1],checkedObserved true .legacy==[1,1,2])

end Solidity.Yul.Adapters.PhysicalObject.Controls
