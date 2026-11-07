import Solidity.Backend.Passes.ComparisonReferenceCapture
import Solidity.Backend.Passes.LinkedControls
import Solidity.Backend.Passes.CapturedValueStability
import Solidity.Backend.PrimitivePackets.Comparisons.Controls

/-! Runtime comparison chooses an old populated array and captures its alias.
The consuming read includes both original array elements and the independent
object in its observation vector; no heap object or map is fabricated. -/
namespace Solidity.Backend.Passes.ComparisonReferenceCaptureControls
open Evm Evm.Memory Evm.Compiler Backend.PrimitivePackets
open Comparisons (Order prim ty)
open Comparisons.Controls (word word_repr)
open Lowering.V07 (integerValue)
open Controls.Fixture (C σ machine base fixture_repr)
open ComparisonReferenceCapture
abbrev A : RefTy := .array (.prim .uint)
def Γ (signed : Bool) : Ctx := .val (prim signed) :: .val (prim signed) :: CompileExamples.Γ
def F (signed : Bool) : Frag (Γ signed) :=
  ((Frag.init CompileExamples.Γ).push (.val (prim signed)) .ok).push (.val (prim signed)) .ok
abbrev i (signed : Bool) : Idx (Γ signed) (.val (prim signed)) := .here
abbrev j (signed : Bool) : Idx (Γ signed) (.val (prim signed)) := .there .here
abbrev dst (signed : Bool) : Idx (Γ signed) (.mem A) := .there (.there (.there .here))
abbrev yes (signed : Bool) : Idx (Γ signed) (.mem A) := .there (.there (.there (.there (.there .here))))
abbrev no (signed : Bool) : Idx (Γ signed) (.mem A) := .there (.there (.there (.there .here)))
def name : Var := .user "chosen"
def state (signed : Bool) (x y : Int)
    (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi) (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi) :
    State C (Γ signed) :=
  (σ.push (t := .val (prim signed)) (integerValue (ty signed) y hy)).push
    (t := .val (prim signed)) (integerValue (ty signed) x hx)
def target (signed : Bool) (x y : Int)
    (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi) (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi) : Machine :=
  writeMachine (writeMachine machine 4 (word signed y hy)) 5 (word signed x hx)

theorem frame_eight : StateRepr 1 0 8 (Frag.init CompileExamples.Γ) σ base machine :=
  memory_frame fixture_repr (by decide)
    (fun r => by unfold base; split <;> decide +kernel)
    (fun r => by unfold base; split <;> decide +kernel)

theorem represented (signed : Bool) (x y : Int)
    (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi) (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi) :
    StateRepr 1 0 8 (F signed) (state signed x y hx hy) base (target signed x y hx hy) :=
  (frame_eight.consVal (integerValue (ty signed) y hy) (word signed y hy)
    (word_repr signed y hy) (by decide)).consVal
      (integerValue (ty signed) x hx) (word signed x hx) (word_repr signed x hx) (by change 6 ≤ 8; decide)

def cert (order : Order) (signed : Bool) :=
  whole (C := C) 0 (F signed) order signed (i signed) (j signed) name
    (dst signed) (yes signed) (no signed) rfl

theorem inhabited (order : Order) (signed : Bool) (x y : Int)
    (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi) (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi) :
    type_of% (execution order signed (i signed) (j signed) name (dst signed) (yes signed) (no signed) rfl
      (represented signed x y hx hy) (by change 7 ≤ 8; decide) x y hx hy rfl rfl) :=
  execution order signed (i signed) (j signed) name (dst signed) (yes signed) (no signed) rfl
    (represented signed x y hx hy) (by change 7 ≤ 8; decide) x y hx hy rfl rfl

def read : Val C (.mem A :: Γ signed) .uint :=
  .readMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))
def reader (order : Order) (signed : Bool) :
    CompiledVal 0 (code (C := C) 0 (F signed) order signed (i signed) (j signed)
      name (dst signed) (yes signed) (no signed) rfl).frag read :=
  (compileVal 0 _ read).get (by cases order <;> cases signed <;> rfl)
theorem reader_public (order : Order) (signed : Bool) :
    compileVal 0 _ (read (signed := signed)) = some (reader order signed) :=
  (Option.some_get _).symm

def cells : List Nat := [6,5,4,3,2,1,0,7,16,17,18,20,21]
def observe : Evm.Out → Option (List Word × List Word)
  | .ok m _ => some (cells.map m.mem,m.stack)
  | _ => none

theorem false_vector : observe (run ((cert .lt false).code ++ (reader .lt false).code)
    (target false 5 3 (by decide) (by decide))) =
    some ([w[16],w[5],w[3],w[0],w[16],w[16],w[20],w[0],w[2],w[7],w[9],w[1],w[4]],[w[7]]) := by decide +kernel

theorem true_vector : observe (run ((cert .gt false).code ++ (reader .gt false).code)
    (target false 5 3 (by decide) (by decide))) =
    some ([w[20],w[5],w[3],w[0],w[20],w[16],w[20],w[0],w[2],w[7],w[9],w[1],w[4]],[w[4]]) := by decide +kernel

theorem signed_vector : observe (run ((cert .lt true).code ++ (reader .lt true).code)
    (target true (-1) 1 (by decide) (by decide))) =
    some ([w[20],.val (sword (-1)),w[1],w[0],w[20],w[16],w[20],w[0],w[2],w[7],w[9],w[1],w[4]],[w[4]]) := by decide +kernel

theorem equality_vectors (order : Order) :
    observe (run ((cert order false).code ++ (reader order false).code)
      (target false 5 5 (by decide) (by decide))) =
    some ([if Comparisons.result order 5 5 then w[20] else w[16],w[5],w[5],w[0],
      if Comparisons.result order 5 5 then w[20] else w[16],w[16],w[20],w[0],w[2],w[7],w[9],w[1],w[4]],
      [if Comparisons.result order 5 5 then w[4] else w[7]]) := by
  cases order <;> decide +kernel

theorem tails (tail : List Word) :
    observe (run ((cert .gt false).code ++ (reader .gt false).code)
      {(target false 5 3 (by decide) (by decide)) with stack := tail}) =
    some ([w[20],w[5],w[3],w[0],w[20],w[16],w[20],w[0],w[2],w[7],w[9],w[1],w[4]],w[4]::tail) := by
  let start := state false 5 3 (by decide) (by decide)
  let machine0 := target false 5 3 (by decide) (by decide)
  let output := ((start.setLocal (dst false) (some CompileExamples.r1)).push
    (t := .mem A) (some CompileExamples.r1))
  have sourceRun : (program .gt false (i false) (j false) name (dst false) (yes false) (no false) rfl).run start =
      .ok ⟨output,List.prefix_refl _⟩ :=
    ConditionalReferenceCapture.source name (Comparisons.value .gt false (i false) (j false))
      (dst false) (yes false) (no false) rfl start true
      (Comparisons.intrinsic_run start .gt false (i false) (j false) 5 3 (by decide) (by decide) rfl rfl)
      CompileExamples.r1 CompileExamples.r0 rfl rfl
  have admitted := ComparisonReferenceCapture.input .gt false (i false) (j false) name
    (dst false) (yes false) (no false) rfl (represented false 5 3 (by decide) (by decide)) (by decide)
  obtain ⟨canonical,selected,_,empty,allRuns⟩ :=
    compilation_success_shared_mapped (cert .gt false) admitted rfl sourceRun
  have mapped := (allRuns []).2
  rw [(code (C := C) 0 (F false) .gt false (i false) (j false) name
    (dst false) (yes false) (no false) rfl).cert.pushes_zero,Nat.add_zero] at mapped
  obtain ⟨w,relation,reads⟩ := CapturedValueStability.value_shared read (reader .gt false)
    mapped.1 (CompileExamples.uint 4 (by decide)) (by with_unfolding_all rfl)
  have word : w = w[4] := by
    obtain ⟨a,hw,hv⟩ := relation
    have same : a = (⟨4,by decide⟩ : Fin W) := Fin.ext (by change a.val = 4; change (4 : Int) = (a.val : Int) at hv; omega)
    exact hw.trans (congrArg Word.val same)
  rw [word] at reads
  have joinedRun (saved : List Word) :
      run ((cert .gt false).code ++ (reader .gt false).code) {machine0 with stack := saved} =
      .ok ({canonical with stack := saved}.push w[4]) 0 := by
    rw [run_append_ok (allRuns saved).1]
    exact reads saved
  have projected : cells.map canonical.mem =
      [w[20],w[5],w[3],w[0],w[20],w[16],w[20],w[0],w[2],w[7],w[9],w[1],w[4]] := by
    have observed := true_vector
    change observe (run ((cert .gt false).code ++ (reader .gt false).code) {machine0 with stack := []}) = _ at observed
    rw [joinedRun []] at observed
    change some (cells.map canonical.mem,[w[4]]) = some (_,_) at observed
    exact (Prod.mk.inj (Option.some.inj observed)).1
  rw [joinedRun tail]
  change some (cells.map canonical.mem,w[4]::tail) = _
  rw [projected]

theorem stale_pointer_refused :
    ¬ StateRepr 1 0 8 (F false) (state false 5 3 (by decide) (by decide)) base
      (writeMachine (target false 5 3 (by decide) (by decide)) 0 w[16]) := by
  intro assumed
  obtain ⟨r,get,pointer⟩ := assumed.pointers (yes false)
  have same : CompileExamples.r1 = r := Option.some.inj get
  subst r
  change w[16] = w[20] at pointer
  have different : w[16] ≠ w[20] := by decide +kernel
  exact different pointer

theorem corrupted_tail :
    observe (run ((cert .gt false).code ++ (reader .gt false).code)
      {(target false 5 3 (by decide) (by decide)) with stack := [w[77]]}) ≠
    some ([w[20],w[5],w[3],w[0],w[20],w[16],w[20],w[0],w[2],w[7],w[9],w[1],w[4]],[w[4],w[88]]) := by decide +kernel

def wrongProgram : Prog C (Γ false) (.mem A :: Γ false) :=
  .cons (.declMem A name (some (.alias (.var (dst false) rfl))) rfl rfl)
    (.cons (.ite (Comparisons.value .gt false (.there (i false)) (.there (j false)))
      (.cons (.rebindMem (.there (dst false)) (.alias (.var (.there (yes false)) rfl))) .nil)
      (.cons (.rebindMem (.there (dst false)) (.alias (.var (.there (no false)) rfl))) .nil)) .nil)
def wrongCode : CompiledProg 0 (F false) wrongProgram :=
  (Memory.compileProg 0 (F false) wrongProgram).get (by rfl)
theorem wrong_public : Memory.compileProg 0 (F false) wrongProgram = some wrongCode := rfl

def nativeLocals (out : TRes (Solidity.Out C σ.H (.mem A :: Γ false))) : Option (List Int) :=
  match out with
  | .error _ => none
  | .ok o => some [((TEnv.get .here o.st.env).map (fun r => (r.id : Int))).getD (-1),
      (TEnv.get (.there (i false)) o.st.env).val,(TEnv.get (.there (j false)) o.st.env).val,
      (TEnv.get (.there (.there (.there .here))) o.st.env).val,
      ((TEnv.get (.there (dst false)) o.st.env).map (fun r => (r.id : Int))).getD (-1),
      ((TEnv.get (.there (no false)) o.st.env).map (fun r => (r.id : Int))).getD (-1),
      ((TEnv.get (.there (yes false)) o.st.env).map (fun r => (r.id : Int))).getD (-1)]

theorem native_order_vectors :
    nativeLocals (wrongProgram.run (state false 5 3 (by decide) (by decide))) = some [0,5,3,0,1,0,1] ∧
    nativeLocals ((program .gt false (i false) (j false) name (dst false) (yes false) (no false) rfl).run
      (state false 5 3 (by decide) (by decide))) = some [1,5,3,0,1,0,1] := by
  constructor <;> decide +kernel

def wrongReader : CompiledVal 0 wrongCode.frag (read (signed := false)) :=
  (compileVal 0 wrongCode.frag read).get (by rfl)
theorem wrong_reader_public : compileVal 0 wrongCode.frag (read (signed := false)) = some wrongReader := rfl

theorem wrong_order_vector :
    observe (run (wrongCode.code ++ wrongReader.code) (target false 5 3 (by decide) (by decide))) =
    some ([w[16],w[5],w[3],w[0],w[20],w[16],w[20],w[0],w[2],w[7],w[9],w[1],w[4]],[w[7]]) := by decide +kernel

theorem signedness_distinguished :
    observe (run ((cert .lt true).code ++ (reader .lt true).code)
      (target true (-1) 1 (by decide) (by decide))) ≠
    some ([w[16],.val (sword (-1)),w[1],w[0],w[16],w[16],w[20],w[0],w[2],w[7],w[9],w[1],w[4]],[w[7]]) := by decide +kernel

theorem frame_refused :
    ¬ (cert .gt false).Input 1 6 base (state false 5 3 (by decide) (by decide))
      (target false 5 3 (by decide) (by decide)) := by
  intro admitted
  have bound : 7 ≤ 6 := admitted.2.1
  omega

theorem source_component (order : Order) (signed : Bool) (p : Roadmap.Pipeline) (fuel : Nat)
    (x y : Int) (hx : (ty signed).lo ≤ x ∧ x ≤ (ty signed).hi) (hy : (ty signed).lo ≤ y ∧ y ≤ (ty signed).hi) :
    type_of% (Comparisons.source_run (Comparisons.Controls.global p) Comparisons.Controls.frame fuel
      (Comparisons.Controls.source signed x y hx hy) order signed .here (.there .here) x y hx hy rfl rfl) :=
  Comparisons.source_run (Comparisons.Controls.global p) Comparisons.Controls.frame fuel
    (Comparisons.Controls.source signed x y hx hy) order signed .here (.there .here) x y hx hy rfl rfl

/-- info: 'Solidity.Backend.Passes.ComparisonReferenceCaptureControls.wrong_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_public
/-- info: 'Solidity.Backend.Passes.ComparisonReferenceCaptureControls.native_order_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms native_order_vectors
/-- info: 'Solidity.Backend.Passes.ComparisonReferenceCaptureControls.wrong_reader_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_reader_public
/-- info: 'Solidity.Backend.Passes.ComparisonReferenceCaptureControls.wrong_order_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_order_vector
/-- info: 'Solidity.Backend.Passes.ComparisonReferenceCaptureControls.signedness_distinguished' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signedness_distinguished
/-- info: 'Solidity.Backend.Passes.ComparisonReferenceCaptureControls.frame_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms frame_refused
/-- info: 'Solidity.Backend.Passes.ComparisonReferenceCaptureControls.frame_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms frame_eight
/-- info: 'Solidity.Backend.Passes.ComparisonReferenceCaptureControls.represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms represented
/-- info: 'Solidity.Backend.Passes.ComparisonReferenceCaptureControls.inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inhabited
/-- info: 'Solidity.Backend.Passes.ComparisonReferenceCaptureControls.reader_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reader_public
/-- info: 'Solidity.Backend.Passes.ComparisonReferenceCaptureControls.false_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms false_vector
/-- info: 'Solidity.Backend.Passes.ComparisonReferenceCaptureControls.true_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms true_vector
/-- info: 'Solidity.Backend.Passes.ComparisonReferenceCaptureControls.signed_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signed_vector
/-- info: 'Solidity.Backend.Passes.ComparisonReferenceCaptureControls.equality_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms equality_vectors
/-- info: 'Solidity.Backend.Passes.ComparisonReferenceCaptureControls.tails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tails
/-- info: 'Solidity.Backend.Passes.ComparisonReferenceCaptureControls.stale_pointer_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stale_pointer_refused
/-- info: 'Solidity.Backend.Passes.ComparisonReferenceCaptureControls.corrupted_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms corrupted_tail
/-- info: 'Solidity.Backend.Passes.ComparisonReferenceCaptureControls.source_component' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_component
end Solidity.Backend.Passes.ComparisonReferenceCaptureControls
