import Solidity.Backend.InternalFlow.RuntimeFrameV3PrimitiveCallerFrame
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarRecursiveControls
import Solidity.Backend.InternalFlow.RuntimeFrameV3EffectfulScalarSource

/-! Inhabited native calls with a real private allocation and old-object write.
Assigned and discarded primitive returns use the same arguments and body.
Only source/kernel evidence is claimed, not a target compiler or heap frame. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource CountdownWitness
namespace Q
abbrev C := CountdownWitness.P.C
abbrev Γ := ScalarRecursiveSource.Controls.Γ
abbrev caller := ScalarRecursiveSource.Controls.caller
abbrev args := ScalarRecursiveSource.Controls.args
end Q
abbrev B : RefTy := .array (.prim .bool)
def allocate : Stmt Q.C (Frame A) (Frame A) :=
 .block (.cons (.declMem B (.user "private") (some (.newArr (.lit 3 rfl) rfl)) rfl rfl) .nil)
def body : Prog Q.C (Frame A) (Frame A) :=
 .cons allocate (.cons EffectfulScalarSource.write (.cons (.assignLocal .here (.simple (.lit 5 rfl))) .nil))
def invoke (destination : Option (Idx Q.Γ (.val .uint))) : Stmt Q.C Q.Γ Q.Γ :=
 .call "primitiveFrame" Q.args (.val .uint (.user "result") destination) body

def allocated := (Q.caller.alloc (defaultArray .bool (⟨3,by decide⟩ : Fin W))).1
def extension : Q.caller.H <+: allocated.H := List.prefix_append _ _
def oldReference : HRef allocated.H A := CompileExamples.r0.wk extension
def changed := allocated.withHeap (allocated.heap.set oldReference
 (MObj.setElem .dyn (allocated.heap.get oldReference) 0 (countValue 37 (by decide))))
def output : Solidity.Out Q.C Q.caller.H Q.Γ :=
 ⟨changed.setLocal .here (countValue 5 (by decide)),extension⟩
def discarded : Solidity.Out Q.C Q.caller.H Q.Γ := ⟨changed,extension⟩

theorem native : (invoke (some .here)).run Q.caller=.ok output := by with_unfolding_all rfl

theorem native_discarded : (invoke none).run Q.caller=.ok discarded := by with_unfolding_all rfl

theorem retained_scalar : TEnv.get (.there .here : Idx Q.Γ (.val .uint)) output.st.env=
 LTy.TDenote.wk output.ext (.val .uint) (TEnv.get (.there .here : Idx Q.Γ (.val .uint)) Q.caller.env) :=
 assigned_slot "primitiveFrame" Q.args (.user "result") .here body Q.caller output native (.there .here) (by decide)

theorem retained_reference : TEnv.get (.there (.there .here) : Idx Q.Γ (.mem A)) output.st.env=
 LTy.TDenote.wk output.ext (.mem A) (TEnv.get (.there (.there .here) : Idx Q.Γ (.mem A)) Q.caller.env) :=
 assigned_slot "primitiveFrame" Q.args (.user "result") .here body Q.caller output native (.there (.there .here)) (by decide)

theorem discarded_frame : discarded.st.env=TEnv.wk discarded.ext Q.Γ Q.caller.env :=
 discarded_env "primitiveFrame" Q.args (.user "result") body Q.caller discarded native_discarded

theorem observations :
 ((TEnv.get (.here : Idx Q.Γ (.val .uint)) output.st.env).val,
 (TEnv.get (.there .here : Idx Q.Γ (.val .uint)) output.st.env).val,
 (TEnv.get (.there (.there .here) : Idx Q.Γ (.mem A)) output.st.env).map HRef.id,
 (TEnv.get (.there (.there (.there .here)) : Idx Q.Γ (.mem A)) output.st.env).map HRef.id,
 (TEnv.get (.there (.there (.there (.there .here))) : Idx Q.Γ (.mem A)) output.st.env).map HRef.id,
 output.st.H.length,output.st.heap.len oldReference .dyn)=
 (5,2,some 0,some 0,some 1,3,2) := by with_unfolding_all rfl

theorem wrong_scalar : (TEnv.get (.there .here : Idx Q.Γ (.val .uint)) output.st.env).val≠3 := by decide +kernel

theorem private_not_escaped :
 (TEnv.get (.there (.there .here) : Idx Q.Γ (.mem A)) output.st.env).map HRef.id≠some 2 := by decide +kernel

theorem not_keeps : ¬Heap.Keeps output.ext Q.caller.heap output.st.heap := by
 intro kept
 have object := kept CompileExamples.r0
 have values := congrArg (fun object : MObj output.st.H A => object.val.map (fun value => value.val)) object
 with_unfolding_all change ([37,9] : List Int)=[7,9] at values
 have different : ([37,9] : List Int)≠[7,9] := by decide
 exact different values

theorem discarded_result : (TEnv.get (.here : Idx Q.Γ (.val .uint)) discarded.st.env).val=77 := rfl

theorem not_revert : (invoke (some .here)).run Q.caller≠.error .revert := by
 rw [native]
 intro wrong
 cases wrong

def privateReference : HRef output.st.H B := ⟨2,by with_unfolding_all rfl⟩

theorem heap_observations :
 ((output.st.heap.get oldReference).val.map (fun value => value.val),
 (output.st.heap.get (CompileExamples.r1.wk output.ext)).val.map (fun value => value.val),
 (output.st.heap.get privateReference).val)=
 ([37,9],[4],[false,false,false]) := by with_unfolding_all rfl

def absent := Q.caller.setLocal (.there (.there .here)) (none : Option (HRef Q.caller.H A))

theorem bad_arguments : (invoke (some .here)).run absent=.error .revert := by with_unfolding_all rfl

theorem wrong_destination : (invoke (some .here)).run Q.caller≠
 (invoke (some (.there .here))).run Q.caller := by
 rw [native]
 intro wrong
 have restored := assigned_slot "primitiveFrame" Q.args (.user "result") (.there .here)
  body Q.caller output wrong.symm (.here : Idx Q.Γ (.val .uint)) (by decide)
 have impossible := congrArg (fun value : PrimTy.uint.Denote => value.val) restored
 change (5:Int)=77 at impossible
 omega

end Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.native

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.native_discarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.native_discarded

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.retained_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.retained_scalar

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.retained_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.retained_reference

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.discarded_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.discarded_frame

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.observations' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.observations

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.wrong_scalar' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.wrong_scalar

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.private_not_escaped' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.private_not_escaped

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.not_keeps' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.not_keeps

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.discarded_result' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.discarded_result

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.not_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.not_revert

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.heap_observations' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.heap_observations

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.bad_arguments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.bad_arguments

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.wrong_destination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.PrimitiveCallerFrame.Controls.wrong_destination
