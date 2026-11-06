import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarControls

/-! A public compiler-selected scoped allocation at the populated scalar callee
entry. This is a callee-only word-memory prefix, not a recursive compiler or a
whole caller/world representation. The dead private slot retains its pointer. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource CountdownWitness
abbrev F := CountdownWitness.F.push (.val .uint) .ok

def declaration : StmtFrag 2 (C:=P.C) F (F.push (.mem (.array (.prim .bool))) .ok)
 (.declMem (.array (.prim .bool)) (.user "private")
  (some (.newArr (AllocatingScalarSource.lengthExpr (C:=P.C) (R:=A)) rfl)) rfl rfl)
 (declareNewCode 2 (AllocatingScalarSource.lengthExpr (C:=P.C) (R:=A))) :=
 .allocate F .bool (.user "private") (AllocatingScalarSource.lengthExpr (C:=P.C) (R:=A)) (by decide) rfl

def selected : CompiledStmt 2 (C:=P.C) F (AllocatingScalarSource.allocate (R:=A)) :=
 ⟨(F.push (.mem (.array (.prim .bool))) .ok).restrict (Frame A),
 declareNewCode 2 (AllocatingScalarSource.lengthExpr (C:=P.C) (R:=A)) ++ [],
 .block _ _ (.cons declaration (.nil _))⟩

theorem public_selection : Memory.compileStmt 2 F (AllocatingScalarSource.allocate (C:=P.C) (R:=A))=some selected := by
 rfl

def initial := CountdownWitness.callee.push (t:=.val .uint) (countValue 0 (by decide))

theorem native_entry : initial=AllocatingScalarSource.Controls.initial := by
 rfl

def input := writeMachine AllocatorReturn.Checks.input 4 w[0]
def after := AllocatingScalarSource.allocated initial
def addresses := upd P.base initial.H.length (⟨22,by decide⟩ : Fin W)
def target := writeMachine (allocateMachine input (⟨22,by decide⟩ : Fin W) AllocatingScalarSource.size) 5 w[22]

theorem represented : StateRepr 1 2 16 F initial P.base input := by
 exact AllocatorReturn.Checks.represented.consVal (p:=.uint) (countValue 0 (by decide)) w[0]
   (ReprV.uint_of rfl) (by decide)

theorem ownership : StructAllocatorRepr initial.heap P.base 16 (⟨22,by decide⟩ : Fin W) input := by
 exact AllocatorReturn.Checks.ownership.localWrite 4 (by decide) (by decide) w[0]

theorem default_entry : run [.push w[0],.mstore 4] AllocatorReturn.Checks.input=.ok input 0 := by
 rfl

theorem exact_cost : selected.cert.cost initial=4 := by
 rfl

theorem frame_room : 2+frameNeedStmt (AllocatingScalarSource.allocate (C:=P.C) (R:=A)) ≤16 := by
 decide

theorem source_endpoint : AllocatingScalarSource.allocate.run initial=
 .ok ⟨after,AllocatingScalarSource.extension initial⟩ :=
 AllocatingScalarSource.scoped_allocation initial

theorem endpoint :
 run selected.code input=.ok target 0 ∧
 StateRepr 1 2 16 F after addresses target ∧
 StructAllocatorRepr after.heap addresses 16 (⟨26,by decide⟩ : Fin W) target ∧
 target.stack=input.stack ∧ Footprint.Words 8 16 input target := by
 obtain ⟨_,executed,repr,owner,stack,words⟩ :=
  Footprint.declare (σ:=initial) represented ownership (by decide) .bool (AllocatingScalarSource.lengthExpr (C:=P.C) (R:=A)) rfl AllocatingScalarSource.size rfl
   (by decide) (lo:=8) (by decide) (by decide)
 exact ⟨by simpa only [selected,List.append_nil] using executed,repr.drop (.push .refl),owner,stack,words⟩

theorem observations :
 (target.stack,[target.mem 0,target.mem 2,target.mem 3,target.mem 4,target.mem 5,
 target.mem 8,target.mem 9,target.mem 16,target.mem 17,target.mem 18,target.mem 20,
 target.mem 21,target.mem 22,target.mem 23,target.mem 24,target.mem 25])=
 ([w[77]],[w[26],w[16],w[2],w[0],w[22],w[10],w[99],w[2],w[7],w[9],w[1],w[4],w[3],w[0],w[0],w[0]]) := by
 rfl

theorem wrong_cursor : target.mem 0 ≠ w[25] := by
 decide

theorem wrong_result : target.mem 4 ≠ w[22] := by
 decide

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.public_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.public_selection

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.native_entry' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.native_entry

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.represented

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.ownership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.ownership

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.default_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.default_entry

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.exact_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.exact_cost

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.frame_room' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.frame_room

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.source_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.source_endpoint

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.endpoint

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.observations' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.observations

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.wrong_cursor' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.wrong_cursor

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.wrong_result' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScalarTarget.wrong_result
