import Solidity.Backend.Aggregates.G18SourceMapping
import Solidity.Backend.Aggregates.G18ScalarMappingControls

/-! Actual Source-machine storage fixtures at Env.cellTy, with nonempty
locals, heap, journal and logs. No physical source-to-target frame is claimed. -/
namespace Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls
open Lowering.V07

abbrev E (c : Solidity.Backend.Aggregates.ScalarMapping.Controls.Sample) : Source.Env := Solidity.Backend.Aggregates.ScalarMapping.Controls.env c.ty

def typed (c : Solidity.Backend.Aggregates.ScalarMapping.Controls.Sample) (key : Bool) : (E c).cellTy (Solidity.Backend.Aggregates.ScalarMapping.Controls.path key) = .int c.ty := rfl

def storage (c : Solidity.Backend.Aggregates.ScalarMapping.Controls.Sample) : Source.Storage (E c).layout (E c).cellTy :=
  ((Source.Storage.empty.write (Solidity.Backend.Aggregates.ScalarMapping.Controls.path true) (.int c.a c.ha)).write
    (Solidity.Backend.Aggregates.ScalarMapping.Controls.path false) (.int c.b c.hb))

def frame : Source.Fr :=
  {this := ⟨41,by decide⟩, sender := ⟨37,by decide⟩, value := ⟨5,by decide⟩,
   static := false, contract := "fixture", cd := [17,34]}

def state (c : Solidity.Backend.Aggregates.ScalarMapping.Controls.Sample) : Source.St (E c) :=
  {ex := ⟨⟨fun a => ⟨⟨(a.val+17) % 2^256, Nat.mod_lt _ (by decide)⟩, 3, some 9, storage c⟩⟩, Source.Transient.empty, [.account ⟨99,by decide⟩ (Source.Account.empty _)]⟩,
   heap := (Source.Heap.empty.alloc ⟨.bool,.val (.bool true)⟩).1,
   events := [], logs := [(⟨13,by decide⟩,[1,2])],
   fnLocals := ⟨[.bool],.cons (.bool false) .nil⟩}

def locals (c : Solidity.Backend.Aggregates.ScalarMapping.Controls.Sample) : Source.Locals (E c).layout [.bool] := .cons (.bool true) .nil

theorem cells : ∀ c : Solidity.Backend.Aggregates.ScalarMapping.Controls.Sample, Solidity.Backend.Aggregates.ScalarMapping.Cells c.ty ((Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c).ex.world.accounts Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.frame.this).storage (Solidity.Backend.Aggregates.ScalarMapping.Controls.beforeValue c) Solidity.Backend.Aggregates.ScalarMapping.Controls.path (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.typed c) := by
  intro c key
  cases key
  · refine ⟨c.b,c.hb,?_,?_⟩
    · exact Solidity.Source.Storage.write_read _ _ _
    · simp only [Solidity.Backend.Aggregates.ScalarMapping.Controls.beforeValue,Solidity.Backend.Aggregates.ScalarMapping.Controls.value,Solidity.Backend.Aggregates.ScalarMapping.Controls.entries,Solidity.Backend.Aggregates.ScalarMapping.Controls.fallback,Solidity.SVal.find_key,Solidity.SVal.find_nil,Solidity.SMap.toList_cons,Solidity.SMap.toList_nil,Solidity.Semantics.lookupBy,↓reduceIte] <;> rfl
  · refine ⟨c.a,c.ha,?_,?_⟩
    · change (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.storage c).read (Solidity.Backend.Aggregates.ScalarMapping.Controls.path true) = _
      rw [Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.storage,Solidity.Source.Storage.write_other _ (by decide +kernel),Solidity.Source.Storage.write_read]
    · simp only [Solidity.Backend.Aggregates.ScalarMapping.Controls.beforeValue,Solidity.Backend.Aggregates.ScalarMapping.Controls.value,Solidity.Backend.Aggregates.ScalarMapping.Controls.entries,Solidity.Backend.Aggregates.ScalarMapping.Controls.fallback,Solidity.SVal.find_key,Solidity.SVal.find_nil,Solidity.SMap.toList_cons,Solidity.SMap.toList_nil,Solidity.Semantics.lookupBy,↓reduceIte] <;> rfl

/-- All three actual phase results, not an input oracle. -/
def PhasePost (c : Solidity.Backend.Aggregates.ScalarMapping.Controls.Sample) : Prop :=
  (Source.readAt (E := E c) (Γ := [.bool]) frame (Solidity.Backend.Aggregates.ScalarMapping.Controls.path true) ((E c).cellTy (Solidity.Backend.Aggregates.ScalarMapping.Controls.path true))).run (locals c,state c) = (.ok (.int c.a c.ha),(locals c,state c)) ∧
  (Source.writeAt (E := E c) (Γ := [.bool]) frame (Solidity.Backend.Aggregates.ScalarMapping.Controls.path false) (.int c.a c.ha)).run (locals c,state c) = (.ok (), (locals c,writtenState (state c) frame (Solidity.Backend.Aggregates.ScalarMapping.Controls.path false) (.int c.a c.ha))) ∧
  CopyPost c.ty ((state c).ex.world.accounts frame.this).storage (Solidity.Backend.Aggregates.ScalarMapping.Controls.beforeValue c) (Solidity.Backend.Aggregates.ScalarMapping.Controls.afterValue c) Solidity.Backend.Aggregates.ScalarMapping.Controls.path (typed c) true false c.a c.ha Solidity.Backend.Aggregates.ScalarMapping.Controls.base (Solidity.Backend.Aggregates.ScalarMapping.Controls.beforeStore c) (Solidity.Backend.Aggregates.ScalarMapping.Controls.beforeTarget c)

theorem certificate : ∀ c : Solidity.Backend.Aggregates.ScalarMapping.Controls.Sample, Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.PhasePost c := by
  intro c
  obtain ⟨n,range,after,readResult,writeResult,post⟩ := Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.copy_phases (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E c) [.bool] .bool c.ty Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.frame (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c) (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals c) (Solidity.Backend.Aggregates.ScalarMapping.Controls.entries c.ty c.a c.b c.ha c.hb) (Solidity.Backend.Aggregates.ScalarMapping.Controls.fallback c.ty c.b c.hb) Solidity.Backend.Aggregates.ScalarMapping.Controls.path (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.typed c) Solidity.Backend.Aggregates.ScalarMapping.Controls.path_injective (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.cells c) (fun _ => rfl) rfl Solidity.Backend.Aggregates.ScalarMapping.Controls.base (Solidity.Backend.Aggregates.ScalarMapping.Controls.beforeStore c) (Solidity.Backend.Aggregates.ScalarMapping.Controls.represented c.ty c.a c.b c.ha c.hb) (Solidity.Backend.Aggregates.ScalarMapping.Controls.beforeTarget c) (Solidity.Backend.Aggregates.ScalarMapping.Controls.target_initial c.ty c.a c.b c.ha c.hb) true false
  have knownRead := Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.read (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E c) [.bool] Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.frame (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c) (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals c) (Solidity.Backend.Aggregates.ScalarMapping.Controls.path true) (.int c.a c.ha) rfl (by
    change (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.storage c).read (Solidity.Backend.Aggregates.ScalarMapping.Controls.path true) = _
    rw [Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.storage,Solidity.Source.Storage.write_other _ (by decide +kernel),Solidity.Source.Storage.write_read])
  have sameValue := Except.ok.inj (congrArg Prod.fst (knownRead.symm.trans readResult))
  have observed := congrArg Solidity.Source.Val.key sameValue
  have same : c.a = n := Option.some.inj observed
  subst n
  have saved := post.1.1
  have expected := Solidity.Storage.Representation.mapping_source_save (Solidity.Backend.Aggregates.ScalarMapping.Controls.entries c.ty c.a c.b c.ha c.hb) (Solidity.Backend.Aggregates.ScalarMapping.Controls.fallback c.ty c.b c.hb) (.prim (Solidity.Lowering.V07.integerValue c.ty c.a c.ha)) false
  have sameAfter : after = Solidity.Backend.Aggregates.ScalarMapping.Controls.afterValue c := Option.some.inj (saved.symm.trans expected)
  subst after
  exact ⟨readResult,writeResult,post⟩

def afterState (c : Solidity.Backend.Aggregates.ScalarMapping.Controls.Sample) : Source.St (E c) :=
  writtenState (state c) frame (Solidity.Backend.Aggregates.ScalarMapping.Controls.path false) (.int c.a c.ha)

def view (c : Solidity.Backend.Aggregates.ScalarMapping.Controls.Sample) (s : Source.St (E c)) : List (Option Int) × Nat × Nat × List (Roadmap.Address × Roadmap.Bytes) :=
  ([((s.ex.world.accounts frame.this).storage.read (Solidity.Backend.Aggregates.ScalarMapping.Controls.path true)).bind Source.Val.key,
    ((s.ex.world.accounts frame.this).storage.read (Solidity.Backend.Aggregates.ScalarMapping.Controls.path false)).bind Source.Val.key],
   s.ex.journal.length,s.heap.next,s.logs)

theorem state_cells : ∀ c : Solidity.Backend.Aggregates.ScalarMapping.Controls.Sample, Solidity.Backend.Aggregates.ScalarMapping.Cells c.ty ((Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.afterState c).ex.world.accounts Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.frame.this).storage (Solidity.Backend.Aggregates.ScalarMapping.Controls.afterValue c) Solidity.Backend.Aggregates.ScalarMapping.Controls.path (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.typed c) := by
  intro c
  have post := (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.certificate c).2.2.1.2.1
  simpa only [Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.afterState,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.writtenState,Solidity.Source.ExecState.apply,Solidity.Source.World.set_get] using post

theorem rollback : ∀ c : Solidity.Backend.Aggregates.ScalarMapping.Controls.Sample, let after := Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.writtenState (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c) Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.frame (Solidity.Backend.Aggregates.ScalarMapping.Controls.path false) (Solidity.Source.Val.int c.a c.ha); {after with ex := after.ex.undo} = Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c := by
  intro c
  dsimp only [Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.writtenState]
  rw [Solidity.Source.ExecState.undo_apply]

theorem ordered : Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.view Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned) = ([some 7,some 11],1,1,[(⟨13,by decide⟩,[1,2])]) ∧ Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.view Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.afterState Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned) = ([some 7,some 7],2,1,[(⟨13,by decide⟩,[1,2])]) ∧ Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.view Solidity.Backend.Aggregates.ScalarMapping.Controls.signed (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state Solidity.Backend.Aggregates.ScalarMapping.Controls.signed) = ([some (-1),some 11],1,1,[(⟨13,by decide⟩,[1,2])]) ∧ Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.view Solidity.Backend.Aggregates.ScalarMapping.Controls.signed (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.afterState Solidity.Backend.Aggregates.ScalarMapping.Controls.signed) = ([some (-1),some (-1)],2,1,[(⟨13,by decide⟩,[1,2])]) := by
  simp only [Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.view,Prod.mk.injEq]
  decide +kernel

theorem complete_frame : ∀ c : Solidity.Backend.Aggregates.ScalarMapping.Controls.Sample, { Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.afterState c with ex := (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c).ex } = Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c := by
  intro c
  rfl

theorem wrong_phase : (Solidity.Source.writeAt (E := Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned) (Γ := [.bool]) (τ := .int .u8) Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.frame (Solidity.Backend.Aggregates.ScalarMapping.Controls.path false) (Solidity.Source.Val.int 7 (by decide))).run (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned) ≠ (.ok (),(Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned)) := by
  intro wrong
  have actual := (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.certificate Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned).2.1
  have lengths := congrArg (fun result => result.2.2.ex.journal.length) (actual.symm.trans wrong)
  change 2 = 1 at lengths
  contradiction

theorem static_control : ∀ c : Solidity.Backend.Aggregates.ScalarMapping.Controls.Sample, (Solidity.Source.writeAt (E := Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E c) (Γ := [.bool]) (τ := .int c.ty) {Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.frame with static := true} (Solidity.Backend.Aggregates.ScalarMapping.Controls.path false) (Solidity.Source.Val.int c.a c.ha)).run (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals c,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c) = (.error (.revert []),(Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals c,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c)) ∧ Solidity.Evm.run Solidity.Backend.Aggregates.ScalarMapping.Controls.code (Solidity.Backend.Aggregates.ScalarMapping.Controls.beforeTarget c) = .ok (Solidity.Backend.Aggregates.ScalarMapping.writtenMachine (K := .bool) (Solidity.Backend.Aggregates.ScalarMapping.Controls.beforeTarget c) Solidity.Backend.Aggregates.ScalarMapping.Controls.base false (Solidity.PrimTy.toWord (Solidity.Lowering.V07.integerValue c.ty c.a c.ha))) 0 := by
  intro c
  constructor
  · exact Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.refused (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.E c) [.bool] _ (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state c) (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.locals c) (Solidity.Backend.Aggregates.ScalarMapping.Controls.path false) (.int c.a c.ha) rfl rfl
  · exact (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.certificate c).2.2.2.1

theorem negative_controls : Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.view Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.afterState Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned) ≠ Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.view Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned) ∧ Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.view Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned ({Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.afterState Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned with ex := (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.afterState Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned).ex.undo}) = Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.view Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned (Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned) ∧ (((Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.afterState Solidity.Backend.Aggregates.ScalarMapping.Controls.unsigned).ex.world.accounts ⟨99,by decide⟩).storage.read (Solidity.Backend.Aggregates.ScalarMapping.Controls.path false)).bind Solidity.Source.Val.key = some 11 ∧ Solidity.Source.Halt.revert [] ≠ Solidity.Source.Halt.timeout ∧ Solidity.Source.Halt.revert [] ≠ Solidity.Source.Halt.stuck "storage cell type" := by
  simp only [Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.view,Prod.mk.injEq]
  decide +kernel

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.cells' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms cells

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms certificate

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.state_cells' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms state_cells

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.rollback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms rollback

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.complete_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_frame

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.wrong_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_phase

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.static_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms static_control

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls.negative_controls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms negative_controls
end Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.Controls
