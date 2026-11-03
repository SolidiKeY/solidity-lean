import Solidity.Backend.Aggregates.G18ScalarMapping
import Solidity.Source.Hoare

/-! Actual Source-machine storage phases for the captured-key mapping
consumer. The independent structured target remains symbolic. -/
namespace Solidity.Backend.Aggregates.ScalarMapping.SourceMachine
open Lowering.V07

/-- The existing account operation, including its original journal entry.
This is an endpoint description, not another execution relation. -/
def writtenState {E : Source.Env} (s : Source.St E) (F : Source.Fr)
    (p : Source.SPath) (v : Source.Val E.layout (E.cellTy p)) : Source.St E :=
  {s with ex := s.ex.apply (.account F.this fun a =>
    {a with storage := a.storage.write p v})}

theorem read : ∀ (E : Solidity.Source.Env) (Γ : Solidity.Source.RCtx) (F : Solidity.Source.Fr) (s : Solidity.Source.St E) (l : Solidity.Source.Locals E.layout Γ) (p : Solidity.Source.SPath) (v : Solidity.Source.Val E.layout (E.cellTy p)), E.transientRoot p = false → (s.ex.world.accounts F.this).storage.read p = some v → (Solidity.Source.readAt (E := E) (Γ := Γ) F p (E.cellTy p)).run (l,s) = (.ok v,(l,s)) := by
  intro E Γ F s l p v persistent read
  simp only [Solidity.Source.readAt, Solidity.Source.readCell, Solidity.Source.EM.st, bind_pure_comp, persistent, Bool.false_eq_true, ↓reduceIte, bind_map_left, ↓reduceDIte, bind_pure]
  rw [Solidity.Source.Hoare.run_bind]
  change ExceptT.run (match (s.ex.world.accounts F.this).storage.read p with
    | some w => (pure w : Solidity.Source.EM E Γ _)
    | none => Solidity.Source.EM.halt (Solidity.Source.Halt.stuck "storage cell without a value")) (l,s) = _
  rw [read]
  rfl

theorem write : ∀ (E : Solidity.Source.Env) (Γ : Solidity.Source.RCtx) (F : Solidity.Source.Fr) (s : Solidity.Source.St E) (l : Solidity.Source.Locals E.layout Γ) (p : Solidity.Source.SPath) (v : Solidity.Source.Val E.layout (E.cellTy p)), E.transientRoot p = false → F.static = false → (Solidity.Source.writeAt (E := E) (Γ := Γ) F p v).run (l,s) = (.ok (), (l, Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.writtenState s F p v)) := by
  intro E Γ F s l p v persistent mutable
  simp only [Solidity.Source.writeAt, dite_true, Solidity.Source.setCell, persistent, Bool.false_eq_true, ite_false, Solidity.Source.applyOp, mutable]
  rfl

theorem copy_phases : ∀ (E : Solidity.Source.Env) (Γ : Solidity.Source.RCtx) (K : Solidity.PrimTy) (t : Solidity.Source.IntTy) (F : Solidity.Source.Fr) (s : Solidity.Source.St E) (l : Solidity.Source.Locals E.layout Γ) (entries : Solidity.SMap K (.prim (Solidity.Lowering.V07.integerPrim t))) (fallback : Solidity.SVal (.prim (Solidity.Lowering.V07.integerPrim t))) (paths : K.Denote → Solidity.Source.SPath) (typed : ∀ k, E.cellTy (paths k) = .int t), Function.Injective paths → Solidity.Backend.Aggregates.ScalarMapping.Cells t (s.ex.world.accounts F.this).storage (.map entries fallback) paths typed → (∀ k, E.transientRoot (paths k) = false) → F.static = false → ∀ (base : Solidity.Evm.Slot) (store : Solidity.Storage.Representation.Store), Solidity.Storage.Representation.ValueRep (.map entries fallback) (.map .word) (Solidity.Storage.ofSlot base) store → ∀ (target : Solidity.Evm.Machine), (∀ key : K.Denote, target.store.cells (Solidity.Backend.Aggregates.ScalarMapping.slot base key) = Solidity.Backend.StorageOps.TargetOperations.encodeWord (store (Solidity.Backend.Aggregates.ScalarMapping.location (Solidity.Storage.ofSlot base) key))) → ∀ src dst : K.Denote, ∃ (n : Int) (range : t.lo ≤ n ∧ n ≤ t.hi) (after : Solidity.SVal (Solidity.Backend.Aggregates.ScalarMapping.MapTy K t)), (Solidity.Source.readAt (E := E) (Γ := Γ) F (paths src) (E.cellTy (paths src))).run (l,s) = (.ok ((typed src).symm ▸ Solidity.Source.Val.int n range),(l,s)) ∧ (Solidity.Source.writeAt (E := E) (Γ := Γ) F (paths dst) ((typed dst).symm ▸ Solidity.Source.Val.int n range)).run (l,s) = (.ok (), (l,Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.writtenState s F (paths dst) ((typed dst).symm ▸ Solidity.Source.Val.int n range))) ∧ Solidity.Backend.Aggregates.ScalarMapping.CopyPost t (s.ex.world.accounts F.this).storage (.map entries fallback) after paths typed src dst n range base store target := by
  intro E Γ K t F s l entries fallback paths typed injective cells persistent mutable base store represented target initial src dst
  obtain ⟨n,range,after,sourceRead,post⟩ := Solidity.Backend.Aggregates.ScalarMapping.copy t (s.ex.world.accounts F.this).storage entries fallback paths typed injective cells base store represented target initial src dst
  refine ⟨n,range,after,?_,?_,post⟩
  · exact Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.read E Γ F s l (paths src) _ (persistent src) sourceRead
  · exact Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.write E Γ F s l (paths dst) _ (persistent dst) mutable

theorem refused : ∀ (E : Solidity.Source.Env) (Γ : Solidity.Source.RCtx) (F : Solidity.Source.Fr) (s : Solidity.Source.St E) (l : Solidity.Source.Locals E.layout Γ) (p : Solidity.Source.SPath) (v : Solidity.Source.Val E.layout (E.cellTy p)), E.transientRoot p = false → F.static = true → (Solidity.Source.writeAt (E := E) (Γ := Γ) F p v).run (l,s) = (.error (.revert []), (l,s)) := by
  intro E Γ F s l p v persistent static
  simp only [Solidity.Source.writeAt, dite_true, Solidity.Source.setCell, persistent, Bool.false_eq_true, ite_false, Solidity.Source.applyOp, static, ite_true]
  rfl

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms read

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms write

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.copy_phases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copy_phases

/-- info: 'Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms refused
end Solidity.Backend.Aggregates.ScalarMapping.SourceMachine
