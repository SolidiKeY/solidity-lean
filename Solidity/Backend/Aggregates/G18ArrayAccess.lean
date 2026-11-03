import Solidity.Backend.Aggregates.G18Storage
import Solidity.Backend.Aggregates.G18SourceMapping
import Solidity.Source.Eval

/-! Dynamic storage array access consumes actual declared path types and
actual Source length cells. Element typing alone does not establish bounds. -/
namespace Solidity.Backend.Aggregates.SourceArray

theorem read_typed : ∀ (E : Solidity.Source.Env) (Γ : Solidity.Source.RCtx) (F : Solidity.Source.Fr) (s : Solidity.Source.St E) (l : Solidity.Source.Locals E.layout Γ) (p : Solidity.Source.SPath) (τ : Solidity.Source.STy) (typed : E.cellTy p = τ) (v : Solidity.Source.Val E.layout τ), E.transientRoot p = false → (s.ex.world.accounts F.this).storage.read p = some (cast (congrArg (Solidity.Source.Val E.layout) typed.symm) v) → (Solidity.Source.readAt (E := E) (Γ := Γ) F p τ).run (l,s) = (.ok v,(l,s)) := by
  intro E Γ F s l p τ typed v persistent initial
  subst τ
  exact Solidity.Backend.Aggregates.ScalarMapping.SourceMachine.read E Γ F s l p v persistent initial

theorem length_type : ∀ (E : Solidity.Source.Env) (p : Solidity.Source.SPath) (t : Solidity.Source.IntTy), E.pathTy p = some (.array .storage (.int t) none) → E.cellTy p = .int .u256 := by
  intro E p t array
  simp only [Solidity.Source.Env.cellTy,array,Option.map_some,Option.getD_some,Solidity.Source.STy.cell]

theorem element_type : ∀ (E : Solidity.Source.Env) (p : Solidity.Source.SPath) (t : Solidity.Source.IntTy), E.pathTy p = some (.array .storage (.int t) none) → ∀ i : Nat, E.cellTy (p.go (.index i)) = .int t := by
  intro E p t array i
  have path := Solidity.Backend.Aggregates.array_path E p .storage (.int t) none array i
  unfold Solidity.Source.Env.cellTy Solidity.Source.SPath.go
  rw [path]
  rfl

theorem length_run : ∀ (E : Solidity.Source.Env) (Γ : Solidity.Source.RCtx) (F : Solidity.Source.Fr) (s : Solidity.Source.St E) (l : Solidity.Source.Locals E.layout Γ) (p : Solidity.Source.SPath) (t : Solidity.Source.IntTy) (array : E.pathTy p = some (.array .storage (.int t) none)) (len : Nat) (range : Solidity.Source.IntTy.u256.lo ≤ (len : Int) ∧ (len : Int) ≤ Solidity.Source.IntTy.u256.hi), E.transientRoot p = false → (s.ex.world.accounts F.this).storage.read p = some (cast (congrArg (Solidity.Source.Val E.layout) (Solidity.Backend.Aggregates.SourceArray.length_type E p t array).symm) (Solidity.Source.Val.int (len : Int) range)) → (Solidity.Source.readLen (E := E) (Γ := Γ) F p).run (l,s) = (.ok len,(l,s)) := by
  intro E Γ F s l p t array len range persistent initial
  have read := Solidity.Backend.Aggregates.SourceArray.read_typed E Γ F s l p (.int .u256) (Solidity.Backend.Aggregates.SourceArray.length_type E p t array) (.int (len : Int) range) persistent initial
  rw [Solidity.Source.readLen,Solidity.Source.Hoare.run_bind,read]
  rfl

theorem index_success : ∀ (E : Solidity.Source.Env) (Γ : Solidity.Source.RCtx) (F : Solidity.Source.Fr) (s : Solidity.Source.St E) (l : Solidity.Source.Locals E.layout Γ) (p : Solidity.Source.SPath) (t : Solidity.Source.IntTy) (array : E.pathTy p = some (.array .storage (.int t) none)) (len : Nat) (range : Solidity.Source.IntTy.u256.lo ≤ (len : Int) ∧ (len : Int) ≤ Solidity.Source.IntTy.u256.hi), E.transientRoot p = false → (s.ex.world.accounts F.this).storage.read p = some (cast (congrArg (Solidity.Source.Val E.layout) (Solidity.Backend.Aggregates.SourceArray.length_type E p t array).symm) (Solidity.Source.Val.int (len : Int) range)) → ∀ (i : Nat), i < len → (Solidity.Source.indexLoc (E := E) (Γ := Γ) (l := .storage) (σ := .int t) (k := none) F (.storRef rfl p) i).run (l,s) = (.ok (.stor (p.go (.index i))),(l,s)) := by
  intro E Γ F s l p t array len range persistent initial i bound
  have actual := Solidity.Backend.Aggregates.SourceArray.length_run E Γ F s l p t array len range persistent initial
  unfold Solidity.Source.indexLoc Solidity.Source.lengthOf
  rw [Solidity.Source.Hoare.run_bind,actual]
  simp only [bound,ite_true]
  rfl

theorem index_failure : ∀ (E : Solidity.Source.Env) (Γ : Solidity.Source.RCtx) (F : Solidity.Source.Fr) (s : Solidity.Source.St E) (l : Solidity.Source.Locals E.layout Γ) (p : Solidity.Source.SPath) (t : Solidity.Source.IntTy) (array : E.pathTy p = some (.array .storage (.int t) none)) (len : Nat) (range : Solidity.Source.IntTy.u256.lo ≤ (len : Int) ∧ (len : Int) ≤ Solidity.Source.IntTy.u256.hi), E.transientRoot p = false → (s.ex.world.accounts F.this).storage.read p = some (cast (congrArg (Solidity.Source.Val E.layout) (Solidity.Backend.Aggregates.SourceArray.length_type E p t array).symm) (Solidity.Source.Val.int (len : Int) range)) → ∀ (i : Nat), ¬ i < len → (Solidity.Source.indexLoc (E := E) (Γ := Γ) (l := .storage) (σ := .int t) (k := none) F (.storRef rfl p) i).run (l,s) = (.error (.revert (Solidity.Source.panicData .index)),(l,s)) := by
  intro E Γ F s l p t array len range persistent initial i bound
  have actual := Solidity.Backend.Aggregates.SourceArray.length_run E Γ F s l p t array len range persistent initial
  unfold Solidity.Source.indexLoc Solidity.Source.lengthOf
  rw [Solidity.Source.Hoare.run_bind,actual]
  simp only [bound,ite_false]
  rfl

theorem read_element : ∀ (E : Solidity.Source.Env) (Γ : Solidity.Source.RCtx) (F : Solidity.Source.Fr) (s : Solidity.Source.St E) (l : Solidity.Source.Locals E.layout Γ) (p : Solidity.Source.SPath) (t : Solidity.Source.IntTy) (array : E.pathTy p = some (.array .storage (.int t) none)) (len : Nat) (range : Solidity.Source.IntTy.u256.lo ≤ (len : Int) ∧ (len : Int) ≤ Solidity.Source.IntTy.u256.hi), E.transientRoot p = false → (s.ex.world.accounts F.this).storage.read p = some (cast (congrArg (Solidity.Source.Val E.layout) (Solidity.Backend.Aggregates.SourceArray.length_type E p t array).symm) (Solidity.Source.Val.int (len : Int) range)) → ∀ (i : Nat), i < len → ∀ (T : Solidity.Ty) (target : Solidity.SVal T) (pt : Solidity.Path T (.prim (Solidity.Lowering.V07.integerPrim t))), Solidity.Backend.Aggregates.IntCellAt t (s.ex.world.accounts F.this).storage target (p.go (.index i)) (Solidity.Backend.Aggregates.SourceArray.element_type E p t array i) pt → ∃ (n : Int) (range : t.lo ≤ n ∧ n ≤ t.hi), ((Solidity.Source.indexLoc (E := E) (Γ := Γ) (l := .storage) (σ := .int t) (k := none) F (.storRef rfl p) i) >>= fun (loc : Solidity.Source.Loc E.layout Γ (.int t)) => Solidity.Source.readLoc (E := E) (Γ := Γ) (τ := .int t) F loc).run (l,s) = (.ok (.int n range),(l,s)) ∧ target.find pt = some (.prim (Solidity.Lowering.V07.integerValue t n range)) := by
  intro E Γ F s l p t array len range persistent initial i bound T target pt related
  obtain ⟨n,nrange,sourceRead,targetRead⟩ := related
  have here := Solidity.Backend.Aggregates.SourceArray.index_success E Γ F s l p t array len range persistent initial i bound
  have transport : ∀ (A B : Solidity.Source.STy) (h : A = B) (v : Solidity.Source.Val E.layout A), h ▸ v = cast (congrArg (Solidity.Source.Val E.layout) h) v := by
    intro A B h v
    cases h
    rfl
  have adjusted := sourceRead.trans (congrArg some (transport _ _ (Solidity.Backend.Aggregates.SourceArray.element_type E p t array i).symm (.int n nrange)))
  have cell := Solidity.Backend.Aggregates.SourceArray.read_typed E Γ F s l (p.go (.index i)) (.int t) (Solidity.Backend.Aggregates.SourceArray.element_type E p t array i) (.int n nrange) persistent adjusted
  refine ⟨n,nrange,?_,targetRead⟩
  rw [Solidity.Source.Hoare.run_bind,here]
  simpa only [Solidity.Source.readLoc,Solidity.Source.STy.byRef,Solidity.Source.STy.loc?,Option.isSome_none,Bool.false_eq_true,ite_false] using cell

/-- info: 'Solidity.Backend.Aggregates.SourceArray.read_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms read_typed

/-- info: 'Solidity.Backend.Aggregates.SourceArray.length_type' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms length_type

/-- info: 'Solidity.Backend.Aggregates.SourceArray.element_type' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms element_type

/-- info: 'Solidity.Backend.Aggregates.SourceArray.length_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms length_run

/-- info: 'Solidity.Backend.Aggregates.SourceArray.index_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms index_success

/-- info: 'Solidity.Backend.Aggregates.SourceArray.index_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms index_failure

/-- info: 'Solidity.Backend.Aggregates.SourceArray.read_element' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms read_element
end Solidity.Backend.Aggregates.SourceArray
