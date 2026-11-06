import Solidity.Lowering.StorageOps.SourceArrayWrite
/-! Bounds precede actual Source writeLoc and guarded target payload use.
No child presence/type, writable mode, aggregate fuel or encoding premise is
needed for this failure branch. Source panic and target revert are distinct;
this establishes no world rollback or address compiler. -/
namespace Solidity.Lowering.StorageOps.SourceArrayWriteFailure
theorem source_outside : ∀ (E : Solidity.Source.Env) (Γ : Solidity.Source.RCtx)
 (frame : Solidity.Source.Fr) (path : Solidity.Source.SPath) (σ : Solidity.Source.STy) (i : Nat)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_ordinary : E.transientRoot path=false)
 (typed : E.cellTy path = .int Solidity.Source.IntTy.u256)
 (header : Solidity.Source.Val E.layout (E.cellTy path)) (n : Int)
 (bound : Solidity.Source.IntTy.u256.lo ≤ n ∧ n ≤ Solidity.Source.IntTy.u256.hi)
 (_present : (state.ex.world.accounts frame.this).storage.read path=some header)
 (_cast : typed ▸ header = (.int n bound : Solidity.Source.Val E.layout (.int Solidity.Source.IntTy.u256)))
 (value : Solidity.Source.Val E.layout σ) (budget : Nat) (_outside : n.toNat≤i),
 (Solidity.Lowering.StorageOps.SourceArrayWrite.write (E:=E) (Γ:=Γ) frame budget path σ i value).run (locals,state)=
 (.error (.revert (Solidity.Source.panicData .index)),(locals,state)) := by
  intro E Γ frame path σ i locals state ordinary typed header n bound present cast value budget outside
  unfold Solidity.Lowering.StorageOps.SourceArrayWrite.write
  rw [Solidity.Source.Hoare.run_bind,
    Solidity.Lowering.StorageOps.SourceArrayIndex.locate E Γ frame path σ i locals state ordinary typed header n bound present cast,
    if_neg (Nat.not_lt_of_ge outside)]


theorem bounds_failure : ∀ (E : Solidity.Source.Env) (Γ : Solidity.Source.RCtx)
 (frame : Solidity.Source.Fr) (path : Solidity.Source.SPath) (σ : Solidity.Source.STy) (i : Nat)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_ordinary : E.transientRoot path=false)
 (typed : E.cellTy path = .int Solidity.Source.IntTy.u256)
 (header : Solidity.Source.Val E.layout (E.cellTy path)) (n : Int)
 (bound : Solidity.Source.IntTy.u256.lo ≤ n ∧ n ≤ Solidity.Source.IntTy.u256.hi)
 (_present : (state.ex.world.accounts frame.this).storage.read path=some header)
 (_cast : typed ▸ header = (.int n bound : Solidity.Source.Val E.layout (.int Solidity.Source.IntTy.u256)))
 (value : Solidity.Source.Val E.layout σ) (budget : Nat) (_outside : n.toNat≤i)
 (machine : Solidity.Evm.Machine) (tail : List Solidity.Evm.Word) (slot : Solidity.Evm.Slot)
 (fits : i<Solidity.Evm.W) (targetValue : Fin Solidity.Evm.W)
 (_targetHeader : machine.store slot=n.toNat),
 (Solidity.Lowering.StorageOps.SourceArrayWrite.write (E:=E) (Γ:=Γ) frame budget path σ i value).run (locals,state)=
 (.error (.revert (Solidity.Source.panicData .index)),(locals,state)) ∧
 Solidity.Evm.run Solidity.Backend.StorageOps.TargetArrayWrite.code
 {machine with stack:=.val ⟨i,fits⟩ :: .slot slot :: .val targetValue :: tail}=.revert := by
  intro E Γ frame path σ i locals state ordinary typed header n bound present cast value budget outside machine tail slot fits targetValue targetHeader
  refine ⟨source_outside E Γ frame path σ i locals state ordinary typed header n bound present cast value budget outside, ?_⟩
  rw [Solidity.Backend.StorageOps.TargetArrayWrite.run_current,targetHeader,if_neg (Nat.not_lt_of_ge outside)]


/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteFailure.source_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_outside

/-- info: 'Solidity.Lowering.StorageOps.SourceArrayWriteFailure.bounds_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bounds_failure
end Solidity.Lowering.StorageOps.SourceArrayWriteFailure
