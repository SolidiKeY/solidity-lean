import Solidity.Backend.MemoryOps.PhysicalArrayReframe

/-! Unproved target statements: these are TYPE-CHECKED PROPOSITION DEFINITIONS, not
proved facts, axioms, evaluator assumptions or completed compiler interfaces.
No downstream theorem may assume these goals. Proofs belong in separately checked
proofs using actual producer results and the cell-agreement law. -/
namespace Solidity.Backend.MemoryOps.Physical

/-- Observer glue target: retain the initial independent Source and
byte observations, replacing only the word machine by a derived representation
of the SAME reached object. Whole machine equality is intentionally absent. -/
def UintArrayReframeGoal {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (address : Nat) (hp : Heap H)
    (r : HRef H (.array (.prim .uint))) (base : Fin Evm.W)
    (left right : Evm.Machine) (bytes : Environment.Memory) : Prop :=
  UintArrayAt y address hp r base left bytes →
  Evm.Memory.ArrayRepr hp r base right →
  UintArrayAt y address hp r base right bytes

/-- Assembly target, using only INITIAL local alignment, whole
published word-state/MemOK premises, and physical input representation. The
actual complete word delete program and reached byte relation are conclusions;
no successful output, target-machine equality or final agreement is assumed. -/
def ResolvedDeletePhysicalGoal {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (y : Source.EMState E Γ) (address : Nat) (G : Source.Glob E) (Fsrc : Source.Fr)
    (fuel nps : Nat) (σ : State C Δ) (r : HRef σ.H (.array (.prim .uint)))
    (sroot : Source.Idx Γ (.array .memory (.int .u256) none))
    (sindex : Source.Idx Γ (.int .u256))
    (troot : Idx Δ (.mem (.array (.prim .uint)))) (tindex : Idx Δ (.val .uint))
    (i : Fin Evm.W) (L b frame : Nat) (F : Evm.Frag Δ)
    (base : Nat → Fin Evm.W) (m : Evm.Machine) (bytes : Environment.Memory)
    (SH : Source.HeapTy) : Prop :=
  UintArrayAt y address σ.heap r (base r.id) m bytes →
  y.1.get sroot=.memRef rfl address →
  y.1.get sindex=sourceUint (Evm.Memory.indexValue i) →
  TEnv.get troot σ.env=some r →
  TEnv.get tindex σ.env=Evm.Memory.indexValue i →
  i.val<σ.heap.len r .dyn →
  Evm.Memory.StateRepr L b frame F σ base m →
  Source.MemOK E SH y →
  let byteNext := Environment.writeBytes bytes (32*((base r.id).val+1+i.val))
    (List.replicate 32 (0 : UInt8))
  ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine),
    (Source.evalE G Fsrc (fuel+3) (sourceUintIndexedDelete sroot sindex)).run y=
      (.ok Source.RVal.unit,z) ∧
    (Source.execS G Fsrc (fuel+4) nps none
      (.expr (sourceUintIndexedDelete sroot sindex) : Source.RStmt E [] false .body Γ Γ) y.1).run
        (.nil,y.2)=(.ok (.normal y.1),(.nil,z.2)) ∧
    Stmt.run σ (.deleteMem (.loc (.index .dyn (.var troot rfl) (.simple (.local tindex)))) rfl)=
      .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
    Evm.run (Evm.Memory.deleteLocalCode b troot
      (Evm.compileVal b (.simple (.local tindex) : Val C Δ .uint))) m=.ok target 0 ∧
    UintArrayAt z address out r (base r.id) target byteNext ∧
    Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧
    Source.MemOK E SH z ∧ z.1=y.1 ∧ z.2={y.2 with heap:=z.2.heap} ∧
    target.stack=m.stack ∧
    Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target

end Solidity.Backend.MemoryOps.Physical
