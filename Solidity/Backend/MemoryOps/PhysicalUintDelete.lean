import Solidity.Backend.MemoryOps.PhysicalUintWrite
import Solidity.Backend.MemoryOps.SourceUintDelete

/-! G34: a real primitive element deletion, with independently represented
Source/intrinsic/word/physical-byte outputs. Existing constructors and compilers
are reused. Element clear is NOT whole-array replacement or recursive delete.
The byte operation is an explicit scaled MSTORE, not an index/path byte compiler.
Whole local-pointer word deletion still requires its existing StateRepr/MemOK
certificate; it is not inferred from the smaller per-array relation. -/
namespace Solidity.Backend.MemoryOps.Physical

/-- Existing primitive uint default has the exact full-width zero byte image. -/
theorem uint_delete_bytes : Semantics.wordBytes 0=List.replicate 32 (0 : UInt8) := by decide

/-- Actual Source.deleteLoc agrees with the actual default write. The reached
representation and all exterior/neighbor frames are derived from INITIAL input;
no desired delete execution or reached agreement is a premise. -/
theorem UintArrayAt.delete_cell {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H}
    {r : HRef H (.array (.prim .uint))} {base : Fin Evm.W}
    {m : Evm.Machine} {bytes : Environment.Memory}
    (h : UintArrayAt y address hp r base m bytes) (F : Source.Fr) (fuel : Nat)
    (i : Fin Evm.W) (hi : i.val<hp.len r .dyn) :
    let cell := base.val+1+i.val
    let next := Evm.Memory.writeMachine m cell (.val (Evm.wmod 0))
    let byteNext := Environment.writeBytes bytes (32*cell) (List.replicate 32 (0 : UInt8))
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index r .dyn (Evm.Memory.indexValue i)) (PrimTy.dflt .uint)=some out ∧
      (Source.deleteLoc (E := E) (Γ := Γ) F (fuel+1) (τ := .int .u256)
        (.mem address i.val)).run y=(.ok (),z) ∧
      Evm.run (Evm.Memory.writeArrayCode base)
        ((m.push (.val (Evm.wmod 0))).push (.val i))=.ok next 0 ∧
      (∃ offset : Fin Evm.W,offset.val=32*cell ∧ ∀ tail : List Environment.Word,
        Environment.cryptoStep (.op .MSTORE)
          ⟨lenU offset.val offset.isLt::lenU 0 (by decide)::tail,bytes⟩=some ⟨tail,byteNext⟩) ∧
      UintArrayAt z address out r base next byteNext ∧
      z.1=y.1 ∧ z.2={y.2 with heap:=z.2.heap} ∧
      (∀ b,b≠address → z.2.heap.get b=y.2.heap.get b) ∧
      (∀ {Q : RefTy} (q : HRef H Q),r.id≠q.id → out.get q=hp.get q) ∧
      (∀ k,k<32*cell ∨ 32*cell+32≤k → byteNext k=bytes k) := by
  simpa only [uint_delete_bytes] using h.write_cell F (fuel+1) i (Evm.wmod 0) hi

/-- Actual local-root/index syntax reaches the SAME derived delete output.
The returned unit differs from the discarded statement result; original source
parameter count remains explicit. No arbitrary side-effect order is inferred. -/
theorem UintArrayAt.delete_expression {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H}
    {r : HRef H (.array (.prim .uint))} {base : Fin Evm.W}
    {m : Evm.Machine} {bytes : Environment.Memory}
    (h : UintArrayAt y address hp r base m bytes) (G : Source.Glob E)
    (F : Source.Fr) (fuel nps : Nat)
    (root : Source.Idx Γ (.array .memory (.int .u256) none))
    (index : Source.Idx Γ (.int .u256)) (i : Fin Evm.W)
    (hroot : y.1.get root=.memRef rfl address)
    (hindex : y.1.get index=sourceUint (Evm.Memory.indexValue i))
    (hi : i.val<hp.len r .dyn) :
    let next := Evm.Memory.writeMachine m (base.val+1+i.val) (.val (Evm.wmod 0))
    let byteNext := Environment.writeBytes bytes (32*(base.val+1+i.val)) (List.replicate 32 (0 : UInt8))
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index r .dyn (Evm.Memory.indexValue i)) (PrimTy.dflt .uint)=some out ∧
      (Source.deleteLoc (E := E) (Γ := Γ) F (fuel+2) (τ := .int .u256) (.mem address i.val)).run y=(.ok (),z) ∧
      (Source.evalE G F (fuel+3) (sourceUintIndexedDelete root index)).run y=(.ok Source.RVal.unit,z) ∧
      (Source.execS G F (fuel+4) nps none
        (.expr (sourceUintIndexedDelete root index) : Source.RStmt E [] false .body Γ Γ) y.1).run
          (.nil,y.2)=(.ok (.normal y.1),(.nil,z.2)) ∧
      Evm.run (Evm.Memory.writeArrayCode base)
        ((m.push (.val (Evm.wmod 0))).push (.val i))=.ok next 0 ∧
      (∃ offset : Fin Evm.W,offset.val=32*(base.val+1+i.val) ∧ ∀ tail : List Environment.Word,
        Environment.cryptoStep (.op .MSTORE)
          ⟨lenU offset.val offset.isLt::lenU 0 (by decide)::tail,bytes⟩=some ⟨tail,byteNext⟩) ∧
      UintArrayAt z address out r base next byteNext ∧ z.1=y.1 ∧
      z.2={y.2 with heap:=z.2.heap} ∧
      (∀ b,b≠address → z.2.heap.get b=y.2.heap.get b) ∧
      (∀ {Q : RefTy} (q : HRef H Q),r.id≠q.id → out.get q=hp.get q) := by
  dsimp only
  obtain ⟨out,z,ht,hd,hw,hbyte,hr,hl,hs,hother,htyped,_⟩ := h.delete_cell F (fuel+1) i hi
  have he : (Source.evalE G F (fuel+3) (sourceUintIndexedDelete root index)).run y=
      (.ok Source.RVal.unit,z) :=
    h.source.eval_delete_of_run G F fuel root index (Evm.Memory.indexValue i) hroot hindex hi hd
  have hstmt := source_expr_statement_run G F (fuel+3) nps _ y z Source.RVal.unit he
  refine ⟨out,z,ht,hd,he,?_,hw,hbyte,hr,hl,hs,hother,htyped⟩
  simpa only [hl] using hstmt

/-- Out-of-bounds deletion exposes Source's exact index panic and intrinsic
None. This small relation does not fabricate a byte-revert state or payload. -/
theorem UintArrayAt.delete_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H}
    {r : HRef H (.array (.prim .uint))} {base : Fin Evm.W}
    {m : Evm.Machine} {bytes : Environment.Memory}
    (h : UintArrayAt y address hp r base m bytes) (F : Source.Fr) (fuel : Nat)
    (i : Fin Evm.W) (hi : hp.len r .dyn≤i.val) :
    (Source.deleteLoc (E := E) (Γ := Γ) F (fuel+1) (τ := .int .u256)
      (.mem address i.val)).run y=(.error (.revert (Source.panicData .index)),y) ∧
    hp.writeAddr (.index r .dyn (Evm.Memory.indexValue i)) (PrimTy.dflt .uint)=none ∧
    Evm.run (Evm.Memory.writeArrayCode base)
      ((m.push (.val (Evm.wmod 0))).push (.val i))=.revert := by
  obtain ⟨hs,ht⟩ := h.source.delete_bounds F fuel (Evm.Memory.indexValue i) hi
  refine ⟨hs,ht,?_⟩
  rcases Evm.Memory.writeArray_correct h.words i (PrimTy.dflt .uint)
      (.val (Evm.wmod 0)) (Evm.ReprV.uint_of rfl) with ⟨out,ht',_,_⟩ | ⟨_,hr⟩
  · rw [ht] at ht'
    cases ht'
  · exact hr

/-- The corresponding intrinsic delete statement uses the SAME derived heap.
Only actual initial typed root/index alignment is required; no whole word-state
certificate is manufactured from a per-array representation. The word side
runs `writeArrayCode`, not the compiled `deleteLocalCode` (that correspondence
is proved separately by `resolved_delete_physical` in PhysicalLocalDeleteGoal). -/
theorem UintArrayAt.delete_typed {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (σ : State C Δ)
    (r : HRef σ.H (.array (.prim .uint))) {base : Fin Evm.W}
    {m : Evm.Machine} {bytes : Environment.Memory}
    (h : UintArrayAt y address σ.heap r base m bytes) (G : Source.Glob E)
    (F : Source.Fr) (fuel nps : Nat)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) none))
    (sindex : Source.Idx Γ (.int .u256))
    (troot : Idx Δ (.mem (.array (.prim .uint)))) (tindex : Idx Δ (.val .uint))
    (i : Fin Evm.W) (hsroot : y.1.get sroot=.memRef rfl address)
    (hsindex : y.1.get sindex=sourceUint (Evm.Memory.indexValue i))
    (htroot : TEnv.get troot σ.env=some r) (htindex : TEnv.get tindex σ.env=Evm.Memory.indexValue i)
    (hi : i.val<σ.heap.len r .dyn) :
    let next := Evm.Memory.writeMachine m (base.val+1+i.val) (.val (Evm.wmod 0))
    let byteNext := Environment.writeBytes bytes (32*(base.val+1+i.val)) (List.replicate 32 (0 : UInt8))
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ),
      (Source.evalE G F (fuel+3) (sourceUintIndexedDelete sroot sindex)).run y=(.ok Source.RVal.unit,z) ∧
      Stmt.run σ (.deleteMem (.loc (.index .dyn (.var troot rfl) (.simple (.local tindex)))) rfl)=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (Evm.Memory.writeArrayCode base)
        ((m.push (.val (Evm.wmod 0))).push (.val i))=.ok next 0 ∧
      UintArrayAt z address out r base next byteNext ∧
      z.1=y.1 ∧ z.2={y.2 with heap:=z.2.heap} := by
  dsimp only
  obtain ⟨out,z,ht,_,he,_,hw,_,hr,hl,hs,_,_⟩ :=
    h.delete_expression G F fuel nps sroot sindex i hsroot hsindex hi
  have htyped : TRun.deleteMem (.loc (.index .dyn (.var troot rfl) (.simple (.local tindex)))) σ=
      .ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
    simp only [TRun.deleteMem,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,htroot,htindex,
      bind,Except.bind,pure,Except.pure,TRun.clearT,ht,TRes.ofOpt]
  exact ⟨out,z,he,htyped,hw,hr,hl,hs⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.UintArrayAt.delete_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UintArrayAt.delete_typed
/-- info: 'Solidity.Backend.MemoryOps.Physical.uint_delete_bytes' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms uint_delete_bytes
/-- info: 'Solidity.Backend.MemoryOps.Physical.UintArrayAt.delete_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UintArrayAt.delete_cell
/-- info: 'Solidity.Backend.MemoryOps.Physical.UintArrayAt.delete_expression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UintArrayAt.delete_expression
/-- info: 'Solidity.Backend.MemoryOps.Physical.UintArrayAt.delete_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UintArrayAt.delete_bounds
end Solidity.Backend.MemoryOps.Physical
