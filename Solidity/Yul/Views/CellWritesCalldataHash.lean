import Solidity.Yul.Views.FiniteCellWrites
import Solidity.Yul.Views.CalldataHashBinding

/-! One actual Source computation performs finite typed cell writes and then
hashes a calldata local. Successful hashing allocates once and preserves both
reached storage banks. Physical hashing binds the clipped payload only; it is
not allocator header/FMP realization or general source/Yul correspondence. -/
namespace Solidity.Yul.Views.CellWritesCalldataHash

def afterWrites {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (requests : List (FiniteCellWrites.Request E F.this)) := ((FiniteCellWrites.program F requests).run s).2

def program {E Γ} (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (index : Source.Idx Γ (.bytes .calldata)) (requests : List (FiniteCellWrites.Request E F.this)) :
    Source.EM E Γ (Source.RVal E.layout Source.STy.bytes32) := do
  FiniteCellWrites.program F requests
  Source.evalE G F horizon (sourceCalldataHashExpr index)

theorem locals {E Γ} (F : Source.Fr) (s : Source.EMState E Γ)
    (requests : List (FiniteCellWrites.Request E F.this)) (allowed : F.static=false) :
    (afterWrites F s requests).1=s.1 := by
  rw [afterWrites,FiniteCellWrites.run F s requests allowed]

theorem run {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ)
    (index : Source.Idx Γ (.bytes .calldata)) (off len : Nat)
    (requests : List (FiniteCellWrites.Request E F.this)) (allowed : F.static=false)
    (localValue : s.1.get index=Source.Val.cdRef rfl off len) :
    let bs := (F.cd.drop off).take len
    (program G F (n+4) index requests).run s=
      (.ok (.val (Source.mkBytes (D:=E.layout) (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash bs)))),
        objectAllocatedState (afterWrites F s requests) (Source.Data.bytes (l:=.memory) bs)) := by
  first | (simp only;done) | skip
  have first : (FiniteCellWrites.program F requests).run s=(.ok (),afterWrites F s requests) := by
    rw [afterWrites,FiniteCellWrites.run F s requests allowed]
  unfold program
  rw [Source.Hoare.run_bind,first]
  dsimp only
  apply sourceCalldataHash_run
  rw [locals F s requests allowed]
  exact localValue

theorem reencode {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ)
    (index : Source.Idx Γ (.bytes .calldata)) (off len : Nat)
    (requests : List (FiniteCellWrites.Request E F.this))
    (ps ts : List (ScalarPath E.layout (E.lay F.this))) (psep : finiteSeparated ps) (tsep : finiteSeparated ts)
    (registered : ∀ request ∈ requests, FiniteCellWrites.Registered ps ts request)
    (maps : SlotView × SlotView) (before : FiniteCellWrites.Views F ps ts s maps)
    (allowed : F.static=false) (localValue : s.1.get index=Source.Val.cdRef rfl off len) :
    let reached := (program G F (n+4) index requests).run s
    finiteEncode ps (reached.2.2.ex.world.accounts F.this).storage (packedMask ps maps.1)=some (FiniteCellWrites.raw requests maps).1 ∧
    finiteEncode ts (reached.2.2.ex.transient.cells F.this) (packedMask ts maps.2)=some (FiniteCellWrites.raw requests maps).2 := by
  dsimp only
  rw [run G F n s index off len requests allowed localValue]
  exact FiniteCellWrites.reencode F s ps ts psep tsep requests registered maps before allowed

theorem physical_hash {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ)
    (index : Source.Idx Γ (.bytes .calldata)) (off len : Nat)
    (requests : List (FiniteCellWrites.Request E F.this)) (allowed : F.static=false)
    (localValue : s.1.get index=Source.Val.cdRef rfl off len) (dst : Nat) (memory : ByteView) :
    let bs := (F.cd.drop off).take len
    let value := Source.mkBytes (D:=E.layout) (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash bs))
    value.word=some (keccak256 G.fixed.evm (calldatacopy memory F.cd dst off bs.length) dst bs.length) := by
  have retained : (afterWrites F s requests).1.get index=Source.Val.cdRef rfl off len := by
    rw [locals F s requests allowed]
    exact localValue
  exact (sourceCalldataHash_physical G F n (afterWrites F s requests) index off len dst memory retained).2.1

theorem MemOK {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ)
    (index : Source.Idx Γ (.bytes .calldata)) (off len : Nat)
    (requests : List (FiniteCellWrites.Request E F.this)) (allowed : F.static=false)
    (localValue : s.1.get index=Source.Val.cdRef rfl off len) (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H ((program G F (n+4) index requests).run s).2 := by
  rw [run G F n s index off len requests allowed localValue]
  have safe := FiniteCellWrites.MemOK F s requests H ok
  exact (objectAllocRef_MemOK H (afterWrites F s requests) (Source.Data.bytes (l:=.memory) ((F.cd.drop off).take len))
    rfl trivial trivial (.bytes _) safe).1

theorem low_horizon {E Γ} (G : Source.Glob E) (F : Source.Fr) (horizon : Nat) (s : Source.EMState E Γ)
    (index : Source.Idx Γ (.bytes .calldata)) (requests : List (FiniteCellWrites.Request E F.this))
    (allowed : F.static=false) (low : horizon<4) :
    (program G F horizon index requests).run s=(.error .timeout,afterWrites F s requests) := by
  have first : (FiniteCellWrites.program F requests).run s=(.ok (),afterWrites F s requests) := by
    rw [afterWrites,FiniteCellWrites.run F s requests allowed]
  unfold program
  rw [Source.Hoare.run_bind,first]
  dsimp only
  have casesN : horizon=0 ∨ horizon=1 ∨ horizon=2 ∨ horizon=3 := by omega
  rcases casesN with rfl | rfl | rfl | rfl <;> rfl
theorem low_reencode {E Γ} (G : Source.Glob E) (F : Source.Fr) (horizon : Nat) (s : Source.EMState E Γ)
    (index : Source.Idx Γ (.bytes .calldata)) (requests : List (FiniteCellWrites.Request E F.this))
    (ps ts : List (ScalarPath E.layout (E.lay F.this))) (psep : finiteSeparated ps) (tsep : finiteSeparated ts)
    (registered : ∀ request ∈ requests, FiniteCellWrites.Registered ps ts request)
    (maps : SlotView × SlotView) (before : FiniteCellWrites.Views F ps ts s maps)
    (allowed : F.static=false) (low : horizon<4) :
    let reached := (program G F horizon index requests).run s
    finiteEncode ps (reached.2.2.ex.world.accounts F.this).storage (packedMask ps maps.1)=some (FiniteCellWrites.raw requests maps).1 ∧
    finiteEncode ts (reached.2.2.ex.transient.cells F.this) (packedMask ts maps.2)=some (FiniteCellWrites.raw requests maps).2 := by
  dsimp only
  rw [low_horizon G F horizon s index requests allowed low]
  exact FiniteCellWrites.reencode F s ps ts psep tsep requests registered maps before allowed

theorem static {E Γ} (G : Source.Glob E) (F : Source.Fr) (horizon : Nat) (s : Source.EMState E Γ)
    (index : Source.Idx Γ (.bytes .calldata)) (request : FiniteCellWrites.Request E F.this)
    (rest : List (FiniteCellWrites.Request E F.this)) (blocked : F.static=true) :
    (program G F horizon index (request::rest)).run s=(.error (.revert []),s) := by
  unfold program
  rw [Source.Hoare.run_bind,FiniteCellWrites.static F s request rest blocked]
/-- Observe the actual program result through the owner's getV conversion. -/
theorem observed {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ)
    (index : Source.Idx Γ (.bytes .calldata)) (off len : Nat)
    (requests : List (FiniteCellWrites.Request E F.this)) (allowed : F.static=false)
    (localValue : s.1.get index=Source.Val.cdRef rfl off len) (dst : Nat) (memory : ByteView) :
    let bs := (F.cd.drop off).take len
    (((program G F (n+4) index requests >>= Source.getV).run s).1.map Source.Val.word)=
      .ok (some (keccak256 G.fixed.evm (calldatacopy memory F.cd dst off bs.length) dst bs.length)) := by
  rw [Source.Hoare.run_bind,run G F n s index off len requests allowed localValue]
  dsimp only
  exact congrArg Except.ok (physical_hash G F n s index off len requests allowed localValue dst memory)
end Solidity.Yul.Views.CellWritesCalldataHash
