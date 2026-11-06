import Solidity.Lowering.V08.LiteralFailureCalldataDecode
import Solidity.Source.ExprProgress

/-! Owned storage-byte decoding consumers of existing Source definitions.
No storage layout, evaluator or decoder is changed. -/
namespace Solidity.Lowering.V08.LiteralFailureStorageDecode
open Solidity Source

theorem read_cell {E : Env} {Γ : RCtx} (F : Fr) (p : SPath)
 (P : EMState E Γ → Prop)
 (default : (Val.default E.layout (E.cellTy p)).isSome = true) :
 Hoare P (readCell F p) (fun _ y => P y) (fun e y => P y ∧ NotStuck e) := by
 unfold readCell
 refine Hoare.bind (Hoare.st' (Q:=fun _ y => P y) (fun _ hy => hy)) fun state => ?_
 have present : (if E.transientRoot p then (state.ex.transient.cells F.this).read p
  else (state.ex.world.accounts F.this).storage.read p).isSome = true := by
   split <;> exact Storage.read_isSome _ p default
 dsimp only
 cases observed : (if E.transientRoot p then (state.ex.transient.cells F.this).read p
  else (state.ex.world.accounts F.this).storage.read p) with
 | some value =>
   simp only [observed]
   exact Hoare.pure' fun _ hy => hy
 | none =>
   rw [observed] at present
   cases present

theorem read_at {E : Env} {Γ : RCtx} (F : Fr) (p : SPath) (τ : STy)
 (P : EMState E Γ → Prop) (correct : E.cellTy p = τ)
 (default : (Val.default E.layout τ).isSome = true) :
 Hoare P (readAt F p τ) (fun _ y => P y) (fun e y => P y ∧ NotStuck e) := by
 unfold readAt
 refine Hoare.bind (read_cell F p P (by rw [correct]; exact default)) fun value => ?_
 rw [dif_pos correct]
 exact Hoare.pure' fun _ hy => hy

theorem bytes_cell {E : Env} (p : SPath)
 (typed : E.pathTy p = some (.bytes .storage)) : E.cellTy p = .int IntTy.u256 := by
 simp only [Env.cellTy, typed, Option.map_some, STy.cell, Option.getD_some]

theorem index_cell {E : Env} (p : SPath) (i : Nat)
 (typed : E.pathTy p = some (.bytes .storage)) :
 E.cellTy (p.go (.index i)) = .fixedBytes 1 (by decide) := by
 simp only [Env.cellTy, Env.pathTy_go, typed, Option.bind_some, Env.stepTy,
  Option.map_some, STy.cell, STy.isValue, Option.getD_some]
 rfl

/-- Actual length read derived from the declared bytes path, for arbitrary
state invariants. This does not assert that the later byte-copy loop finishes. -/
theorem length_read {E : Env} {Γ : RCtx} (F : Fr) (p : SPath)
 (typed : E.pathTy p = some (.bytes .storage)) (P : EMState E Γ → Prop) :
 Hoare P (readLen F p) (fun _ y => P y) (fun e y => P y ∧ NotStuck e) := by
 unfold readLen
 refine Hoare.bind (read_at F p (.int IntTy.u256) P (bytes_cell p typed) rfl) fun value => ?_
 obtain ⟨number,bounded,rfl⟩ := Val.eq_int value
 exact Hoare.pure' fun _ hy => hy

/-- The existing byte-cell read, including its actual default value. No
in-bounds or physical byte-memory claim follows from this layout fact. -/
theorem byte_read {E : Env} {Γ : RCtx} (F : Fr) (p : SPath) (i : Nat)
 (typed : E.pathTy p = some (.bytes .storage)) (P : EMState E Γ → Prop) :
 Hoare P (readAt F (p.go (.index i)) (.fixedBytes 1 (by decide)))
  (fun _ y => P y) (fun e y => P y ∧ NotStuck e) :=
 read_at F (p.go (.index i)) _ P (index_cell p i typed) rfl

/-- Combined preservation/progress for the actual byte-copy recursion. The
explicit bind/match form follows the published loadBytes_keep reduction. -/
theorem load_bytes {E : Env} {Γ : RCtx} (F : Fr) (p : SPath)
 (typed : E.pathTy p = some (.bytes .storage)) (P : EMState E Γ → Prop)
 (fuel i count : Nat) :
 Hoare P (loadBytes F fuel p i count) (fun _ y => P y)
  (fun e y => P y ∧ NotStuck e) := by
 induction fuel generalizing i count with
 | zero => cases count <;> exact Hoare.halt' fun _ hy => ⟨hy,trivial⟩
 | succ fuel ih =>
   cases count with
   | zero => exact Hoare.pure' fun _ hy => hy
   | succ count =>
     show Hoare P (do
      match ← readAt F (p.go (.index i)) (.fixedBytes 1 (by decide)) with
      | .fixedBytes bs _ => pure ((bs.headD 0) :: (← loadBytes F fuel p (i+1) count))) _ _
     exact Hoare.bind (byte_read F p i typed P) fun value => match value with
      | .fixedBytes _ _ => Hoare.bind (ih (i+1) count) fun _ => Hoare.pure' fun _ hy => hy

theorem load_memory {E : Env} {Γ : RCtx} (F : Fr) (fuel : Nat) (p : SPath)
 (typed : E.pathTy p = some (.bytes .storage)) (P : EMState E Γ → Prop) :
 Hoare P (loadMem F fuel (.bytes .memory) p)
  (fun data y => P y ∧ ∃ bytes, data = .bytes bytes)
  (fun e y => P y ∧ NotStuck e) := by
 cases fuel with
 | zero => exact Hoare.halt' fun _ hy => ⟨hy,trivial⟩
 | succ fuel =>
   show Hoare P (do pure (Data.bytes (D:=E.layout) (l:=.memory) (← loadBytes F fuel p 0 (← readLen F p)))) _ _
   refine Hoare.bind (length_read F p typed P) fun count => ?_
   refine Hoare.bind (load_bytes F p typed P fuel 0 count) fun bytes => ?_
   exact Hoare.pure' fun _ hy => ⟨hy,bytes,rfl⟩

theorem stored_bytes {E : Env} {Γ : RCtx} (F : Fr) (fuel : Nat) (p : SPath)
 (typed : E.pathTy p = some (.bytes .storage)) (P : EMState E Γ → Prop) :
 Hoare P (bytesOfRV F fuel (.val (.storRef rfl p) : RVal E.layout (.bytes .storage)))
  (fun _ y => P y) (fun e y => P y ∧ NotStuck e) := by
 unfold bytesOfRV
 refine Hoare.bind (load_memory F fuel p typed P) fun data => ?_
 intro y hy
 obtain ⟨hy,bytes,rfl⟩ := hy
 exact hy

theorem bytes_ok {E : Env} {Γ : RCtx} (F : Fr) (fuel : Nat) {H : HeapTy}
 (value : RVal E.layout (.bytes .storage)) :
 Hoare (fun y => MemOK E H y ∧ RValOK E y.2.heap.ty value)
  (bytesOfRV F fuel value : EM E Γ Roadmap.Bytes)
  (fun _ y => MemOK E H y) (fun e y => MemOK E H y ∧ NotStuck e) := by
 cases value with
 | val value =>
   cases value with
   | memRef h _ => cases h
   | cdRef h _ _ => cases h
   | storRef h p =>
     intro y hy
     exact stored_bytes F fuel p hy.2 (fun y => MemOK E H y) y hy.1

theorem arm {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (fuel : Nat)
 {H : HeapTy} {types : List STy} (data : RExpr E Γ (.bytes .storage))
 (admitted : types.all (STy.decodable E) = true)
 (hdata : Hoare (MemOK E H) (evalE G F fuel data)
  (fun value y => MemOK E H y ∧ RValOK E y.2.heap.ty value)
  (fun e y => MemOK E H y ∧ NotStuck e)) :
 Hoare (MemOK E H) (evalE G F (fuel+1) (.abiDecode data rfl admitted))
  (fun value y => MemOK E H y ∧ RValOK E y.2.heap.ty value)
  (fun e y => MemOK E H y ∧ NotStuck e) := by
 simp only [evalE]
 exact Hoare.bind hdata fun value => Hoare.bind (bytes_ok F fuel value) fun bytes => abiDecodeData_ok bytes admitted

theorem local_ok {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (fuel : Nat)
 {H : HeapTy} {types : List STy} (index : Source.Idx Γ (.bytes .storage))
 (admitted : types.all (STy.decodable E) = true) :
 Hoare (MemOK E H) (evalE G F (fuel+1+1) (.abiDecode (.local index) rfl admitted))
  (fun value y => MemOK E H y ∧ RValOK E y.2.heap.ty value)
  (fun e y => MemOK E H y ∧ NotStuck e) :=
 arm G F (fuel+1) (.local index) admitted (evalE_local_ok G F fuel index)

end Solidity.Lowering.V08.LiteralFailureStorageDecode
