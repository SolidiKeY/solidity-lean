import Solidity.Lowering.V08.LiteralFailureChoiceDecode

/-! Existing local-assignment effects composed with actual conditional ABI
decoding. No state rollback or new evaluator is assumed. -/
namespace Solidity.Lowering.V08.LiteralFailureEffectDecode
open Solidity Source

theorem assign_run {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 (index : Source.Idx Γ .bool) (bit : Bool) (locals : Locals E.layout Γ) (state : St E) :
 (evalE G F (n+3) (.assign (.local index) (.bool bit))).run (locals,state) =
 (.ok (.val (.bool bit)),(locals.set index (.bool bit),state)) := by
 rfl

theorem assign_ok {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 {H : HeapTy} (index : Source.Idx Γ .bool) (bit : Bool) :
 Hoare (MemOK E H) (evalE G F (n+3) (.assign (.local index) (.bool bit)))
  (fun value y => MemOK E H y ∧ RValOK E y.2.heap.ty value)
  (fun e y => MemOK E H y ∧ NotStuck e) := by
 intro initial invariant
 rcases initial with ⟨locals,state⟩
 rw [assign_run]
 exact ⟨⟨⟨invariant.1.1,LocalsOK.set locals index invariant.1.2 trivial⟩,invariant.2⟩,trivial⟩

/-- Relative to an actual condition-expression triple; the assignment
corollary below discharges it, including the changed caller locals. -/
theorem choice {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 {H : HeapTy} {τ : STy} (condition : RExpr E Γ .bool) (yes no : Source.Idx Γ τ)
 (condition_ok : Hoare (MemOK E H) (evalE G F (n+1) condition)
  (fun value y => MemOK E H y ∧ RValOK E y.2.heap.ty value)
  (fun e y => MemOK E H y ∧ NotStuck e)) :
 Hoare (MemOK E H) (evalE G F (n+1+1) (.cond condition (.local yes) (.local no)))
  (fun value y => MemOK E H y ∧ RValOK E y.2.heap.ty value)
  (fun e y => MemOK E H y ∧ NotStuck e) := by
 simp only [evalE]
 refine Hoare.bind condition_ok fun value => ?_
 cases value with
 | val value =>
   obtain ⟨bit,rfl⟩ := Val.eq_bool value
   cases bit
   · exact Hoare.conseq (evalE_local_ok G F n no)
      (fun _ h => h.1) (fun _ _ h => h) (fun _ _ h => h)
   · exact Hoare.conseq (evalE_local_ok G F n yes)
      (fun _ h => h.1) (fun _ _ h => h) (fun _ _ h => h)

theorem assigned_choice {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 {H : HeapTy} {τ : STy} (condition : Source.Idx Γ .bool) (bit : Bool)
 (yes no : Source.Idx Γ τ) :
 Hoare (MemOK E H)
  (evalE G F (n+4) (.cond (.assign (.local condition) (.bool bit)) (.local yes) (.local no)))
  (fun value y => MemOK E H y ∧ RValOK E y.2.heap.ty value)
  (fun e y => MemOK E H y ∧ NotStuck e) :=
 choice G F (n+2) _ yes no (assign_ok G F n condition bit)

theorem calldata_ok {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 {H : HeapTy} {types : List STy} (condition : Source.Idx Γ .bool) (bit : Bool)
 (yes no : Source.Idx Γ (.bytes .calldata))
 (admitted : types.all (STy.decodable E) = true) :
 Hoare (MemOK E H)
  (evalE G F (n+5) (.abiDecode
   (.cond (.assign (.local condition) (.bool bit)) (.local yes) (.local no)) rfl admitted))
  (fun value y => MemOK E H y ∧ RValOK E y.2.heap.ty value)
  (fun e y => MemOK E H y ∧ NotStuck e) :=
 LiteralFailureCalldataDecode.arm G F (n+4) _ admitted (assigned_choice G F n condition bit yes no)

theorem memory_ok {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 {H : HeapTy} {types : List STy} (condition : Source.Idx Γ .bool) (bit : Bool)
 (yes no : Source.Idx Γ (.bytes .memory))
 (admitted : types.all (STy.decodable E) = true) :
 Hoare (MemOK E H)
  (evalE G F (n+5) (.abiDecode
   (.cond (.assign (.local condition) (.bool bit)) (.local yes) (.local no)) rfl admitted))
  (fun value y => MemOK E H y ∧ RValOK E y.2.heap.ty value)
  (fun e y => MemOK E H y ∧ NotStuck e) :=
 evalE_abiDecode_ok G F (n+4) _ rfl admitted (assigned_choice G F n condition bit yes no)

theorem storage_ok {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 {H : HeapTy} {types : List STy} (condition : Source.Idx Γ .bool) (bit : Bool)
 (yes no : Source.Idx Γ (.bytes .storage))
 (admitted : types.all (STy.decodable E) = true) :
 Hoare (MemOK E H)
  (evalE G F (n+5) (.abiDecode
   (.cond (.assign (.local condition) (.bool bit)) (.local yes) (.local no)) rfl admitted))
  (fun value y => MemOK E H y ∧ RValOK E y.2.heap.ty value)
  (fun e y => MemOK E H y ∧ NotStuck e) :=
 LiteralFailureStorageDecode.arm G F (n+4) _ admitted (assigned_choice G F n condition bit yes no)

end Solidity.Lowering.V08.LiteralFailureEffectDecode
