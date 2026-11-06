import Solidity.Lowering.V08.LiteralFailureStorageDecode

/-! Actual conditional-local data selection composed with existing ABI decode
arms. No expression evaluator or admission rule is added. -/
namespace Solidity.Lowering.V08.LiteralFailureChoiceDecode
open Solidity Source

theorem choice_ok {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 {H : HeapTy} {τ : STy} (condition : Source.Idx Γ .bool)
 (yes no : Source.Idx Γ τ) :
 Hoare (MemOK E H)
  (evalE G F (n+1+1) (.cond (.local condition) (.local yes) (.local no)))
  (fun value y => MemOK E H y ∧ RValOK E y.2.heap.ty value)
  (fun e y => MemOK E H y ∧ NotStuck e) := by
 simp only [evalE]
 refine Hoare.bind (evalE_local_ok G F n condition) fun value => ?_
 cases value with
 | val value =>
   obtain ⟨bit,rfl⟩ := Val.eq_bool value
   cases bit
   · exact Hoare.conseq (evalE_local_ok G F n no)
      (fun _ h => h.1) (fun _ _ h => h) (fun _ _ h => h)
   · exact Hoare.conseq (evalE_local_ok G F n yes)
      (fun _ h => h.1) (fun _ _ h => h) (fun _ _ h => h)

theorem calldata_ok {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 {H : HeapTy} {types : List STy} (condition : Source.Idx Γ .bool)
 (yes no : Source.Idx Γ (.bytes .calldata))
 (admitted : types.all (STy.decodable E) = true) :
 Hoare (MemOK E H)
  (evalE G F (n+1+1+1) (.abiDecode (.cond (.local condition) (.local yes) (.local no)) rfl admitted))
  (fun value y => MemOK E H y ∧ RValOK E y.2.heap.ty value)
  (fun e y => MemOK E H y ∧ NotStuck e) :=
 LiteralFailureCalldataDecode.arm G F (n+1+1) _ admitted (choice_ok G F n condition yes no)

theorem storage_ok {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 {H : HeapTy} {types : List STy} (condition : Source.Idx Γ .bool)
 (yes no : Source.Idx Γ (.bytes .storage))
 (admitted : types.all (STy.decodable E) = true) :
 Hoare (MemOK E H)
  (evalE G F (n+1+1+1) (.abiDecode (.cond (.local condition) (.local yes) (.local no)) rfl admitted))
  (fun value y => MemOK E H y ∧ RValOK E y.2.heap.ty value)
  (fun e y => MemOK E H y ∧ NotStuck e) :=
 LiteralFailureStorageDecode.arm G F (n+1+1) _ admitted (choice_ok G F n condition yes no)

theorem memory_ok {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 {H : HeapTy} {types : List STy} (condition : Source.Idx Γ .bool)
 (yes no : Source.Idx Γ (.bytes .memory))
 (admitted : types.all (STy.decodable E) = true) :
 Hoare (MemOK E H)
  (evalE G F (n+1+1+1) (.abiDecode (.cond (.local condition) (.local yes) (.local no)) rfl admitted))
  (fun value y => MemOK E H y ∧ RValOK E y.2.heap.ty value)
  (fun e y => MemOK E H y ∧ NotStuck e) :=
 evalE_abiDecode_ok G F (n+1+1) _ rfl admitted (choice_ok G F n condition yes no)

end Solidity.Lowering.V08.LiteralFailureChoiceDecode
