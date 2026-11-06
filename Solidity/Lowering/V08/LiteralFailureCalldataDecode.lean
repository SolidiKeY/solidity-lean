import Solidity.Source.Calldata

/-! G21 preservation/progress consumer for the existing calldata abi.decode
arm. No decoder, source constructor or calldata admission rule is added. -/
namespace Solidity.Lowering.V08.LiteralFailureCalldataDecode
open Solidity Source

/-- Reading a typed calldata bytes reference keeps the actual state and cannot
be stuck; physical input extent is not inferred from logical reference size. -/
theorem bytes_ok {E : Env} {Γ : RCtx} (F : Fr) (n : Nat) {H : HeapTy}
 (v : RVal E.layout (.bytes .calldata)) :
 Hoare (fun y => MemOK E H y ∧ RValOK E y.2.heap.ty v)
  (bytesOfRV F n v : EM E Γ Roadmap.Bytes)
  (fun _ y => MemOK E H y) (fun e y => MemOK E H y ∧ NotStuck e) := by
 cases v with
 | val a =>
   obtain ⟨h,off,len,rfl⟩ := Val.cd_shape rfl a
   simp only [bytesOfRV]
   exact Hoare.pure' fun _ hy => hy.1

/-- The existing decoder consumes the actual calldata bytes, preserving its
original failure behavior. This arm is relative to its data expression; the
local corollary below discharges that premise using the published law. -/
theorem arm {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 {H : HeapTy} {types : List STy} (data : RExpr E Γ (.bytes .calldata))
 (admitted : types.all (STy.decodable E) = true)
 (hdata : Hoare (MemOK E H) (evalE G F n data)
  (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v)
  (fun e y => MemOK E H y ∧ NotStuck e)) :
 Hoare (MemOK E H) (evalE G F (n+1) (.abiDecode data rfl admitted))
  (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v)
  (fun e y => MemOK E H y ∧ NotStuck e) := by
 simp only [evalE]
 exact Hoare.bind hdata fun v => Hoare.bind (bytes_ok F n v) fun bs => abiDecodeData_ok bs admitted

/-- Closed for every existing typed calldata-bytes local, not a desired-run
premise or an assumed data-expression progress theorem. -/
theorem local_ok {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 {H : HeapTy} {types : List STy} (index : Idx Γ (.bytes .calldata))
 (admitted : types.all (STy.decodable E) = true) :
 Hoare (MemOK E H) (evalE G F (n+1+1) (.abiDecode (.local index) rfl admitted))
  (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v)
  (fun e y => MemOK E H y ∧ NotStuck e) :=
 arm G F (n+1) (.local index) admitted (evalE_local_ok G F n index)

/-- Exact local execution, including actual partial calldata extraction and
all subsequent decoder allocation/failures; no outcome is assumed. -/
theorem local_run {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 (types : List STy) (admitted : types.all (STy.decodable E) = true)
 (off len : Nat) (older : Locals E.layout Γ) (state : St E) :
 (evalE G F (n+2)
  (.abiDecode (.local .here) rfl admitted : RExpr E (.bytes .calldata :: Γ) (STy.ret types))).run
  (.cons (.cdRef rfl off len) older,state) =
 (abiDecodeData ((F.cd.drop off).take len) types).run
  (.cons (.cdRef rfl off len) older,state) := by
 rfl

end Solidity.Lowering.V08.LiteralFailureCalldataDecode
