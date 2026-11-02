import Solidity.Source.Preservation.Encoding
import Solidity.Source.Preservation.ValueConversions
import Solidity.Source.Preservation.StatementFrames

/-! Remaining actual ABI encoding evaluator arms. Selector eligibility is the
existing `AbiKind.argsOK` implicit-conversion condition, not a new input policy.
All triples preserve the full invariant on every halt as well as success.
-/
namespace Solidity.Source.Preservation
open EM
variable {E : Env} {Γ : RCtx}

theorem selector_source (B : DeclName → DeclName → Bool) {s : STy} (h : s.implicit B (.fixedBytes 4 (by decide)) = true) :
    (s.isValue = true ∨ (∃ q, s = .rational q) ∨ (∃ q k, s = .hexConst q k)) ∨
      ∃ bs, s = .stringLit bs := by
  cases s with
  | fixedBytes k hk => exact Or.inl (.inl rfl)
  | rational q => exact Or.inl (.inr (.inl ⟨q, rfl⟩))
  | hexConst q k => exact Or.inl (.inr (.inr ⟨q, k, rfl⟩))
  | stringLit bs => exact Or.inr ⟨bs, rfl⟩
  | _ => change false = true at h; cases h

theorem selectorConv_mem {H : HeapTy} (F : Fr) (n : Nat) {s : STy}
    (hs : s.implicit E.isBase (.fixedBytes 4 (by decide)) = true) (v : RVal E.layout s) :
    Hoare (MemOK E H) (convRV F n (.fixedBytes 4 (by decide)) v : EM E Γ _)
      (fun _ y => MemOK E H y) (fun _ y => MemOK E H y) := by
  rcases selector_source E.isBase hs with hv | ⟨bs, rfl⟩
  · exact convRV_pres F n (.inl hs) hv v H
  · simp only [convRV, reduceCtorEq, ↓reduceDIte, pure_bind]
    exact Hoare.pure' fun _ h => h

theorem evalE_encodePacked_mem (G : Glob E) (F : Fr) (n : Nat) {H : HeapTy}
    {ts : List STy} (args : RArgs E Γ ts)
    (ha : Hoare (MemOK E H) (evalArgs G F n args)
      (fun _ y => MemOK E H y) (fun _ y => MemOK E H y)) :
    Hoare (MemOK E H) (evalE G F (n + 1) (.abiEncode .encodePacked args))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  simp only [evalE]
  exact Hoare.bind ha fun vs => Hoare.bind (encodeVals_mem F n true vs) fun bs =>
    Hoare.bind (allocBytes_mem bs) fun v => Hoare.pure' fun _ h => h

theorem evalE_encodeWithSelector_mem (G : Glob E) (F : Fr) (n : Nat) {H : HeapTy}
    {s : STy} {ts : List STy} (args : RArgs E Γ (s :: ts))
    (hs : s.implicit E.isBase (.fixedBytes 4 (by decide)) = true)
    (ha : Hoare (MemOK E H) (evalArgs G F n args)
      (fun _ y => MemOK E H y) (fun _ y => MemOK E H y)) :
    Hoare (MemOK E H) (evalE G F (n + 1) (.abiEncode .encodeWithSelector args))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  simp only [evalE]
  refine Hoare.bind ha fun vs => ?_
  cases vs with
  | cons s vs =>
    simp only [pure_bind]
    exact Hoare.bind (selectorConv_mem F n hs s) fun w =>
      Hoare.bind (getV_keep (MemOK E H) w) fun sel =>
        Hoare.bind (encodeVals_mem F n false vs) fun data =>
          Hoare.bind (allocBytes_mem (sel.bytesOf ++ data)) fun v => Hoare.pure' fun _ h => h

theorem evalE_encodeWithSignature_mem (G : Glob E) (F : Fr) (n : Nat) {H : HeapTy}
    {s : STy} {ts : List STy} (args : RArgs E Γ (s :: ts))
    (ha : Hoare (MemOK E H) (evalArgs G F n args)
      (fun _ y => MemOK E H y) (fun _ y => MemOK E H y)) :
    Hoare (MemOK E H) (evalE G F (n + 1) (.abiEncode .encodeWithSignature args))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  simp only [evalE]
  refine Hoare.bind ha fun vs => ?_
  cases vs with
  | cons s vs =>
    simp only [pure_bind]
    exact Hoare.bind (bytesOfRV_mem F n s) fun sig =>
      Hoare.bind (encodeVals_mem F n false vs) fun data =>
        Hoare.bind (allocBytes_mem ((wordBytes (G.fixed.hash sig)).take 4 ++ data)) fun v => Hoare.pure' fun _ h => h

/-- All source-admitted encoding kinds, using the original signature check. -/
theorem evalE_abiKind_mem (G : Glob E) (F : Fr) (n : Nat) {H : HeapTy}
    (k : AbiKind) {ts : List STy} (args : RArgs E Γ ts) (hk : k.argsOK E.isBase ts = true)
    (ha : Hoare (MemOK E H) (evalArgs G F n args)
      (fun _ y => MemOK E H y) (fun _ y => MemOK E H y)) :
    Hoare (MemOK E H) (evalE G F (n + 1) (.abiEncode k args))
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  cases k with
  | encode => exact evalE_abiEncode_mem G F n args ha
  | encodePacked => exact evalE_encodePacked_mem G F n args ha
  | encodeWithSelector =>
    cases ts with
    | nil => cases hk
    | cons t ts =>
      simp only [AbiKind.argsOK, Bool.and_eq_true] at hk
      exact evalE_encodeWithSelector_mem G F n args hk.1 ha
  | encodeWithSignature =>
    cases ts with
    | nil => cases hk
    | cons t ts => exact evalE_encodeWithSignature_mem G F n args ha

#print axioms evalE_abiKind_mem
#print axioms selectorConv_mem
#print axioms evalE_encodePacked_mem
#print axioms evalE_encodeWithSelector_mem
#print axioms evalE_encodeWithSignature_mem
end Solidity.Source.Preservation
