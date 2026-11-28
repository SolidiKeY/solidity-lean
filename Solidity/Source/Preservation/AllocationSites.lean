import Solidity.Source.Decode
import Solidity.Source.Preservation.Frames

namespace Solidity.Source.Preservation
open EM
variable {E : Env} {Γ : RCtx}

example {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat) (bs : List UInt8)
    (s : EMState E Γ) :
    (evalE G F (n+1) (Γ := Γ) (.str bs)).run s = (.ok (.strLit bs), s) := by rfl
example {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat) (nl : NumLit) (len : Nat)
    (s : EMState E Γ) :
    (evalE G F (n+1) (Γ := Γ) (.bytesLit nl len)).run s = (.ok (.hex nl.value len), s) := by rfl
example {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat) (bs : List UInt8)
    (plan : FailureExecution.RuntimePlan) (known : Bool) (s : EMState E Γ) :
    ((evalE (plan := plan) (calldataKnown := known) G F n (Γ := Γ) (.str bs)).run s).2 = s := by
  cases n <;> cases known <;> rfl
example {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat) (nl : NumLit) (len : Nat)
    (plan : FailureExecution.RuntimePlan) (known : Bool) (s : EMState E Γ) :
    ((evalE (plan := plan) (calldataKnown := known) G F n (Γ := Γ) (.bytesLit nl len)).run s).2 = s := by
  cases n <;> cases known <;> rfl

example {E : Env} {Γ : RCtx} (F : Fr) (n : Nat) (bs : List UInt8) :
    (convRV F n (.bytes .memory) (.strLit bs) : EM E Γ _) =
      (do let v ← allocRef (Data.bytes (l := .memory) bs); pure (.val v)) := by rfl
example {E : Env} {Γ : RCtx} (F : Fr) (n : Nat) (bs : List UInt8) :
    (convRV F n (.string .memory) (.strLit bs) : EM E Γ _) =
      (do let v ← allocRef (Data.string (l := .memory) bs); pure (.val v)) := by rfl

theorem allocBytes_mem {H : HeapTy} (bs : Roadmap.Bytes) :
    Hoare (MemOK E H) (allocRef (Data.bytes (l := .memory) bs) : EM E Γ (Val E.layout (.bytes .memory)))
      (fun v y => MemOK E H y ∧ v.RefOK E y.2.heap.ty) (fun _ y => MemOK E H y) :=
  Hoare.conseq (allocRef_mem _ rfl trivial trivial) (fun _ h => ⟨h, .bytes bs⟩)
    (fun _ _ h => h) (fun _ _ h => h)

theorem allocString_mem {H : HeapTy} (bs : Roadmap.Bytes) :
    Hoare (MemOK E H) (allocRef (Data.string (l := .memory) bs) : EM E Γ (Val E.layout (.string .memory)))
      (fun v y => MemOK E H y ∧ v.RefOK E y.2.heap.ty) (fun _ y => MemOK E H y) :=
  Hoare.conseq (allocRef_mem _ rfl trivial trivial) (fun _ h => ⟨h, .string bs⟩)
    (fun _ _ h => h) (fun _ _ h => h)

theorem literalBytes_mem {H : HeapTy} (F : Fr) (n : Nat) (bs : Roadmap.Bytes) :
    Hoare (MemOK E H) (convRV F n (.bytes .memory) (.strLit bs) : EM E Γ _)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  simp only [convRV, reduceCtorEq, ↓reduceDIte, pure_bind]
  exact Hoare.bind (allocBytes_mem bs) fun v => Hoare.pure' fun _ h => h

theorem literalString_mem {H : HeapTy} (F : Fr) (n : Nat) (bs : Roadmap.Bytes) :
    Hoare (MemOK E H) (convRV F n (.string .memory) (.strLit bs) : EM E Γ _)
      (fun v y => MemOK E H y ∧ RValOK E y.2.heap.ty v) (fun _ y => MemOK E H y) := by
  simp only [convRV, reduceCtorEq, ↓reduceDIte, pure_bind]
  exact Hoare.bind (allocString_mem bs) fun v => Hoare.pure' fun _ h => h

#print axioms literalBytes_mem
#print axioms literalString_mem
end Solidity.Source.Preservation
