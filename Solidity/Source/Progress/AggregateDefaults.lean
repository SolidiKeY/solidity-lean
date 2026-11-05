import Solidity.Source.Progress.ReadyDefaults
import Solidity.Source.Preservation.LocalFrames

/-! Finite aggregate default shapes over the existing Source types. Fixed
memory arrays and memory structs recursively witness their element/field
defaults. This is a proof certificate, not a replacement type representation;
the original evaluator, ZeroReady and default/allocation policies are unchanged. -/
namespace Solidity.Source.Progress
open EM
variable {E : Env} {Γ : RCtx}

inductive FiniteDefault (E : Env) : STy → Prop
  | ready {τ : STy} : ZeroReady E τ → FiniteDefault E τ
  | fixed {σ : STy} (m : Nat) : FiniteDefault E σ →
      FiniteDefault E (.array .memory σ (some m))
  | structNew (dn : DeclName) :
      (∀ τ ∈ E.layout.fields dn, FiniteDefault E τ) →
      FiniteDefault E (.struct .memory dn)

theorem finite_defaults_at : ∀ n : Nat,
    (∀ τ, FiniteDefault E τ → NS (zeroVal (E:=E) (Γ:=Γ) n τ)) ∧
    (∀ τ, FiniteDefault E τ → ∀ m, NS (zeroElems (E:=E) (Γ:=Γ) n τ m)) ∧
    (∀ ts, (∀ τ ∈ ts, FiniteDefault E τ) → NS (zeroFields (E:=E) (Γ:=Γ) n ts))
  | 0 => ⟨fun _ _=>NS.halt' (fun _ h=>by cases h),
      (fun _ _ m=>by cases m <;> rw [zeroElems] <;> exact NS.halt' (fun _ h=>by cases h)),
      (fun ts _=>by cases ts <;> rw [zeroFields] <;> exact NS.halt' (fun _ h=>by cases h))⟩
  | n+1 => by
    refine ⟨?_,?_,?_⟩
    · intro τ shape
      cases shape with
      | ready ready => exact zero_ready_ns ready (n+1)
      | @fixed σ m element =>
        rw [zeroVal,show Val.default E.layout (.array .memory σ (some m)) = none from rfl]
        simp only [STy.loc?,↓reduceIte]
        cases n with
        | zero =>
          rw [zeroData.eq_1]
          exact NS.bind (NS.halt' (fun _ h=>by cases h)) (fun data=>allocRef_ns rfl data)
        | succ n =>
          rw [zeroData]
          exact NS.bind (NS.bind ((finite_defaults_at n).2.1 σ element m) (fun _=>NS.pure' _))
            (fun data=>allocRef_ns rfl data)
      | structNew dn fields =>
        rw [zeroVal,show Val.default E.layout (.struct .memory dn) = none from rfl]
        simp only [STy.loc?,↓reduceIte]
        cases n with
        | zero =>
          rw [zeroData.eq_1]
          exact NS.bind (NS.halt' (fun _ h=>by cases h)) (fun data=>allocRef_ns rfl data)
        | succ n =>
          rw [zeroData]
          exact NS.bind (NS.bind ((finite_defaults_at n).2.2 _ fields) (fun _=>NS.pure' _))
            (fun data=>allocRef_ns rfl data)
    · intro τ shape m
      cases m with
      | zero => exact NS.pure' _
      | succ m =>
        rw [zeroElems]
        exact NS.bind ((finite_defaults_at n).1 τ shape) (fun _=>
          NS.bind ((finite_defaults_at n).2.1 τ shape m) (fun _=>NS.pure' _))
    · intro ts shapes
      cases ts with
      | nil => exact NS.pure' _
      | cons τ ts =>
        rw [zeroFields]
        refine NS.bind ((finite_defaults_at n).1 τ (shapes τ (by simp only [List.mem_cons,true_or]))) (fun _=>?_)
        exact NS.bind ((finite_defaults_at n).2.2 ts (fun σ member=>
          shapes σ (by simp only [List.mem_cons,member,or_true]))) (fun _=>NS.pure' _)

theorem finite_default_ns {τ : STy} (shape : FiniteDefault E τ) (n : Nat) :
    NS (zeroVal (E:=E) (Γ:=Γ) n τ) := (finite_defaults_at n).1 τ shape

theorem finite_default_progress_and_memory {τ : STy} (shape : FiniteDefault E τ)
    (n : Nat) (H : HeapTy) :
    NS (zeroVal (E:=E) (Γ:=Γ) n τ) ∧
    Hoare (MemOK E H) (zeroVal (E:=E) (Γ:=Γ) n τ)
      (fun v y=>MemOK E H y ∧ v.RefOK E y.2.heap.ty) (fun _ y=>MemOK E H y) :=
  ⟨finite_default_ns shape n,(Source.zeroOK n).val H τ⟩

theorem finite_default_vals_ns (n : Nat) : ∀ ts,
    (∀ τ ∈ ts, FiniteDefault E τ) → NS (zeroVals (E:=E) (Γ:=Γ) n ts)
  | [], _ => NS.pure' _
  | τ::ts, shapes => by
    rw [zeroVals]
    refine NS.bind (finite_default_ns (shapes τ (by simp only [List.mem_cons,true_or])) n) (fun _=>?_)
    exact NS.bind (finite_default_vals_ns n ts (fun σ member=>
      shapes σ (by simp only [List.mem_cons,member,or_true]))) (fun _=>NS.pure' _)

#print axioms finite_defaults_at
#print axioms finite_default_ns
#print axioms finite_default_progress_and_memory
#print axioms finite_default_vals_ns
end Solidity.Source.Progress
