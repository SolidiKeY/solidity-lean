import Solidity.Source.Progress.ReadyArguments

/-! Default return-slot progress for explicit ready types. Empty memory bytes,
strings and dynamic arrays allocate through the existing zeroData/zeroVal path;
other types retain an explicit existing Val.default witness. No default policy
or horizon behavior is changed. -/
namespace Solidity.Source.Progress
open EM
variable {E : Env} {Γ : RCtx}

inductive EmptyMemoryType : STy → Prop
  | bytes : EmptyMemoryType (.bytes .memory)
  | string : EmptyMemoryType (.string .memory)
  | array (σ : STy) : EmptyMemoryType (.array .memory σ none)

inductive ZeroReady (E : Env) : STy → Prop
  | value {τ : STy} : (Val.default E.layout τ).isSome = true → ZeroReady E τ
  | memory {τ : STy} : EmptyMemoryType τ → ZeroReady E τ

theorem EmptyMemoryType.location {τ : STy} (ready : EmptyMemoryType τ) : τ.loc? = some .memory := by
  cases ready <;> rfl

theorem ZeroReady.boundary {τ : STy} (ready : ZeroReady E τ) :
    (Val.default E.layout τ).isSome = true ∨ τ.loc? = some .memory := by
  cases ready with
  | value defaults => exact .inl defaults
  | memory empty => exact .inr empty.location

theorem empty_zeroData_ns {τ : STy} (ready : EmptyMemoryType τ) :
    ∀ n, NS (zeroData (E := E) (Γ := Γ) n τ)
  | 0 => NS.halt' (fun _ h => by cases h)
  | _+1 => by cases ready <;> exact NS.pure' _

theorem zero_ready_ns {τ : STy} (ready : ZeroReady E τ) (n : Nat) :
    NS (zeroVal (E := E) (Γ := Γ) n τ) := by
  cases ready with
  | value defaults => exact zeroVal_ns n defaults
  | memory empty =>
    cases n with
    | zero => exact NS.halt' (fun _ h => by cases h)
    | succ n =>
      have absent : Val.default E.layout τ = none := by cases empty <;> rfl
      rw [zeroVal,absent,if_pos empty.location]
      exact NS.bind (empty_zeroData_ns empty n) (fun data => allocRef_ns empty.location data)

theorem zero_ready_vals_ns (n : Nat) : ∀ (types : List STy),
    (∀ τ ∈ types, ZeroReady E τ) → NS (zeroVals (E := E) (Γ := Γ) n types)
  | [], _ => NS.pure' _
  | τ :: types, ready => by
    rw [zeroVals]
    refine NS.bind (zero_ready_ns (ready τ (by simp only [List.mem_cons,true_or])) n) (fun _ => ?_)
    exact NS.bind (zero_ready_vals_ns n types (fun σ member => ready σ
      (by simp only [List.mem_cons,member,or_true]))) (fun _ => NS.pure' _)

#print axioms zero_ready_ns
#print axioms zero_ready_vals_ns
end Solidity.Source.Progress
