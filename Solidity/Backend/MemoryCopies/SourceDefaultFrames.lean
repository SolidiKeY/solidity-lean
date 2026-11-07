import Solidity.Backend.MemoryCopies.SourceFramesCore

/-! Every existing Source default traversal only allocates. The statement is
uniform in Source types and horizons, including partially completed runs. -/
namespace Solidity.Backend.MemoryCopies
open AllocatesOnly

variable {E : Source.Env} {Γ : Source.RCtx}

mutual

theorem zeroData_allocates : ∀ (fuel : Nat) (τ : Source.STy),
    AllocatesOnly (Source.zeroData (E := E) (Γ := Γ) fuel τ)
  | 0, _ => halt _
  | fuel + 1, τ => by
    simp only [Source.zeroData]
    split
    · exact pure' _
    · exact pure' _
    · exact pure' _
    · exact bind (zeroElems_allocates fuel _ _) (fun _ => pure' _)
    · exact bind (zeroFields_allocates fuel _) (fun _ => pure' _)
    · exact bind (zeroVal_allocates fuel _) (fun _ => pure' _)

theorem zeroVal_allocates : ∀ (fuel : Nat) (τ : Source.STy),
    AllocatesOnly (Source.zeroVal (E := E) (Γ := Γ) fuel τ)
  | 0, _ => halt _
  | fuel + 1, τ => by
    simp only [Source.zeroVal]
    split
    · exact pure' _
    · split
      · exact bind (zeroData_allocates fuel τ) (fun data => allocRef data)
      · exact halt _

theorem zeroElems_allocates : ∀ (fuel : Nat) (τ : Source.STy) (length : Nat),
    AllocatesOnly (Source.zeroElems (E := E) (Γ := Γ) fuel τ length)
  | 0, _, length => by cases length <;> exact halt _
  | _ + 1, _, 0 => pure' _
  | fuel + 1, τ, length + 1 =>
    bind (zeroVal_allocates fuel τ) (fun _ =>
      bind (zeroElems_allocates fuel τ length) (fun _ => pure' _))

theorem zeroFields_allocates : ∀ (fuel : Nat) (types : List Source.STy),
    AllocatesOnly (Source.zeroFields (E := E) (Γ := Γ) fuel types)
  | 0, types => by cases types <;> exact halt _
  | _ + 1, [] => pure' _
  | fuel + 1, τ :: types =>
    bind (zeroVal_allocates fuel τ) (fun _ =>
      bind (zeroFields_allocates fuel types) (fun _ => pure' _))

end

/-- An inhabited frame certificate for all default shapes and horizons. -/
def defaultTraversalFrames (E : Source.Env) (Γ : Source.RCtx) :
    DefaultTraversalFrameCertificate E Γ :=
  ⟨zeroData_allocates, zeroVal_allocates, zeroElems_allocates, zeroFields_allocates⟩

/-- The actual outcome, whether success or Halt, has the preserved reached frame. -/
def defaultOutcomeCertificate {E : Source.Env} {Γ : Source.RCtx}
    (fuel : Nat) (τ : Source.STy) (before : Source.EMState E Γ) :
    SourceDefaultOutcomeCertificate fuel τ before
      ((Source.zeroVal (E := E) (Γ := Γ) fuel τ).run before).2
      ((Source.zeroVal (E := E) (Γ := Γ) fuel τ).run before).1 := by
  have preserved : AllocationExtension before
      ((Source.zeroVal (E := E) (Γ := Γ) fuel τ).run before).2 :=
    zeroVal_allocates fuel τ before
  exact ⟨rfl, preserved.frame, preserved.growth, preserved.old⟩

#print axioms defaultTraversalFrames
#print axioms defaultOutcomeCertificate
end Solidity.Backend.MemoryCopies
