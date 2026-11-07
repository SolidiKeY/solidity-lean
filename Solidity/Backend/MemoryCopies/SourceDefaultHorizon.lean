import Solidity.Backend.MemoryCopies.SourceDefaultHorizonInterface
import Solidity.Backend.MemoryCopies.SourceCopyHorizon
import Solidity.Backend.MemoryCopies.SourceFields

/-! Default traversal fuel extension and canonical existing construction results.
All statements concern existing Source operations; no shape selector is added. -/
namespace Solidity.Backend.MemoryCopies
variable {E : Source.Env} {Γ : Source.RCtx}

mutual

theorem zeroData_horizon : ∀ (fuel slack : Nat) (type : Source.STy),
    CopyHorizonExtends (Source.zeroData (E := E) (Γ := Γ) fuel type)
      (Source.zeroData (fuel + slack) type)
  | 0, slack, type => CopyHorizonExtends.timeout _
  | fuel + 1, slack, type => by
    have budget : fuel + 1 + slack = (fuel + slack) + 1 := by omega
    rw [budget]
    simp only [Source.zeroData]
    split
    · exact CopyHorizonExtends.refl _
    · exact CopyHorizonExtends.refl _
    · exact CopyHorizonExtends.refl _
    · exact CopyHorizonExtends.bind (zeroElems_horizon fuel slack _ _) (fun _ => .refl _)
    · exact CopyHorizonExtends.bind (zeroFields_horizon fuel slack _) (fun _ => .refl _)
    · exact CopyHorizonExtends.bind (zeroVal_horizon fuel slack _) (fun _ => .refl _)

theorem zeroVal_horizon : ∀ (fuel slack : Nat) (type : Source.STy),
    CopyHorizonExtends (Source.zeroVal (E := E) (Γ := Γ) fuel type)
      (Source.zeroVal (fuel + slack) type)
  | 0, slack, type => CopyHorizonExtends.timeout _
  | fuel + 1, slack, type => by
    have budget : fuel + 1 + slack = (fuel + slack) + 1 := by omega
    rw [budget]
    simp only [Source.zeroVal]
    split
    · exact CopyHorizonExtends.refl _
    · split
      · exact CopyHorizonExtends.bind (zeroData_horizon fuel slack type) (fun _ => .refl _)
      · exact CopyHorizonExtends.refl _

theorem zeroElems_horizon : ∀ (fuel slack : Nat) (type : Source.STy) (count : Nat),
    CopyHorizonExtends (Source.zeroElems (E := E) (Γ := Γ) fuel type count)
      (Source.zeroElems (fuel + slack) type count)
  | 0, slack, type, count => by cases count <;> exact CopyHorizonExtends.timeout _
  | fuel + 1, slack, type, 0 => by
    have budget : fuel + 1 + slack = (fuel + slack) + 1 := by omega
    rw [budget]
    exact CopyHorizonExtends.refl _
  | fuel + 1, slack, type, count + 1 => by
    have budget : fuel + 1 + slack = (fuel + slack) + 1 := by omega
    rw [budget]
    exact CopyHorizonExtends.bind (zeroVal_horizon fuel slack type) (fun _ =>
      .bind (zeroElems_horizon fuel slack type count) (fun _ => .refl _))

theorem zeroFields_horizon : ∀ (fuel slack : Nat) (types : List Source.STy),
    CopyHorizonExtends (Source.zeroFields (E := E) (Γ := Γ) fuel types)
      (Source.zeroFields (fuel + slack) types)
  | 0, slack, types => by cases types <;> exact CopyHorizonExtends.timeout _
  | fuel + 1, slack, [] => by
    have budget : fuel + 1 + slack = (fuel + slack) + 1 := by omega
    rw [budget]
    exact CopyHorizonExtends.refl _
  | fuel + 1, slack, type :: types => by
    have budget : fuel + 1 + slack = (fuel + slack) + 1 := by omega
    rw [budget]
    exact CopyHorizonExtends.bind (zeroVal_horizon fuel slack type) (fun _ =>
      .bind (zeroFields_horizon fuel slack types) (fun _ => .refl _))
end

def sourceDefaultHorizons (E : Source.Env) (Γ : Source.RCtx) : SourceDefaultHorizonCertificate E Γ :=
  ⟨zeroData_horizon,zeroVal_horizon,zeroElems_horizon,zeroFields_horizon⟩

theorem SourceConstructionCertificate.horizon_exact {type : Source.STy} {memory : type.loc? = some .memory}
    (construction : SourceConstructionCertificate E type memory) (before : Source.EMState E Γ) (slack : Nat) :
    (Source.zeroVal (E := E) (Γ := Γ) (construction.horizon + slack) type).run before =
      (Source.zeroVal construction.horizon type).run before := by
  obtain ⟨after,root,data,certificate,_,_⟩ := construction.execution before 0
  have execution : (Source.zeroVal (E := E) (Γ := Γ) construction.horizon type).run before =
      (.ok (.memRef memory root),after) := by
    simpa only [Nat.add_zero] using certificate.execution
  exact ((zeroVal_horizon construction.horizon slack type).success before after (.memRef memory root) execution).trans execution.symm

theorem SourceValueConstruction.horizon_exact {type : Source.STy}
    (construction : SourceValueConstruction E type) (before : Source.EMState E Γ) (slack : Nat) :
    (Source.zeroVal (E := E) (Γ := Γ) (construction.horizon + slack) type).run before =
      (Source.zeroVal construction.horizon type).run before := by
  obtain ⟨value,after,run,_,_⟩ := construction.execution before 0
  have execution : (Source.zeroVal (E := E) (Γ := Γ) construction.horizon type).run before = (.ok value,after) := by
    simpa only [Nat.add_zero] using run
  exact ((zeroVal_horizon construction.horizon slack type).success before after value execution).trans execution.symm

theorem SourceFieldsConstruction.horizon_exact {types : List Source.STy}
    (construction : SourceFieldsConstruction E types) (before : Source.EMState E Γ) (slack : Nat) :
    (Source.zeroFields (E := E) (Γ := Γ) (construction.horizon + slack) types).run before =
      (Source.zeroFields construction.horizon types).run before := by
  obtain ⟨values,after,run,_,_⟩ := construction.execution before 0
  have execution : (Source.zeroFields (E := E) (Γ := Γ) construction.horizon types).run before = (.ok values,after) := by
    simpa only [Nat.add_zero] using run
  exact ((zeroFields_horizon construction.horizon slack types).success before after values execution).trans execution.symm

#print axioms zeroData_horizon
#print axioms zeroVal_horizon
#print axioms zeroElems_horizon
#print axioms zeroFields_horizon
#print axioms sourceDefaultHorizons
#print axioms SourceConstructionCertificate.horizon_exact
#print axioms SourceValueConstruction.horizon_exact
#print axioms SourceFieldsConstruction.horizon_exact
end Solidity.Backend.MemoryCopies
