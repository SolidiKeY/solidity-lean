import Solidity.Source.Machine
import Solidity.Semantics.Run

/-! G18.02 admission boundary. These laws consume the real declaration-derived
Source.Env.pathTy and actual intrinsic root typing. They do not certify a graph
or lower an execution. In particular static-array path typing has no bounds
check: the source execution must still perform that check. -/
namespace Solidity.Backend.Aggregates

/-- Declaration/type correspondence interface (no execution simulation). Not yet
instantiated; `root_path` restates its `root_agrees` field. -/
structure DeclarationRoots (E : Source.Env) (C : Contract) where
  sourceName : Name → Source.DeclName
  sourceType : Ty → Source.STy
  root_agrees : ∀ (name : Name) (ty : Ty), C.rootType name = some ty →
    E.rootTy (sourceName name) = some (sourceType ty)

theorem DeclarationRoots.root_path {E : Source.Env} {C : Contract}
    (d : DeclarationRoots E C) (name : Name) (ty : Ty)
    (h : C.rootType name = some ty) :
    E.pathTy ⟨d.sourceName name, []⟩ = some (d.sourceType ty) := d.root_agrees name ty h

/-- Preserve the complete ordered suffix; no field/index/key reordering. -/
theorem path_append (E : Source.Env) (p : Source.SPath) (steps : List Source.Step) :
    E.pathTy {p with steps := p.steps ++ steps} =
      steps.foldl (fun o s => o.bind (E.stepTy · s)) (E.pathTy p) := by
  exact List.foldl_append

theorem path_step (E : Source.Env) (p : Source.SPath) (τ : Source.STy)
    (h : E.pathTy p = some τ) (step : Source.Step) :
    E.pathTy {p with steps := p.steps ++ [step]} = E.stepTy τ step := by
  rw [path_append, h]
  rfl

theorem array_path (E : Source.Env) (p : Source.SPath) (l : Source.DataLoc)
    (τ : Source.STy) (n : Option Nat) (h : E.pathTy p = some (.array l τ n)) (i : Nat) :
    E.pathTy {p with steps := p.steps ++ [.index i]} = some τ :=
  path_step E p (.array l τ n) h (.index i)

theorem mapping_path (E : Source.Env) (p : Source.SPath) (k v : Source.STy)
    (h : E.pathTy p = some (.mapping k v)) (bytes : List UInt8) :
    E.pathTy {p with steps := p.steps ++ [.key bytes]} = some v :=
  path_step E p (.mapping k v) h (.key bytes)

theorem struct_path (E : Source.Env) (p : Source.SPath) (l : Source.DataLoc)
    (name : Source.DeclName) (h : E.pathTy p = some (.struct l name)) (i : Nat) :
    E.pathTy {p with steps := p.steps ++ [.field i]} = E.fieldTy? name .storage i :=
  path_step E p (.struct l name) h (.field i)

#print axioms path_append
#print axioms array_path
#print axioms mapping_path
#print axioms struct_path
end Solidity.Backend.Aggregates
