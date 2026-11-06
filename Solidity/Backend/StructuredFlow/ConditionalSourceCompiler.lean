import Solidity.Lowering.G19.ConditionalStatement
import Solidity.Evm.Correct

/-! Compile the existing V07-related conditional statement, preserving its
actual Source run and reached map as well as the intrinsic compiler contract. -/
namespace Solidity.Backend.StructuredFlow.ConditionalSourceCompiler
open Solidity.Lowering.V07 Solidity.Lowering.G19

def emit {C : Contract} {Γ : Ctx} {p : PrimTy} (base : Nat)
    (ci ca : Idx Γ (.val .bool)) (i a j b : Idx Γ (.val p)) : List Evm.Instr :=
  Evm.compileProg base (ConditionalStatement.code (C := C) ci ca i a j b)

theorem code_exact {C : Contract} {Γ : Ctx} {p : PrimTy} (base : Nat)
    (ci ca : Idx Γ (.val .bool)) (i a j b : Idx Γ (.val p)) :
    emit (C := C) base ci ca i a j b =
      Evm.compileProg base (ConditionalStatement.code (C := C) ci ca i a j b) := by rfl

theorem correct {E : Source.Env} {srcΓ : Source.RCtx} {τ : Source.STy}
    {C : Contract} {Γ : Ctx} {p : PrimTy}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {returns : List Source.STy} {M : Bool} {k : Source.SCtx}
    (source : Source.EMState E srcΓ) (target : State C Γ) (m : ContextMap srcΓ Γ)
    (R : (σ : Source.STy) → (u : LTy) → Source.Val E.layout σ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (c : Bool), R .bool (.val .bool) v c → v = .bool c)
    (ci ca : Source.Idx srcΓ .bool) (i a j b : Source.Idx srcΓ τ)
    (tci tca : Idx Γ (.val .bool)) (ti ta tj tb : Idx Γ (.val p))
    (mapCI : m.slot ci = ⟨.val .bool,tci⟩) (mapCA : m.slot ca = ⟨.val .bool,tca⟩)
    (mapI : m.slot i = ⟨.val p,ti⟩) (mapA : m.slot a = ⟨.val p,ta⟩)
    (mapJ : m.slot j = ⟨.val p,tj⟩) (mapB : m.slot b = ⟨.val p,tb⟩) {L base : Nat} {F₀ F₁ : Evm.Frag Γ} {machine : Evm.Machine}
    (entry : Evm.Sim C L base F₀ target machine)
    (checked : Evm.inFragP F₀ (ConditionalStatement.code (C := C) tci tca ti ta tj tb) = some F₁)
    (capacity : L + Evm.Prog.pushes (ConditionalStatement.code (C := C) tci tca ti ta tj tb) ≤ Evm.Lmax) :
    let choice : Bool := TEnv.get tca target.env
    (Source.execS G F (fuel+4) nps ph (R := returns) (M := M)
      (ConditionalStatement.statement (k := k) ci ca i a j b) source.1).run (.nil,source.2) =
      (.ok (Source.Out.normal (ConditionalAssignments.sourceAfter source ci choice i a j b).1),(.nil,source.2)) ∧
    (ConditionalStatement.code (C := C) tci tca ti ta tj tb).run target =
      .ok ⟨ConditionalAssignments.targetAfter target tci choice ti ta tj tb,List.prefix_refl _⟩ ∧
    m.Related R (ConditionalAssignments.sourceAfter source ci choice i a j b).1
      (ConditionalAssignments.targetAfter target tci choice ti ta tj tb).env ∧
    (ConditionalAssignments.targetAfter target tci choice ti ta tj tb).glob = target.glob ∧
    Evm.StmtOut C (L + Evm.Prog.pushes (ConditionalStatement.code (C := C) tci tca ti ta tj tb)) base F₁
      (Evm.Prog.shrinks (ConditionalStatement.code (C := C) tci tca ti ta tj tb))
      (Evm.Prog.pays (ConditionalStatement.code (C := C) tci tca ti ta tj tb))
      (Solidity.Prog.asserts (ConditionalStatement.code (C := C) tci tca ti ta tj tb))
      ((ConditionalStatement.code (C := C) tci tca ti ta tj tb).run target)
      (Evm.run (emit (C := C) base tci tca ti ta tj tb) machine) machine := by
  rcases ConditionalStatement.correct G F fuel nps ph source target m R aligned boolReflect
    ci ca i a j b tci tca ti ta tj tb mapCI mapCA mapI mapA mapJ mapB with
    ⟨src,tgt,related,globals⟩
  exact ⟨src,tgt,related,globals,Evm.prog_sim _ entry checked capacity⟩

end Solidity.Backend.StructuredFlow.ConditionalSourceCompiler
