import Solidity.Lowering.G19.ConditionalReturn
import Solidity.Evm.Correct

/-! Actual compiler of mapped conditional assignments then bare return.
The true capture classifies Source return, not an emitted EVM RETURN. -/
namespace Solidity.Backend.StructuredFlow.ConditionalReturnCompiler
open Solidity.Lowering.V07 Solidity.Lowering.G19
open ConditionalReturn (statement code reached)

def emit {C : Contract} {Γ : Ctx} {p : PrimTy} (base : Nat) (ci ca : Idx Γ (.val .bool))
    (i a j b : Idx Γ (.val p)) : List Evm.Instr :=
  Evm.compileProg base (code (C := C) ci ca i a j b)

theorem correct {E : Source.Env} {srcΓ : Source.RCtx} {τ : Source.STy}
    {C : Contract} {Γ : Ctx} {p : PrimTy}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {M : Bool} {k : Source.SCtx}
    (source : Source.EMState E srcΓ) (target : State C Γ) (m : ContextMap srcΓ Γ)
    (R : (σ : Source.STy) → (u : LTy) → Source.Val E.layout σ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (c : Bool), R .bool (.val .bool) v c → v = .bool c)
    (ci ca : Source.Idx srcΓ .bool) (i a j b : Source.Idx srcΓ τ)
    (tci tca : Idx Γ (.val .bool)) (ti ta tj tb : Idx Γ (.val p))
    (mapCI : m.slot ci = ⟨.val .bool,tci⟩) (mapCA : m.slot ca = ⟨.val .bool,tca⟩)
    (mapI : m.slot i = ⟨.val p,ti⟩) (mapA : m.slot a = ⟨.val p,ta⟩)
    (mapJ : m.slot j = ⟨.val p,tj⟩) (mapB : m.slot b = ⟨.val p,tb⟩)
    {L base : Nat} {frame : Evm.Frag Γ} {outFrame : Evm.Frag (.val .bool :: Γ)}
    {machine : Evm.Machine} (entry : Evm.Sim C L base frame target machine)
    (checked : Evm.inFragP frame (code (C := C) tci tca ti ta tj tb) = some outFrame)
    (capacity : L + Evm.Prog.pushes (code (C := C) tci tca ti ta tj tb) ≤ Evm.Lmax) :
    let choice : Bool := TEnv.get tca target.env
    (Source.execS G F (fuel+6) nps ph (M := M)
      (statement (k := k) ci ca i a j b) source.1).run (.nil,source.2) =
      (.ok (Source.Out.ret (ConditionalAssignments.sourceAfter source ci choice i a j b).1),(.nil,source.2)) ∧
    (code tci tca ti ta tj tb).run target =
      .ok ⟨reached target tci choice ti ta tj tb,List.prefix_refl _⟩ ∧
    (m.wk (Thin.drop (t := .val .bool) .refl)).Related R (ConditionalAssignments.sourceAfter source ci choice i a j b).1
      (reached target tci choice ti ta tj tb).env ∧
    TEnv.get .here (reached target tci choice ti ta tj tb).env = true ∧
    (reached target tci choice ti ta tj tb).glob = target.glob ∧
    Evm.StmtOut C (L + Evm.Prog.pushes (code (C := C) tci tca ti ta tj tb)) base outFrame
      (Evm.Prog.shrinks (code (C := C) tci tca ti ta tj tb))
      (Evm.Prog.pays (code (C := C) tci tca ti ta tj tb))
      (Solidity.Prog.asserts (code (C := C) tci tca ti ta tj tb))
      ((code (C := C) tci tca ti ta tj tb).run target)
      (Evm.run (emit (C := C) base tci tca ti ta tj tb) machine) machine := by
  rcases ConditionalReturn.correct G F fuel nps ph (M := M) (k := k)
    source target m R aligned boolReflect ci ca i a j b tci tca ti ta tj tb
    mapCI mapCA mapI mapA mapJ mapB with ⟨src,typed,related,flag,globals⟩
  exact ⟨src,typed,related,flag,globals,Evm.prog_sim _ entry checked capacity⟩

end Solidity.Backend.StructuredFlow.ConditionalReturnCompiler
