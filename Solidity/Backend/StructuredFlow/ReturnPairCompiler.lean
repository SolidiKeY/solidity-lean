import Solidity.Lowering.G19.ReturnPair
import Solidity.Evm.Correct

/-! Compile the existing mapped return selector and its conditionally suppressed
caller assignments. The captured flag classifies Source return; no EVM RETURN. -/
namespace Solidity.Backend.StructuredFlow.ReturnPairCompiler
open Solidity.Lowering.V07 Solidity.Lowering.G19

def emit {C : Contract} {Γ : Ctx} {p q : PrimTy} (base : Nat)
    (ci ca : Idx Γ (.val .bool)) (i a : Idx Γ (.val p)) (dest donor : Idx Γ (.val q)) : List Evm.Instr :=
  Evm.compileProg base (ReturnPair.code (C := C) ci ca i a dest donor)

theorem correct {E : Source.Env} {Γs : Source.RCtx} {τ σ : Source.STy}
    {C : Contract} {Γ : Ctx} {p q : PrimTy}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {M : Bool} {k : Source.SCtx} (s : Source.EMState E Γs) (t : State C Γ) (m : ContextMap Γs Γ)
    (R : (α : Source.STy) → (u : LTy) → Source.Val E.layout α → u.TDenote C t.H → Prop)
    (aligned : m.Related R s.1 t.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool), R .bool (.val .bool) v b → v = .bool b)
    (ci ca : Source.Idx Γs .bool) (i a : Source.Idx Γs τ) (dest donor : Source.Idx Γs σ)
    (tci tca : Idx Γ (.val .bool)) (ti ta : Idx Γ (.val p)) (tdest tdonor : Idx Γ (.val q))
    (mapCI : m.slot ci = ⟨.val .bool,tci⟩) (mapCA : m.slot ca = ⟨.val .bool,tca⟩)
    (mapI : m.slot i = ⟨.val p,ti⟩) (mapA : m.slot a = ⟨.val p,ta⟩)
    (mapDest : m.slot dest = ⟨.val q,tdest⟩) (mapDonor : m.slot donor = ⟨.val q,tdonor⟩)
    {L base : Nat} {F₀ : Evm.Frag Γ} {F₁ : Evm.Frag (.val .bool :: Γ)} {machine : Evm.Machine}
    (entry : Evm.Sim C L base F₀ t machine)
    (checked : Evm.inFragP F₀ (ReturnPair.code (C := C) tci tca ti ta tdest tdonor) = some F₁)
    (capacity : L + Evm.Prog.pushes (ReturnPair.code (C := C) tci tca ti ta tdest tdonor) ≤ Evm.Lmax) :
    let choice : Bool := TEnv.get tca t.env
    (Source.execS G F (fuel+8) nps ph (R := []) (M := M)
      (ReturnPair.statement (k := k) ci ca i a dest donor) s.1).run (.nil,s.2) =
      (.ok (if choice then Source.Out.ret (ReturnPair.sourceAfter s ci choice i a dest donor).1
        else Source.Out.normal (ReturnPair.sourceAfter s ci choice i a dest donor).1),(.nil,s.2)) ∧
    (ReturnPair.code (C := C) tci tca ti ta tdest tdonor).run t =
      .ok ⟨ReturnPair.reached t tci choice ti ta tdest tdonor,List.prefix_refl _⟩ ∧
    (m.wk (Thin.drop (t := .val .bool) .refl)).Related R
      (ReturnPair.sourceAfter s ci choice i a dest donor).1 (ReturnPair.reached t tci choice ti ta tdest tdonor).env ∧
    TEnv.get .here (ReturnPair.reached t tci choice ti ta tdest tdonor).env = choice ∧
    (ReturnPair.reached t tci choice ti ta tdest tdonor).glob = t.glob ∧
    Evm.StmtOut C (L + Evm.Prog.pushes (ReturnPair.code (C := C) tci tca ti ta tdest tdonor)) base F₁
      (Evm.Prog.shrinks (ReturnPair.code (C := C) tci tca ti ta tdest tdonor))
      (Evm.Prog.pays (ReturnPair.code (C := C) tci tca ti ta tdest tdonor))
      (Solidity.Prog.asserts (ReturnPair.code (C := C) tci tca ti ta tdest tdonor))
      ((ReturnPair.code (C := C) tci tca ti ta tdest tdonor).run t)
      (Evm.run (emit (C := C) base tci tca ti ta tdest tdonor) machine) machine := by
  rcases ReturnPair.correct G F fuel nps ph s t m R aligned boolReflect
    ci ca i a dest donor tci tca ti ta tdest tdonor mapCI mapCA mapI mapA mapDest mapDonor with
    ⟨src,typed,related,flag,globals⟩
  exact ⟨src,typed,related,flag,globals,Evm.prog_sim _ entry checked capacity⟩

end Solidity.Backend.StructuredFlow.ReturnPairCompiler
