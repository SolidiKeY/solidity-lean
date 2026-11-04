import Solidity.Lowering.G19.ReturnTail
import Solidity.Evm.Correct

/-! Compile the existing mapped return selector and its conditionally suppressed
caller assignment. The captured flag classifies Source return; no EVM RETURN. -/
namespace Solidity.Backend.StructuredFlow.ReturnTailCompiler
open Solidity.Lowering.V07 Solidity.Lowering.G19

def emit {C : Contract} {Γ : Ctx} {p : PrimTy} (base : Nat)
    (ci ca : Idx Γ (.val .bool)) (dest donor : Idx Γ (.val p)) : List Evm.Instr :=
  Evm.compileProg base (ReturnTail.code (C := C) ci ca dest donor)

/-- Extract only the successful native witness from the existing compiler
contract for an actual successful typed run with no panic/payment arms. -/
theorem normal_of_ok {C : Contract} {L base : Nat} {Γ : Ctx} {frame : Evm.Frag Γ}
    {shrinks : Bool} {H : HTy} {o : Solidity.Out C H Γ} {out : Evm.Out} {initial : Evm.Machine}
    (h : Evm.StmtOut C L base frame shrinks false false (.ok o) out initial) :
    ∃ final, out = .ok final 0 ∧ final.stack = initial.stack ∧ Evm.Sim C L base frame o.st final := by
  cases h with
  | inl h =>
    rcases h with ⟨other,final,same,run,stack,_,repr⟩
    cases same
    exact ⟨final,run,stack,repr⟩
  | inr h => cases h.1
  | panic impossible _ => cases impossible
  | refused impossible _ => cases impossible
  | diverge h => cases h.1

theorem correct {E : Source.Env} {Γs : Source.RCtx} {σ : Source.STy}
    {C : Contract} {Γ : Ctx} {p : PrimTy}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {M : Bool} {k : Source.SCtx} (s : Source.EMState E Γs) (t : State C Γ) (m : ContextMap Γs Γ)
    (R : (α : Source.STy) → (u : LTy) → Source.Val E.layout α → u.TDenote C t.H → Prop)
    (aligned : m.Related R s.1 t.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool), R .bool (.val .bool) v b → v = .bool b)
    (ci ca : Source.Idx Γs .bool) (dest donor : Source.Idx Γs σ)
    (tci tca : Idx Γ (.val .bool)) (tdest tdonor : Idx Γ (.val p))
    (mapCI : m.slot ci = ⟨.val .bool,tci⟩) (mapCA : m.slot ca = ⟨.val .bool,tca⟩)
    (mapDest : m.slot dest = ⟨.val p,tdest⟩) (mapDonor : m.slot donor = ⟨.val p,tdonor⟩)
    {L base : Nat} {F₀ : Evm.Frag Γ} {F₁ : Evm.Frag (.val .bool :: Γ)} {machine : Evm.Machine}
    (entry : Evm.Sim C L base F₀ t machine)
    (checked : Evm.inFragP F₀ (ReturnTail.code (C := C) tci tca tdest tdonor) = some F₁)
    (capacity : L + Evm.Prog.pushes (ReturnTail.code (C := C) tci tca tdest tdonor) ≤ Evm.Lmax) :
    let choice : Bool := TEnv.get tca t.env
    (Source.execS G F (fuel+6) nps ph (R := []) (M := M)
      (ReturnTail.statement (k := k) ci ca dest donor) s.1).run (.nil,s.2) =
      (.ok (if choice then Source.Out.ret (ReturnTail.sourceAfter s ci choice dest donor).1
        else Source.Out.normal (ReturnTail.sourceAfter s ci choice dest donor).1),(.nil,s.2)) ∧
    (ReturnTail.code (C := C) tci tca tdest tdonor).run t =
      .ok ⟨ReturnTail.reached t tci choice tdest tdonor,List.prefix_refl _⟩ ∧
    (m.wk (Thin.drop (t := .val .bool) .refl)).Related R
      (ReturnTail.sourceAfter s ci choice dest donor).1 (ReturnTail.reached t tci choice tdest tdonor).env ∧
    TEnv.get .here (ReturnTail.reached t tci choice tdest tdonor).env = choice ∧
    (ReturnTail.reached t tci choice tdest tdonor).glob = t.glob ∧
    Evm.StmtOut C (L + Evm.Prog.pushes (ReturnTail.code (C := C) tci tca tdest tdonor)) base F₁
      (Evm.Prog.shrinks (ReturnTail.code (C := C) tci tca tdest tdonor))
      (Evm.Prog.pays (ReturnTail.code (C := C) tci tca tdest tdonor))
      (Solidity.Prog.asserts (ReturnTail.code (C := C) tci tca tdest tdonor))
      ((ReturnTail.code (C := C) tci tca tdest tdonor).run t)
      (Evm.run (emit (C := C) base tci tca tdest tdonor) machine) machine := by
  rcases ReturnTail.correct G F fuel nps ph s t m R aligned boolReflect
    ci ca dest donor tci tca tdest tdonor mapCI mapCA mapDest mapDonor with
    ⟨src,typed,related,flag,globals⟩
  exact ⟨src,typed,related,flag,globals,Evm.prog_sim _ entry checked capacity⟩

end Solidity.Backend.StructuredFlow.ReturnTailCompiler
