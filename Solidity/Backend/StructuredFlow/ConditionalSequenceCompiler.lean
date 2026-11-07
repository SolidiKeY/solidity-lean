import Solidity.Lowering.G19.ConditionalSequence
import Solidity.Backend.StructuredFlow.ConditionalSourceCompiler

/-! Compiler connection for the existing V07-related conditional followed by
an assignment in its reached caller context. No new lowering relation. -/
namespace Solidity.Backend.StructuredFlow.ConditionalSequenceCompiler
open Solidity.Lowering.V07 Solidity.Lowering.G19

def emit {C : Contract} {Γ : Ctx} {p q : PrimTy} (base : Nat)
    (ci ca : Idx Γ (.val .bool)) (i a j b : Idx Γ (.val p))
    (dest donor : Idx Γ (.val q)) : List Evm.Instr :=
  Evm.compileProg base (ConditionalSequence.code (C := C) ci ca i a j b dest donor)

theorem code_exact {C : Contract} {Γ : Ctx} {p q : PrimTy} (base : Nat)
    (ci ca : Idx Γ (.val .bool)) (i a j b : Idx Γ (.val p))
    (dest donor : Idx Γ (.val q)) :
    emit (C := C) base ci ca i a j b dest donor =
      Evm.compileProg base (ConditionalSequence.code (C := C) ci ca i a j b dest donor) := by rfl

theorem emit_split : ∀ {C : Solidity.Contract} {Γ : Solidity.Ctx} {p q : Solidity.PrimTy}
    (base : Nat) (ci ca : Solidity.Idx Γ (.val .bool)) (i a j b : Solidity.Idx Γ (.val p))
    (dest donor : Solidity.Idx Γ (.val q)),
    Solidity.Backend.StructuredFlow.ConditionalSequenceCompiler.emit (C := C) base ci ca i a j b dest donor =
      Solidity.Backend.StructuredFlow.ConditionalSourceCompiler.emit (C := C) base ci ca i a j b ++
        Solidity.Evm.compileProg base (show Solidity.Prog C Γ Γ from
          .cons (.assignLocal dest (.simple (.local donor))) .nil) := by
  intros
  rfl

theorem correct {E : Source.Env} {Γs : Source.RCtx} {τ σ : Source.STy}
    {C : Contract} {Γ : Ctx} {p q : PrimTy}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {returns : List Source.STy} {M : Bool} {k : Source.SCtx}
    (s : Source.EMState E Γs) (t : State C Γ) (m : ContextMap Γs Γ)
    (R : (α : Source.STy) → (u : LTy) → Source.Val E.layout α → u.TDenote C t.H → Prop)
    (aligned : m.Related R s.1 t.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (b : Bool), R .bool (.val .bool) v b → v = .bool b)
    (ci ca : Source.Idx Γs .bool) (i a j b : Source.Idx Γs τ) (dest donor : Source.Idx Γs σ)
    (tci tca : Idx Γ (.val .bool)) (ti ta tj tb : Idx Γ (.val p)) (tdest tdonor : Idx Γ (.val q))
    (mapCI : m.slot ci = ⟨.val .bool,tci⟩) (mapCA : m.slot ca = ⟨.val .bool,tca⟩)
    (mapI : m.slot i = ⟨.val p,ti⟩) (mapA : m.slot a = ⟨.val p,ta⟩)
    (mapJ : m.slot j = ⟨.val p,tj⟩) (mapB : m.slot b = ⟨.val p,tb⟩)
    (mapDest : m.slot dest = ⟨.val q,tdest⟩) (mapDonor : m.slot donor = ⟨.val q,tdonor⟩) {L base : Nat} {F₀ F₁ : Evm.Frag Γ} {machine : Evm.Machine}
    (entry : Evm.Sim C L base F₀ t machine)
    (checked : Evm.inFragP F₀ (ConditionalSequence.code (C := C) tci tca ti ta tj tb tdest tdonor) = some F₁)
    (capacity : L + Evm.Prog.pushes (ConditionalSequence.code (C := C) tci tca ti ta tj tb tdest tdonor) ≤ Evm.Lmax) :
    let choice : Bool := TEnv.get tca t.env
    (Source.execS G F (fuel+6) nps ph (R := returns) (M := M)
      (ConditionalSequence.statement (k := k) ci ca i a j b dest donor) s.1).run (.nil,s.2) =
      (.ok (Source.Out.normal (ConditionalSequence.sourceAfter s ci choice i a j b dest donor).1),(.nil,s.2)) ∧
    (ConditionalSequence.code (C := C) tci tca ti ta tj tb tdest tdonor).run t =
      .ok ⟨ConditionalSequence.targetAfter t tci choice ti ta tj tb tdest tdonor,List.prefix_refl _⟩ ∧
    m.Related R (ConditionalSequence.sourceAfter s ci choice i a j b dest donor).1
      (ConditionalSequence.targetAfter t tci choice ti ta tj tb tdest tdonor).env ∧
    (ConditionalSequence.targetAfter t tci choice ti ta tj tb tdest tdonor).glob = t.glob ∧
    Evm.StmtOut C (L + Evm.Prog.pushes (ConditionalSequence.code (C := C) tci tca ti ta tj tb tdest tdonor)) base F₁
      (Evm.Prog.shrinks (ConditionalSequence.code (C := C) tci tca ti ta tj tb tdest tdonor))
      (Evm.Prog.pays (ConditionalSequence.code (C := C) tci tca ti ta tj tb tdest tdonor))
      (Solidity.Prog.asserts (ConditionalSequence.code (C := C) tci tca ti ta tj tb tdest tdonor))
      ((ConditionalSequence.code (C := C) tci tca ti ta tj tb tdest tdonor).run t)
      (Evm.run (emit (C := C) base tci tca ti ta tj tb tdest tdonor) machine) machine := by
  rcases ConditionalSequence.correct G F fuel nps ph s t m R aligned boolReflect
    ci ca i a j b dest donor tci tca ti ta tj tb tdest tdonor
    mapCI mapCA mapI mapA mapJ mapB mapDest mapDonor with ⟨src,tgt,related,globals⟩
  exact ⟨src,tgt,related,globals,Evm.prog_sim _ entry checked capacity⟩

end Solidity.Backend.StructuredFlow.ConditionalSequenceCompiler
