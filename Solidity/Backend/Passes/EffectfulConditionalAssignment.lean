import Solidity.Backend.Passes.MappedTail
import Solidity.Backend.Passes.CapturedValueStability
import Solidity.Lowering.V07.ConditionalAssignments

/-! The published effectful conditional expression, its actual compiled prefix,
and captured-result readback. The initial independent context relation and full
physical Input remain premises. No admission/world/bytecode theorem is inferred. -/
namespace Solidity.Backend.Passes.EffectfulConditionalAssignment
open Evm Evm.Memory Evm.Compiler Solidity.Lowering.V07
open ConditionalAssignments

def reached {C : Contract} {Γ : Ctx} {p : PrimTy} (target : State C Γ)
    (ci ca : Idx Γ (.val .bool)) (i a j b : Idx Γ (.val p)) :
    State C (.val p :: .val .bool :: Γ) :=
  let choice : Bool := TEnv.get ca target.env
  ((targetAfter target ci choice i a j b).push (t := .val .bool) choice).push
    (TEnv.get (if choice then a else b) (TEnv.set ci choice target.env))

theorem payment_free {C : Contract} {Γ : Ctx} {p : PrimTy}
    (ci ca : Idx Γ (.val .bool)) (i a j b : Idx Γ (.val p)) :
    Evm.Prog.pays (code (C := C) ci ca i a j b) = false := by rfl

theorem execution {E : Source.Env} {srcΓ : Source.RCtx} {τ : Source.STy}
    {C : Contract} {Γ : Ctx} {p : PrimTy}
    (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (m : ContextMap srcΓ Γ)
    (R : (σ : Source.STy) → (u : LTy) → Source.Val E.layout σ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (c : Bool), R .bool (.val .bool) v c → v = .bool c)
    (ci ca : Source.Idx srcΓ .bool) (i a j b : Source.Idx srcΓ τ)
    (tci tca : Idx Γ (.val .bool)) (ti ta tj tb : Idx Γ (.val p))
    (mapCI : m.slot ci = ⟨.val .bool,tci⟩) (mapCA : m.slot ca = ⟨.val .bool,tca⟩)
    (mapI : m.slot i = ⟨.val p,ti⟩) (mapA : m.slot a = ⟨.val p,ta⟩)
    (mapJ : m.slot j = ⟨.val p,tj⟩) (mapB : m.slot b = ⟨.val p,tb⟩)
    {offset L frame : Nat} {F : Frag Γ}
    (compiled : CompiledProg offset F (code tci tca ti ta tj tb))
    (readback : CompiledVal offset compiled.frag
      (.simple (.local .here) : Val C (.val p :: .val .bool :: Γ) p))
    {base : Nat → Fin W} {machine : Machine}
    (input : (Compilation.memory compiled).Input L frame base target machine) :
    let choice : Bool := TEnv.get tca target.env
    let sv := (source.1.set ci (.bool choice)).get (if choice then a else b)
    let tv := TEnv.get (if choice then ta else tb) (TEnv.set tci choice target.env)
    (Source.evalE G SF (fuel+3) (.cond (.assign (.local ci) (.local ca))
      (.assign (.local i) (.local a)) (.assign (.local j) (.local b)))).run source =
      (.ok (.val sv),sourceAfter source ci choice i a j b) ∧
    R τ (.val p) sv tv ∧
    m.Related R (sourceAfter source ci choice i a j b).1
      (targetAfter target tci choice ti ta tj tb).env ∧
    ∃ (canonical : Machine) (selected : Nat → Fin W) (word : Word),
      ReprV p tv word ∧ canonical.stack = [] ∧ ∀ tail,
        (Compilation.memory compiled).Input L frame base target {machine with stack := tail} ∧
        run compiled.code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
        MappedOutput (.memory compiled) L frame base target {machine with stack := tail}
          (reached target tci tca ti ta tj tb) {canonical with stack := tail} selected ∧
        run readback.code {canonical with stack := tail} = .ok ({canonical with stack := tail}.push word) 0 ∧
        run (compiled.code ++ readback.code) {machine with stack := tail} =
          .ok ({canonical with stack := tail}.push word) 0 := by
  have sourceFacts := transport G SF fuel source target m R aligned boolReflect
    ci ca i a j b tci tca ti ta tj tb mapCI mapCA mapI mapA mapJ mapB
  have sourceRun := prefix_run target tci tca (TEnv.get tca target.env) ti ta tj tb rfl
  obtain ⟨canonical,selected,_,empty,runs⟩ := compilation_success_shared_mapped
    (.memory compiled) input (payment_free tci tca ti ta tj tb) sourceRun
  have represented := (runs []).2.1
  obtain ⟨word,repr,values⟩ := CapturedValueStability.value_shared
    (.simple (.local .here)) readback represented
    (TEnv.get (if (TEnv.get tca target.env : Bool) = true then ta else tb) (TEnv.set tci (TEnv.get tca target.env) target.env)) rfl
  refine ⟨sourceFacts.1,sourceFacts.2.2.1,sourceFacts.2.2.2,canonical,selected,word,repr,empty,?_⟩
  intro tail
  have mapped := (runs tail).2
  rw [compiled.cert.pushes_zero,Nat.add_zero] at mapped
  exact ⟨compilation_input_stack (.memory compiled) input tail,(runs tail).1,mapped,values tail,
    (run_append_ok (c₂ := readback.code) (runs tail).1).trans (values tail)⟩

end Solidity.Backend.Passes.EffectfulConditionalAssignment
