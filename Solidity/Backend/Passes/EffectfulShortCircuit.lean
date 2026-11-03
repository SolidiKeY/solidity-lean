import Solidity.Backend.Passes.MappedTail
import Solidity.Lowering.V07.ShortCircuit

/-! The published effectful Source Boolean assignment fragment, connected to
actual accepted compiler output. No SourceSpec, admission, ABI or world theorem
is inferred. The physical Input is retained, not replaced by source alignment. -/
namespace Solidity.Backend.Passes.EffectfulShortCircuit
open Evm Evm.Compiler Solidity.Lowering.V07

/-- The captured local remains in the compiled context. Source alignment below
continues to describe the caller context, before that fresh result binder. -/
def reached {C : Contract} {Γ : Ctx} (target : State C Γ) (conj : Bool)
    (i a j b : Idx Γ (.val .bool)) : State C (.val .bool :: Γ) :=
  let x := TEnv.get a target.env
  let y := TEnv.get b (TEnv.set i x target.env)
  if needsRight conj x then ((target.setLocal i x).setLocal j y).push (t := .val .bool) y
  else (target.setLocal i x).push (t := .val .bool) x

theorem payment_free {C : Contract} {Γ : Ctx} (conj : Bool)
    (i a j b : Idx Γ (.val .bool)) :
    Evm.Prog.pays (shortAssignPrefix (C := C) conj i a j b) = false := by
  first | rfl | decide | omega | (cases conj <;> rfl)

/-- Both independent evaluations, reached Source alignment, and actual emitted
execution share the same typed input. Machine and selected map precede all saved
tails; no post-execution representation or preservation equality is assumed. -/
theorem execution {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (SF : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (c : Bool), R .bool (.val .bool) v c → v = .bool c)
    (conj : Bool) (i a j b : Source.Idx srcΓ .bool) (ti ta tj tb : Idx Γ (.val .bool))
    (mapI : m.slot i = ⟨.val .bool,ti⟩) (mapA : m.slot a = ⟨.val .bool,ta⟩)
    (mapJ : m.slot j = ⟨.val .bool,tj⟩) (mapB : m.slot b = ⟨.val .bool,tb⟩)
    {offset L frame : Nat} {F : Frag Γ}
    (compiled : Compilation offset F (shortAssignPrefix conj ti ta tj tb))
    {base : Nat → Fin W} {machine : Machine}
    (input : compiled.Input L frame base target machine) :
    let x := TEnv.get ta target.env
    let y := TEnv.get tb (TEnv.set ti x target.env)
    let srcPost := if needsRight conj x then
      ((source.1.set i (.bool x)).set j (.bool y),source.2) else (source.1.set i (.bool x),source.2)
    (Source.evalE G SF (fuel+3) (.binary (if conj then .and else .or)
      (.assign (.local i) (.local a)) (.assign (.local j) (.local b)))).run source =
      (.ok (.val (.bool (if needsRight conj x then y else x))),srcPost) ∧
    m.Related R srcPost.1
      (if needsRight conj x then TEnv.set tj y (TEnv.set ti x target.env)
        else TEnv.set ti x target.env) ∧
    (shortAssignPrefix conj ti ta tj tb).run target =
      .ok ⟨reached target conj ti ta tj tb,by dsimp only [reached]; split <;> exact List.prefix_refl _⟩ ∧
    ∃ (canonical : Machine) (outBase : Nat → Fin W), canonical.stack = [] ∧ ∀ tail,
      compiled.Input L frame base target {machine with stack := tail} ∧
      run compiled.code {machine with stack := tail} = .ok {canonical with stack := tail} 0 ∧
      MappedOutput compiled (L + Evm.Prog.pushes (shortAssignPrefix (C := C) conj ti ta tj tb))
        frame base target {machine with stack := tail}
        (reached target conj ti ta tj tb) {canonical with stack := tail} outBase := by
  first
  | (solve | simp only)
  | (solve | decide)
  | (solve | omega)
  | (solve | rfl)
  |
    have transported := short_assignment_transport G SF fuel source target m R aligned boolReflect
      conj i a j b ti ta tj tb mapI mapA mapJ mapB
    have hs := short_assign_prefix_run target conj ti ta tj tb (TEnv.get ta target.env) rfl
    obtain ⟨canonical,outBase,_,empty,runs⟩ := compilation_success_shared_mapped
      compiled input (payment_free conj ti ta tj tb) hs
    exact ⟨transported.1,transported.2.2.1,hs,canonical,outBase,empty,
      fun tail => ⟨compilation_input_stack compiled input tail,runs tail⟩⟩


end Solidity.Backend.Passes.EffectfulShortCircuit
