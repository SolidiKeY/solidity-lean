import Solidity.Yul.World.LogBuiltin
/-! Success inversion for the actual intrinsic LOG leaf. Full ordered
observations are retained; these laws do not certify operand evaluation,
Source emit encoding, G01, G51 embedding or compiler/world/resource adequacy. -/
namespace Solidity.Yul.World
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes)
variable {D : Layout} {L T : Address → Solidity.Source.SPath → STy} {Memory : Type}
theorem logAdapter_success_iff (port : BytePort Memory) (entry : ObservedEffects D L T)
    (memory : Memory) (static : Bool) (emitter : Address) (count : Fin 5)
    (topics : Vector Word count.val) (offset size : Word) (out : ObservedEffects D L T) :
    logAdapter port entry memory static emitter count topics offset size = some out ↔
      static = false ∧ ∃ bytes, port.load memory offset size = some bytes ∧
        out = emitObserved entry ⟨emitter,count,topics,bytes⟩ := by
  constructor
  · intro completed
    cases static with
    | true =>
      simp only [logAdapter, ↓reduceIte] at completed
      cases completed
    | false =>
      cases loaded : port.load memory offset size with
      | none =>
        simp only [logAdapter, Bool.false_eq_true, ↓reduceIte, loaded,
          bind, Option.bind_none] at completed
        cases completed
      | some bytes =>
        simp only [logAdapter, Bool.false_eq_true, ↓reduceIte, loaded,
          bind, Option.bind_some, pure, Option.some.injEq] at completed
        exact ⟨rfl,bytes,rfl,completed.symm⟩
  · rintro ⟨rfl,bytes,loaded,rfl⟩
    exact logAdapter_exact port entry memory emitter count topics offset size bytes loaded
theorem logBuiltin_success {a : Nat} (builtin : Solidity.Yul.Builtin a 0)
    (port : BytePort Memory) (entry : ObservedEffects D L T) (memory : Memory)
    (frame : CallFrame) (args : Fin a → Word) (out : ObservedEffects D L T)
    (completed : logBuiltin builtin port entry memory frame args = some out) :
    frame.static = false ∧ ∃ log, log.emitter = frame.this ∧ out = emitObserved entry log := by
  cases builtin <;> simp only [logBuiltin] at completed <;> first
  | (solve | cases completed)
  | (obtain ⟨normal,bytes,loaded,equal⟩ :=
       (logAdapter_success_iff port entry memory frame.static frame.this _ _ _ _ out).mp completed
     exact ⟨normal,_,rfl,equal⟩)
theorem logBuiltin_not_identity {a : Nat} (builtin : Solidity.Yul.Builtin a 0)
    (port : BytePort Memory) (entry : ObservedEffects D L T) (memory : Memory)
    (frame : CallFrame) (args : Fin a → Word) :
    logBuiltin builtin port entry memory frame args ≠ some entry := by
  intro completed
  obtain ⟨_,log,_,equal⟩ := logBuiltin_success builtin port entry memory frame args entry completed
  have length := congrArg (fun s : ObservedEffects D L T => s.trace.length) equal
  simp only [emitObserved, List.length_append, List.length_singleton] at length
  omega
end Solidity.Yul.World
