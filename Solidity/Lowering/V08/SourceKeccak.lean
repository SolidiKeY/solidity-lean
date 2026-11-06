import Solidity.Lowering.V08.SourceEnvironment
import Solidity.Lowering.V08.CryptoObservations

/-! Actual independent source literal Keccak execution. Literal-to-memory
conversion allocates: the exact resulting heap is retained, never equated with
the input heap. No new hash premise, emitter, decoder or evaluator is introduced.
General argument effects, canonical representation and SourceSpec remain open. -/
namespace Solidity.Lowering.V08.SourceKeccak
open Solidity
open Source

def literal {E : Source.Env} {Γ : RCtx} (bytes : Roadmap.Bytes) : RExpr E Γ STy.bytes32 :=
  .builtin .keccak256 (.cons (.str bytes) .nil) rfl

/-- The actual published literal-conversion allocation, in the existing state. -/
def afterLiteral {E : Source.Env} (state : Source.St E) (bytes : Roadmap.Bytes) : Source.St E :=
  { state with heap := (state.heap.alloc ⟨.bytes .memory, .bytes bytes⟩).1 }

/-- The literal hash reads its freshly allocated byte object. -/
theorem eval_literal {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (horizon : Nat) (bytes : Roadmap.Bytes) (locals : Source.Locals E.layout Γ)
    (state : Source.St E) :
    (Source.evalE global frame (horizon + 5) (literal bytes)).run (locals, state) =
      (.ok (.val (Source.mkBytes (n := 32) (h := by decide +kernel)
        (Source.wordBytes (global.fixed.hash bytes)))), (locals, afterLiteral state bytes)) := by
  simp only [literal, Source.evalE, Source.evalBuiltin, Source.evalArgs, Source.convRV, Source.bytesOfRV, Source.ret32, Source.allocRef, Source.alloc, Source.EM.st, Source.EM.setSt, Source.heapBytes, Source.heapObj, reduceCtorEq, decide_false, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte, STy.bytes32]
  simp only [pure_bind, STy.loc?, reduceCtorEq, ↓reduceDIte, afterLiteral]
  simp only [bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.bindCont,
    ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure, StateT.get,
    StateT.modifyGet, modify, modifyGet, get, getThe,
    MonadStateOf.get, MonadStateOf.modifyGet,
    liftM, monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map, Source.Heap.alloc_get]

/-- The bytes32 constructor does not pad or truncate an existing word. -/
theorem mk_wordBytes {D : Source.Layout} (word : Roadmap.Word) :
    (Source.mkBytes (n := 32) (h := by decide +kernel) (Source.wordBytes word) :
      Source.Val D STy.bytes32) =
      .fixedBytes (Source.wordBytes word) (Source.wordBytes_length word) := by
  simp only [Source.mkBytes, Source.fitBytes,
    List.take_left' (Source.wordBytes_length word)]

/-- Actual expression execution, with the existing intrinsic hash observation.
The published fixed.Keccak contract is explicit; no source execution is assumed. -/
theorem eval_transport {E : Source.Env} {Γ : RCtx} (global : Glob E)
    (pin : global.fixed.Keccak) (frame : Fr) (horizon : Nat)
    (bytes : Roadmap.Bytes) (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.evalE global frame (horizon + 5) (literal bytes)).run (locals, state) =
      (.ok (.val (Source.mkBytes (n := 32) (h := by decide +kernel)
        (Semantics.wordBytes (keccakBytes (bytes.map (fun b => (b.toNat : Int)))).1.toNat))),
       (locals, afterLiteral state bytes)) := by
  rw [eval_literal, CryptoObservations.fixed_keccak_bytes global.fixed pin bytes]

/-- The exact successful bytes also decode to the fixed bounded word. -/
theorem word_observation (word : Roadmap.Word) :
    Source.bytesNat (Source.wordBytes word) = word.val :=
  Source.wordBytes_value word

theorem zero_horizon {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (bytes : Roadmap.Bytes) (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.evalE global frame 0 (literal bytes)).run (locals, state) =
      (.error .timeout, (locals, state)) := rfl

/-- Complete nonheap fields, including journal, world, transient cells, logs,
events and function locals, remain exactly those of the input machine. -/
theorem retained {E : Source.Env} (state : Source.St E) (bytes : Roadmap.Bytes) :
    (afterLiteral state bytes).ex = state.ex ∧
    (afterLiteral state bytes).events = state.events ∧
    (afterLiteral state bytes).logs = state.logs ∧
    (afterLiteral state bytes).fnLocals = state.fnLocals := ⟨rfl, rfl, rfl, rfl⟩

theorem allocated {E : Source.Env} (state : Source.St E) (bytes : Roadmap.Bytes) :
    (afterLiteral state bytes).heap.get state.heap.next =
      some ⟨.bytes .memory, .bytes bytes⟩ :=
  Source.Heap.alloc_get state.heap _

#print axioms mk_wordBytes
#print axioms eval_transport
#print axioms word_observation
#print axioms zero_horizon
#print axioms retained
#print axioms allocated
#print axioms eval_literal
end Solidity.Lowering.V08.SourceKeccak
