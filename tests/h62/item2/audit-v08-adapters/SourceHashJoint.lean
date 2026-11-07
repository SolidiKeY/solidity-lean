import Solidity.Lowering.V08.SourceCustomErrorControls

/-! Regression: exact Keccak output must not erase the literal allocation.
The existing populated Source fixture supplies the fixed pin and actual run
for arbitrary input bytes, including empty bytes. No Source admission, target
compiler selection, hash noncollision or canonical full-pass claim is made. -/
namespace H62.AuditV08Adapters.SourceHashJoint
open Solidity Source
open Solidity.Lowering.V08
open SourceCustomErrorControls

def Joint (pipeline : Roadmap.Pipeline) (static : Bool) (fuel : Nat)
    (bytes : Roadmap.Bytes) : Prop :=
  (global pipeline).fixed.Keccak ∧
  (Source.evalE (global pipeline) {frame with static:=static} (fuel+5)
    (SourceKeccak.literal bytes)).run (locals,populated) =
    (.ok (.val (Source.mkBytes (n:=32) (h:=by decide +kernel)
      (Semantics.wordBytes (keccakBytes (bytes.map (fun b => (b.toNat : Int)))).1.toNat))),
      (locals,SourceKeccak.afterLiteral populated bytes)) ∧
  (SourceKeccak.afterLiteral populated bytes).heap.get populated.heap.next =
    some ⟨.bytes .memory,.bytes bytes⟩

theorem joint (pipeline : Roadmap.Pipeline) (static : Bool) (fuel : Nat)
    (bytes : Roadmap.Bytes) : Joint pipeline static fuel bytes :=
  ⟨Roadmap.Controls.toyFixed_keccak,
    SourceKeccak.eval_transport (global pipeline) Roadmap.Controls.toyFixed_keccak
      {frame with static:=static} fuel bytes locals populated,
    SourceKeccak.allocated populated bytes⟩

/-- The full successful result cannot silently reuse the input heap. -/
theorem unchanged_heap_refused (pipeline : Roadmap.Pipeline) (static : Bool) (fuel : Nat)
    (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) {frame with static:=static} (fuel+5)
      (SourceKeccak.literal bytes)).run (locals,populated) ≠
      (.ok (.val (Source.mkBytes (n:=32) (h:=by decide +kernel)
        (Semantics.wordBytes (keccakBytes (bytes.map (fun b => (b.toNat : Int)))).1.toNat))),
        (locals,populated)) := by
  rw [(joint pipeline static fuel bytes).2.1]
  intro same
  have heapSame := congrArg (fun result => result.2.2.heap.next) same
  change 2 = 1 at heapSame
  cases heapSame

/-- All nonheap machine fields of this same reached result retain their inputs. -/
theorem nonheap_retained (bytes : Roadmap.Bytes) :
    (SourceKeccak.afterLiteral populated bytes).ex = populated.ex ∧
    (SourceKeccak.afterLiteral populated bytes).events = populated.events ∧
    (SourceKeccak.afterLiteral populated bytes).logs = populated.logs ∧
    (SourceKeccak.afterLiteral populated bytes).fnLocals = populated.fnLocals :=
  SourceKeccak.retained populated bytes

#print axioms joint
#print axioms unchanged_heap_refused
#print axioms nonheap_retained
end H62.AuditV08Adapters.SourceHashJoint
