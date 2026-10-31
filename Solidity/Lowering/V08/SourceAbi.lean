import Solidity.Lowering.V08.SourceKeccak
import Solidity.Lowering.V08.AbiObservations

/-! Actual published ABI expression execution. Individual argument/encoding
steps are premises of the composition law, not presumed source/target adequacy.
No encoder, decoder, state layer or length admission bound is introduced. -/
namespace Solidity.Lowering.V08.SourceAbi
open Solidity Source

theorem execute {E : Source.Env} {Γ : RCtx} {types : List STy}
    (global : Glob E) (frame : Fr) (horizon : Nat) (packed : Bool)
    (args : RArgs E Γ types) (locals next last : Source.Locals E.layout Γ)
    (state middle final : Source.St E) (values : Source.RVals E.layout types) (data : Roadmap.Bytes)
    (arguments : (Source.evalArgs global frame horizon args).run (locals,state) =
      (.ok values,(next,middle)))
    (encoding : (Source.encodeVals frame horizon packed values : Source.EM E Γ _).run
      (next,middle) = (.ok data,(last,final))) :
    (Source.evalE global frame (horizon+1)
      (.abiEncode (if packed then .encodePacked else .encode) args)).run (locals,state) =
      (.ok (.val (.memRef rfl final.heap.next)),(last,SourceKeccak.afterLiteral final data)) := by
  simp only [ExceptT.run] at arguments encoding
  cases packed <;>
    simp only [Source.evalE, Bool.false_eq_true, ↓reduceIte, arguments, encoding,
      Source.allocRef, Source.alloc, Source.EM.st, Source.EM.setSt, SourceKeccak.afterLiteral,
      STy.loc?, ↓reduceDIte, bind, pure, ExceptT.bind, ExceptT.pure,
      ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure, StateT.get,
      StateT.modifyGet, modify, modifyGet, get, getThe, MonadStateOf.get,
      MonadStateOf.modifyGet, liftM, monadLift, MonadLift.monadLift, ExceptT.lift,
      Functor.map, StateT.map] <;> rfl

def literal {E : Source.Env} {Γ : RCtx} (packed : Bool) (bytes : Roadmap.Bytes) :
    RExpr E Γ (.bytes .memory) :=
  .abiEncode (if packed then .encodePacked else .encode) (.cons (.str bytes) .nil)

/-- A raw string literal is encoded directly: no input-memory allocation occurs.
Only the result object is allocated, at the actual reached allocator next. -/
theorem literal_execution {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (horizon : Nat) (packed : Bool) (bytes : Roadmap.Bytes)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.evalE global frame (horizon+4) (literal packed bytes)).run (locals,state) =
      (.ok (.val (.memRef rfl state.heap.next)),
        (locals,SourceKeccak.afterLiteral state
          (if packed then bytes else Source.abiLayout [(true,bytes)]))) := by
  apply execute global frame (horizon+3) packed (.cons (.str bytes) .nil)
    locals locals locals state state state (.cons (.strLit bytes) .nil)
  · rfl
  · cases packed
    · rfl
    · change ((.ok (bytes ++ []),(locals,state)) :
        Source.R Roadmap.Bytes × (Source.Locals E.layout Γ × Source.St E)) =
        (.ok bytes,(locals,state))
      rw [List.append_nil]

/-- Independent existing byte observations, not a general intrinsic tuple encoder. -/
theorem single_dynamic_bytes (bytes : Roadmap.Bytes) :
    Source.abiLayout [(true,bytes)] =
      Semantics.wordBytes 32 ++ (Semantics.wordBytes bytes.length ++ Semantics.pad32 bytes) := by
  simp only [Source.abiLayout, Source.abiLayout.go, List.length_cons, List.length_nil, List.append_nil, List.nil_append,
    natWordBytes_transport, pad32_transport]

/-- This is precisely the ABI data following the existing Error selector.
It neither treats abi.encode as revert execution nor introduces an ABI emitter. -/
theorem error_payload_projection (bytes : Roadmap.Bytes) :
    Semantics.errorSelector ++ Source.abiLayout [(true,bytes)] = Semantics.encodeError bytes := by
  rw [single_dynamic_bytes]
  simp only [Semantics.encodeError,List.append_assoc]

theorem zero_horizon {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (packed : Bool) (bytes : Roadmap.Bytes) (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.evalE global frame 0 (literal packed bytes)).run (locals,state) =
      (.error .timeout,(locals,state)) := rfl

theorem argument_horizon_zero {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (packed : Bool) (bytes : Roadmap.Bytes) (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.evalE global frame 1 (literal packed bytes)).run (locals,state) =
      (.error .timeout,(locals,state)) := rfl

/-- A typed bytes32 word read, proved without reducing the word's computation. -/
theorem word_bytes_field {D : Source.Layout} (word : Roadmap.Word) :
    (Source.mkBytes (n:=32) (h:=by decide +kernel) (Source.wordBytes word) : Source.Val D STy.bytes32).word = some word := by
  rw [SourceKeccak.mk_wordBytes]
  simp only [Source.Val.word,Source.wordBytes_length,Nat.sub_self,List.replicate_zero,
    List.append_nil,Source.wordBytes_value]
  congr 1
  apply Fin.ext
  simp only [Source.toWord,Nat.mod_eq_of_lt word.isLt]

theorem encode_fixed_bytes32 {E : Source.Env} {Γ : RCtx}
    (frame : Fr) (horizon : Nat) (packed : Bool) (value : Source.Val E.layout STy.bytes32)
    (word : Roadmap.Word) (observation : value.word = some word) :
    (Source.encodeOne frame horizon packed (.val value) : Source.EM E Γ _) =
      pure (false,Source.wordBytes word) := by
  have take : (Source.wordBytes word).take 32 = Source.wordBytes word :=
    List.take_of_length_le (Nat.le_of_eq (Source.wordBytes_length word))
  cases packed <;> simp only [STy.bytes32,Source.encodeOne,observation,
    Bool.false_eq_true,↓reduceIte,take]

/-- Merely unfold the existing five-part source layout; no new emitter. -/
theorem five_parts (first last a b c : Roadmap.Bytes) :
    Source.abiLayout [(true,first),(false,a),(false,b),(true,last),(false,c)] =
      Source.wordBytes (Source.toWord 160) ++
      (a ++ (b ++ (Source.wordBytes (Source.toWord
        (160 + (Source.wordBytes (Source.toWord first.length) ++ Source.pad32 first).length)) ++
      (c ++ ((Source.wordBytes (Source.toWord first.length) ++ Source.pad32 first) ++
        (Source.wordBytes (Source.toWord last.length) ++ Source.pad32 last)))))) := by
  simp only [Source.abiLayout,Source.abiLayout.go,List.length_cons,List.length_nil,
    List.append_nil,List.append_assoc]

theorem take_word (word : Roadmap.Word) (tail : Roadmap.Bytes) :
    (Source.wordBytes word ++ tail).take 32 = Source.wordBytes word :=
  List.take_left' (Source.wordBytes_length word)

theorem drop_word (word : Roadmap.Word) (tail : Roadmap.Bytes) (number : Nat) :
    (Source.wordBytes word ++ tail).drop (32+number) = tail.drop number := by
  simpa only [Source.wordBytes_length] using
    (List.drop_length_add_append (l₁:=Source.wordBytes word) (l₂:=tail) number)

#print axioms word_bytes_field
#print axioms encode_fixed_bytes32
#print axioms five_parts
#print axioms take_word
#print axioms drop_word

#print axioms execute
#print axioms literal_execution
#print axioms single_dynamic_bytes
#print axioms error_payload_projection
#print axioms zero_horizon
#print axioms argument_horizon_zero
end Solidity.Lowering.V08.SourceAbi
