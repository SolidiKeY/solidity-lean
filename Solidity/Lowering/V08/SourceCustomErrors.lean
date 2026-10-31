import Solidity.Lowering.V08.SourceEmit
import Solidity.Lowering.V08.SelectorObservations

/-! Actual custom-error source execution and exact existing selector/ABI byte
observations. Canonical signature INPUT representation is an explicit independent
premise, not an ASCII profile cap, hash collision assumption or new emitter. -/
namespace Solidity.Lowering.V08.SourceCustomErrors
open Solidity Source

theorem execute {E : Source.Env} {Γ : RCtx} {types : List STy}
    (global : Glob E) (frame : Fr) (horizon : Nat) (error : Decl)
    (typed : error.paramTys E = some types) (args : RConvArgs E Γ types)
    (locals next : Source.Locals E.layout Γ) (state middle final : Source.St E)
    (values : Source.Vals E.layout types) (data : Roadmap.Bytes)
    (arguments : (Source.evalConvArgs global frame horizon args).run (locals,state) =
      (.ok values,(next,middle)))
    (encoding : (Source.encodeVals frame horizon false values.toR : Source.EM E [] _).run
      (Source.L0 E,middle) = (.ok data,(Source.L0 E,final))) :
    (Source.execS global frame (horizon+1) 0 none
      (.revertError error typed args : RStmt E [] false .body Γ Γ) locals).run (Source.L0 E,state) =
      (.error (.revert (global.selector (Source.sigOf E.layout error.name types) ++ data)),
        (Source.L0 E,final)) := by
  simp only [ExceptT.run] at arguments encoding
  simp only [Source.execS,Source.EM.sub,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,StateT.pure,StateT.get,StateT.modifyGet,modify,modifyGet,get,getThe,
    MonadStateOf.get,MonadStateOf.modifyGet,liftM,monadLift,MonadLift.monadLift,
    ExceptT.lift,Functor.map,StateT.map,Source.EM.halt,throw,throwThe,MonadExceptOf.throw,arguments,encoding]

theorem selector_of_bytes {E : Source.Env} (global : Glob E) (pin : global.fixed.Keccak)
    (characters : List Char) (signature : String)
    (bytes : Source.asciiBytes characters = signature.toUTF8.toList) :
    global.selector characters = Semantics.selectorBytes (Semantics.customSelector signature) := by
  rw [← SelectorObservations.signature_selector]
  unfold Source.Glob.selector Source.selector
  rw [bytes]
  apply congrArg (fun word : Roadmap.Word => (Source.wordBytes word).take 4)
  apply Fin.ext
  change global.fixed.evm.keccak signature.toUTF8.toList =
    Roadmap.Evm.keccakWord signature.toUTF8.toList % 2^256
  rw [pin.1]
  simp only [Roadmap.Evm.keccakWord,Nat.mod_mod]

theorem selector_length {E : Source.Env} (global : Glob E) (characters : List Char) :
    (global.selector characters).length = 4 := by
  simp only [Source.Glob.selector,List.length_take,Source.wordBytes_length]
  rfl

/-- The two published input encodings differ here. No claim that this is an
admitted identifier, and no hash noncollision premise, follows from this fact. -/
theorem nonascii_utf8 : "é".toUTF8.toList = [195,169] := by
  change ((⟨#[195,169]⟩ : ByteArray).toList) = _
  have size : (⟨#[195,169]⟩ : ByteArray).size = 2 := rfl
  unfold ByteArray.toList
  repeat' (rw [ByteArray.toList.loop]; simp only [size,Nat.reduceLT,Nat.reduceAdd,if_true,if_false])
  rfl

theorem distinct_input_encodings : Source.asciiBytes ['é'] ≠ "é".toUTF8.toList := by
  rw [nonascii_utf8]
  decide +kernel

#print axioms execute
#print axioms selector_of_bytes
#print axioms selector_length
#print axioms nonascii_utf8
#print axioms distinct_input_encodings
end Solidity.Lowering.V08.SourceCustomErrors
