import Solidity.Lowering.V08.LiteralFailureStorageDecodeControls

/-! Kernel success control decomposed into actual copied bytes and the
already-proved state invariant. No evaluator, decoder or budget change. -/
namespace Solidity.Lowering.V08.LiteralFailureStorageSuccessControls
open Solidity Source LiteralFailureStorageDecode LiteralFailureStorageDecodeControls

def locals : Locals environment.layout (.bytes .storage :: [.bytes .memory,.bool]) :=
 .cons (.storRef rfl path) caller

def word : List UInt8 := List.replicate 31 0 ++ [1]

theorem copied_observed :
 ((bytesOfRV frame 34 reference).run (locals,canonical)).1.toOption = some word := by
 decide +kernel

theorem run_from_observation {E : Env} {Γ : RCtx} {α : Type}
 (action : EM E Γ α) (initial : EMState E Γ) (value : α)
 (keep : Hoare (fun y => y = initial) action (fun _ y => y = initial)
  (fun e y => y = initial ∧ NotStuck e))
 (observation : (action.run initial).1.toOption = some value) :
 action.run initial = (.ok value,initial) := by
 have preservation := keep initial rfl
 cases execution : action.run initial with
 | mk outcome reached =>
   cases outcome with
   | error failure =>
     simp only [execution,Except.toOption] at observation
     cases observation
   | ok result =>
     simp only [execution,Except.toOption,Option.some.injEq] at observation
     have reached_eq : reached = initial := by
      simpa only [execution] using preservation
     cases observation
     cases reached_eq
     rfl

theorem copied_full :
 (bytesOfRV frame 34 reference).run (locals,canonical) =
 (.ok word,(locals,canonical)) := by
 exact run_from_observation _ _ _
  (stored_bytes frame 34 path typed (fun y => y = (locals,canonical))) copied_observed

theorem word_read : wordAt word 0 = 1 := by decide +kernel

theorem word_decoder {Γ : RCtx} :
 (abiDecodeData word [.bool] : EM environment Γ (RVal environment.layout .bool)) =
 pure (.val (.bool true)) := by
 unfold abiDecodeData
 have full : ¬ word.length < 32 * ([STy.bool] : List STy).length := by decide +kernel
 rw [if_neg full]
 simp only [decodeArgs,decodeArg,word_read,decodeWord,decodeElemWord]
 rfl

theorem decode_true (pipeline : Roadmap.Pipeline) :
 (evalE (global pipeline) frame 35 decoder).run
  (.cons (.storRef rfl path) caller,canonical) =
 (.ok (.val (.bool true)),(.cons (.storRef rfl path) caller,canonical)) := by
 simp only [decoder,evalE,EM.locals,Locals.get,bind,pure,ExceptT.bind,ExceptT.pure,
  ExceptT.run,ExceptT.mk,ExceptT.bindCont,StateT.bind,StateT.pure,StateT.get,
  get,getThe,MonadStateOf.get,liftM,monadLift,MonadLift.monadLift,ExceptT.lift,
  Functor.map,StateT.map]
 have actual := copied_full
 simp only [ExceptT.run,reference,locals] at actual
 rw [actual]
 dsimp only
 rw [word_decoder]
 rfl

theorem wrong_zero_word :
 ((bytesOfRV frame 34 reference).run (locals,canonical)).1.toOption ≠
 some (List.replicate 32 0) := by
 rw [copied_observed]
 decide +kernel

theorem caller_bool (pipeline : Roadmap.Pipeline) :
 ((evalE (global pipeline) frame 35 decoder).run (locals,canonical)).2.1.get
  (.there (.there .here)) = .bool true := by
 simp only [locals]
 rw [decode_true pipeline]
 rfl

theorem older_alias (pipeline : Roadmap.Pipeline) :
 ((evalE (global pipeline) frame 35 decoder).run (locals,canonical)).2.2.heap.get 0 =
 some ⟨.bytes .memory,.bytes [9,7]⟩ := by
 simp only [locals]
 rw [decode_true pipeline]
 rfl

theorem wrong_order : word.reverse ≠ word := by decide +kernel

#print axioms word_read
#print axioms word_decoder
#print axioms wrong_zero_word
#print axioms caller_bool
#print axioms older_alias
#print axioms wrong_order
#print axioms copied_observed
#print axioms run_from_observation
#print axioms copied_full
#print axioms decode_true
end Solidity.Lowering.V08.LiteralFailureStorageSuccessControls
