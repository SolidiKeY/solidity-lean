import Solidity.Lowering.V08.LiteralFailureReturnSlots

/-! A sufficient relation between existing indexed Source values, actual heap
contents, existing encoder parts and existing intrinsic ABI values. It is not
an admission predicate, alternate AST, codec or assumed encoder execution. -/
namespace Solidity.Lowering.V08.LiteralFailureMixedEncoding
open Solidity Source
open LiteralFailureDynamicError (abiWord marker_word)

inductive Represented {E : Env} (state : St E) :
 {types : RCtx} → Source.Vals E.layout types →
 {shapes : List AbiEntry.Shape} → AbiEntry.Vals shapes → List (Bool × Roadmap.Bytes) → Prop
 | nil : Represented state .nil .nil []
 | uint {types shapes values encoded parts} (w : Roadmap.Word)
   (tail : @Represented E state types values shapes encoded parts) :
   Represented state (.cons (SourceEnvironment.sourceWord w) values)
    (.cons (.word (abiWord w)) encoded) ((false,wordBytes w)::parts)
 | bytes {types shapes values encoded parts} (address : Nat) (bs : Roadmap.Bytes)
   (heap : state.heap.get address=some ⟨.bytes .memory,.bytes bs⟩ ∨
    state.heap.get address=some ⟨.string .memory,.string bs⟩)
   (tail : @Represented E state types values shapes encoded parts) :
   Represented state (.cons (.memRef rfl address : Source.Val E.layout (.bytes .memory)) values)
    (.cons (.bytes bs) encoded) ((true,bs)::parts)

theorem word_agreement (w : Roadmap.Word) : wordBytes w=AbiEntry.wordBytes w.val := by
 have identity : toWord w.val=w := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt w.isLt
 exact (congrArg wordBytes identity).symm.trans (LiteralFailureDynamicListError.word_transport w.val)

theorem parts_run {E : Env} {Γ types shapes} {values : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} {parts} (F : Fr) (fuel : Nat)
 (locals : Locals E.layout Γ) (state : St E)
 (represented : Represented state values encoded parts) :
 (encodeParts F fuel false values.toR : EM E Γ _).run (locals,state)=
 (.ok parts,(locals,state)) := by
 induction represented with
 | nil => rfl
 | uint w tail ih =>
  simp only [Vals.toR,encodeParts,encodeOne,marker_word,Bool.false_eq_true,↓reduceIte]
  dsimp only [ExceptT.run] at ih
  simp only [bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,
   ExceptT.mk,StateT.bind,StateT.pure,ih]
 | bytes address bs heap tail ih =>
  rcases heap with heap | heap <;>
   simp only [Vals.toR,encodeParts,encodeOne,bytesOfRV,heapBytes,heapObj,EM.st,
    bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,liftM,
    monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map,heap]
  all_goals
   dsimp only [ExceptT.run] at ih
   rw [ih]
   rfl

theorem go_agreement {E : Env} {types shapes} {values : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} {parts} (state : St E)
 (represented : Represented state values encoded parts) (offset : Nat) :
 Source.abiLayout.go parts offset=AbiEntry.assemble.go encoded.parts offset := by
 induction represented generalizing offset with
 | nil => rfl
 | uint w tail ih =>
  simp only [Source.abiLayout.go,AbiEntry.Vals.parts,AbiEntry.Shape.dynamic,
   AbiEntry.Val.enc,abiWord,AbiEntry.assemble.go,Bool.false_eq_true,↓reduceIte,
   word_agreement,ih]
 | bytes address bs heap tail ih =>
  simp only [Source.abiLayout.go,AbiEntry.Vals.parts,AbiEntry.Shape.dynamic,
   AbiEntry.Val.enc,AbiEntry.assemble.go,↓reduceIte]
  rw [LiteralFailureDynamicListError.tail_agreement,ih,
   LiteralFailureDynamicListError.word_transport]
  simp only [AbiEntry.Val.enc,List.append_assoc]

theorem head_extent {E : Env} {types shapes} {values : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} {parts} (state : St E)
 (represented : Represented state values encoded parts) (offset : Nat) :
 encoded.parts.foldl (fun acc part=>acc+if part.1 then 32 else part.2.length) offset=
 offset+32*parts.length := by
 induction represented generalizing offset with
 | nil => simp only [AbiEntry.Vals.parts,List.foldl_nil,List.length_nil,Nat.mul_zero,Nat.add_zero]
 | uint w tail ih =>
  simp only [AbiEntry.Vals.parts,AbiEntry.Shape.dynamic,AbiEntry.Val.enc,AbiEntry.wordBytes,
   List.length_map,List.length_range,List.foldl_cons,Bool.false_eq_true,↓reduceIte,
   ih,List.length_cons]
  omega
 | bytes address bs heap tail ih =>
  simp only [AbiEntry.Vals.parts,AbiEntry.Shape.dynamic,List.foldl_cons,↓reduceIte,ih,List.length_cons]
  omega

theorem encoding_run {E : Env} {Γ types shapes} {values : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} {parts} (F : Fr) (fuel : Nat)
 (locals : Locals E.layout Γ) (state : St E)
 (represented : Represented state values encoded parts) :
 (encodeVals F fuel false values.toR : EM E Γ _).run (locals,state)=
 (.ok (AbiEntry.encodeArgs encoded),(locals,state)) := by
 have actual := parts_run F fuel locals state represented
 dsimp only [ExceptT.run] at actual
 have layout : Source.abiLayout parts=AbiEntry.encodeArgs encoded := by
  simp only [Source.abiLayout,AbiEntry.encodeArgs,AbiEntry.assemble,
   head_extent state represented,Nat.zero_add,go_agreement state represented]
 simp only [encodeVals,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,
  ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,actual,Bool.false_eq_true,↓reduceIte,layout]
/-- Discharges the existing G38 encoding premise from concrete field evidence. -/
theorem encodingAt {E : Env} {types shapes} {values : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} {parts} (F : Fr) (fuel : Nat) (state : St E)
 (represented : Represented state values encoded parts) :
 Backend.FailurePaths.Premises.EncodingAt F fuel values.toR state state
  (AbiEntry.encodeArgs encoded) := encoding_run F fuel (L0 E) state represented
end Solidity.Lowering.V08.LiteralFailureMixedEncoding
