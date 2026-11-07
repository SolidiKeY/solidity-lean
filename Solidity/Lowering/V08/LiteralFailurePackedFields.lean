import Solidity.Lowering.V08.LiteralFailureCopyEncoding

/-! Derivation of actual published packed parts from synchronized typed fields.
These Prop witnesses relate existing values to existing encoder parts. They do
not define another encoder or admit source inputs. -/
namespace Solidity.Lowering.V08.LiteralFailurePackedFields
open Solidity Source
open LiteralFailureLocatedFields (Head Fields)
open LiteralFailureConvertedFields (Keeps)
open LiteralFailureCopySequence (Plan)

inductive Piece : {shape : AbiEntry.Shape} → AbiEntry.Val shape → (Bool × Roadmap.Bytes) → Prop
 | uint (w : Roadmap.Word) : Piece (.word (LiteralFailureDynamicError.abiWord w)) (false,AbiEntry.wordBytes w.val)
 | boolean (b : Bool) : Piece (.word (BoolErrorAbi.word b)) (false,[if b then 1 else 0])
 | bytes (bs : Roadmap.Bytes) : Piece (.bytes bs) (true,bs)

inductive Pieces : {shapes : List AbiEntry.Shape} → AbiEntry.Vals shapes → List (Bool × Roadmap.Bytes) → Prop
 | nil : Pieces .nil []
 | cons {shape shapes encoded encodeds part parts} (head : @Piece shape encoded part)
   (tail : @Pieces shapes encodeds parts) : Pieces (.cons encoded encodeds) (part::parts)

theorem piece_unique {shape} {encoded : AbiEntry.Val shape} {left right}
 (a : Piece encoded left) (b : Piece encoded right) : left=right := by
 cases a with
 | uint w =>
  generalize h : (AbiEntry.Val.word (LiteralFailureDynamicError.abiWord w))=value at b
  cases b with
  | uint other =>
   have same : w.val=other.val := congrArg (fun v=>match v with | .word x=>x.val) h
   have equal : w=other := Fin.ext same
   cases equal
   rfl
 | boolean flag =>
  generalize h : (AbiEntry.Val.word (BoolErrorAbi.word flag))=value at b
  cases b with
  | boolean other => cases flag <;> cases other <;> cases h <;> rfl
 | bytes bs =>
  generalize h : (AbiEntry.Val.bytes bs)=value at b
  cases b with
  | bytes other => cases h; rfl

theorem pieces_unique {shapes} {encoded : AbiEntry.Vals shapes} {left right}
 (a : Pieces encoded left) (b : Pieces encoded right) : left=right := by
 induction a generalizing right with
 | nil => cases b; rfl
 | cons head tail ih =>
  cases b with
  | cons other rest => rw [piece_unique head other,ih rest]

theorem one_witness {E : Env} {Γ type shape} {value : Source.Val E.layout type}
 {encoded : AbiEntry.Val shape} (F : Fr) (fuel : Nat) (locals : Locals E.layout Γ) (state : St E)
 (head : Head F state value encoded) :
 ∃ part, Piece encoded part ∧
  (encodeOne F fuel true (.val value) : EM E Γ _).run (locals,state)=(.ok part,(locals,state)) := by
 cases head with
 | known field =>
  cases field with
  | uint w rest =>
   refine ⟨_,.uint w,?_⟩
   simp only [encodeOne,LiteralFailureDynamicError.marker_word,STy.packedWidth,↓reduceIte,
    pure,ExceptT.pure,ExceptT.run,LiteralFailureMixedEncoding.word_agreement]
   rfl
  | boolean b rest =>
   refine ⟨_,.boolean b,?_⟩
   cases b <;> rfl
  | bytes address bs heap rest =>
   refine ⟨_,.bytes bs,?_⟩
   rcases heap with heap | heap <;>
    simp only [encodeOne,bytesOfRV,heapBytes,heapObj,EM.st,
     bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
     StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,liftM,
     monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map,heap]
  | string address bs heap rest =>
   refine ⟨_,.bytes bs,?_⟩
   simp only [encodeOne,bytesOfRV,heapBytes,heapObj,EM.st,
    bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,liftM,
    monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map,heap]
 | calldataBytes off len => exact ⟨_,.bytes _,rfl⟩
 | calldataString off len => exact ⟨_,.bytes _,rfl⟩

theorem parts_witness {E : Env} {Γ types shapes} {values : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} (F : Fr) (fuel : Nat) (locals : Locals E.layout Γ) (state : St E)
 (fields : Fields F state values encoded) :
 ∃ parts, Pieces encoded parts ∧
  (encodeParts F fuel true values.toR : EM E Γ _).run (locals,state)=(.ok parts,(locals,state)) := by
 induction fields with
 | nil => exact ⟨[],.nil,rfl⟩
 | cons head tail ih =>
  rcases one_witness F fuel locals state head with ⟨part,piece,actual⟩
  rcases ih with ⟨parts,pieces,tailRun⟩
  refine ⟨part::parts,.cons piece pieces,?_⟩
  simp only [Vals.toR]
  rw [encodeParts]
  dsimp only [ExceptT.run] at actual tailRun
  simp only [bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,
   ExceptT.mk,StateT.bind,StateT.pure,actual,tailRun]


theorem encoding_run {E : Env} {Γ types shapes} {values : Source.Vals E.layout types}
 {encoded : AbiEntry.Vals shapes} (F : Fr) (fuel : Nat) (locals : Locals E.layout Γ) (state : St E)
 (fields : Fields F state values encoded) :
 ∃ parts, Pieces encoded parts ∧
 (encodeVals F fuel true values.toR : EM E Γ _).run (locals,state)=
 (.ok (parts.foldr (fun (part : Bool × Roadmap.Bytes) tail=>part.2++tail) []),(locals,state)) := by
 rcases parts_witness F fuel locals state fields with ⟨parts,pieces,actual⟩
 refine ⟨parts,pieces,?_⟩
 dsimp only [ExceptT.run] at actual
 simp only [encodeVals,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,
  ExceptT.mk,StateT.bind,StateT.pure,actual,↓reduceIte]

theorem expression_run {E : Env} {Γ types shapes copies} {arguments : RConvArgs E Γ types}
 {encoded : AbiEntry.Vals shapes} (G : Glob E) (F : Fr) (extra : Nat)
 (locals : Locals E.layout Γ) (state : St E) (plan : Plan F state locals arguments encoded copies) :
 ∃ (middle : St E) (parts : List (Bool × Roadmap.Bytes)), Pieces encoded parts ∧
 (evalE G F (types.length+extra+5) (.abiEncode .encodePacked (LiteralFailureCopyEncoding.expressions arguments))).run (locals,state)=
 (.ok (.val (.memRef rfl middle.heap.next)),
  (locals,SourceKeccak.afterLiteral middle (parts.foldr (fun (part : Bool × Roadmap.Bytes) tail=>part.2++tail) []))) ∧
 Keeps F state (SourceKeccak.afterLiteral middle (parts.foldr (fun (part : Bool × Roadmap.Bytes) tail=>part.2++tail) [])) ∧
 middle.heap.next=state.heap.next+copies ∧
 (SourceKeccak.afterLiteral middle (parts.foldr (fun (part : Bool × Roadmap.Bytes) tail=>part.2++tail) [])).heap.next=state.heap.next+copies+1 ∧
 SourceKeccak.afterLiteral middle (parts.foldr (fun (part : Bool × Roadmap.Bytes) tail=>part.2++tail) [])=
  {state with heap:=(SourceKeccak.afterLiteral middle (parts.foldr (fun (part : Bool × Roadmap.Bytes) tail=>part.2++tail) [])).heap} := by
 rcases LiteralFailureCopyEncoding.arguments_run G F extra locals state plan with ⟨values,middle,actual,fields,kept,next,nonheap⟩
 rcases encoding_run F (types.length+extra+4) locals middle fields with ⟨parts,pieces,encoding⟩
 refine ⟨middle,parts,pieces,?_,?_,next,?_,?_⟩
 · exact SourceAbi.execute G F (types.length+extra+4) true (LiteralFailureCopyEncoding.expressions arguments)
    locals locals locals state middle middle values.toR _ actual
    encoding
 · intro types shapes values encoded fields
   exact LiteralFailureLocatedFields.fields_after F middle _ (kept values encoded fields)
 · change middle.heap.next+1=state.heap.next+copies+1
   omega
 · exact congrArg (fun source=>{source with heap:=(SourceKeccak.afterLiteral middle (parts.foldr (fun (part : Bool × Roadmap.Bytes) tail=>part.2++tail) [])).heap}) nonheap

end Solidity.Lowering.V08.LiteralFailurePackedFields
