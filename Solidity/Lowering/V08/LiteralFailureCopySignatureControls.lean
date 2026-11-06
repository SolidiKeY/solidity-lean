import Solidity.Lowering.V08.LiteralFailureCopySignature
import Solidity.Lowering.V08.LiteralFailureCopySelectorControls
namespace Solidity.Lowering.V08.LiteralFailureCopySignatureControls
open Solidity Source
open LiteralFailureCopySignature
abbrev E := LiteralFailureCopySelectorControls.E
abbrev state := LiteralFailureCopySelectorControls.state
abbrev frame := LiteralFailureCopySelectorControls.frame
abbrev global := LiteralFailureCopySelectorControls.global
abbrev types := LiteralFailureCopySelectorControls.types
abbrev values := LiteralFailureCopySelectorControls.values
abbrev encoded := LiteralFailureCopySelectorControls.encoded
abbrev middle := LiteralFailureCopySelectorControls.middle
abbrev context : RCtx := [.bytes .memory,.bytes .calldata,.int IntTy.u256,.string .memory,.bool,.bytes .memory]
def locals (address off len : Nat) (w : Roadmap.Word) (flag : Bool) : Locals E.layout context :=
 .cons (.memRef rfl address) (.cons (.cdRef rfl off len) (.cons (SourceEnvironment.sourceWord w)
  (.cons (.memRef rfl 1) (.cons (.bool flag) (.cons (.memRef rfl 0) .nil)))))
def arguments : RConvArgs E context types :=
 .cons (.local (.there .here)) rfl (.cons (.local (.there (.there .here))) rfl
  (.cons (.local (.there (.there (.there .here)))) rfl (.cons (.local (.there (.there (.there (.there .here))))) rfl .nil)))
def packet (p : Roadmap.Pipeline) (data first : Roadmap.Bytes) (off len : Nat) (w : Roadmap.Word) (flag : Bool) :=
 (wordBytes ((global p).fixed.hash first)).take 4++AbiEntry.encodeArgs (encoded data first off len w flag)
def result (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes) (off len : Nat) (w : Roadmap.Word) (flag : Bool) :=
 SourceKeccak.afterLiteral (middle data first second third off len) (packet p data first off len w flag)
def expression : RExpr E context (.bytes .memory) :=
 .abiEncode .encodeWithSignature (.cons (.local .here) (LiteralFailureCopyEncoding.expressions arguments))

theorem plan (data first second third : Roadmap.Bytes) (address off len : Nat) (w : Roadmap.Word) (flag : Bool) :
 LiteralFailureCopySequence.Plan (frame data) (state first second third) (locals address off len w flag)
 arguments (encoded data first off len w flag) 1 :=
 .cons (.there .here) rfl (.bytes (.there .here) off len rfl)
  (.cons (.there (.there .here)) rfl (.read (.there (.there .here)) rfl (.known (.uint w .nil)))
   (.cons (.there (.there (.there .here))) rfl (.read (.there (.there (.there .here))) rfl (.known (.string 1 first rfl .nil)))
    (.cons (.there (.there (.there (.there .here)))) rfl (.read (.there (.there (.there (.there .here)))) rfl (.known (.boolean flag .nil))) .nil)))

theorem actual_arguments (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes)
 (address off len : Nat) (w : Roadmap.Word) (flag : Bool) :
 (evalArgs (global p) (frame data) 9 (.cons (.local .here) (LiteralFailureCopyEncoding.expressions arguments))).run
 (locals address off len w flag,state first second third)=
 (.ok (.cons (.val (.memRef rfl address)) (values w flag).toR),
 (locals address off len w flag,middle data first second third off len)) := rfl

theorem fields (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes)
 (address off len : Nat) (w : Roadmap.Word) (flag : Bool) :
 LiteralFailureLocatedFields.Fields (frame data) (middle data first second third off len) (values w flag) (encoded data first off len w flag) := by
 rcases arguments_run (global p) (frame data) 0 .here _ _ (plan data first second third address off len w flag) with
  ⟨vs,mid,actual,fields,kept,next,nonheap⟩
 change (evalArgs (global p) (frame data) 9 (.cons (.local .here) (LiteralFailureCopyEncoding.expressions arguments))).run
  (locals address off len w flag,state first second third)=
  (.ok (.cons (.val (.memRef rfl address)) vs.toR),(locals address off len w flag,mid)) at actual
 rw [actual_arguments] at actual
 have stateEq := congrArg (fun r=>r.2.2) actual
 have valueEq := Except.ok.inj (congrArg Prod.fst actual)
 cases stateEq
 injection valueEq with _ _ _ tailEq
 have valuesEq := LiteralFailureCopySelector.values_injective tailEq
 cases valuesEq
 exact fields

theorem actual_expression (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes)
 (off len : Nat) (w : Roadmap.Word) (flag : Bool) :
 (evalE (global p) (frame data) 10 expression).run (locals 1 off len w flag,state first second third)=
 (.ok (.val (.memRef rfl 5)),(locals 1 off len w flag,result p data first second third off len w flag)) :=
 SourceAbi.signature_execute (global p) (frame data) 9 _ _ _ _ _ _ _ _ _
 (.val (.memRef rfl 1)) (values w flag).toR first _
 (actual_arguments p data first second third 1 off len w flag)
 (LiteralFailureSignatureBytes.signature_read (frame data) 9 .here first
  (locals 1 off len w flag) (locals 1 off len w flag) (middle data first second third off len)
  ⟨1,rfl,.inr (LiteralFailureMixedExpression.old_object (state first second third) ((data.drop off).take len) _ _ rfl)⟩)
 (LiteralFailureLocatedFields.encoding_run (frame data) 9 _ _ (fields p data first second third 1 off len w flag))

theorem applied (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes)
 (off len : Nat) (w : Roadmap.Word) (flag : Bool) :
 ∃ mid : St E,
 (evalE (global p) (frame data) 10 expression).run (locals 1 off len w flag,state first second third)=
 (.ok (.val (.memRef rfl mid.heap.next)),(locals 1 off len w flag,SourceKeccak.afterLiteral mid (packet p data first off len w flag))) ∧
 LiteralFailureDynamicListError.represented (locals 1 off len w flag) mid .here first ∧
 mid.heap.next=5 ∧ (SourceKeccak.afterLiteral mid (packet p data first off len w flag)).heap.next=6 := by
 rcases expression_run (global p) (frame data) 0 .here _ _ first ⟨1,rfl,.inr rfl⟩
  (plan data first second third 1 off len w flag) with ⟨mid,actual,preserved,kept,next,count,nonheap⟩
 exact ⟨mid,actual,preserved,next,count⟩

theorem old_alias (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes)
 (off len : Nat) (w : Roadmap.Word) (flag : Bool) :
 (result p data first second third off len w flag).heap.get 1=some ⟨.string .memory,.string first⟩ :=
 LiteralFailureMixedExpression.old_object _ _ _ _ (LiteralFailureMixedExpression.old_object _ _ _ _ rfl)

theorem dangling_after_copy (data first second third : Roadmap.Bytes) :
 (evalE (global .legacy) (frame data) 10 expression).run
 (locals 99 0 1 ⟨300,by decide +kernel⟩ true,state first second third)=
 (.error (.stuck "dangling memory reference"),(locals 99 0 1 ⟨300,by decide +kernel⟩ true,middle data first second third 0 1)) := rfl

theorem timeout_before_read (data first second third : Roadmap.Bytes) :
 (evalE (global .legacy) (frame data) 5 expression).run
 (locals 99 0 1 ⟨300,by decide +kernel⟩ true,state first second third)=
 (.error .timeout,(locals 99 0 1 ⟨300,by decide +kernel⟩ true,middle data first second third 0 1)) := rfl

theorem hash_agreement (p : Roadmap.Pipeline) (signature : Roadmap.Bytes) :
 (wordBytes ((global p).fixed.hash signature)).take 4=
 (Semantics.wordBytes (keccakBytes (signature.map (fun byte=>(byte.toNat : Int)))).1.toNat).take 4 :=
 SourceAbi.signature_prefix_transport (global p) Roadmap.Controls.toyFixed_keccak signature

theorem wrong_cursor (p : Roadmap.Pipeline) (data first second third : Roadmap.Bytes)
 (off len : Nat) (w : Roadmap.Word) (flag : Bool) :
 (evalE (global p) (frame data) 10 expression).run (locals 1 off len w flag,state first second third)≠
 (.ok (.val (.memRef rfl 5)),(locals 1 off len w flag,middle data first second third off len)) := by
 rw [actual_expression]
 intro equal
 have bad := congrArg (fun r=>r.2.2.heap.next) equal
 change (6 : Nat)=5 at bad
 cases bad

def render := LiteralFailureTypedFieldsControls.render
def observe (p : Roadmap.Pipeline) (data first : Roadmap.Bytes) (off len : Nat) (w : Roadmap.Word) (flag : Bool) : String :=
 match (evalE (global p) (frame data) 10 expression).run (locals 1 off len w flag,state first [128] [171,0]) with
 | (.ok (.val (.memRef _ ptr)),(_,after)) =>
  match after.heap.get ptr,after.heap.get 4,after.heap.get 1 with
  | some ⟨.bytes .memory,.bytes bs⟩,some ⟨.bytes .memory,.bytes copied⟩,some ⟨.string .memory,.string old⟩ =>
   "{\"pointer\":"++toString ptr++",\"cursor\":"++toString after.heap.next++",\"copy\":"++render copied++",\"old\":"++render old++",\"bytes\":"++render bs++"}"
  | _,_,_ => "null"
 | _ => "null"
def suite (p : Roadmap.Pipeline) := "["++String.intercalate "," [
 observe p [] [] 0 0 ⟨0,by decide +kernel⟩ false,
 observe p [99,0,255,128,7] [195,169] 1 3 ⟨300,by decide +kernel⟩ true,
 observe p (List.replicate 31 255++[0]++List.replicate 33 128) (List.replicate 33 255) 32 33 ⟨2^256-1,by decide +kernel⟩ false,
 observe p [0,255,128] (List.replicate 31 0) 99 33 ⟨2^255,by decide +kernel⟩ true,
 observe p ([0]++List.replicate 33 128++[255]) (List.replicate 32 0) 1 32 ⟨42,by decide +kernel⟩ false]++"]"
#eval "COPY_SIGNATURE_LEGACY="++suite .legacy
#eval "COPY_SIGNATURE_VIAIR="++suite .viaIR
#print axioms signature_kept
#print axioms arguments_run
#print axioms expression_run
#print axioms plan
#print axioms actual_arguments
#print axioms fields
#print axioms actual_expression
#print axioms applied
#print axioms old_alias
#print axioms dangling_after_copy
#print axioms timeout_before_read
#print axioms hash_agreement
#print axioms wrong_cursor
end Solidity.Lowering.V08.LiteralFailureCopySignatureControls
