import Solidity.Backend.AbiWorld.ReturnWordTransport
import Solidity.Backend.AbiWorld.ErrorReadWindowControls

namespace Solidity.Backend.AbiWorld.ReturnWordTransportControls
open Semantics Failure ReturnWordTransport
open ErrorReadWindowControls (machine jsonPackets)

def u (n : Nat) (hn : n < AbiEntry.W := by decide) : UInt := LibraryResultPacket.uint ⟨n,hn⟩
def xs : List UInt := [u 300,u (2^255),u (2^256-1)]
def suffix : List UInt8 := [222,173,0,255]
def contract : Contract := {vars := []}
def rets : Binders [.val .uint,.val .uint,.val .uint] :=
  ((Binders.nil.snoc .uint (.user "a")).snoc .uint (.user "b")).snoc .uint (.user "c")

theorem read_three :
    (ExternalReturnBytes.words xs.length (AbiEntry.encodeArgs (values xs) ++ suffix)).map
      (fun ws => ws.map Subtype.val) = .ok [300,((2^255:Nat):Int),((2^256-1:Nat):Int)] := by
  rw [words_readback]
  rfl

theorem bind_three :
    (ExternalReturnBytes.decode (C:=contract) (H:=[]) rets (AbiEntry.encodeArgs (values xs) ++ suffix)).map
      (fun r => ([r.1.1.val,r.1.2.1.val,r.1.2.2.1.val],r.2.map Subtype.val)) = .ok ([((2^256-1:Nat):Int),((2^255:Nat):Int),300],[]) := by
  rw [decode_transport rets xs (by decide) suffix]
  rfl

theorem truncated_refused : ExternalReturnBytes.words xs.length
    ((AbiEntry.encodeArgs (values xs)).take (32*xs.length-1)) = .error .revert :=
  truncated xs (by unfold xs; intro h; cases h)

/-- Zero demand is a low-level property, not a Source declared-return rule. -/
theorem zero_demand : ExternalReturnBytes.words 0 [1] = .ok [] := by rfl

theorem one_demand : ExternalReturnBytes.words 1 [1] = .error .revert := by rfl

theorem too_many_demanded : ExternalReturnBytes.words 4 (AbiEntry.encodeArgs (values xs) ++ suffix) = .error .revert := by
  have short : (AbiEntry.encodeArgs (values xs) ++ suffix).length < 4*32 := by
    rw [encoded_values,List.length_append,byte_length]
    simp only [xs,List.length_cons,List.length_nil,suffix]
    decide
  rw [ExternalReturnBytes.words,if_neg (Nat.not_le_of_gt short)]

theorem wrong_order : AbiEntry.encodeArgs (values xs.reverse) ≠ AbiEntry.encodeArgs (values xs) := by decide +kernel

theorem emitted_application :
    Slice.checkedRun (emit 8 (.returned (AbiEntry.encodeArgs (values xs)))) machine =
      some ({machine with memory := Slice.putBytes machine.memory 8 (AbiEntry.encodeArgs (values xs))},
        some (.success (AbiEntry.encodeArgs (values xs)))) ∧
    ExternalReturnBytes.words xs.length
      (Slice.getBytes (Slice.putBytes machine.memory 8 (AbiEntry.encodeArgs (values xs))) 8
        (AbiEntry.encodeArgs (values xs)).length) = .ok (xs.map semanticWord) := by
  have size : (AbiEntry.encodeArgs (values xs)).length = 96 := by
    rw [encoded_values,byte_length]
    rfl
  have fits : Fits 8 (AbiEntry.encodeArgs (values xs)) := by
    simp only [Fits,size]
    decide
  simpa only [List.append_nil] using emitted xs 8 [] machine fits (by decide)

def samples : List (List UInt) := [[],[u 0],[u 300,u (2^256-1)],xs,
  List.replicate 31 (u 300),List.replicate 32 (u 0),List.replicate 33 (u (2^256-1))]
def packets : List (List UInt8) := samples.map (fun vs => AbiEntry.encodeArgs (values vs) ++ suffix)
def wordsJson (vs : List UInt) : String :=
  match ExternalReturnBytes.words vs.length (AbiEntry.encodeArgs (values vs) ++ suffix) with
  | .error _ => "null"
  | .ok ws => "[" ++ String.intercalate "," (ws.map (fun w => toString w.val)) ++ "]"
end Solidity.Backend.AbiWorld.ReturnWordTransportControls
#print axioms Solidity.Backend.AbiWorld.ReturnWordTransportControls.read_three
#print axioms Solidity.Backend.AbiWorld.ReturnWordTransportControls.bind_three
#print axioms Solidity.Backend.AbiWorld.ReturnWordTransportControls.truncated_refused
#print axioms Solidity.Backend.AbiWorld.ReturnWordTransportControls.zero_demand
#print axioms Solidity.Backend.AbiWorld.ReturnWordTransportControls.one_demand
#print axioms Solidity.Backend.AbiWorld.ReturnWordTransportControls.too_many_demanded
#print axioms Solidity.Backend.AbiWorld.ReturnWordTransportControls.wrong_order
#print axioms Solidity.Backend.AbiWorld.ReturnWordTransportControls.emitted_application
#eval IO.println ("RETURN_WORD_PACKETS=" ++ Solidity.Backend.AbiWorld.ErrorReadWindowControls.jsonPackets Solidity.Backend.AbiWorld.ReturnWordTransportControls.packets)
#eval IO.println ("RETURN_WORD_VALUES=" ++ "[" ++ String.intercalate "," (Solidity.Backend.AbiWorld.ReturnWordTransportControls.samples.map Solidity.Backend.AbiWorld.ReturnWordTransportControls.wordsJson) ++ "]")
