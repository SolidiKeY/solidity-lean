import Solidity.Lowering.V08.LiteralFailureSliceChain
import Solidity.Lowering.V08.LiteralFailureNestedSliceControls
namespace Solidity.Lowering.V08.LiteralFailureSliceChainControls
open Solidity Source
open LiteralFailureSliceChain
abbrev E := LiteralFailureNestedSliceControls.E
abbrev frame := LiteralFailureNestedSliceControls.frame
abbrev state := LiteralFailureNestedSliceControls.state
abbrev global := LiteralFailureNestedSliceControls.global
abbrev older := LiteralFailureNestedSliceControls.older
abbrev types := LiteralFailureNestedSliceControls.types
abbrev values := LiteralFailureNestedSliceControls.values
open LiteralFailureNestedSliceControls (word)
def context : RCtx := [.bytes .calldata,.int IntTy.u256,.int IntTy.u256,.int IntTy.u256,.int IntTy.u256,.int IntTy.u256]++LiteralFailureSliceEncodingControls.olderTypes
def locals (off len : Nat) (s e u v t : Roadmap.Word) (q m : Nat) (w : Roadmap.Word) : Locals E.layout context :=
 .cons (.cdRef rfl off len) (.cons (SourceEnvironment.sourceWord s)
  (.cons (SourceEnvironment.sourceWord e) (.cons (SourceEnvironment.sourceWord u)
   (.cons (SourceEnvironment.sourceWord v) (.cons (SourceEnvironment.sourceWord t) (older q m w))))))
def first : RExpr E context (.bytes .calldata) := .slice (.local .here) rfl (.local (.there .here)) rfl (.local (.there (.there .here))) rfl false
def second : RExpr E context (.bytes .calldata) := .slice first rfl (.local (.there (.there (.there .here)))) rfl (.const (Q.ofInt 0)) zero_isIndex true
def third : RExpr E context (.bytes .calldata) := .slice second rfl (.local (.there (.there (.there (.there .here))))) rfl (.local (.there (.there (.there (.there (.there .here)))))) rfl false
theorem checked (off len : Nat) (s e u v t : Roadmap.Word) (q m : Nat) (w : Roadmap.Word)
 (order : s.val≤e.val) (bound : e.val≤len) (fromBound : u.val≤e.val-s.val)
 (order2 : v.val≤t.val) (bound2 : t.val≤e.val-s.val-u.val) :
 Checked (locals off len s e u v t q m w) third 4 (off+s.val+u.val+v.val) (t.val-v.val) :=
 .range (.from (.range (.local .here off len rfl) (.there .here) (.there (.there .here)) s e rfl rfl order bound)
  (.there (.there (.there .here))) u rfl fromBound) (.there (.there (.there (.there .here)))) (.there (.there (.there (.there (.there .here))))) v t rfl rfl order2 bound2
def tail : RArgs E context types := .cons (.local (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.local (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.local (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil))
theorem lookups (off len : Nat) (s e u v t : Roadmap.Word) (q m : Nat) (w : Roadmap.Word) :
 LiteralFailureMixedExpression.LocalArgs (locals off len s e u v t q m w) tail (values q m w) :=
 .cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil))
def expression : RExpr E context (.bytes .memory) := .abiEncode .encode (.cons third tail)
def packet (data : Roadmap.Bytes) (off : Nat) (s u v t : Roadmap.Word) (q m : Nat) (w : Roadmap.Word) :=
 AbiEntry.encodeArgs (LiteralFailureCalldataPrefixControls.encoded data (off+s.val+u.val+v.val) (t.val-v.val) q m w)

theorem actual (p : Roadmap.Pipeline) (data text : Roadmap.Bytes) (off len : Nat)
 (s e u v t : Roadmap.Word) (q m : Nat) (w : Roadmap.Word)
 (order : s.val≤e.val) (bound : e.val≤len) (fromBound : u.val≤e.val-s.val)
 (order2 : v.val≤t.val) (bound2 : t.val≤e.val-s.val-u.val) :
 (evalE (global p) (frame data) 8 expression).run (locals off len s e u v t q m w,state text)=
 (.ok (.val (.memRef rfl 3)),(locals off len s e u v t q m w,SourceKeccak.afterLiteral (state text) (packet data off s u v t q m w))) :=
 encode_run (global p) (frame data) 6 (state text)
 (checked off len s e u v t q m w order bound fromBound order2 bound2) (by decide +kernel) (by decide +kernel)
 (lookups off len s e u v t q m w) (LiteralFailureSliceEncodingControls.fields data text q m w)

def effectTail : RArgs E context [.bytes .memory] := .cons (.abiEncode .encode .nil) .nil
def badFrom : RExpr E context (.bytes .memory) := .abiEncode .encode (.cons (.slice third rfl (.local (.there (.there (.there (.there (.there .here)))))) rfl (.const (Q.ofInt 0)) zero_isIndex true) effectTail)
def badRange : RExpr E context (.bytes .memory) := .abiEncode .encode (.cons (.slice third rfl (.local (.there (.there (.there (.there .here))))) rfl (.local (.there (.there (.there (.there (.there .here)))))) rfl false) effectTail)
theorem from_failure (p : Roadmap.Pipeline) (data text : Roadmap.Bytes) (off len : Nat)
 (s e u v t : Roadmap.Word) (q m : Nat) (w : Roadmap.Word)
 (order : s.val≤e.val) (bound : e.val≤len) (fromBound : u.val≤e.val-s.val)
 (order2 : v.val≤t.val) (bound2 : t.val≤e.val-s.val-u.val) (wrong : t.val-v.val<t.val) :
 (evalE (global p) (frame data) 8 badFrom).run (locals off len s e u v t q m w,state text)=
 (.error (.revert []),(locals off len s e u v t q m w,state text)) :=
 encode_from_revert (global p) (frame data) 5 (state text)
 (checked off len s e u v t q m w order bound fromBound order2 bound2) (by decide +kernel)
 (.there (.there (.there (.there (.there .here))))) t rfl wrong effectTail
theorem range_failure (p : Roadmap.Pipeline) (data text : Roadmap.Bytes) (off len : Nat)
 (s e u v t : Roadmap.Word) (q m : Nat) (w : Roadmap.Word)
 (order : s.val≤e.val) (bound : e.val≤len) (fromBound : u.val≤e.val-s.val)
 (order2 : v.val≤t.val) (bound2 : t.val≤e.val-s.val-u.val) (wrong : t.val-v.val<t.val) :
 (evalE (global p) (frame data) 8 badRange).run (locals off len s e u v t q m w,state text)=
 (.error (.revert []),(locals off len s e u v t q m w,state text)) :=
 encode_range_revert (global p) (frame data) 5 (state text)
 (checked off len s e u v t q m w order bound fromBound order2 bound2) (by decide +kernel)
 (.there (.there (.there (.there .here)))) (.there (.there (.there (.there (.there .here))))) v t rfl rfl (.inr wrong) effectTail
theorem effect_tail_allocates :
 ((evalArgs (global .legacy) (frame []) 4 effectTail).run
  (locals 0 0 (word 0) (word 0) (word 0) (word 0) (word 0) 0 0 (word 0),state [])).2.2.heap.next=4 := rfl

theorem timeout (data text : Roadmap.Bytes) :
 (evalE (global .legacy) (frame data) 3 third).run (locals 0 4 (word 0) (word 4) (word 0) (word 0) (word 4) 0 0 (word 300),state text)=
 (.error .timeout,(locals 0 4 (word 0) (word 4) (word 0) (word 0) (word 4) 0 0 (word 300),state text)) := rfl

def render := LiteralFailureCalldataCopyControls.render
def observe (p : Roadmap.Pipeline) (mode : Nat) (data : Roadmap.Bytes) (off len : Nat)
 (s e u v t : Roadmap.Word) (q m : Nat) (w : Roadmap.Word) : String :=
 match (evalE (global p) (frame data) 8 (if mode=0 then expression else if mode=1 then badFrom else badRange)).run
  (locals off len s e u v t q m w,state [0,255]) with
 | (.ok (.val (.memRef _ address)),(_,after)) =>
  match after.heap.get address with
  | some ⟨.bytes .memory,.bytes bs⟩ => "{\"pointer\":"++toString address++",\"cursor\":"++toString after.heap.next++",\"bytes\":"++render bs++"}"
  | _ => "null"
 | (.error (.revert bs),(_,after)) => "{\"revert\":"++render bs++",\"cursor\":"++toString after.heap.next++"}"
 | _ => "null"
def suite (p : Roadmap.Pipeline) := "["++String.intercalate "," [
 observe p 0 [] 0 0 (word 0) (word 0) (word 0) (word 0) (word 0) 0 0 (word 0),
 observe p 0 [9,10,20,30,40,50] 1 5 (word 1) (word 5) (word 1) (word 1) (word 2) 4 1 (word 300),
 observe p 0 ([0]++List.replicate 31 255++[0]++List.replicate 33 128) 0 66 (word 0) (word 66) (word 1) (word 31) (word 64) 32 33 (word (2^256-1)),
 observe p 0 [0,255,128] 1 100 (word 1) (word 100) (word 1) (word 0) (word 33) 99 31 (word (2^255)),
 observe p 0 ([0]++List.replicate 32 0++[255]) 0 34 (word 0) (word 34) (word 1) (word 0) (word 32) 32 2 (word 42),
 observe p 1 [9,10,20,30,40,50] 1 5 (word 1) (word 5) (word 1) (word 1) (word 2) 4 1 (word 300),
 observe p 2 [9,10,20,30,40,50] 1 5 (word 1) (word 5) (word 1) (word 1) (word 2) 4 1 (word 300)]++"]"
#eval "SLICE_CHAIN_LEGACY="++suite .legacy
#eval "SLICE_CHAIN_VIAIR="++suite .viaIR
#print axioms height_positive
#print axioms run
#print axioms arguments_run
#print axioms encode_run
#print axioms range_revert
#print axioms from_revert
#print axioms encode_from_revert
#print axioms encode_range_revert
#print axioms checked
#print axioms lookups
#print axioms actual
#print axioms from_failure
#print axioms range_failure
#print axioms effect_tail_allocates
#print axioms timeout
end Solidity.Lowering.V08.LiteralFailureSliceChainControls
