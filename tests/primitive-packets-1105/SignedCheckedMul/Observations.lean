import Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls
namespace Solidity.Backend.PrimitivePackets.SignedCheckedMul.Observations
open Evm Evm.Memory Controls Source.SemanticsExamples

def pairs : List (PrimTy.int.Denote × PrimTy.int.Denote) :=
 [(negSeven,nine),(nine,negSeven),(negSeven,negNine),(minimum,minus),(minus,minimum),
 (maximum,two),(minimum,minimum),(minimum,two),(two,minimum),(maximum,negNine),
 (minimum,one),(one,minimum),(maximum,minus),(minus,maximum),(minimum,zero),(zero,minimum)]
def word : Word → String | .val v=>toString v.val | .slot _=>"slot"
def bytes (bs : List UInt8) := "["++String.intercalate "," (bs.map (fun b=>toString b.toNat))++"]"
def row (p : Roadmap.Pipeline) (a b : PrimTy.int.Denote) :=
 let s := SignedDiv.Controls.source a b
 let sr := (Source.evalE (G0 p) {F0 with checked:=true} 3
  (.binary .mul (.local .here) (.local (.there .here)))).run s
 let sourceResult := match sr.1 with
  | .ok (.val v)=>"ok:"++reprStr v.key
  | .error (.revert bs)=>"panic:"++bytes bs
  | _=>"unexpected"
 let tr := run (selected (C:=SignedDiv.Controls.P) 0 SignedDiv.Controls.F
  (.here : Idx SignedDiv.Controls.Γ (.val .int)) (.there .here)).code
  {SignedDiv.Controls.machine a b with stack:=[w[77],w[88]]}
 let targetResult := match tr with
  | .ok m skip=>"ok:"++reprStr (m.stack.map word)++";skip:"++toString skip++
    ";cells:"++reprStr ([0,1,2,3,4,5,16,17,18,20,21].map (fun c=>word (m.mem c)))
  | .revert=>"coarse-revert"
  | .fault=>"fault"
 "pipeline="++(if p=.legacy then "legacy" else "viaIR")++";a="++toString a.val++
 ";b="++toString b.val++";source="++sourceResult++";target="++targetResult
#eval IO.println ("SIGNED_CHECKED_MUL\n"++String.intercalate "\n"
 (pairs.flatMap (fun ab=>[Roadmap.Pipeline.legacy,.viaIR].map (fun p=>row p ab.1 ab.2))))
end Solidity.Backend.PrimitivePackets.SignedCheckedMul.Observations
