#!/usr/bin/env python3
"""Generate kernel controls plus differential observations; never register roots."""
import argparse
from pathlib import Path
EXAMPLES=[
 'hashMember? "#keccak256" = some .keccak',
 'hashMember? "#sha256" = some .sha256',
 'hashMember? "#ripemd160" = some .ripemd160',
 'hashMember? "#ecrecover" = some .ecrecover',
 'hashMember? "keccak256" = none',
 'hashMember? "#α" = none',
 'hashMember? "" = none',
 'fnParts? "function()" = some ([], [], false)',
 'fnParts? "function(uint,bool)externalreturns(address)" = some (["uint","bool"], ["address"], true)',
 'fnParts? "function(function(uint,bool)returns(uint),uint[2])returns(bool)" = some (["function(uint,bool)returns(uint)","uint[2]"], ["bool"], false)',
 'fnParts? "function(α,β[])returns(γ)" = some (["α","β[]"], ["γ"], false)',
 'fnParts? "function(uint" = none',
 'fnParts? "function()garbage" = none',
 'fnParts? "function()returns(uint" = none',
 'fnParts? "function()returns()" = some ([], [], false)',
 'splitTopCommas "" = []',
 'splitTopCommas "α,(uint,bool),uint[2]" = ["α","(uint,bool)","uint[2]"]',
 'shapeUnder [("α[]",8),("α#function(uint)",1),("αβ",2),("α",3)] "α" = [("[]",8),("#function(uint)",1)]',
 'fnRow? [("α#function(uint)",0)] "α" = some "function(uint)"',
 'hexBytes? "00_ab_FF" = some [0,171,255]',
 'hexBytes? "0" = none',
 'hexBytes? "αβ" = none',
]
OBS = r'''
def migrationObservations : List (String × String) :=
  [("canonNested", canonFnTy [] "function(uint256[]memory,function(address)returns(uint256))externalreturns(int256)"),
   ("canonEnum", canonFnTy ["E"] "function(E[]storage,E)returns(uint256)"),
   ("abiTuple", abiFnType "(uint,int,address,bytes32[])"),
   ("abiFunction", abiFnType "function(uint,int[])externalreturns(address)"),
   ("refNarrow", reprStr (fnRefElem? (default : Contract) "uint8[]memory")),
   ("refStorage", reprStr (fnRefElem? (default : Contract) "bytes2[]storage")),
   ("refByteReject", reprStr (fnRefElem? (default : Contract) "bytes1[]memory")),
   ("refFunctionReject", reprStr (fnRefElem? (default : Contract) "function(uint)[]memory")),
   ("refStructReject", reprStr (fnRefStruct? (default : Contract) "Unknownmemory")),
   ("unicodeParts", reprStr (fnParts? "function(α,β[])returns(γ)")),
   ("shape", reprStr (shapeUnder [("α[]",8),("α#function(uint)",1),("αβ",2)] "α")),
   ("trim", reprStr (([" \tα\r\n", "α\nβ", " α ", "\t\r\n"] : List String).map fun s => TRIM_EXPR))]
#eval show IO Unit from do
  let some path ← IO.getEnv "SYNTAX_OBSERVATIONS" | throw (IO.userError "SYNTAX_OBSERVATIONS required")
  IO.FS.writeFile path (Lean.Json.mkObj (migrationObservations.map fun (n,s) => (n,Lean.Json.str s))).compress
'''
if __name__=="__main__":
 p=argparse.ArgumentParser();p.add_argument("--new",action="store_true");p.add_argument("--output",type=Path,required=True);a=p.parse_args()
 text="import Solidity.Syntax.Elab.Values\nopen Solidity\n"
 if a.new:
  text += "example (s : String) (n : Nat) : (s.drop n).copy.toList = s.toList.drop n := String.toList_copy_drop\n"
  text += "example (s : String) (n : Nat) : (s.dropEnd n).copy.toList = s.toList.take (s.toList.length - n) := String.toList_copy_dropEnd\n"
 if a.new:
  text += "\n".join("example : "+e+" := by decide +kernel" for e in EXAMPLES)+"\n"
 else:
  text += "def baselineChecks : List Bool := ["+",\n".join("decide ("+e+")" for e in EXAMPLES)+"]\n"
  text += '#eval show IO Unit from do\n  unless baselineChecks.all id do throw (IO.userError "baseline compatibility case failed")\n  IO.println "22 baseline runtime compatibility cases pass (not proof certificates)"\n'
 text += OBS.replace("TRIM_EXPR","s.trimAscii.copy" if a.new else "s.trim")
 a.output.write_text(text)
