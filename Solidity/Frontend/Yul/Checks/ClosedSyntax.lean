import Solidity.Frontend.Yul.ClosedParse
namespace Solidity.Yul.Checks.ClosedSyntax
open Solidity.Frontend.Checked

def parsed (body : String) : Bool :=
  (Solidity.Yul.ClosedSyntax.parse []
    (ascii ("assembly (\"memory-safe\") { " ++ body ++ " }"))).toOption.isSome

example : parsed "let answer:=mulDiv(7,11,3) function mulDiv(a,b,d)->r{r:=div(mul(a,b),d)}" =
    true := by decide +kernel
example : parsed "let answer:=helper() function helper()->r{r:=7}" = true := by decide +kernel
example : parsed "let x:=x" = false := by decide +kernel
example : parsed "let captured:=7 function helper()->r{r:=captured}" = false := by decide +kernel
example : parsed "for{let i:=3} i {i:=sub(i,1)}{continue}" = true := by decide +kernel
example : parsed "for{let i:=3} i {i:=sub(i,1)}{} pop(i)" = false := by decide +kernel
example : parsed "for{{function bad(){}}} 0 {}{}" = false := by decide +kernel
example : parsed "break" = false := by decide +kernel

/-- Flags are retained by the grammar certificate but NOT admitted here. -/
example : (Solidity.Yul.ClosedSyntax.parse []
    (ascii "assembly {let x:=7 pop(x)}")).toOption.isSome = true := by decide +kernel

theorem parsed_mulDiv_inhabited :
    Nonempty (Solidity.Yul.ClosedSyntax.Parsed []
      (ascii "assembly (\"memory-safe\") { let answer:=mulDiv(7,11,3) function mulDiv(a,b,d)->r{r:=div(mul(a,b),d)} }")) :=
  (Solidity.Yul.ClosedSyntax.parse_iff [] _).mp (by decide +kernel)

end Solidity.Yul.Checks.ClosedSyntax
