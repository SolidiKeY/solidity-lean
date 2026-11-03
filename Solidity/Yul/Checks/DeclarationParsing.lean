import Solidity.Yul.DeclarationParse
set_option Elab.async false
namespace Solidity.Yul.Checks.DeclarationParsing
open Solidity.Frontend.Checked

def namedBlock (body : String) : Bool :=
  (parseDeclarationAssembly [] []
    (ascii ("assembly (\"memory-safe\") { " ++ body ++ " }"))).isSome

example : namedBlock "function twice(a)->r {for {let i:=0} i {i:=sub(i,1)} {r:=add(r,2)}} let a:=3" =
    true := by decide +kernel
example : namedBlock "let a:=3 function twice(a)->r {r:=add(a,a)}" = false := by decide +kernel
example : namedBlock "let later:=3 function later(){}" = false := by decide +kernel
example : namedBlock "for {let i:=0} 0 {let phase:=1} {let phase:=2} let i:=7" =
    true := by decide +kernel
example : namedBlock "function this(){}" = false := by decide +kernel
example : namedBlock "for {let i:=0} 0 {} {let i:=1}" = false := by decide +kernel
example : namedBlock "function bad(" = false := by decide +kernel

/-- Name checking alone deliberately does not claim expression/control/flag
admission. These boundaries must remain visible to the later typed importer. -/
example : namedBlock "let self:=self" = true := by decide +kernel
example : namedBlock "break" = true := by decide +kernel
example : (parseDeclarationAssembly [] []
    (ascii "assembly { let a:=7 }")).isSome = true := by decide +kernel
example : (parseDeclarationAssembly ["x"] []
    (ascii "assembly (\"memory-safe\") { let x:=7 }")).isSome = false := by decide +kernel
example : (parseDeclarationAssembly ["x"] []
    (ascii "assembly (\"memory-safe\") { function helper(x)->r {r:=x} }")).isSome = true := by decide +kernel

theorem parsed_combination_inhabited :
    Nonempty (DeclarationAssembly [] []
      (ascii "assembly (\"memory-safe\") { function twice(a)->r {for {let i:=0} i {i:=sub(i,1)} {r:=add(r,2)}} let a:=3 }")) :=
  (parseDeclarationAssembly_iff _ _ _).mp (by decide +kernel)

end Solidity.Yul.Checks.DeclarationParsing
