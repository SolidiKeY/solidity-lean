import Solidity.SolcValidation.IrHex
open Solidity.SolcValidation.IrSyntax
namespace HexControls
private def wrap (body : String) : String := "object \"A\" { code { " ++ body ++ " } }"
private def accepted (s : String) : Bool := (parse s).toOption.isSome
-- Full parser cases: these were refused before the literal importer extension.
example : accepted (wrap "let x := hex\"\"") = true := rfl
example : accepted (wrap "let x := hex\"00ff\"") = true := rfl
example : accepted (wrap "pop(hex\"0123\")") = true := rfl
example : accepted (wrap "switch hex\"01\" case hex\"02\" {} default {}") = true := rfl
example : accepted (wrap "switch 0 case hex\"61\" {} case \"a\" {}") = false := rfl
example : accepted (wrap "let x := hex\"0\"") = false := rfl
example : accepted (wrap "let x := hex\"gg\"") = false := rfl
example : accepted (wrap "pop(hex\"01\", 0)") = false := rfl
example : accepted (wrap "let x := datasize(hex\"00\")") = false := rfl
example : accepted (wrap ("let x := hex\"" ++ String.mk (List.replicate 64 'f') ++ "\"")) = true := by decide
example : accepted (wrap ("let x := hex\"" ++ String.mk (List.replicate 66 '0') ++ "\"")) = false := by decide
example : accepted ("object \"A\" { code {} data \"d\" hex\"" ++ String.mk (List.replicate 66 '0') ++ "\" }") = true := by decide
-- Actual word values distinguish byte order and leading zeroes.
example : ((LitTok.hex [0x12, 0x34]).decode.map Fin.val) = some (0x1234 * 256^30) := by decide
example : ((LitTok.hex [0, 0xff]).decode.map Fin.val) = some (0xff * 256^30) := by decide
example : ((LitTok.hex []).decode.map Fin.val) = some 0 := rfl
example : (LitTok.hex (List.replicate 33 0)).decode = none := rfl
example : ((LitTok.hex (List.replicate 32 0xff)).decode.map Fin.val) = some (2^256-1) := by decide
example : (parse (wrap "let x := hex\"00ff\"")).toOption.map (fun p => p.tokens) =
    lex (wrap "let x := hex\"00ff\"") := rfl
#check @hex_decode
#check @hex_string_decode
#check @hex_too_long
#check @eval_hex
end HexControls
