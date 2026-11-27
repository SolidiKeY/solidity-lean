import Solidity.SolcValidation.IrParse

/-! Literal and lexer boundary controls for the frozen solc validator inventory.
All inputs are inline; these checks assert reader behavior, not compiler fidelity. -/
namespace Solidity.Examples.FrontendValidation.SolcValidation
open Solidity.SolcValidation.IrSyntax

#guard hexDigit? 'F' == some 15
#guard hexDigit? 'g' == none
#guard (toByte? 255).isSome
#guard (toByte? 256).isNone
#guard (escapeByte 'n').map Fin.val == some 10
#guard (escapeByte 'q').isNone
#guard (decodeString "\\x41".toList).map (List.map Fin.val) == some [65]
#guard (decodeString "\\x4z".toList).isNone
#guard (stringWord []).isSome
#guard (stringWord (List.replicate 33 0)).isNone
#guard (LitTok.num 7).decode.isSome
#guard (LitTok.num (2 ^ 256)).decode.isNone
#guard isIdStart '$'
#guard !isIdStart '0'
#guard isIdChar '.'
#guard !isIdChar '-'
#guard lexString [] "ok\" tail".toList == some ("ok", " tail".toList)
#guard (lexString [] "unterminated".toList).isNone
#guard ((lexHex "41\"".toList []).map fun p => p.1.map Fin.val) == some [65]
#guard (lexHex "4\"".toList []).isNone
#guard dropBlock "*/tail".toList == some "tail".toList
#guard (dropBlock "missing".toList).isNone
#guard hexValue "aF".toList == some 175
#guard hexValue "ax".toList == none
#guard lexNumber '0' "x2a ".toList == some (42, " ".toList)
#guard (lexNumber '0' "1".toList).isNone
#guard (lexGo 2 "x".toList []).isSome
#guard (lexGo 0 "x".toList []).isNone
#guard (lex "{ let x := 42 }").isSome
#guard (lex "@").isNone

end Solidity.Examples.FrontendValidation.SolcValidation
