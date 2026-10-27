import Solidity.Tools.Upstream
open Solidity Lean
namespace CompoundAbiShape
private def C : Contract := contract!{}
private def decoded (T : RawExpr) : RawExpr := .call "#abiDecode" [.name "data",T,.num 0,.num 1]
private def static : RawExpr := .index (.index (.name "uint16") (.num 2)) (.num 3)
private def dynamic : RawExpr := .call "#abiArrayType" [.index (.name "uint24") (.num 3)]
private def mixed : RawExpr := .call "#abiArrayType" [.index (.name "uint8[]") (.num 1)]
-- The reader is partial elaborator code, so finite metadata checks run as
-- frontend checks. They do not purport to prove interpreter equivalence.
#eval (do
  for (T,ws) in [(static,[("[][]",16)]),(dynamic,[("[][]",24)]),(mixed,[("[][][]",8)]),
      (.call "#abiArrayType" [.name "bytes2"],[("[]",16),("[]#bytes",2)]),
      (.call "#abiArrayType" [.name "address"],[("[]#address",20)]),
      (.call "#abiArrayType" [.name "int8"],[("[]",8)])] do
    unless exprShape C [] (decoded T) == ws do
      throw (IO.userError s!"compound decoder rows changed: {exprShape C [] (decoded T)}")
  for wrong in [[("[][]",8)],[("[][]#bytes",2)],[("[]",16)]] do
    if (shapeCheck C [] wrong (decoded static)).isOk then throw (IO.userError "wrong shape admitted")
  for T in [.call "#abiArrayType" [.name "uint8",.name "uint8"],.index (.name "uint8") (.name "n")] do
    unless (abiTyExpr? T).isNone do throw (IO.userError "malformed ABI type admitted")
  let shadow := {C with funs := [("#abiDecode",{params := [],body := []})]}
  unless (exprShape shadow [] (decoded static)).isEmpty do throw (IO.userError "shadowed decoder reclassified")
  if (Solidity.Tools.Upstream.ABI.shape 10 (.array .uint) [("[]#enum",1)] "").isOk then
    throw (IO.userError "nominal enum range refusal changed")
  : IO Unit)
end CompoundAbiShape
