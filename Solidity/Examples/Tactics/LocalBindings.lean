import Solidity.Calculus.Notation

/-!
# Binding-local width and ABI metadata

Shadowed locals must never inherit a byte/function/reference shape from an
outer binding. Captures retain the source shape, while changing metadata
alone leaves the scoped context and formula binders unchanged.
-/

namespace Solidity.Examples.Tactics.LocalBindings

private def C : Contract := { vars := [] }

private def byteOuter : ECtx := [("x", .val .uint 24 [("#bytes", 3)])]
private def plainInner : ECtx := ("x", .val .uint) :: byteOuter

#guard localBytes? byteOuter "x" == some 3
#guard localBytes? plainInner "x" == none
#guard localBytes? plainInner.tail "x" == some 3
#guard (encodeCallArg C plainInner "bytes3" (.name "x")).toOption.isNone

private def functionOuter : ECtx :=
  [("f", .val .uint 256 [("#function(uint)returns(uint)", 0)])]
#guard localFn? functionOuter "f" == some "function(uint)returns(uint)"
#guard localFn? (("f", .val .uint) :: functionOuter) "f" == none

private def narrowOuter : ECtx := [("xs", .mem (.array .uint) [("[]", 8)])]
private def wideInner : ECtx := ("xs", .mem (.array .uint)) :: narrowOuter
#guard localShape wideInner "xs" == []
#guard (shapeCheck C wideInner [("[]", 8)] (.name "xs")).toOption.isNone
#guard (shapeCheck C narrowOuter [("[]", 8)] (.name "xs")).isOk

-- Attaching an empty shape must clear metadata, without adding a local.
#guard (narrowOuter.setShape "xs" []).toOption == some [("xs", .mem (.array .uint))]
#guard (wideInner.setShape "xs" [("[]", 16)]).toOption ==
  some (("xs", .mem (.array .uint) [("[]", 16)]) :: narrowOuter)
#guard (ECtx.setShape "xs" [("[]", 8)] []).toOption.isNone

-- The capture is one real binding, carrying the source's shape itself.
#guard (ElabM.runFrom (do
    let x ← captureRef C "mv" (.mem (.array .uint)) (.name "xs")
    let Γ ← ctx
    pure (Γ.length == 2 && localShape Γ (toString x) == [("[]", 8)]))
  { funs := [] } (narrowOuter, 1)).toOption.map Prod.fst == some true

-- Metadata changes do not introduce formula binders or alter typed positions.
#guard newBinders [("x", .val .uint)] byteOuter == []
#guard (newBinders [] byteOuter).map Prod.snd == [.val .uint]
#guard byteOuter.toNCtx.length == byteOuter.length

-- Parallel update typing refines a binding; it must retain the target's shape.
#guard ((elabUpd C narrowOuter [.assign "xs" (.name "xs")]).toOption.map
  (fun (_, Γ) => localShape Γ "xs")) == some [("[]", 8)]
#guard ((elabUpd C [("xs", .alias (.array .uint) [("[]", 8)])]
  [.assign "xs" (.name "xs")]).toOption.map
  (fun (_, Γ) => localShape Γ "xs")) == some [("[]", 8)]
#guard ((elabUpd C [("text", .mem (.array .uint) (dynBytesRowsOf "string"))]
  [.assign "text" (.name "text")]).toOption.map
  (fun (_, Γ) => localShape Γ "text")) == some (dynBytesRowsOf "string")

-- A modality after the update must still reject a value outside uint8.
#guard (do
  let (_, Γ) ← elabUpd C narrowOuter [.assign "xs" (.name "xs")]
  pure (ElabM.runFrom' (elabStmtsP C
    [.assign (.index (.name "xs") (.num 0)) (.num 256)])
    { funs := [] } (Γ, 1)).toOption.isNone).toOption == some true

-- Only the core scoped type determines whether another binder is needed.
#guard newBinders [("x", .val .uint 256)] [("x", .val .uint 8)] == []

end Solidity.Examples.Tactics.LocalBindings
