import Solidity.Calculus.Spec

/-! # Existing intrinsic obligation construction

This is a typed executable builder over the existing Contract, Raw syntax and
Fml. Producer-owned loop lowering and entry premises are supplied explicitly;
no Lean environment or syntax construction occurs. The default plain fragment
still refuses reference parameters until the source modality/input bridge lands.
Arbitrary callback values are not a source-soundness certificate.
-/
namespace Solidity.Frontend.ExecutableAst.Shared

abbrev BodyLoopLowerer :=
  List String → Nat → List RawStmt → ElabM (List RawStmt)

abbrev PlainEntryPre :=
  (C : Contract) → (Γ : NCtx) → Fml C Γ.ctx

/-- The existing direct assertion builder, with its producer dependencies explicit.
Keep reference inputs refused: closeN uses box binders for nonprimitive locals,
whereas the producer's source obligations require modality-specific binders. -/
def assertionObligation (lowerBodyLoops : BodyLoopLowerer) (callPre : PlainEntryPre)
    (C : Contract) (name : String) (box : Bool) : Except String (Fml C []) := do
  let some d := Semantics.lookupBy name C.funs | throw "missing function"
  unless d.rets.isEmpty do throw "plain return obligation"
  unless d.params.all (fun nt => nt.2 matches .prim _) do
    throw "plain reference obligation"
  let ctx ← d.paramCtx
  let (raw, st) ← (lowerBodyLoops [] 0 d.body).runFrom { funs := C.funs }
    (ctx, RawStmt.maxIdxs d.body + 1)
  let raw ← lowerReturns [] raw
  let ⟨_, program⟩ ← (elabProgAtS.go C 0 raw st (source := true)).mapError (·.2)
  let Γ := ECtx.toNCtx st.1
  let m := if box then Modality.box else .diamond
  return Fml.closeN true Γ (.imp (callPre C Γ)
    (.imp (Fml.wt C) (.modal m program .nil .tt)))

/-- One executable choice of the existing specified/plain formula builders.
The explicit callbacks must be the reviewed producer helpers at source call sites. -/
def obligation (lowerBodyLoops : BodyLoopLowerer) (callPre : PlainEntryPre)
    (C : Contract) (name : String) (specified box : Bool) :
    Except String (Fml C []) :=
  if specified then specObligation C name
  else assertionObligation lowerBodyLoops callPre C name box

end Solidity.Frontend.ExecutableAst.Shared
