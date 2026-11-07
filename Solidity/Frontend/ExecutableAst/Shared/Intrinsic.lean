import Solidity.Frontend.ExecutableAst.Shared.Scope

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

/-- Guards the native control-tuple regression: primitive return values must be
executed through the existing return/loop lowerers, rather than making every
returning function unknown. Return locals are fresh program declarations, not
entry binders. Width-bearing and reference declarations remain refused here;
this executable construction alone is not a source-transport theorem. -/
def primitiveReturnObligation (lowerBodyLoops : BodyLoopLowerer)
    (callPre : PlainEntryPre) (C : Contract) (d : FunDecl) (box : Bool) :
    Except String (Fml C []) := do
  unless d.rets.all (fun nt => nt.2 matches .prim _) && d.widths.isEmpty do
    throw "plain return obligation"
  unless d.params.all (fun nt => nt.2 matches .prim _) do
    throw "plain reference obligation"
  Scope.validateScopes (d.params.map (·.1) ++ d.rets.map (·.1)) d.body
  let ctx ← d.paramCtx
  let declarations : List RawStmt := d.rets.map fun (name, T) => RawStmt.decl (rawTyW [] T name) name none
  let prepare : ElabM (List String × List RawStmt) := do
    let body ← renameStmts [] (declarations ++ d.body)
    let returns : List String := (body.take d.rets.length).filterMap fun
      | .decl _ name _ => some name
      | _ => none
    let raw ← lowerBodyLoops returns returns.length body
    pure (returns, raw)
  let ((returns, raw), st) ← prepare.runFrom { funs := C.funs } (ctx, Scope.bodySeed C d)
  let raw ← lowerReturns returns raw
  let ⟨_, program⟩ ← (elabProgAtS.go C 0 raw st (source := true)).mapError (·.2)
  let Γ := ECtx.toNCtx st.1
  let m := if box then Modality.box else .diamond
  return Fml.closeN true Γ (.imp (callPre C Γ)
    (.imp (Fml.wt C) (.modal m program .nil .tt)))

/-- The existing direct assertion builder, with its producer dependencies explicit.
Keep reference inputs refused: closeN uses box binders for nonprimitive locals,
whereas the producer's source obligations require modality-specific binders. -/
def assertionObligation (lowerBodyLoops : BodyLoopLowerer) (callPre : PlainEntryPre)
    (C : Contract) (name : String) (box : Bool) : Except String (Fml C []) := do
  let some d := Semantics.lookupBy name C.funs | throw "missing function"
  if !d.rets.isEmpty then
    return ← primitiveReturnObligation lowerBodyLoops callPre C d box
  unless d.params.all (fun nt => nt.2 matches .prim _) do
    throw "plain reference obligation"
  let ctx ← d.paramCtx
  let (raw, st) ← (do
    let body ← renameStmts [] d.body
    lowerBodyLoops [] 0 body).runFrom { funs := C.funs } (ctx, Scope.bodySeed C d)
  Scope.validateScopes (d.params.map (·.1)) d.body
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
