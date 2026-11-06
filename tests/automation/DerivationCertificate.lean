import Solidity.Frontend.Testing

open Solidity Solidity.Frontend Lean Elab Command Meta

/-! Diagnostic only: certify the computed residue, without claiming that its
remaining leaves prove the source specification. This mirrors Seq.prove's
lemmaFor rather than accepting a native decision as a proof. -/
elab "#walk_certificate " n:ident " to " output:str : command => do
  let ns := n.getId
  let rows ← reportRows ns
  let mut results : Array Json := #[]
  for r in rows do
    unless r.tag == .specified do continue
    let result ← liftTermElabM <| withCurrHeartbeats do
      let C := mkConst ns
      let R := mkConst ``RuleSet.all
      let formula ← testFormula ns r
      let phi ← Symex.evaluable formula
      let H := mkApp2 (mkConst ``Hyps.nil) C (ctxE [])
      let np ← Seq.paramCount H phi
      let qTy := mkApp (mkConst ``Option [0]) (mkApp (mkConst ``List [0]) (mkConst ``Expr))
      let start ← IO.monoNanosNow
      let some leaves ← unsafe Meta.evalExpr (Option (List Expr)) qTy
        (mkAppN (mkConst ``Seq.residueQuoteWithin)
          #[C,toExpr (128:Nat),R,quoteConstName ns,toExpr np,ctxE [],H,phi])
        | throwError "128-step walk did not produce a residue"
      let walked ← IO.monoNanosNow
      let leafTy := mkApp (mkConst ``Seq.SLeaf) C
      let listTy := mkApp (mkConst ``List [0]) leafTy
      let resTy := mkApp (mkConst ``Option [0]) listTy
      let ls ← mkListLit leafTy leaves
      let someLs := mkApp2 (mkConst ``Option.some [0]) listTy ls
      let type := mkApp3 (mkConst ``Eq [1]) resTy
        (mkAppN (mkConst ``Seq.residueWithin) #[C,toExpr (128:Nat),R,ctxE [],H,formula]) someLs
      let value := mkApp2 (mkConst ``Eq.refl [1]) resTy someLs
      let checking ← IO.monoNanosNow
      let checked ← Derive.kernelLemma type value
      let done ← IO.monoNanosNow
      let some name := checked.constName? | throwError "expected a checked auxiliary theorem"
      unless ← usesOnlyStandardAxioms name do throwError "nonstandard residue certificate"
      return Json.mkObj [("function",toJson r.name),("leaves",toJson leaves.length),
        ("compiledWalkMs",toJson ((walked-start).toFloat/1000000)),
        ("certificateAssemblyMs",toJson ((checking-walked).toFloat/1000000)),
        ("kernelCertificateMs",toJson ((done-checking).toFloat/1000000)),
        ("status",toJson "checked-residue-not-program-proof")]
    results := results.push result
    IO.eprintln ("RESIDUE_CERTIFICATE " ++ result.compress)
  IO.FS.writeFile output.getString (toJson results).pretty
