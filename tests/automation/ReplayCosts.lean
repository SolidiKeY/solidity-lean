import Solidity.Frontend.Testing

open Solidity Solidity.Frontend Lean Elab Command Meta

namespace ReplayCosts

def leaves {C : Contract} {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) :
    Option (List (Seq.SLeaf C)) := some [⟨_, H, φ⟩]

def quoted {C : Contract} (c : Expr) (np : Option Nat) {Γ : Ctx}
    (H : Hyps C [] Γ) (φ : Fml C Γ) : Option (List Expr) :=
  some [Seq.SLeaf.quote c np H φ]

-- Keep branch refutation identical; disable only terminal leaf checks.
def residue {C : Contract} {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) :=
  (Seq.run .all leaves Seq.refuteLanded 128 H φ 128).map (·.1)

def quoteResidue {C : Contract} (c : Expr) (np : Option Nat) {Γ : Ctx}
    (H : Hyps C [] Γ) (φ : Fml C Γ) :=
  (Seq.run .all (quoted c np) Seq.refuteLanded 128 H φ 128).map (·.1)

private def certify (ty lhs rhs : Expr) : MetaM Float := do
  let equality := mkApp3 (mkConst ``Eq [1]) ty lhs rhs
  let proof := mkApp2 (mkConst ``Eq.refl [1]) ty rhs
  let start ← IO.monoNanosNow
  let name ← withOptions (Elab.async.set · false) <| mkAuxLemma [] equality proof (cache := false)
  let checked := mkConst name
  let elapsed := ((← IO.monoNanosNow)-start).toFloat/1000000
  let some name := checked.constName? | throwError "expected checked theorem"
  unless ← usesOnlyStandardAxioms name do throwError "nonstandard axiom"
  return elapsed

def stripped {C : Contract} (φ : Decide.LFml C) : Decide.LFml C :=
  φ.dropPrem (fun _ => true)

def trivial {C : Contract} (φ : Decide.LFml C) : Decide.LFml C :=
  φ.dropPrem fun P => match P with
    | @Decide.LFml.eq _ .bool a b => a.isTT && b.isTT
    | _ => false

elab "#split_replay " n:ident " to " output:str : command => do
  let ns := n.getId
  let mut results : Array Json := #[]
  for r in ← reportRows ns do
    unless r.tag == .specified do continue
    let result ← liftTermElabM <| withCurrHeartbeats do
      let C := mkConst ns
      let formula ← testFormula ns r
      let phi ← Symex.evaluable formula
      let H := mkApp2 (mkConst ``Hyps.nil) C (ctxE [])
      let np ← Seq.paramCount H phi
      let qTy := mkApp (mkConst ``Option [0]) (mkApp (mkConst ``List [0]) (mkConst ``Expr))
      let some ls ← unsafe Meta.evalExpr (Option (List Expr)) qTy
        (mkAppN (mkConst ``quoteResidue) #[C,quoteConstName ns,toExpr np,ctxE [],H,phi])
        | throwError "walk failed"
      let leafTy := mkApp (mkConst ``Seq.SLeaf) C
      let listTy := mkApp (mkConst ``List [0]) leafTy
      let resTy := mkApp (mkConst ``Option [0]) listTy
      let rhs := mkApp2 (mkConst ``Option.some [0]) listTy (← mkListLit leafTy ls)
      let walkMs ← certify resTy (mkAppN (mkConst ``residue) #[C,ctxE [],H,formula]) rhs
      let mut checks : Array Json := #[]
      for l in ls do
        let l ← whnf l
        let args := l.getAppArgs
        let Γ := args[2]!
        let pair ← whnf args[3]!
        let parts := pair.getAppArgs
        let lhs := mkAppN (mkConst ``Seq.leafCheckS) #[C,Γ,parts[2]!,parts[3]!]
        let ty := mkApp (mkConst ``Option [0]) (mkConst ``Bool)
        let value ← unsafe Meta.evalExpr (Option Bool) ty lhs
        let ms ← certify ty lhs (toExpr value)
        let wrapped ← mkAppM ``Hyps.wrap #[parts[2]!, parts[3]!]
        let lower ← mkAppM ``Fml.toLS #[toExpr true, mkApp (mkConst ``Decide.SymS.init) C, wrapped]
        let quoted ← unsafe Meta.evalExpr (Option (Expr × String))
          (mkApp (mkConst ``Option [0]) (mkApp2 (mkConst ``Prod [0,0]) (mkConst ``Expr) (mkConst ``String)))
          (mkApp3 (mkConst ``Decide.LFml.quoteOpt) C (quoteConstName ns) lower)
        let mut stages : Array (String × Json) := #[]
        if let some (reduced, printed) := quoted then
          let lty := mkApp (mkConst ``Decide.LFml) C
          let loweredMs ← certify (mkApp (mkConst ``Option [0]) lty) lower
            (mkApp2 (mkConst ``Option.some [0]) lty reduced)
          let decision ← mkAppM ``Decide.LFml.decideLift #[reduced]
          let decided ← unsafe Meta.evalExpr Bool (mkConst ``Bool) decision
          let decidedMs ← certify (mkConst ``Bool) decision (toExpr decided)
          stages := #[("loweringKernelMs",toJson loweredMs),("decisionKernelMs",toJson decidedMs),
            ("decisionResult",toJson decided),("reduced",toJson printed)]
          for (label, pass) in [("stripped", ``stripped), ("sliced", ``Decide.LFml.slice), ("trivial", ``trivial)] do
            let transformed := mkApp2 (mkConst pass) C reduced
            let some (candidate, _) ← unsafe Meta.evalExpr (Option (Expr × String))
              (mkApp (mkConst ``Option [0]) (mkApp2 (mkConst ``Prod [0,0]) (mkConst ``Expr) (mkConst ``String)))
              (mkApp3 (mkConst ``Decide.LFml.quoteOpt) C (quoteConstName ns)
                (mkApp2 (mkConst ``Option.some [0]) lty transformed)) | throwError "quote failed"
            let passMs ← certify lty transformed candidate
            let check ← mkAppM ``Decide.LFml.decideLift #[candidate]
            let passed ← unsafe Meta.evalExpr Bool (mkConst ``Bool) check
            let checkMs ← certify (mkConst ``Bool) check (toExpr passed)
            stages := stages ++ #[(label ++ "PassKernelMs",toJson passMs),
              (label ++ "DecisionKernelMs",toJson checkMs),(label ++ "Result",toJson passed)]
        checks := checks.push (Json.mkObj ([("result",toJson value),("kernelMs",toJson ms)] ++ stages.toList))
      return Json.mkObj [("function",toJson r.name),("walkAndRefutationKernelMs",toJson walkMs),
        ("leafChecks",toJson checks),("status",toJson "checked-diagnostic-components")]
    results := results.push result
    IO.eprintln ("REPLAY_SPLIT " ++ result.compress)
  IO.FS.writeFile output.getString (toJson results).pretty

end ReplayCosts
