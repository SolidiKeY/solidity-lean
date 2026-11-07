import tests.h62.item2.«audit-evm-compiler».JointWitness

/-! Read-only audit of literal closed equality theorem types. A successful row
reuses the original kernel-checked theorem; it creates no new proof declaration.
Non-equalities remain pending rather than inferring feasibility from syntax. -/
open Lean Meta
open Solidity.H62.EvmCompilerAudit.Tool

def checkDeclaration (target name : Name) (ci : ConstantInfo) : MetaM Json := do
  let fields := [("module", toJson target.toString), ("name", toJson name.toString),
    ("source_user_name", toJson (privateToUserName name).toString),
    ("type_expr", toJson (reprStr ci.type))]
  if !(ci.type.isAppOfArity ``Eq 3) then
    return Json.mkObj (fields ++ [("status", toJson "pending"),
      ("reason", toJson "not-a-direct-equality")])
  ensureClosedEquality ci
  let axioms ← collectAxioms name
  unless axioms.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "closed equality has nonstandard axioms"
  return Json.mkObj (fields ++ [("status", toJson "closed-equality-checked"),
    ("reduced_input_binders", toJson (0 : Nat)),
    ("axioms", toJson (axioms.map Name.toString))])

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let [namesPath, module] := args | throw (IO.userError "expected names-file and one module")
  let requested := ((← IO.FS.readFile namesPath).splitOn "\n").filter (· != "")
  let target := module.toName
  let env ← importModules #[{module := target}] {} 0
  let mut matched : Nat := 0
  for (name, ci) in env.constants.toList.mergeSort (fun a b => a.1.toString ≤ b.1.toString) do
    if let .thmInfo _ := ci then
      if requested.contains name.toString then
        unless (env.getModuleIdxFor? name).any (fun idx => env.header.moduleNames[idx.toNat]! == target) do
          throw (IO.userError "requested theorem has wrong defining module")
        let (row, _, _) ← (checkDeclaration target name ci).toIO
          {fileName := "<closed-equality-audit>", fileMap := FileMap.ofString ""}
          {env := env}
        matched := matched + 1
        IO.println row.compress
  unless matched == requested.length do
    throw (IO.userError "requested theorem identities missing or duplicated")
