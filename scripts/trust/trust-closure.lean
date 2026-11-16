import Solidity.Theorems
import Lean

/-! Statement-type trust closure. Guards against reporting only direct imports
or including theorem proof bodies as trusted definitions. Definition bodies,
mutual inductive constructors and recursor blocks are followed explicitly. -/
open Lean Meta Elab Command

private def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!.toString
  | none => "<current>"

private def dependencies (c : ConstantInfo) : MetaM (List Name × Bool) := do
  let proofValue ← isProp c.type
  let mut out := c.type.getUsedConstants.toList
  match c with
  | .thmInfo _ => pure ()
  | .defnInfo v => unless proofValue do out := v.value.getUsedConstants.toList ++ out
  | .opaqueInfo v => unless proofValue do out := v.value.getUsedConstants.toList ++ out
  | .inductInfo v => out := v.all ++ v.ctors ++ out
  | .ctorInfo v => out := v.induct :: out
  | .recInfo v =>
    out := v.all ++ out
    for rule in v.rules do out := rule.rhs.getUsedConstants.toList ++ out
  | _ => pure ()
  return (out, proofValue)

private def controlHidden : Nat := 7
private def controlDefinition : Nat := controlHidden
private theorem controlProof : True := (fun _ : Nat => True.intro) controlHidden
private opaque controlOpaqueProof : True := (fun _ : Nat => True.intro) controlHidden
private inductive ControlBlock where
  | node : Nat → ControlBlock

private theorem controlOuter : True := by
  exact (fun _ : Nat => True.intro) semantic
where
  semantic : Nat := 7

-- A theorem can own executable source needed by another statement. The
-- ceiling bookkeeping control preserves these lines inside an enclosing proof.
run_elab do
  let helper ← getConstInfo ``controlOuter.semantic
  if ← isProp helper.type then throwError "where auxiliary control is not executable"
  let (deps, _) ← dependencies (← getConstInfo ``controlOuter)
  if deps.contains ``controlOuter.semantic then throwError "proof body entered declaration closure"

-- Regression controls exercise the actual traversal, not a source-text proxy.
run_elab do
  for (n, expected) in [(``controlDefinition, true), (``controlProof, false),
      (``controlOpaqueProof, false)] do
    let info ← getConstInfo n
    let (deps, _) ← dependencies info
    unless deps.contains ``controlHidden == expected do
      throwError "definition/proof closure control failed: {n}"
  let (deps, _) ← dependencies (← getConstInfo ``ControlBlock)
  unless deps.contains ``ControlBlock.node do throwError "inductive constructor omitted"

run_elab do
  let env ← getEnv
  let roots := env.constants.toList.filterMap fun (n, c) =>
    if moduleOf env n == "Solidity.Theorems" && (c matches .thmInfo _) then some n else none
  if roots.isEmpty then throwError "empty statements page"
  for n in roots do
    let axioms ← collectAxioms n
    for a in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "disallowed headline axiom {a} in {n}"
    logInfo m!"TRUST_AXIOMS {n}: {axioms}"
  let mut pending : List Name := roots
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  let mut missingModules : Std.HashSet String := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some c := env.find? n | throwError "unknown closure constant {n}"
    let (deps, proofValue) ← dependencies c
    pending := deps ++ pending
    -- Generated match/recursion auxiliaries share their source owner's span.
    -- Never silently assign zero lines to a missing declaration range.
    let mut owner := n
    let mut ranges ← findDeclarationRangesCore? owner
    while ranges.isNone && !owner.isAnonymous do
      owner := owner.getPrefix
      if moduleOf env owner == moduleOf env n then
        ranges ← findDeclarationRangesCore? owner
    if ranges.isNone then missingModules := missingModules.insert (moduleOf env n)
    let mut statementOnly := proofValue && (c.value? true).isSome
    if let some ownerInfo := env.find? owner then
      let ownerProof ← isProp ownerInfo.type
      statementOnly := ownerProof && (ownerInfo.value? true).isSome
    let ownerRanges := ranges
    let nonProofOwnerFallback := !proofValue && statementOnly
    if nonProofOwnerFallback then
      -- A generated default's proof-valued projection owner does not locate
      -- the default's executable syntax. H420 uses an explicit module ceiling.
      ranges := none
      statementOnly := false
      missingModules := missingModules.insert (moduleOf env n)
    rows := rows.push <| Json.mkObj [
      ("name", toJson n.toString), ("module", toJson (moduleOf env n)),
      ("theorem", toJson (proofValue && (c.value? true).isSome)),
      ("sourceOwner", toJson owner.toString), ("statementOnly", toJson statementOnly),
      ("nonProofOwnerFallback", toJson nonProofOwnerFallback),
      ("ownerStart", toJson (ownerRanges.map (·.range.pos.line))),
      ("ownerEnd", toJson (ownerRanges.map (·.range.endPos.line))),
      ("start", toJson (ranges.map (·.range.pos.line))),
      ("end", toJson (ranges.map (·.range.endPos.line)))]
  -- H420: source ceilings need all source theorem bodies removed, including
  -- proofs outside the headline closure. Generated proofs with no independent
  -- source command are reconciled through the compiled source index in JS.
  let mut ceilingProofs : Array Json := #[]
  for (n, info) in env.constants.toList do
    let module := moduleOf env n
    unless missingModules.contains module do continue
    unless (info.value? true).isSome do continue
    unless ← isProp info.type do continue
    let ranges ← findDeclarationRangesCore? n
    ceilingProofs := ceilingProofs.push <| Json.mkObj [
      ("name", toJson n.toString), ("module", toJson module),
      ("start", toJson (ranges.map (·.range.pos.line))),
      ("end", toJson (ranges.map (·.range.endPos.line)))]
  liftM <| IO.println <| "TRUST_CLOSURE_JSON=" ++ (Json.mkObj [
    ("schema", toJson (1 : Nat)), ("roots", toJson (roots.map Name.toString)),
    ("declarations", Json.arr rows), ("ceilingProofs", Json.arr ceilingProofs)]).compress
