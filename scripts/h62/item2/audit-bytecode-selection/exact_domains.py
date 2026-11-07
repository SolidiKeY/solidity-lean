#!/usr/bin/env python3
"""Guard against replacing joint kernel-binder domains with copied signatures.

Render proof-specific witnesses using the existing pinned hypothesis elaborator.
This is not a census, an inspection-acceptance gate or a witness-ledger linker.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

from census import BASE, MAP, mask, mapped_references

MACRO_PATH = "tests/h62/item2/audit-bytecode-selection/HypothesisDomains.lean"
FIXTURE_PATH = "tests/h62/item2/audit-bytecode-selection/exact-gate-domains.txt"
NAMESPACE = "Solidity.H62.BytecodeSelection.HypothesisAudit"
MACRO_SHA256 = "27ba183e9fc5db42bf9e4733d31ce7f988cbc564db4a5b7ded7405b239a1ebe6"
TARGETS = {
    "head_certificate_executed_domain": "Solidity.Backend.AbiEntry.Interface.HeadGateCertificate.executed",
    "word_certificate_executed_domain": "Solidity.Backend.AbiEntry.Interface.WordGateCertificate.executed",
    "word_correspondence_domain": "Solidity.Backend.AbiEntry.WordGate.correspondence",
    "head_semantic_rejection_domain": "Solidity.Backend.AbiEntry.HeadGate.semantic_rejection",
}
# Explicit public-method slice; private helpers and other modules remain out of this renderer.
for gate, prefix in (("HeadGate", "head"), ("WordGate", "word")):
    for method in ("admitted", "selected", "run_program", "executed", "rejected_iff"):
        TARGETS[prefix + "_" + method + "_domain"] = "Solidity.Backend.AbiEntry." + gate + "." + method
    TARGETS[prefix + "_certificate_selected_domain"] = "Solidity.Backend.AbiEntry.Interface." + gate + "Certificate.selected"

for method in ("admitted", "selected", "run_program", "executed", "entry_form",
               "entry_rejection", "entry_success", "short_before_word", "insufficient_fuel"):
    TARGETS["single_" + method + "_domain"] = "Solidity.Backend.AbiEntry.SingleWordGate." + method
for field in ("selected", "executed", "entry_rejection"):
    TARGETS["single_certificate_" + field + "_domain"] = "Solidity.Backend.AbiEntry.Interface.SingleWordGateCertificate." + field

for method in ("admitted", "selected", "code", "run_program", "executed", "entry_rejection",
               "validated_word", "decoded_and_bound", "short_before_word"):
    TARGETS["binding_" + method + "_domain"] = "Solidity.Backend.AbiEntry.BoolBinding." + method
for field in ("selected", "executed", "entry_rejection"):
    TARGETS["binding_certificate_" + field + "_domain"] = "Solidity.Backend.AbiEntry.Interface.BoolBindingCertificate." + field

for gate, prefix, methods in (
    ("UnsignedGate", "unsigned", ("admitted", "selected", "condition_code", "run_program", "executed", "rejected_iff", "enum_rejection", "uint_rejection", "bool_rejection", "enum_correspondence", "uint_correspondence", "bool_correspondence")),
    ("SignedGate", "signed", ("admitted", "selected", "run_program", "executed", "rejected_iff", "correspondence")),
    ("BytesGate", "bytes", ("admitted", "selected", "run_program", "executed"))):
    for method in methods:
        TARGETS[prefix + "_" + method + "_domain"] = "Solidity.Backend.AbiEntry." + gate + "." + method
    for field in ("selected", "executed"):
        TARGETS[prefix + "_certificate_" + field + "_domain"] = "Solidity.Backend.AbiEntry.Interface." + gate + "Certificate." + field

for field in ("correct", "capacity"):
    TARGETS["tail_inherited_" + field + "_domain"] = "Solidity.Backend.AbiEntry.Interface.TailGuardCertificate." + field

for field in ("raw", "reference"):
    TARGETS["raw_tail_" + field + "_domain"] = "Solidity.Backend.AbiEntry.Interface.RawTailGuardCertificate." + field

for method in ("correct", "capacity", "reference"):
    TARGETS["tail_method_" + method + "_domain"] = "Solidity.Backend.AbiEntry.TailGuard." + method
for method in ("raw", "reference"):
    TARGETS["raw_tail_method_" + method + "_domain"] = "Solidity.Backend.AbiEntry.RawTailGuard." + method

for method in ("correct", "capacity", "lazy_revert", "eager_bytes_panic", "eager_array_panic"):
    TARGETS["length_method_" + method + "_domain"] = "Solidity.Backend.AbiEntry.LengthCheck." + method
for field in ("correct", "capacity", "lazy_revert"):
    TARGETS["length_certificate_" + field + "_domain"] = "Solidity.Backend.AbiEntry.Interface.LengthCheckCertificate." + field

for method in ("tail_raw", "region_raw", "tail_correct", "region_correct", "tail_capacity", "region_capacity"):
    TARGETS["offset_method_" + method + "_domain"] = "Solidity.Backend.AbiEntry.OffsetChecks." + method
for field in ("tail_correct", "region_correct", "tail_capacity", "region_capacity"):
    TARGETS["offset_certificate_" + field + "_domain"] = "Solidity.Backend.AbiEntry.Interface.OffsetChecksCertificate." + field

for method in ("correct", "capacity", "classified", "early_revert"):
    TARGETS["head_check_method_" + method + "_domain"] = "Solidity.Backend.AbiEntry.HeadCheck." + method
for field in ("correct", "capacity", "classified", "early_revert"):
    TARGETS["head_check_certificate_" + field + "_domain"] = "Solidity.Backend.AbiEntry.Interface.HeadCheckCertificate." + field


PRODUCERS = ["Solidity/Backend/AbiEntry/" + name + ".lean" for name in
             ("HeadGate", "HeadGateInterface", "WordGate", "WordGateInterface", "SingleWordGate", "SingleWordGateInterface", "BoolBinding", "BoolBindingInterface", "UnsignedGate", "UnsignedGateInterface", "SignedGate", "SignedGateInterface", "BytesGate", "BytesGateInterface", "TailGuard", "TailGuardInterface", "RawTailGuard", "RawTailGuardInterface", "TailGuardControls", "LengthCheck", "LengthCheckInterface", "LengthCheckControls", "OffsetChecks", "OffsetChecksInterface", "OffsetChecksControls", "HeadCheck", "HeadCheckInterface", "HeadCheckControls")]


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def macro_fragment(source):
    start = "namespace " + NAMESPACE + "\n"
    end = "\nprivate theorem dependentToy"
    if source.count(start) != 1 or source.count(end) != 1:
        raise ValueError("ambiguous existing elaborator boundaries")
    fragment = source[source.index(start):source.index(end)]
    if sha(fragment.encode()) != MACRO_SHA256:
        raise ValueError("existing elaborator implementation changed; review required")
    return fragment


def render(macro_source, fixture):
    found = re.findall(r"(?m)^theorem\s+(\w+)\s*:\s*hypotheses_of%\s+(\S+)\s*:=", mask(fixture))
    if len(found) != len(TARGETS) or dict(found) != TARGETS:
        raise ValueError("exact domain targets differ")
    if re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by)\b", mask(fixture)):
        raise ValueError("forbidden fixture mechanism")
    fragment = macro_fragment(macro_source)
    return ("import Lean\nimport Solidity.Backend.AbiEntry.HeadGate\n"
            "import Solidity.Backend.AbiEntry.WordGate\nimport Solidity.Backend.AbiEntry.SingleWordGate\nimport Solidity.Backend.AbiEntry.BoolBinding\nimport Solidity.Backend.AbiEntry.RawTailGuard\nimport Solidity.Backend.AbiEntry.TailGuardControls\nimport Solidity.Backend.AbiEntry.LengthCheckControls\nimport Solidity.Backend.AbiEntry.OffsetChecksControls\nimport Solidity.Backend.AbiEntry.HeadCheckControls\n\n"
            "/-! Guards omission of implicit/self/proof binders from joint hypotheses.\n"
            "Only the original conclusion is replaced by True; no census acceptance follows. -/\n"
            + fragment + "\n" + fixture + "\nend " + NAMESPACE + "\n")


def build(repo):
    repo = repo.resolve()
    macro_raw = (repo / MACRO_PATH).read_bytes()
    fixture_raw = (repo / FIXTURE_PATH).read_bytes()
    frozen_map = subprocess.check_output(["git", "show", BASE + ":" + MAP], cwd=repo)
    allowed, _ = mapped_references(frozen_map.decode())
    if set(PRODUCERS) - set(allowed):
        raise ValueError("explicit producer outside frozen mapped census: " + ", ".join(sorted(set(PRODUCERS) - set(allowed))))
    producers = {}
    for path in PRODUCERS:
        raw = (repo / path).read_bytes()
        frozen = subprocess.check_output(["git", "show", BASE + ":" + path], cwd=repo)
        if raw != frozen:
            raise ValueError("frozen producer source changed: " + path)
        producers[path] = sha(raw)
    program = render(macro_raw.decode(), fixture_raw.decode())
    manifest = {
        "schema_version": 1, "base": BASE, "targets": TARGETS,
        "scope_map_path": MAP, "scope_map_sha256": sha(frozen_map),
        "producer_scope": "All explicit producer leaves mapped; transitive imports are not assigned targets.",
        "generator_sha256": sha(Path(__file__).read_bytes()),
        "macro_source_path": MACRO_PATH, "macro_source_sha256": sha(macro_raw),
        "macro_fragment_sha256": MACRO_SHA256, "fixture_path": FIXTURE_PATH,
        "fixture_sha256": sha(fixture_raw), "producer_source_sha256": producers,
        "generated_lean_sha256": sha(program.encode()),
        "boundary": "Proof-specific binder domains only; not original conclusions, census or metadata-join acceptance.",
        "inspection_accepted": False, "witness_ledger_links_established": False,
    }
    return program, manifest


def export(repo, output):
    output = output.absolute()
    owner = Path(__file__).resolve().parents[4]
    if any(output.resolve().is_relative_to(root.resolve()) for root in (repo, owner)):
        raise ValueError("H44: generated proofs must remain outside repositories")
    if any(p.is_symlink() for p in (output, *output.parents)):
        raise ValueError("symlink output refused")
    manifest_path = output.with_suffix(".manifest.json")
    if output.exists() or manifest_path.exists():
        raise ValueError("existing output refused")
    program, manifest = build(repo)
    with output.open("x") as stream:
        stream.write(program)
    with manifest_path.open("x") as stream:
        stream.write(json.dumps(manifest, sort_keys=True, indent=2) + "\n")
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    result = export(args.repo, args.output)
    print(json.dumps({"targets": result["targets"], "inspection_accepted": False}, sort_keys=True))


if __name__ == "__main__":
    main()


CLOSED_NAMESPACE = NAMESPACE + ".Closed"
CLOSED_CHECKER = r'''
private def closedDomain (name : Lean.Name) : TermElabM Expr := do
  let info ← getConstInfo name
  unless wasOriginallyTheorem (← getEnv) name do
    throwError "closed hypothesis audit: target is not a theorem"
  unless info.levelParams.isEmpty do
    throwError "closed hypothesis audit: universe parameters require review"
  let domain ← explicitDomain info.type
  unless domain.isConstOf ``True do
    throwError "closed hypothesis audit: target has explicit binders"
  return domain

elab "closed_hypotheses_of% " id:ident : term => do
  closedDomain (← realizeGlobalConstNoOverloadWithInfo id)

elab "closed_hypotheses_named% " target:str " against% " expected:str : term => do
  let foundConstants := (← getEnv).constants.toList.filter fun p => p.1.toString == target.getString
  unless foundConstants.length == 1 do
    throwError "closed hypothesis audit: missing or ambiguous kernel name"
  let name := foundConstants.head!.1
  let info ← getConstInfo name
  unless reprStr info.type == expected.getString do
    throwError "closed hypothesis audit: recorded type differs"
  closedDomain name

-- Guard regressions: input binders, non-theorems, universe parameters, hidden
-- binders and corrupted target/type records must never become closed witnesses.
theorem boundToy (_n : Nat) : True := True.intro
def datum : Nat := 0
universe u
theorem polyToy (_t : Type u) : True := True.intro
def hidden : Prop := ∀ (_n : Nat), True
theorem hiddenToy : hidden := by intro _; exact True.intro
theorem toy : True := True.intro
/-- error: closed hypothesis audit: target has explicit binders -/
#guard_msgs in
#check closed_hypotheses_of% boundToy
/-- error: closed hypothesis audit: target is not a theorem -/
#guard_msgs in
#check closed_hypotheses_of% datum
/-- error: closed hypothesis audit: universe parameters require review -/
#guard_msgs in
#check closed_hypotheses_of% polyToy
/-- error: hypothesis audit: hidden binders under reducible result -/
#guard_msgs in
#check closed_hypotheses_of% hiddenToy
/-- error: closed hypothesis audit: missing or ambiguous kernel name -/
#guard_msgs in
#check closed_hypotheses_named% "missing.kernel.name" against% ""
'''

CLOSED_BATCH = r'''
-- Build a command-local immutable name index; each generated theorem is still
-- independently checked by the kernel with the unchanged derived domain.
declare_syntax_cat closedEntry
syntax str " => " ident " against% " str : closedEntry
elab "#closed_hypothesis_batch " "[" entries:closedEntry,* "]" : command => do
  let mut index : Std.HashMap String (List Lean.Name) := {}
  for (name, _) in (← getEnv).constants.toList do
    let key := name.toString
    index := index.insert key (name :: index.getD key [])
  for entry in entries.getElems do
    match entry with
    | `(closedEntry| $target:str => $helper:ident against% $expected:str) =>
      let found := index.getD target.getString []
      unless found.length == 1 do
        throwError "closed hypothesis audit: missing or ambiguous kernel name"
      let name := found.head!
      let info ← getConstInfo name
      unless reprStr info.type == expected.getString do
        throwError "closed hypothesis audit: recorded type differs"
      let domain ← Lean.Elab.Command.liftTermElabM (closedDomain name)
      let helperName := (← getCurrNamespace) ++ helper.getId
      Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {
        name := helperName, levelParams := [], type := domain,
        value := mkConst ``True.intro })
    | _ => throwUnsupportedSyntax
'''



def _frozen_scope(repo, modules):
    frozen_map = subprocess.check_output(["git","show",BASE+":"+MAP],cwd=repo)
    allowed = set(mapped_references(frozen_map.decode())[0])
    producer_sources = {}
    for module in modules:
        if module.startswith("Solidity."):
            path = module.replace(".","/") + ".lean"
        elif module.startswith("SolidityBridge."):
            path = "Bridge/" + module.replace(".","/") + ".lean"
        else:
            raise ValueError("closed target outside frozen mapped census")
        if path not in allowed:
            raise ValueError("closed target outside frozen mapped census")
        producer_sources[path] = sha(subprocess.check_output(["git","show",BASE+":"+path],cwd=repo))
    return frozen_map, producer_sources


def closed_render(repo, rows, source_candidate_names):
    """Reuse the pinned domain transform for observed closed source candidates.

    Python selects candidates only. Lean rechecks original theorem kind, exact
    recorded type, universes and the derived empty domain, including private
    kernel identities. No original conclusion or global census is accepted.
    """
    import kernel_metadata as metadata
    metadata.partition_records(rows, source_candidate_names)
    names = set(source_candidate_names)
    selected = sorted((r for r in rows if r["name"] in names and not r["binders"] and not r["level_params"]),key=lambda r:r["name"])
    if not selected:
        raise ValueError("no closed source candidates")
    fragment = macro_fragment((repo / MACRO_PATH).read_text())
    modules = sorted({r["module"] for r in selected})
    frozen_map, producer_sources = _frozen_scope(repo, modules)
    program = "import Lean\n" + "".join("import " + m + "\n" for m in modules)
    program += "/-! Guard nonempty or stale hypothesis domains from being credited as closed.\nOnly derived empty hypotheses are witnessed; original conclusions are unchanged. -/\n"
    program += fragment + "\nnamespace Closed\nopen Lean Meta Elab Term\n" + CLOSED_CHECKER + CLOSED_BATCH
    program += '/-- error: closed hypothesis audit: recorded type differs -/\n#guard_msgs in\n#check closed_hypotheses_named% "' + CLOSED_NAMESPACE + '.toy" against% "wrong recorded type"\n'
    program += '/-- error: closed hypothesis audit: missing or ambiguous kernel name -/\n#guard_msgs in\n#closed_hypothesis_batch ["missing.kernel.name" => reject_missing against% ""]\n'
    program += '/-- error: closed hypothesis audit: recorded type differs -/\n#guard_msgs in\n#closed_hypothesis_batch ["' + CLOSED_NAMESPACE + '.toy" => reject_type against% "wrong recorded type"]\n'
    targets = {}
    for start in range(0, len(selected), 64):
        batch = selected[start:start+64]
        program += "\n#closed_hypothesis_batch [\n"
        entries = []
        for index, row in enumerate(batch, start):
            helper = "closed_domain_" + str(index).zfill(4)
            entries.append(json.dumps(row["name"],ensure_ascii=False) + " => " + helper + " against% " + json.dumps(row["type_expr"],ensure_ascii=False))
            targets[helper] = metadata.observed_type(row)
        program += ",\n".join(entries) + "\n]\n"
        for index in range(start, start+len(batch)):
            helper = "closed_domain_" + str(index).zfill(4)
            program += "/-- info: '" + CLOSED_NAMESPACE + "." + helper + "' does not depend on any axioms -/\n#guard_msgs in\n#print axioms " + helper + "\n"
    program += "\nend Closed\nend " + NAMESPACE + "\n"
    return program, {"namespace":CLOSED_NAMESPACE,"targets":targets,"modules":modules,
        "macro_sha256":MACRO_SHA256,"generated_lean_sha256":sha(program.encode()),
        "frozen_map_sha256":sha(frozen_map),"producer_source_sha256":producer_sources,
        "kernel_accepted":False,"witness_ledger_linked":False,
        "boundary":"Candidate rendering only until native kernel/guard receipts pass; no original conclusion or full census acceptance"}


DATA_NAMESPACE = NAMESPACE + ".Defaults"
DATA_CHECKER = r'''
private partial def defaultDomainProof (goal : Lean.Expr) : MetaM (Except String Lean.Expr) := do
  let goal ← whnf goal
  if goal.isConstOf ``True then
    return .ok (mkConst ``True.intro)
  unless goal.isAppOfArity ``Exists 2 do
    return .error "unsupported derived domain shape"
  let args := goal.getAppArgs
  let alpha := args[0]!
  let predicate := args[1]!
  if ← isProp alpha then
    return .error "proof binder requires explicit witness"
  let level ← getLevel alpha
  let instanceType := mkApp (mkConst ``Inhabited [level]) alpha
  let some inhabitant ← synthInstance? instanceType
    | return .error "default instance synthesis unsupported at chosen values"
  let value ← instantiateMVars (mkAppN (mkConst ``default [level]) #[alpha,inhabitant])
  if value.hasMVar || value.hasLooseBVars then
    return .error "unresolved default inhabitant"
  match ← defaultDomainProof (mkApp predicate value) with
  | .error reason => return .error reason
  | .ok rest =>
    let proof ← mkAppOptM ``Exists.intro #[some alpha,some predicate,some value,some rest]
    let proof ← instantiateMVars proof
    if proof.hasMVar || proof.hasLooseBVars then
      return .error "unresolved dependent witness"
    return .ok proof

private def dataTarget (name : Lean.Name) : TermElabM (Lean.Expr × Except String Lean.Expr) := do
  let info ← getConstInfo name
  unless wasOriginallyTheorem (← getEnv) name do
    throwError "data hypothesis audit: target is not a theorem"
  unless info.levelParams.isEmpty do
    throwError "data hypothesis audit: universe parameters require review"
  let domain ← explicitDomain info.type
  if domain.isConstOf ``True then
    return (domain,.error "empty domain belongs to closed witness path")
  let proof ← defaultDomainProof domain
  return (← instantiateMVars domain,proof)

elab "default_domain_witness% " id:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo id
  let (_, result) ← dataTarget name
  match result with
  | .ok proof => return proof
  | .error reason => throwError "data hypothesis audit: {reason}"

-- Guard default data witnesses against proof-premise invention, unsupported
-- empty data, hidden binders, wrong kinds and accidental closed-domain credit.
theorem positiveToy (_n : Nat) (_b : Bool) : True := True.intro
theorem dependentToy (n : Nat) (_i : Fin (n+1)) : True := True.intro
theorem proofToy (n : Nat) (_positive : 0 < n) : True := True.intro
theorem emptyToy (_i : Fin 0) : True := True.intro
theorem closedToy : True := True.intro
def datum : Nat := 0
universe u
theorem polyToy (_t : Type u) : True := True.intro
def hidden : Prop := ∀ (_n : Nat), True
theorem hiddenToy : hidden := by intro _; exact True.intro

theorem positive_domain : hypotheses_of% positiveToy := default_domain_witness% positiveToy
theorem dependent_domain : hypotheses_of% dependentToy := default_domain_witness% dependentToy
theorem empty_domain_impossible : ¬ (hypotheses_of% emptyToy) := by
  intro witness
  rcases witness with ⟨value, _⟩
  exact Fin.elim0 value
/-- info: 'Solidity.H62.BytecodeSelection.HypothesisAudit.Defaults.positive_domain' does not depend on any axioms -/
#guard_msgs in
#print axioms positive_domain
/-- info: 'Solidity.H62.BytecodeSelection.HypothesisAudit.Defaults.dependent_domain' depends on axioms: [propext] -/
#guard_msgs in
#print axioms dependent_domain
/-- info: 'Solidity.H62.BytecodeSelection.HypothesisAudit.Defaults.empty_domain_impossible' does not depend on any axioms -/
#guard_msgs in
#print axioms empty_domain_impossible
/-- error: data hypothesis audit: proof binder requires explicit witness -/
#guard_msgs in
#check default_domain_witness% proofToy
/-- error: data hypothesis audit: default instance synthesis unsupported at chosen values -/
#guard_msgs in
#check default_domain_witness% emptyToy
/-- error: data hypothesis audit: empty domain belongs to closed witness path -/
#guard_msgs in
#check default_domain_witness% closedToy
/-- error: data hypothesis audit: target is not a theorem -/
#guard_msgs in
#check default_domain_witness% datum
/-- error: data hypothesis audit: universe parameters require review -/
#guard_msgs in
#check default_domain_witness% polyToy
/-- error: hypothesis audit: hidden binders under reducible result -/
#guard_msgs in
#check default_domain_witness% hiddenToy

declare_syntax_cat dataEntry
syntax str " => " ident " against% " str " expecting% " str : dataEntry
elab "#default_hypothesis_batch " "[" entries:dataEntry,* "]" : command => do
  let mut index : Std.HashMap String (List Lean.Name) := {}
  for (name, _) in (← getEnv).constants.toList do
    let key := name.toString
    index := index.insert key (name :: index.getD key [])
  for entry in entries.getElems do
    match entry with
    | `(dataEntry| $target:str => $helper:ident against% $expected:str expecting% $golden:str) =>
      let found := index.getD target.getString []
      unless found.length == 1 do
        throwError "data hypothesis audit: missing or ambiguous kernel name"
      let name := found.head!
      let info ← getConstInfo name
      unless reprStr info.type == expected.getString do
        throwError "data hypothesis audit: recorded type differs"
      let (domain, result) ← Lean.Elab.Command.liftTermElabM (dataTarget name)
      let helperName := (← getCurrNamespace) ++ helper.getId
      let (status, reason, axioms) ← match result with
        | .error reason => pure ("unsupported-default",reason,#[])
        | .ok proof => do
          Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {
            name := helperName,levelParams := [],type := domain,value := proof })
          let axioms ← collectAxioms helperName
          unless axioms.all (fun n => n == ``propext || n == ``Classical.choice || n == ``Quot.sound) do
            throwError "data hypothesis audit: unexpected axiom"
          pure ("proved","",axioms.map Lean.Name.toString)
      let record := Json.mkObj [("target",toJson target.getString),("helper",toJson helperName.toString),
        ("status",toJson status),("reason",toJson reason),("axioms",toJson axioms)]
      unless golden.getString == "probe" || golden.getString == record.compress do
        throwError "data hypothesis audit: result differs from recorded expectation"
      Lean.Elab.Command.liftCoreM <| Lean.Core.liftIOCore <| IO.println ("H62_DEFAULT_RESULT " ++ record.compress)
    | _ => throwUnsupportedSyntax
'''


DECIDABLE_PREMISE = r'''
-- The decision is reduced by Lean and the resulting proof is kernel checked.
-- False, stuck or missing decisions are unsupported, never assumed premises.
private def decidablePremiseProof (proposition : Lean.Expr) : MetaM (Except String Lean.Expr) := do
  let some decisionInstance ← synthInstance? (mkApp (mkConst ``Decidable) proposition)
    | return .error "decidable premise unsupported at chosen values"
  let decision ← whnf (mkAppN (mkConst ``Decidable.decide) #[proposition,decisionInstance])
  unless decision.isConstOf ``Bool.true do
    return .error "decidable premise unsupported at chosen values"
  let equality ← mkEqRefl (mkConst ``Bool.true)
  let proof := mkAppN (mkConst ``of_decide_eq_true) #[proposition,decisionInstance,equality]
  return .ok (← instantiateMVars proof)
'''


def decidable_checker():
    """Extend the existing domain constructor; retain its refusal/axiom checks."""
    old = '''  if ← isProp alpha then
    return .error "proof binder requires explicit witness"
  let level ← getLevel alpha
  let instanceType := mkApp (mkConst ``Inhabited [level]) alpha
  let some inhabitant ← synthInstance? instanceType
    | return .error "default instance synthesis unsupported at chosen values"
  let value ← instantiateMVars (mkAppN (mkConst ``default [level]) #[alpha,inhabitant])'''
    new = '''  let valueResult ← if ← isProp alpha then
      decidablePremiseProof alpha
    else do
      let level ← getLevel alpha
      let instanceType := mkApp (mkConst ``Inhabited [level]) alpha
      let some inhabitant ← synthInstance? instanceType
        | return .error "default instance synthesis unsupported at chosen values"
      pure (.ok (← instantiateMVars (mkAppN (mkConst ``default [level]) #[alpha,inhabitant])))
  let value ← match valueResult with
    | .error reason => return .error reason
    | .ok value => pure value'''
    if DATA_CHECKER.count(old) != 1:
        raise ValueError("default constructor proof-policy splice changed")
    checker = DECIDABLE_PREMISE + DATA_CHECKER.replace(old,new)
    checker = checker.replace(".Defaults.",".DecidableDefaults.")
    checker = checker.replace("proof binder requires explicit witness","decidable premise unsupported at chosen values")
    # The new positive control needs actual dependent proof values; no premise
    # is supplied by a caller or silently erased by the renderer.
    checker += '''
theorem decidedToy (n : Nat) (_same : n = n) (_room : n ≤ n+1) : True := True.intro
theorem decided_domain : hypotheses_of% decidedToy := default_domain_witness% decidedToy
/-- info: 'Solidity.H62.BytecodeSelection.HypothesisAudit.DecidableDefaults.decided_domain' does not depend on any axioms -/
#guard_msgs in
#print axioms decided_domain
-- Guard the regression of reading unsupported default synthesis as impossibility:
-- proofToy failed at n=0 above but its full dependent domain is inhabited at n=1.
theorem proofToy_alternate : hypotheses_of% proofToy := ⟨1, Nat.zero_lt_succ 0, True.intro⟩
theorem falseToy (_impossible : False) : True := True.intro
theorem false_domain_impossible : ¬ (hypotheses_of% falseToy) := by
  intro witness
  rcases witness with ⟨impossible, _⟩
  exact impossible
/-- info: 'Solidity.H62.BytecodeSelection.HypothesisAudit.DecidableDefaults.proofToy_alternate' does not depend on any axioms -/
#guard_msgs in
#print axioms proofToy_alternate
/-- info: 'Solidity.H62.BytecodeSelection.HypothesisAudit.DecidableDefaults.false_domain_impossible' does not depend on any axioms -/
#guard_msgs in
#print axioms false_domain_impossible
/-- error: data hypothesis audit: decidable premise unsupported at chosen values -/
#guard_msgs in
#check default_domain_witness% falseToy
'''
    return checker


def data_render(repo, rows, source_candidate_names, expectations=None, *, decide_premises=False):
    """Kernel-checked default attempts for candidate hypotheses.

    Unsupported default synthesis is not an impossibility result or coverage.
    Default mode refuses proof binders; the opt-in proof-bearing mode constructs
    actual proofs with checked decisions. Resource exceptions propagate, and
    dependent Exists witnesses pass the kernel without added premises.
    """
    import kernel_metadata as metadata
    metadata.partition_records(rows, source_candidate_names)
    names = set(source_candidate_names)
    selected = sorted((r for r in rows if r["name"] in names and r["binders"] and
                       not r["level_params"] and any(b["proof_binder"] for b in r["binders"]) == decide_premises),key=lambda r:r["name"])
    if not selected:
        raise ValueError("no proof-bearing source candidates" if decide_premises else "no data-only source candidates")
    if expectations is not None and set(expectations) != {r["name"] for r in selected}:
        raise ValueError("default expectation membership differs")
    modules = sorted({r["module"] for r in selected})
    frozen_map, producer_sources = _frozen_scope(repo,modules)
    namespace = NAMESPACE+".DecidableDefaults" if decide_premises else DATA_NAMESPACE
    local_namespace = "DecidableDefaults" if decide_premises else "Defaults"
    fragment = macro_fragment((repo/MACRO_PATH).read_text())
    program = "import Lean\n" + "".join("import "+m+"\n" for m in modules)
    program += "/-! Guard default witness attempts from dropping proof premises or treating unsupported defaults as impossible. Original conclusions are not proved. -/\n"
    program += fragment + "\nnamespace "+local_namespace+"\nopen Lean Meta Elab Term\n" + (decidable_checker() if decide_premises else DATA_CHECKER)
    program += '/-- error: data hypothesis audit: missing or ambiguous kernel name -/\n#guard_msgs in\n#default_hypothesis_batch ["missing.kernel.name" => reject_missing against% "" expecting% "probe"]\n'
    program += '/-- error: data hypothesis audit: recorded type differs -/\n#guard_msgs in\n#default_hypothesis_batch ["'+namespace+'.positiveToy" => reject_type against% "wrong recorded type" expecting% "probe"]\n'
    targets = {}
    for start in range(0,len(selected),8):
        entries=[]
        for index,row in enumerate(selected[start:start+8],start):
            helper="data_domain_"+str(index).zfill(4)
            golden="probe" if expectations is None else expectations[row["name"]]
            if expectations is not None:
                if not isinstance(golden,str) or golden=="probe":
                    raise ValueError("strict default expectations cannot bypass checks")
                record=metadata.parse_json(golden)
                if (not isinstance(record,dict) or set(record)!={"target","helper","status","reason","axioms"} or
                        record["target"]!=row["name"] or record["helper"]!=namespace+"."+helper or
                        record["status"] not in {"proved","unsupported-default"} or
                        not isinstance(record["reason"],str) or not isinstance(record["axioms"],list) or
                        any(a not in {"propext","Classical.choice","Quot.sound"} for a in record["axioms"]) or
                        (record["status"]=="proved" and record["reason"]!="") or
                        (record["status"]=="unsupported-default" and (not record["reason"] or record["axioms"]))):
                    raise ValueError("invalid strict default expectation")
            entries.append(json.dumps(row["name"],ensure_ascii=False)+" => "+helper+" against% "+json.dumps(row["type_expr"],ensure_ascii=False)+" expecting% "+json.dumps(golden,ensure_ascii=False))
            targets[helper]=metadata.observed_type(row)
        program+="\n#default_hypothesis_batch [\n"+",\n".join(entries)+"\n]\n"
    program+="\nend "+local_namespace+"\nend "+NAMESPACE+"\n"
    return program,{"namespace":namespace,"targets":targets,"modules":modules,
        "macro_sha256":MACRO_SHA256,"frozen_map_sha256":sha(frozen_map),
        "producer_source_sha256":producer_sources,"generated_lean_sha256":sha(program.encode()),
        "expected_results":expectations,"kernel_accepted":False,"witness_ledger_linked":False,
        "boundary":"Default attempts only; unsupported is not uninhabited; no proof premises, original conclusions, Source or compiler coverage assumed"}
