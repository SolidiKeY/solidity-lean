#!/usr/bin/env python3
"""Roadmap G00 reconciliation of the feature manifest and upstream ledger.

Reads docs/solidity-features.json and docs/solidity-upstream-inventory.json
(never writes them) and prints the G00 ledger as Markdown: every manifest row
and every upstream symbol classified as in-profile, upstream-rejected or
unresolved, the feature combinations, and the owning roadmap groups.

The exclusion evidence below is transcribed from the repository history
(docs/feature-work/roadmap-g00-scope.md, "Exclusion evidence"). No row is
confirmed: confirmation needs an attributable user decision, which the
history does not contain. `--check` fails if a manifest ID is unowned, an
owner override names an unknown ID or group, or an excluded ID has no
evidence entry.

Usage: python3 scripts/roadmap-g00-scope.py [--check | --write] [--root DIR]
`--write` replaces the generated block of docs/feature-work/roadmap-g00-scope.md;
`--check` also fails if that block is stale.
Standard library only.
"""

import argparse
import collections
import json
import sys
from pathlib import Path

# Evidence tiers for each `scope: exclude` row. "B" = named as deliberately
# out of scope in docs/semantic-gaps.md at the root commit c3a3eef, before
# the agent-authored PR #5 (419f8a4) created the manifest; "B-" = only covered
# by a generic clause there; "C" = first appears in 419f8a4. None is an
# attributable user approval, so every row stays unresolved.
EXCLUSION_EVIDENCE = {
    "inlineAssembly": ("B", "inline assembly other than a canonical whole-byte-buffer rethrow"),
    "gasleft": ("B", "`gasleft()`"),
    "gasOption": ("B-", "gas stipends beyond `transfer`/`send` (the `{gas:}` option is not named)"),
    "rawCalldata": ("B", "raw calldata (`msg.data`, `msg.sig`)"),
    "rawReturndata": ("B", "raw returndata"),
    "lowLevelCall": ("B", "low-level `call(data)` with arbitrary bytes"),
    "delegatecall": ("C", "not named before 419f8a4"),
    "lowLevelStaticcall": ("C", "not named before 419f8a4"),
    "selfdestruct": ("B", "`selfdestruct`"),
    "create2Salt": ("B", "`create2` salts"),
    "addressCode": ("B", "`address.code`, `extcodesize`"),
    "addressCodehash": ("C", "not named before 419f8a4"),
    "storageLayout": ("B-", "storage layout (slot numbers, packing); `layout at` not named"),
    "memoryLayout": ("C", "not named before 419f8a4"),
    "transientLayout": ("C", "not named before 419f8a4"),
    "eventLog": ("B", "the log is dropped; argument effects are kept"),
    "machineResources": ("B-", "compiler-verification.md: \"no gas, no stack limit\" (a model property, not a profile decision)"),
    "blockNumber": ("B", "`block.number`"),
    "txOrigin": ("B", "`tx.origin`"),
    "blockBasefee": ("B", "`block.basefee`"),
    "blockCoinbase": ("B-", "\"block and transaction fields other than those the model reads … ( … )\""),
    "blockDifficulty": ("B-", "generic block-field clause"),
    "blockPrevrandao": ("B-", "generic block-field clause"),
    "blockGaslimit": ("B-", "generic block-field clause"),
    "blockChainid": ("B-", "generic block-field clause"),
    "blockBlobbasefee": ("B-", "generic block-field clause"),
    "blockSlotnum": ("B-", "generic block-field clause (Amsterdam-gated; no pinned EVM target accepts it)"),
    "txGasprice": ("B-", "generic block/transaction-field clause"),
    "blockhashBuiltin": ("C", "a builtin, not a field; not named before 419f8a4"),
    "blobhashBuiltin": ("C", "a builtin, not a field; not named before 419f8a4"),
}

# Owners per obligation stage: source definition, syntax/static checking,
# lowering, backend/EVM. Composition owners (S05, G15, G48-G55) own every
# row and are stated once in the document, not repeated here.
CATEGORY_OWNERS = {
    "lexical": ("S00", "G08", "G16", "G25"),
    "types": ("S00 S01", "G09 G13", "G18", "G27 G32"),
    "declarations": ("S00 S01", "G09 G11 G14", "G20", "G40 G44"),
    "expressions": ("S02", "G10 G13", "G16 G17", "G25 G26"),
    "statements": ("S03.01", "G11", "G19", "G36.01"),
    "storage": ("S04.01", "G09 G13", "G18.02", "G27 G28"),
    "calls": ("S03.03", "G10 G14", "G22", "G42"),
    "environment": ("S04.02", "G10 G13", "G23", "G31 G46.04"),
    "builtins": ("S02", "G10 G13", "G16", "G25"),
    "abi": ("S04.02", "G10 G13", "G21", "G40 G41"),
    "metadata": ("S01 S04.02", "G13", "G23", "G31"),
    "semantics": ("S02", "G13", "G16", "G25"),
}

OWNER_OVERRIDES = {
    # lexical
    "pragmaVersion": ("S00", "G08 G12", "G15", "G54"),
    "pragmaAbicoder": ("S00 S04.02", "G08 G12", "G21", "G40 G41"),
    "pragmaOther": ("S00", "G08 G12", "G15", "G54"),
    "comments": ("S00", "G08", "—", "—"),
    "identifiers": ("S00 S01", "G08 G12", "G16 G17", "G26"),
    "stringLiterals": ("S00 S02", "G08", "G18.03", "G33"),
    "hexLiterals": ("S00 S02", "G08", "G18.03", "G33"),
    "unicodeLiterals": ("S00 S02", "G08", "G18.03", "G33"),
    # types
    "integerTypes": ("S00 S01", "G09 G13", "G16", "G25"),
    "boolType": ("S00 S01", "G09 G13", "G16", "G25"),
    "addressTypes": ("S00 S01", "G09 G13", "G16", "G25 G42"),
    "fixedBytesTypes": ("S00 S01", "G09 G13", "G16", "G25"),
    "enumTypes": ("S00 S01", "G09 G13", "G16", "G25"),
    "valueTypes": ("S00 S01", "G09 G13", "G16", "G25"),
    "internalFunctionTypes": ("S00 S01", "G09 G13", "G20", "G37.03"),
    "externalFunctionTypes": ("S00 S01 S04.03", "G09 G13", "G20 G22.04", "G42.05"),
    "tupleTypes": ("S00 S01", "G09 G13", "G17", "G26"),
    "mappings": ("S00 S01 S04.01", "G09 G13", "G18.02", "G27.02"),
    "fixedArrays": ("S00 S01 S04.01", "G09 G13", "G18", "G27.03 G32"),
    "dynamicArrays": ("S00 S01 S04.01", "G09 G13", "G18", "G27.03 G32"),
    "dynamicBytesType": ("S00 S01 S04.01", "G09 G13", "G18", "G27.03 G32"),
    "stringType": ("S00 S01 S04.01", "G09 G13", "G18", "G27.03 G32"),
    "structTypes": ("S00 S01 S04.01", "G09 G13", "G18", "G27.01 G32"),
    "recursiveTypes": ("S00 S01 S04.01", "G09 G13", "G18.01", "G27.04 G35.05"),
    "storageLocation": ("S01 S04.01", "G09 G13", "G18.02", "G27 G28"),
    "memoryLocation": ("S01 S04.01", "G09 G13", "G18.03", "G32 G34"),
    "calldataLocation": ("S01 S04.01", "G09 G13", "G18.04", "G35.03 G40 G46.02"),
    # declarations
    "sourceUnits": ("S00", "G11 G12", "G23", "G44"),
    "imports": ("S00", "G11 G12", "G23", "G44.02"),
    "contracts": ("S00 S01", "G11 G14", "G20", "G40 G44"),
    "interfaces": ("S00 S01", "G11 G14", "G20", "G42"),
    "libraries": ("S00 S01 S03.03", "G11 G14", "G22.04", "G42.04 G44.02"),
    "freeFunctions": ("S00 S01", "G11 G12", "G20", "G37"),
    "functions": ("S00 S01 S03", "G11 G13", "G20", "G37 G40"),
    "modifiers": ("S03.02", "G11 G14", "G19", "G36.01 G37"),
    "modifierPlaceholder": ("S03.02", "G11", "G19", "G36.01"),
    "constructors": ("S03.02 S04.04", "G11 G14", "G19 G22.03", "G44.01"),
    "receiveFunction": ("S03.03 S04.04", "G11 G14", "G20", "G40"),
    "fallbackFunction": ("S03.03 S04.04", "G11 G14", "G20", "G40"),
    "stateVariables": ("S01 S04.01", "G09 G11", "G18.02", "G27 G44.01"),
    "constants": ("S01", "G09 G13", "G16", "G25"),
    "immutables": ("S01 S04.03", "G09 G13", "G19", "G44.01"),
    "publicGetters": ("S01 S03.03", "G13 G14", "G20", "G40 G41"),
    "visibility": ("S01", "G11 G14", "G20", "G40"),
    "stateMutability": ("S01 S03.03", "G11 G13", "G20 G22", "G40 G42"),
    "overrideDeclarations": ("S01", "G11 G14", "G20", "G37"),
    "inheritance": ("S01 S03.02", "G11 G14", "G19 G20", "G44.01"),
    "structDeclarations": ("S00 S01", "G09", "G18", "G27.01 G32"),
    "enumDeclarations": ("S00 S01", "G09", "G16", "G25"),
    "valueTypeDeclarations": ("S00 S01", "G09 G13", "G16", "G25"),
    "errorDeclarations": ("S00 S01 S04.02", "G09 G11", "G21", "G38 G41"),
    "eventDeclarations": ("S00 S01", "G09 G11", "G23", "G31"),
    "usingFor": ("S01", "G11 G14", "G20", "G37"),
    "operatorAliases": ("S01", "G11 G13 G14", "G16 G20", "G25 G37"),
    # expressions
    "parentheses": ("S00 S02", "G10", "G16", "G26"),
    "names": ("S01 S02", "G10 G12", "G16 G17", "G26"),
    "memberAccess": ("S02", "G10 G13", "G17 G18", "G26 G28 G34"),
    "indexAccess": ("S02", "G10 G13", "G17 G18", "G26 G28 G34"),
    "rangeAccess": ("S02", "G10 G13", "G18.04 G21", "G35.03"),
    "functionCalls": ("S02 S03.03", "G10 G13", "G20", "G37 G42"),
    "namedArguments": ("S02", "G10 G13", "G20", "G37"),
    "callOptions": ("S02 S03.03", "G10 G15", "G22", "G42 G43 G44.03"),
    "arithmetic": ("S02", "G10 G13", "G16", "G25"),
    "comparisons": ("S02", "G10 G13", "G16", "G25"),
    "bitwise": ("S02", "G10 G13", "G16", "G25"),
    "shifts": ("S02", "G10 G13", "G16", "G25"),
    "unaryArithmetic": ("S02", "G10 G13", "G16", "G25"),
    "increments": ("S02", "G10 G13", "G17", "G26 G28"),
    "assignment": ("S02", "G10 G13", "G17", "G26 G28 G34"),
    "compoundAssignment": ("S02", "G10 G13", "G17", "G26 G28"),
    "shortCircuit": ("S02", "G10", "G17", "G26"),
    "conditional": ("S02", "G10 G13", "G17", "G26"),
    "tupleExpressions": ("S02", "G10 G13", "G17", "G26"),
    "inlineArrays": ("S02", "G10 G13", "G18.03", "G33"),
    "structConstruction": ("S02", "G10 G13", "G18.03", "G33"),
    "newMemory": ("S02 S04.01", "G10 G13", "G18.03", "G33"),
    "deleteExpression": ("S02 S04.01", "G10 G13", "G18.05", "G28 G30 G34"),
    "explicitConversions": ("S01 S02", "G10 G13", "G16 G18.05", "G25 G35"),
    "implicitConversions": ("S01", "G13", "G16 G18.05", "G25 G35"),
    "metaTypeExpression": ("S01", "G10 G13", "G23", "G31"),
    # statements
    "returnStatement": ("S03.01", "G11", "G19", "G36.01 G37"),
    "variableDeclarations": ("S03.01", "G11 G13", "G17 G19", "G26"),
    "expressionStatements": ("S03.01", "G11", "G17", "G26"),
    "uncheckedBlock": ("S02 S03.01", "G11", "G16", "G25"),
    "forStatement": ("S03.01", "G11", "G19", "G36"),
    "whileStatement": ("S03.01", "G11", "G19", "G36"),
    "doWhileStatement": ("S03.01", "G11", "G19", "G36"),
    "emitStatement": ("S03.01 S04.02", "G11", "G23", "G31"),
    "revertStatement": ("S03.01 S04.02", "G11", "G21", "G38"),
    "tryStatement": ("S03.03 S04.03", "G11", "G21 G22", "G38 G42"),
    "catchClauses": ("S03.03 S04.02", "G11", "G21", "G38 G41"),
    "canonicalRethrow": ("S03.01 S04.02", "G11 G15", "G21", "G38"),
    # storage
    "arrayLength": ("S04.01", "G10 G13", "G18", "G28 G34"),
    "arrayPush": ("S04.01", "G10 G13", "G18.02", "G30"),
    "arrayPushReference": ("S04.01", "G10 G13", "G18.02", "G30"),
    "arrayPop": ("S04.01", "G10 G13", "G18.02", "G30"),
    "storageAliasing": ("S04.01", "G13", "G18.02", "G28"),
    "memoryAliasing": ("S04.01", "G13", "G18.03", "G34"),
    "storageCopy": ("S04.01", "G13", "G18.05", "G29"),
    "deleteMappingTails": ("S04.01", "G13", "G18.05", "G29 G30"),
    "danglingReferences": ("S04.01", "G13", "G18.05", "G28 G30"),
    "transientState": ("S04.03", "G09 G13", "G23", "G39 G46.03"),
    "logicalStorageBase": ("S04.01", "G09 G13", "G18.02", "G27.05"),
    # calls
    "internalCalls": ("S03.03", "G10 G14", "G20", "G37"),
    "recursiveCalls": ("S03.03 S03.04", "G10 G14", "G20", "G37.02"),
    "functionValues": ("S03.03", "G10 G13", "G20", "G37.03 G42.05"),
    "extensionCalls": ("S03.03", "G10 G14", "G20", "G37"),
    "externalSelfCalls": ("S03.03", "G10 G14", "G22.01", "G42.01"),
    "externalTypedCalls": ("S03.03 S04.03", "G10 G14", "G22.01", "G42.02"),
    "callbackSemantics": ("S03.03 S04.03", "G13", "G22.02", "G42.03"),
    "externalLibraryCalls": ("S03.03 S04.03", "G10 G14", "G22.04", "G42.04"),
    "sendTransfer": ("S03.03 S04.03", "G10 G13", "G22", "G43"),
    "emptyDataValueCall": ("S03.03 S04.03", "G10 G13", "G22", "G43"),
    "valueOption": ("S03.03 S04.03", "G10 G13", "G22", "G43"),
    "newContract": ("S03.03 S04.04", "G10 G13", "G22.03", "G44.03"),
    "creationTry": ("S03.03 S04.04", "G11 G13", "G22.03", "G44.03"),
    # environment
    "msgSender": ("S04.02", "G10 G13", "G23", "G31 G46.04"),
    "msgValue": ("S04.02", "G10 G13", "G23", "G31 G43"),
    "thisAddress": ("S04.02", "G10 G13", "G23", "G31 G46.04"),
    "addressBalance": ("S04.02 S04.03", "G10 G13", "G23", "G31 G43"),
    "blockTimestamp": ("S04.02", "G10 G13", "G23", "G31 G46.04"),
    # builtins
    "assertBuiltin": ("S02 S04.02", "G10 G13", "G21", "G38"),
    "requireBuiltin": ("S02 S04.02", "G10 G13", "G21", "G38"),
    "revertBuiltin": ("S02 S04.02", "G10 G13", "G21", "G38"),
    "addmodBuiltin": ("S02", "G10 G13", "G16", "G25"),
    "mulmodBuiltin": ("S02", "G10 G13", "G16", "G25"),
    "keccakBuiltin": ("S04.02", "G10 G13", "G23", "G31 G46.05"),
    "sha256Builtin": ("S04.02", "G10 G13", "G23", "G31 G46.05"),
    "ripemd160Builtin": ("S04.02", "G10 G13", "G23", "G31 G46.05"),
    "ecrecoverBuiltin": ("S04.02", "G10 G13", "G23", "G31 G46.05"),
    "bytesConcat": ("S02", "G10 G13", "G18.03", "G33 G35"),
    "stringConcat": ("S02", "G10 G13", "G18.03", "G33 G35"),
    "wrapUnwrap": ("S02", "G10 G13", "G16", "G25"),
    "erc7201Builtin": ("S02 S04.02", "G10 G13", "G23", "G31 G46.05"),
    # metadata
    "typeName": ("S01", "G13", "G23", "G31"),
    "interfaceId": ("S01", "G13", "G23", "G31"),
    "functionSelector": ("S01 S04.02", "G13", "G23", "G31 G40"),
    "functionAddress": ("S04.03", "G13", "G22.04", "G42.05"),
    "errorEventSelector": ("S01 S04.02", "G13", "G23", "G31"),
    "typeBounds": ("S01", "G13", "G16", "G25"),
    "creationCode": ("S04.02", "G13", "G23", "G44.02"),
    "runtimeCode": ("S04.02", "G13", "G23", "G44.02"),
    # semantics
    "checkedArithmetic": ("S02", "G13", "G16", "G25"),
    "uncheckedArithmetic": ("S02", "G13", "G16", "G25"),
    "exactConstants": ("S01", "G13", "G16", "G25"),
    "evaluationOrder": ("S02 S03", "G13", "G16 G17", "G26"),
    "defaultInitialization": ("S02 S04.01", "G13", "G18", "G30 G33"),
    "referenceCopyRules": ("S04.01", "G13", "G18.05", "G29 G35"),
    "panicCodes": ("S04.02", "G13", "G21", "G38"),
    "revertPayloads": ("S04.02", "G13", "G21", "G38 G41"),
    "rollback": ("S03.04 S04.03", "G13", "G21 G22", "G38 G39 G47"),
    "termination": ("S03.04", "G13", "G19", "G36.03 G37.02 G49.03"),
    "typeValidation": ("S01", "G13", "G15", "G48"),
    "featureDetection": ("S05", "G15", "G15", "G48"),
    "nonpayableEntry": ("S04.04", "G13", "G22.05", "G40 G43"),
    "abiEntryValidation": ("S04.02", "G13", "G21", "G40"),
    "constructorLifetime": ("S04.04", "G14", "G22.03", "G44 G50.01"),
    "staticCallRestriction": ("S03.03 S04.03", "G13", "G22", "G42.02 G42.05"),
    "worldAssumptions": ("S04.03", "G13", "G22", "G47"),
}

# Rejection owners: a precise refusal is an obligation for every
# non-profile row whatever its evidence (S00: "Include syntax outside the
# profile for precise rejection"; G15: exact profile classification).
REJECTION_OWNERS = {
    "exclude": "S00 G15 (precise refusal; observation side: G01/G06)",
    "upstream": "S00 G08 G11 G15 (precise rejection as invalid/removed)",
}

GROUPS = ({f"S0{i}" for i in range(6)} | {f"G{i:02d}" for i in range(56)})

# Combinations the scope document names: one source construct whose
# classification needs several feature IDs. "in" parts are owned; "out" parts
# are unresolved exclusions.
COMBINATIONS = [
    ("`f{value:v,gas:g}(…)`", ["callOptions", "valueOption"], ["gasOption"], "G15 G22 G43"),
    ("`new C{salt:s,value:v}(…)`", ["callOptions", "newContract", "valueOption"], ["create2Salt"], "G15 G22.03 G44.03"),
    ("byte-oriented `fallback(bytes calldata) returns (bytes memory)`", ["fallbackFunction"], ["rawCalldata", "rawReturndata"], "G15 G20 G40"),
    ("`emit E(args)` under a log-observing property", ["emitStatement", "eventDeclarations"], ["eventLog"], "G15 G23 G31"),
    ("`assembly { revert(add(d,32), mload(d)) }` vs any other assembly", ["canonicalRethrow"], ["inlineAssembly"], "G15 G21 G38"),
    ("`(bool ok,) = a.call{value:v}(\"\")` vs `a.call(data)`", ["emptyDataValueCall", "valueOption"], ["lowLevelCall", "rawReturndata"], "G15 G22 G43"),
    ("literal `layout at` base vs physical layout", ["logicalStorageBase"], ["storageLayout"], "G09 G15 G27.05"),
    ("`T transient x` vs physical transient slots", ["transientState"], ["transientLayout"], "G15 G23 G39"),
    ("loops/recursion vs gas/stack exhaustion", ["termination", "recursiveCalls"], ["machineResources"], "G01 G36.03 G37.02 G49.03"),
    ("`send`/`transfer` vs exact stipend", ["sendTransfer"], ["gasOption", "machineResources"], "G22 G43"),
    ("`type(C).creationCode`/`runtimeCode` vs `address.code`", ["creationCode", "runtimeCode"], ["addressCode", "addressCodehash"], "G15 G44.02"),
    ("`block.timestamp` vs other `block.*`/`tx.*` members", ["blockTimestamp", "msgSender", "msgValue"],
     ["blockNumber", "txOrigin", "txGasprice", "blockCoinbase", "blockChainid"], "G15 G23"),
    ("`view` external call vs low-level `staticcall`", ["staticCallRestriction", "externalTypedCalls"], ["lowLevelStaticcall"], "G15 G42"),
    ("linked library call vs `delegatecall`", ["externalLibraryCalls"], ["delegatecall"], "G15 G42.04"),
]


DOC = "docs/feature-work/roadmap-g00-scope.md"
BEGIN = "<!-- BEGIN generated by scripts/roadmap-g00-scope.py -->"
END = "<!-- END generated by scripts/roadmap-g00-scope.py -->"


def load(root):
    features = json.loads((root / "docs/solidity-features.json").read_text())
    ledger = json.loads((root / "docs/solidity-upstream-inventory.json").read_text())
    return features, ledger


def g00_status(scope):
    return {"model": "in-profile", "abstract": "in-profile",
            "upstream": "upstream-rejected", "exclude": "unresolved"}[scope]


def owners(feature):
    return OWNER_OVERRIDES.get(feature["id"], CATEGORY_OWNERS.get(feature["category"]))


def check(features, ledger):
    errors = []
    ids = {f["id"] for f in features["features"]}
    for key in list(OWNER_OVERRIDES) + list(EXCLUSION_EVIDENCE):
        if key not in ids:
            errors.append(f"unknown feature ID {key}")
    for name, ins, outs, own in COMBINATIONS:
        for key in ins + outs:
            if key not in ids:
                errors.append(f"combination {name}: unknown ID {key}")
        for key in outs:
            if key in ids and next(f for f in features["features"] if f["id"] == key)["scope"] != "exclude":
                errors.append(f"combination {name}: {key} is not excluded")
        for key in ins:
            if key in ids and next(f for f in features["features"] if f["id"] == key)["scope"] not in ("model", "abstract"):
                errors.append(f"combination {name}: {key} is not in profile")
    groups_used = set()
    for row in list(OWNER_OVERRIDES.values()) + list(CATEGORY_OWNERS.values()):
        for cell in row:
            groups_used.update(tok for tok in cell.split() if tok != "—")
    for _, _, _, own in COMBINATIONS:
        groups_used.update(own.split())
    for g in groups_used:
        if g.split(".")[0] not in GROUPS:
            errors.append(f"unknown group {g}")
    for f in features["features"]:
        if f["scope"] in ("model", "abstract") and owners(f) is None:
            errors.append(f"no owner for in-profile {f['id']}")
        if f["scope"] == "exclude" and f["id"] not in EXCLUSION_EVIDENCE:
            errors.append(f"no evidence entry for excluded {f['id']}")
    symbol_ids = {x for kind in ledger["symbols"].values() for xs in kind.values() for x in xs}
    for key in symbol_ids - ids:
        errors.append(f"ledger symbol maps to unknown ID {key}")
    return errors


def symbol_status(targets, scope):
    kinds = {g00_status(scope[t]) for t in targets}
    if len(kinds) == 1:
        return kinds.pop()
    if "in-profile" in kinds:
        return "combination-unresolved" if "unresolved" in kinds else "combination-upstream"
    return "unresolved" if "unresolved" in kinds else "upstream-rejected"


def report(features, ledger):
    rows = features["features"]
    scope = {f["id"]: f["scope"] for f in rows}
    out = []
    emit = out.append
    up = features["upstream"]
    emit(f"Manifest pin: `{up['repository']}` `{up['tag']}` `{up['commit']}`, "
         f"{len(up['sources'])} inspected files; ledger commit `{ledger['commit']}`.")
    emit("")
    emit("### Counts")
    emit("")
    emit("| G00 status | manifest scope | rows |")
    emit("|---|---|---|")
    for (status, sc), n in sorted(collections.Counter((g00_status(f["scope"]), f["scope"]) for f in rows).items()):
        emit(f"| {status} | {sc} | {n} |")
    emit(f"| **total** | | **{len(rows)}** |")
    emit("")
    current = collections.Counter((f["scope"], f["current"]) for f in rows)
    emit("Current statuses at the base (informative; G00 does not change them): "
         + ", ".join(f"{s}/{c} {n}" for (s, c), n in sorted(current.items())) + ".")
    emit("")
    sym = collections.Counter()
    per_kind = collections.defaultdict(lambda: collections.defaultdict(list))
    for kind, table in ledger["symbols"].items():
        for name, targets in table.items():
            st = symbol_status(targets, scope)
            sym[st] += 1
            per_kind[kind][st].append(name)
    emit("| upstream symbols | count |")
    emit("|---|---|")
    for st, n in sorted(sym.items()):
        emit(f"| {st} | {n} |")
    emit(f"| **total** | **{sum(sym.values())}** |")
    emit("")
    unmapped = sorted(set(scope) - {x for t in ledger["symbols"].values() for xs in t.values() for x in xs})
    emit(f"Manifest rows with no ledger symbol (semantic requirements, enumerated by hand): "
         f"{len(unmapped)} — " + ", ".join(f"`{u}`" for u in unmapped) + ".")
    emit("")
    emit("### Manifest rows")
    emit("")
    emit("Owner columns: source definition / syntax and static checking / lowering / backend and EVM.")
    emit("")
    emit("| ID | category | scope | G00 status | evidence | source | syntax | lowering | backend |")
    emit("|---|---|---|---|---|---|---|---|---|")
    for f in sorted(rows, key=lambda f: (g00_status(f["scope"]), f["category"], f["id"])):
        st = g00_status(f["scope"])
        if st == "in-profile":
            o = owners(f)
            ev = "in profile" + (" (abstraction)" if f["scope"] == "abstract" else "")
            emit(f"| `{f['id']}` | {f['category']} | {f['scope']} | {st} | {ev} | {o[0]} | {o[1]} | {o[2]} | {o[3]} |")
        elif st == "unresolved":
            tier, text = EXCLUSION_EVIDENCE[f["id"]]
            emit(f"| `{f['id']}` | {f['category']} | {f['scope']} | {st} | {tier}: {text} | {REJECTION_OWNERS['exclude']} | | | |")
        else:
            emit(f"| `{f['id']}` | {f['category']} | {f['scope']} | {st} | upstream pin | {REJECTION_OWNERS['upstream']} | | | |")
    emit("")
    emit("### Upstream symbols by kind")
    emit("")
    for kind in ledger["symbols"]:
        parts = []
        for st in ("in-profile", "combination-unresolved", "combination-upstream", "unresolved", "upstream-rejected"):
            names = per_kind[kind].get(st)
            if names:
                parts.append(f"{st} ({len(names)}): " + ", ".join(f"`{n}`" for n in sorted(names)))
        emit(f"- **{kind}** — " + "; ".join(parts))
    emit("")
    emit("### Ledger combinations (symbols mapped to in-profile and non-profile rows)")
    emit("")
    emit("| kind | symbol | in-profile IDs | other IDs |")
    emit("|---|---|---|---|")
    for kind, table in ledger["symbols"].items():
        for name, targets in sorted(table.items()):
            if symbol_status(targets, scope).startswith("combination"):
                ins = [t for t in targets if g00_status(scope[t]) == "in-profile"]
                oth = [t for t in targets if g00_status(scope[t]) != "in-profile"]
                emit(f"| {kind} | `{name}` | {', '.join(ins)} | {', '.join(oth)} |")
    emit("")
    emit("### Named feature combinations")
    emit("")
    emit("| construct | in-profile IDs | unresolved IDs | owners |")
    emit("|---|---|---|---|")
    for name, ins, outs, own in COMBINATIONS:
        emit(f"| {name} | {', '.join(ins)} | {', '.join(outs)} | {own} |")
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--root", default=str(Path(__file__).resolve().parent.parent))
    args = ap.parse_args()
    features, ledger = load(Path(args.root))
    errors = check(features, ledger)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    doc = Path(args.root) / DOC
    text = doc.read_text()
    start, end = text.index(BEGIN) + len(BEGIN), text.index(END)
    block = "\n" + report(features, ledger) + "\n"
    if args.write:
        doc.write_text(text[:start] + block + text[end:])
        return 0
    if args.check:
        if text[start:end] != block:
            print(f"{DOC}: generated block is stale (run --write)", file=sys.stderr)
            return 1
        n = sum(1 for f in features["features"] if f["scope"] in ("model", "abstract"))
        print(f"roadmap-g00: {len(features['features'])} rows, {n} in-profile owned, "
              f"{len(EXCLUSION_EVIDENCE)} exclusions with evidence entries, "
              f"{len(COMBINATIONS)} named combinations; 0 errors")
        return 0
    print(report(features, ledger))
    return 0


if __name__ == "__main__":
    sys.exit(main())
