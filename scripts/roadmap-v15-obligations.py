#!/usr/bin/env python3
"""Obligation accounting only: not semantics, a discharge certificate or admission."""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
# Every clause below is an OPEN proof obligation, including the resource clauses.
CLAUSES = {
 "decode": ("G46.01", "Decode this actual byte at a valid instruction boundary under Osaka; account for immediate length and any reference-fork gap."),
 "representation": ("G46.06", "Relate existing intrinsic compiler values/state to the actual numeric frame; apply only when the admitted profile emits this opcode."),
 "stack": ("G46.06", "Prove the actual opcode operand order/arity, stack tail framing, underflow observation and post-height <=1024."),
 "resources": ("G46.06", "Prove exact gas/expansion/access costs, exceptional failure, prefix fuel and approved excluded-resource abstraction; no additional bounds assumed."),
 "continuation": ("G46.06", "Relate PC/code position or terminal outcome, unchanged frame components and the next finite prefix."),
 "numeric": ("G46.01", "Prove the selected arithmetic/comparison/bit operation with its signedness, zero/overflow/shift/boundary cases and declared-width cleanup."),
 "push-immediate": ("G46.01", "Prove big-endian immediate value, exact encoded width and PC advance; separate truncated code right-padding from well-sized compiler output."),
 "jump": ("G46.01", "Prove absolute target/JUMPDEST validity outside PUSH data; conditional zero/nonzero branch and invalid-jump observation."),
 "memory-read": ("G46.02", "Relate exact byte-addressed source interval (offset,length), word/byte conversion and original memory outside the interval."),
 "memory-write": ("G46.02", "Relate exact destination interval and unaffected memory, offset/length arithmetic, alias/overlap behavior and byte order."),
 "memory-expansion": ("G46.02", "Relate maximum reached byte address, zero-length behavior, rounded active words and exact expansion charge/failure."),
 "word-padding": ("G46.02", "Relate 32-byte big-endian word load/store and low-byte MSTORE8 truncation; retain padding and driver representation obligations."),
 "calldata-source": ("G46.02", "Use the current frame calldata, exact offset/size, and zero padding past its end; destination memory is independently related."),
 "code-source": ("G46.02", "Relate own/external code bytes, exact source offset/size and zero padding past code end; retain code/metadata observation policy."),
 "returndata-source": ("G46.02", "Relate last-call return buffer and source offset+length bounds; out-of-range RETURNDATACOPY is exceptional, not zero padded."),
 "return-range": ("G46.02", "Extract exact RETURN/REVERT memory interval before rollback, with byte order, empty range and memory expansion."),
 "storage": ("G46.03", "Consume the published persistent/transient numeric-slot bridge and symbolic-path representation, including approved per-run slot/hash region clauses; persistent SSTORE original/current/new values, warm/cold access, dirty-slot/refund journal rules and transaction-boundary transient reset."),
 "static-permission": ("G47", "Prove static-context permission checks and their exact failure outcomes, including nonzero CALL value."),
 "account": ("G46.04", "Relate the correct 160-bit addressed account, existence/code/balance and warm/cold access context; do not substitute a payment Boolean."),
 "environment": ("G46.04", "Relate the current transaction/block/frame metadata or buffer size, preserving approved observations and post-upfront-fee balances."),
 "hash-bytes": ("G46.05", "Relate exact memory/code byte preimage to the approved fixed hash; use only source-determined per-run CollisionFree and slot RegionsDisjoint where applicable."),
 "call-calldata": ("G46.02", "Relate caller input memory offset/size to the callee calldata; preserve zero-length and exact byte payload behavior."),
 "call-returndata": ("G46.02", "Relate full last-call return buffer and bounded output-memory copy, including short payload tail and failure data."),
 "call-frame": ("G47", "Execute actual CALL/CALLCODE/DELEGATECALL/STATICCALL callee code with the opcode-specific caller/address/value/static inheritance and success bit; arbitrary permitted callees remain in scope."),
 "call-resources": ("G47", "Prove 7 operands for CALL/CALLCODE or 6 for DELEGATECALL/STATICCALL, forwarded gas/EIP-150/stipend, funds/depth checks and frame failure."),
 "precompile": ("G46.05", "For precompile recipients consume the reserved adapter: approved fixed functions, address dispatch, exact bytes, gas, invalid input and exceptional outcomes."),
 "rollback": ("G47", "Use the production account/world journal: persistent/transient storage, balances, nonce/code/log effects and exact rollback/commit boundary; local journals alone do not discharge this."),
 "session": ("G47", "Connect nested frame outcome to transaction validity/upfront fees and continuation of the session, observed events and finite/infinite prefixes."),
 "creation": ("G47", "Consume creation artifacts and run actual initcode, address/nonce/collision/prefund rules, runtime installation and exact result; preserve approved size idealizations."),
 "create-returndata": ("G47", "Relate CREATE/CREATE2 return-buffer reset/success-empty/failure payload behavior and later RETURNDATA observations."),
 "create-hash": ("G46.05", "Relate CREATE/CREATE2 address derivation and CREATE2 salt/initcode hash without assuming address or global hash injectivity."),
 "halt": ("G47", "Prove STOP/RETURN success, REVERT payload failure or exceptional INVALID outcome as appropriate; connect exact caller/transaction observation."),
 "log": ("G47", "Relate LOG topics and memory data, static refusal, event observation and journal log commit/rollback."),
 "selfdestruct": ("G47", "Account for Osaka selfdestruct/balance/account lifecycle and transaction-created-account rules only when admitted code emits it; no source-profile expansion."),
}
COMMON = {"decode", "representation", "stack", "resources", "continuation"}
CALLS = {"CALL", "CALLCODE", "DELEGATECALL", "STATICCALL"}
CREATES = {"CREATE", "CREATE2"}

def canonical_opcodes(source):
    """Read fixed bytes from the reserved table; instantiate its bounded families."""
    table = source.split("def code : Op → UInt8", 1)[1].split("def name : Op → String", 1)[0]
    ops = [(int(b, 16), n) for n, b in re.findall(r"\| \.([A-Z0-9]+) => (0x[0-9a-f]+)", table)]
    if len(ops) != 80:
        raise ValueError("expected the pinned table's 80 fixed opcodes")
    # Fail closed if any reserved bounded-family definition has drifted.
    for family, bound, base in [("DUP", 16, "0x80"), ("SWAP", 16, "0x90"), ("LOG", 5, "0xa0")]:
        if not re.search(r"\| " + family + r" \(n : Fin " + str(bound) + r"\)", source):
            raise ValueError("changed indexed-family bound: " + family)
        if not re.search(r"\| \." + family + r" n => UInt8.ofNat \(" + base + r" \+ n.val\)", table):
            raise ValueError("changed indexed-family byte formula: " + family)
    if "def pushCode (n : Fin 33) : UInt8 := UInt8.ofNat (0x5f + n.val)" not in source or "| push (n : Fin 33) (imm : Vector UInt8 n)" not in source:
        raise ValueError("changed PUSH family definition")
    for prefix, base, count, first in [("PUSH", 0x5f, 33, 0), ("DUP", 0x80, 16, 1),
                                      ("SWAP", 0x90, 16, 1), ("LOG", 0xa0, 5, 0)]:
        ops.extend((base + n, prefix + str(n + first)) for n in range(count))
    if len(set(b for b, _ in ops)) != 150 or len(set(n for _, n in ops)) != 150:
        raise ValueError("duplicate byte or mnemonic in pinned table")
    return sorted(ops)

def required_clauses(byte, name):
    ids = set(COMMON)
    if byte <= 0x1e and name != "STOP": ids.add("numeric")
    if name.startswith("PUSH"): ids.add("push-immediate")
    if name in {"JUMP", "JUMPI", "JUMPDEST"}: ids.add("jump")
    if 0x30 <= byte <= 0x4a or name in {"PC", "GAS", "MSIZE"}: ids.add("environment")
    if name in {"BALANCE", "EXTCODESIZE", "EXTCODECOPY", "EXTCODEHASH", "SELFBALANCE"}: ids.add("account")
    if name in {"MLOAD", "MSTORE", "MSTORE8"}: ids.update({"word-padding", "memory-expansion"})
    if name in {"MLOAD", "MCOPY", "KECCAK256", "RETURN", "REVERT"} or name in CALLS | CREATES or name.startswith("LOG"):
        ids.update({"memory-read", "memory-expansion"})
    if name in {"MSTORE", "MSTORE8", "MCOPY", "CALLDATACOPY", "CODECOPY", "EXTCODECOPY", "RETURNDATACOPY"} or name in CALLS:
        ids.update({"memory-write", "memory-expansion"})
    if name in {"CALLDATALOAD", "CALLDATACOPY"}: ids.add("calldata-source")
    if name in {"CODECOPY", "EXTCODECOPY"}: ids.add("code-source")
    if name == "RETURNDATACOPY": ids.add("returndata-source")
    if name in {"SLOAD", "SSTORE", "TLOAD", "TSTORE"}: ids.add("storage")
    if name in {"SSTORE", "TSTORE", "SELFDESTRUCT"} or name in CALLS | CREATES or name.startswith("LOG"):
        ids.add("static-permission")
    if name in {"SSTORE", "TSTORE", "SELFDESTRUCT"} or name in CALLS | CREATES:
        ids.add("rollback")
    if name in {"KECCAK256", "EXTCODEHASH"}: ids.add("hash-bytes")
    if name in {"RETURN", "REVERT"}: ids.update({"return-range", "halt", "rollback", "session"})
    if name in {"STOP", "INVALID"}: ids.update({"halt", "rollback", "session"})
    if name in CALLS:
        ids.update({"call-calldata", "call-returndata", "call-frame", "call-resources", "account", "precompile", "session"})
    if name in CREATES:
        ids.update({"creation", "create-hash", "account", "session", "create-returndata"})
    if name.startswith("LOG"): ids.update({"log", "rollback"})
    if name == "SELFDESTRUCT": ids.update({"selfdestruct", "account", "session", "halt"})
    return ids

def build_rows(ops):
    return [dict(byte=f"0x{byte:02x}", opcode=name, v15Status="open", dischargedByV15=[],
                 obligations=[dict(id=i, area=CLAUSES[i][0], statement=CLAUSES[i][1], status="open")
                              for i in sorted(required_clauses(byte, name))]) for byte, name in ops]

def validate_rows(rows, ops):
    expected = {name: byte for byte, name in ops}
    if len(rows) != len(ops) or len({r["opcode"] for r in rows}) != len(ops):
        raise ValueError("missing or duplicate opcode rows")
    for row in rows:
        name = row["opcode"]
        if name not in expected or row["byte"] != f"0x{expected[name]:02x}":
            raise ValueError("wrong opcode byte or mnemonic")
        obligations = row["obligations"]
        ids = [c["id"] for c in obligations]
        if len(ids) != len(set(ids)) or set(ids) != required_clauses(expected[name], name):
            raise ValueError("missing, duplicate or unexpected secondary obligation")
        if row["v15Status"] != "open" or row["dischargedByV15"]:
            raise ValueError("accounting cannot discharge semantics")
        for c in obligations:
            if c != dict(id=c["id"], area=CLAUSES[c["id"]][0], statement=CLAUSES[c["id"]][1], status="open"):
                raise ValueError("changed or discharged obligation")

def report():
    ops = canonical_opcodes((ROOT / "Solidity/Backend/Opcode.lean").read_text())
    rows = build_rows(ops); validate_rows(rows, ops)
    manifest = json.loads((ROOT / "Bridge/lake-manifest.json").read_text())
    packages = []
    for p in manifest["packages"]:
        if p["name"] in {"mathlib", "cslib", "auto"}:
            d = ROOT / "Bridge/.lake/packages" / p["name"]
            packages.append(dict(name=p["name"], revision=p.get("rev"), sourcePresent=d.exists(),
                                 oleanCount=len(list(d.glob(".lake/build/lib/lean/**/*.olean")))))
    ledger = json.loads((ROOT / "docs/feature-work/roadmap-g03-ledger.json").read_text())
    groups = {"G46.01", "G46.02", "G46.03", "G46.04", "G46.05", "G46.06", "G47"}
    features = [r["id"] for r in ledger["features"] if groups.intersection(r.get("owners", {}).get("evm", []))]
    return dict(note="Open obligation checklist only, not exhaustive proof certification or an assertion that every opcode is emitted. Reserved reference remains Cancun; Osaka gaps remain open.",
                opcodes=rows, packages=packages, coordinatorFeatureIds=features)

if __name__ == "__main__": print(json.dumps(report(), indent=2))
