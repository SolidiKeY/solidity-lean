"""Guard native replay against weakening externally supplied negative expectations.

Fixed seven-group/fourteen-result inventory agrees with browser-control-completion.cjs
and fresh-spec-controls.mjs. Pins identify the retained exact request journal;
expected outcomes come from this reviewed inventory, never observed replies.
Pending/refuted alternatives and the saved browser stack failure are unchanged.
"""
import hashlib
import json
from pathlib import Path

REQUESTS_SHA256 = "57ec1b7a00aea7f834a270d9de72811d2ea177469dba22af09dabc1873d92e8f"
EXPECTED = [{'wireSha256': '67e5602e133d5da830c3f996cbe0f4d23ee84b7015fae23dd5d6594a9c1504aa',
  'sourceHash': 'bf0d887de89ea546b502595fed2314cb9a5642909d29646adff2fdd7c2045532',
  'expected': [['additionSimple', ['pending', 'refuted']]]},
 {'wireSha256': 'd43d8c6f472fda0fc6f871b4ef6a6f2d069030f215b187d70205ae0434d8d01b',
  'sourceHash': '12ac133902388a42534f6ab7d0c0f829d15e612e100d334e0c4a743ad6121769',
  'expected': [['storageRootReadWrite', ['pending', 'refuted']]]},
 {'wireSha256': 'd4869ed44397c237435f2f084f58c6484afcc2c92947a50f42b5b2576d295d3e',
  'sourceHash': 'f6249d544cee21b975a911ca07897ebcbdc01f3fc0de7be8eb6dca789e08e166',
  'expected': [['storageIndexRootMapping', ['pending', 'refuted']]]},
 {'wireSha256': 'f5b0e66d72b717627a2b64e8481c358df6f716b3c2ca53039382e42db5c675bf',
  'sourceHash': '8fbaa26fae89aa854f88bdcca628fbef8deb86c0e92fe43263ef238af4a1f246',
  'expected': [['whileCountsUp', ['pending', 'refuted']]]},
 {'wireSha256': 'f17d932db443b445b74ea755a2eb06c3bac593a41c2d3a280aeb914b3243e8fb',
  'sourceHash': '12fe08c7ebcb4bced15227fa6d6829b63cce545b88229ff173f03b4ad4efc0fd',
  'expected': [['invariantCountsToBound', ['pending', 'refuted']]]},
 {'wireSha256': '47375e0804271ac998cc945403ae473a77db9399c64d7d84995a297de233296a',
  'sourceHash': '82300ae386c7d20325d3a26af9c47c902b2265dd29b622bc08ed3b1e750cbe4d',
  'expected': [['requireFalseLiteral', ['proved']]]},
 {'wireSha256': 'a4794f40d82abf04d5da6a4957164631b0134807a151f04cf38b089701b67eb9',
  'sourceHash': '2d7aa2231395bc084588c541087fbd1d80bdd104ccb7ef07adbafc0812b4ffef',
  'expected': [['maximum', ['proved']],
               ['falseMaximum', ['refuted']],
               ['storeMaximum', ['proved']],
               ['twoChoices', ['proved']],
               ['constantOne', ['proved']],
               ['falseConstant', ['refuted']],
               ['store', ['proved']],
               ['falseStore', ['refuted']]]}]


def pairs(items):
    result = {}
    for key, value in items:
        if key in result:
            raise ValueError("duplicate replay JSON key")
        result[key] = value
    return result


def validate(requests, records):
    if type(requests) is not list or type(records) is not list or len(requests) != 7 or len(records) != 7:
        raise ValueError("complete seven-group replay inventory required")
    for request, record, expected in zip(requests, records, EXPECTED):
        if not isinstance(request, dict) or any(request.get(k) != value for k, value in expected.items()):
            raise ValueError("reviewed replay inventory or expectations changed")
        if not isinstance(request.get("wire"), str) or hashlib.sha256(request["wire"].encode()).hexdigest() != expected["wireSha256"]:
            raise ValueError("reviewed replay wire changed")
        if not isinstance(record, dict) or any(record.get(k) != expected[k] for k in ("wireSha256", "sourceHash", "expected")):
            raise ValueError("completion identity or expectations changed")
    return requests


def load(directory):
    path = Path(directory)
    with (path / "browser-control-attempts.jsonl").open("rb") as stream:
        raw = stream.read(1024 * 1024 + 1)
    if len(raw) > 1024 * 1024 or hashlib.sha256(raw).hexdigest() != REQUESTS_SHA256:
        raise ValueError("exact replay request journal pin mismatch")
    requests = [json.loads(line, object_pairs_hook=pairs) for line in raw.splitlines()]
    with (path / "browser-control-completion.json").open("rb") as stream:
        completed = stream.read(1024 * 1024 + 1)
    if len(completed) > 1024 * 1024:
        raise ValueError("oversized completion record")
    records = json.loads(completed, object_pairs_hook=pairs)["requests"]
    return validate(requests, records), records
