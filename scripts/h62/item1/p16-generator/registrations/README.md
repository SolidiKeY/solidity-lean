# Proposed extension registration

This proposal requires VY1/VY3 agreement before integration. Each addition uses
one `VY1-Name.json` or `VY3-Name.json` with exactly these fields:

```json
{"module": "Solidity.Yul.Name", "documentation": true}
```

`module` may be null, and `documentation` may be false, but not both. A module
requires `imports/ext-VY1-Name.txt` (or VY3), containing exactly its module
name and LF. True documentation requires `body/ext-VY1-Name.txt` (or VY3),
containing exactly one nonempty balanced Lean doc comment and final LF. A
registration and its matching files are one change. The source module must exist.
Owner prefixes are names, not authentication. The owner must allocate a unique
Name within its prefix; a same-path Git conflict must be reviewed, not silently
resolved. Duplicate imports across all owners and the baseline are rejected.

Baseline nodes retain their original order. Proposed extension names sort
lexically after the baseline, first by owner key then by Name, independently
for imports and documentation. Owners must agree that this order is semantically
and operationally acceptable. Additions omitted from both registration and
interface cannot be discovered by this tool: compare the live owner deltas to
registrations. Registration edits and changes to baseline hashes require review.
The baseline check requires the pinned base commit to exist in the local Git
object database. No owner integration or original-file edit is authorized here.
