# Creation artifacts

[Authoritative source](../../Solidity/Backend/Executable).

Creation correctness must account for constructor execution, runtime code installation and constructor argument layout together. A patch-offset or byte-layout result alone is not a deployment theorem. Artifact tables need exact emitted-byte provenance; linking cannot be solved by assuming the desired compiled contract table.
