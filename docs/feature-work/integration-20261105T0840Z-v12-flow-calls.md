# v12-flow-calls bounded checkpoint

Producer `be36ea8087cefcdb4a1f5a34dd6d44a1302a0223`. Imports only:

- `Solidity/Backend/InternalFlow/RuntimeFrameScopedSource.lean`
- `Solidity/Backend/InternalFlow/RuntimeFrameV3RecursiveScopeCheck.lean`

Statements, premises, exclusions and proof budgets are retained. This does not
establish completion of the lane or discharge its remaining producer obligations.
Touched/library checkpoint gates passed.
Separate read-only finder and skeptic reviews passed with no confirmed findings.
Reviews use exact diff/dependency packets and read-only inspection where available.

The exact source commit has a separate passing finder and skeptic review.
