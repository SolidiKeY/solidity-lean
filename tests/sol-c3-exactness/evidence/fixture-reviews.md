# Separate required fixture and acceptance reviews

Finder and skeptic independently read the fixture sources, checker, exact ledger,
kernel GraphControls and Audit type links, evidence packet and acceptance script.
Both were explicitly read-only and used neither Lean/server nor check execution.

Confirmed findings and fixes:
- Mixed and illegal-interface sources initially differed from intrinsic controls;
  aligned IA→IB→C and A/I names. Added W to the ordering-obstruction source.
- Compiler refusal at Z does not independently observe inherited refusal at W;
  both manifest and output packet explicitly reserve that result to the kernel.
- Rejection substring matching admitted empty/broad expectations; replaced with
  fixed-ledger exact code/type/message diagnostic arrays and count, plus controls.
- JSON expectations alone did not link observations to kernel tests; thirteen
  active typed Audit assertions now bind exact named existing observations.
- Runner snapshots initially omitted fixture inputs; all scripts/ledger/sources
  and coordinator axiom request now bind receipts, and passed logs bind packet
  bytes by SHA-256. Acceptance rejects stale data, wrong orders/diagnostics,
  missing type links and undiscovered extra fixtures.
- Finder found negatives that would become valid in a genuinely completed phase;
  missing-obligation test now forces pending, fake completion removes required
  module inventory so passed full receipts cannot match. Follow-up finder accepts.

Final finder: "fixtures checkpoint passes"; no remaining concrete checkpoint
blocker. Final skeptic: "Fixture source and evidence review: pass". Both
explicitly exclude required registration, full-driver and remaining final gates.
The saved acceptance-fixtures log records 21 general + 9 fixture mutations and
FIXTURES_CHECKPOINT_PASS, 222 explicit constants/constructors and twelve families.

Setup/diagnostic attempt history (not successful final gates):
- Initial fixture file-writing shell had a quoting error; corrected file via
  locked Python write before any compiler execution.
- Initial unchanged run-lean exited127: python3 absent from container PATH.
  Mounted existing Python added to runner PATH; driver then exits1 on eight
  coordinator-owned missing imports. Both raw original/preflight logs retained.
- First source-gate attempt used external SolKey snapshot lacking adjacent pin:
  ENOENT /workspace/.setup/solkey.pin.json. Corrected to repository frozen snapshot
  tests/migration/solkey, verified commit473da8944ca7329e6b76819863591407db26e7ec
  and manifest SHA c8d6166c3d728174eded3c3279fe499470f143943877a1307745f7a6b2da1b37.
  Subsequent TestSuite gate passes552 derived+11 refuted+0 pending+1 excluded,
  2 skip; the early setup result is recorded here as a transcription.
- Independent default-target build stopped by this lane after105.23s to release
  writer lock for reviewer fixes; interrupted=true, exit1, no memory-pressure
  stop. Its raw log/receipt remain. It is not counted as full build success.
- Intermediate fixture acceptance caught outdated Audit hash; manifest corrected
  and fresh guarded kernel/source-bound fixture receipts now pass.

No theorem was weakened, no producer changed, no proof budget raised. All fixture
observations remain external analysis tests, not parser correctness or constructor
body execution proofs. The full schema refuses pending/failed gates.
