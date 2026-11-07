# Static producer endpoint field classification

Frozen source: Solidity/Backend/StorageOps/ProducerInterface.lean, namespace
Solidity.Backend.StorageOps.ProducerInterface. Dependency definition:
Solidity/Storage/Representation/Transport.lean. These are source inspections,
not checked inhabitants, new theorem rows, or permission to repair producer files.
No field is erased or replaced. The whole shared parameter tuple is required.

| Structure | Shared parameters | Fields and scope |
|---|---|---|
| PathEndpoint | n/G/A/B/path/base/slot | supported: PathSupported path; fits: KeysFit base; image: slot equals toSlot of pathLoc using the fitting proof derived from this same path/base/fits |
| StateEndpoint | n/N/L/R/G/A/root/queries/base/hash/preimages/locations/symbolic/numeric/target | represented on root/queries/base/symbolic; run on N/L/R/hash/preimages/locations; transport on N/hash/locations/symbolic/numeric; covered for queries; fitting for locations; observations on the same target/symbolic/fitting |
| ReachedEndpoint | StateEndpoint parameters except target, plus code/before/after | state instantiates StateEndpoint at after; execution requires Evm.run code before = .ok after 0 with that SAME after |

These record types describe one selected path, state or reached execution. They
supply no universal Source compiler producer. Inhabiting a structure type at one
arbitrary tuple cannot establish feasibility at a consumer's different tuple.
Independent field inhabitants are insufficient, especially when execution and
observations must refer to the same after machine.

The run field is not reducible to a trivial finite-list check. FiniteRun has:

- hash_bound: ∀ p, H p < N (all preimages, not only P);
- region_bound: L ≤ N;
- root_bound: R ≤ N;
- regions: RegionsDisjoint N L H (List.range R) P;
- bounded: ∀ l ∈ touched, Loc.Bounded L R l;
- covered: ∀ l ∈ touched, ∀ p ∈ Loc.pres N H l, p ∈ P.

Thus there is a universally quantified hash bound inside a selected finite-run
certificate. Classifying every mentioned FiniteRun as either an inhabited global
producer or purely pointwise feasibility would lose that distinction. Transport
is exactly agreement at the selected touched locations, with the same N/H/stores.
No injectivity outside the selected footprint is inferred.

ProducerInterfaceControls uses one bool scalar, path=nil, root0, N=8/L=1/R=1,
hash=constant0, no preimages, one location and one query. Its state_endpoint and
reached_endpoint definitions share their inputs and refer to an actual scalar
write. They are existing source-level candidate evidence; they have not been
validated under the held pinned toolchain and are not a global compiler witness.
This reading does not prove that a requested backend producer repair is complete,
needed in this exact module, or authorized for this worker. Await the owner's
exact disposition; the router supplied no repair diff in this turn.
