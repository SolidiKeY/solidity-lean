from pathlib import Path
import hashlib,json
root=Path.cwd();area=root/'tests/directruntime-20261104/native-browser/environment';private=root/'.lake/native-browser-environment';out=private/'handoff-data';scratch=Path('/workspace/scratch/browser-chain/environment');assert (scratch/'B-kernel-gate.json').exists();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();intake=json.loads((area/'intake.json').read_text());n=json.loads((private/'native/build.json').read_text());w=json.loads((private/'direct/build.json').read_text());gates=[]
for p in sorted(scratch.glob('*-gate.json')):
 d=json.loads(p.read_text());gates.append({'command':d['command'],'status':'pass' if d['exitCode']==0 else 'fail','receipt':str(p),'sha256':sha(p),'exitCode':d['exitCode'],'wallSeconds':d['wallSeconds'],'sampledRssPeakBytes':d['sampledContainerProcessRssPeakBytes'],'minimumOuterHeadroomBytes':d['minimumOuterHeadroomBytes'],'scope':d['scope']})
archives=[{'path':str(out/name),'bytes':(out/name).stat().st_size,'sha256':sha(out/name)} for name in ['evidence.tar.gz','runtime-artifacts.tar.gz','incremental-cache.tar.gz','evidence-files.json','runtime-files.json','cache-files.json']]
manifest={'guardedRegression':intake['guardedRegression'],'base':'b419c3cf4f642ae519b66bebc26cdf2f7cf93574','sourceBuildHead':'4d7285b80e89741e9da8cb49ce7ab8b62a828a72','adoptedMaster':'e0f4251ff40ad79c37bae53795b7419afe52e8d9','producerHead':intake['producerHead'],'sourceIntake':intake,'fullEightFileByteIdentity':False,'currentSourceBoundary':'All8delivered frontier modules authenticated.Currentpublished7byteexact;Translate35d642 is90479 pluspublishedstandaloneguardtheorem.No runtime definition/import/attribute difference afterexactprojection,publishedproofnotremoved.Not byteidentity/binaryequivalence/fullsourceorABIadequacy.','binaries':{'native':n['executable'],'wasm':w['wasm'],'nativeBytes':(private/'native/direct-check').stat().st_size,'wasmBytes':w['wasmBytes']},'closure':n['closure'],'environmentControlsPerBackend':{'sourceLevelFixtureRequests':16,'proved':8,'refuted':4,'unsupported':4,'additionalPositiveGuards':2,'sourceIdRequestReplyChecks':18,'boxSourceAnnotations':8,'unsupportedSiblingReasons':['unknown name block','unknown name tx'],'refutedReason':'counterexample found'},'metadataGuards':{'successKeys':['msg.sender','msg.value','block.timestamp'],'negativeCases':15,'unsupportedSiblingKeys':['block.number','tx.origin'],'baseFirstErrorPriority':True},'sourceProofControls':{'environmentMemberAxioms':[],'environmentMemberGuardAxioms':['propext','Quot.sound'],'otherDecoderLemmas':['localValueTypeName_of_address','localTypeName_of_narrow','localTypeName_of_fixedBytes'],'otherDecoderAxioms':['propext','Classical.choice','Quot.sound'],'MCPfiles':13,'MCPerrors':0,'boundary':'Kernel decoder/guard equations plus selectedmetadata/modelchecks;not compileridentityauthentication,source/world/ABI/nativeadequacy or exhaustiveoverload/grammarparity.'},'retainedControlsPerBackend':{'address16':{'proved':10,'refuted':2,'unsupported':4,'guards':2},'stateAddressGap':1,'fixedByte20':{'proved':12,'refuted':4,'unsupported':4,'guards':2},'C13':{'proved':9,'unsupported':4,'guard':1},'A8':{'proved':6,'refuted':2,'guard':1},'B84':{'proved':64,'refuted':16,'pending':4,'positiveIdentityDiamondBothCompilerModes':True,'exactOriginalJournal':True},'existing83':{'proved':83,'rounds':1,'timingAcceptance':False},'nativeNegativeVerdicts':14,'browserNegativeVerdicts':{'passed':13,'total':14,'failure':'invariantCountsToBound stack overflow'},'UI':'Fresh edited-source/counterexample/offline controls pass'},'finiteModelControls':{'modalCases':18,'effectCheck':1,'refusals':2,'intrinsicMemoryControls':12},'independentCompilerReceipt':json.loads((private/'producer-args-compilation.json').read_text()),'producerDeliveryBoundary':'Sourcearchive/ticketverified andsourcebyteextractioncomplete. ProducerAST/evidence remainNOTDELIVERED;freshDcompilation isindependent,not historicalsubstitution orproducerreceipt.','optionalKernelCandidateExclusion':json.loads((scratch/'candidate-exclusion.json').read_text()),'ordinaryBoundary':'Actual native/generated-C-WASM boot/request/sourceID/binarybindings andno forbiddenserializedenv/frontendloads observed.SelectedC/object/native/WASM/import/exportinventory and4optionalhelperfamiliesabsent are not universalpurity/sourcepreservation proof.Certificates remainoptional/uncertified.','resources':'Serial12GiB/swap0/CPU1,threads1/-j1,writerlock,4GiBouterreserve;eachgate actualwall/RSS/headroom below.','STOPs':'Originalnative median+21.32%,browserstartup+32.20% andpriornativebuild+26.13%STOPs retained;no unchangedstoppedbenchmarkrerun,no performanceacceptance.','runtimeGate':'pending','gates':gates,'archives':archives,'cache':'32incremental artifacts locallyverified/coordinatorpending;no ship-cache/noH88cross-cachecoherence claim.','reviews':'Independent read-only finder/skepticintake/projectionreviewsPASS;finalarchive/resultsreview recordedinhandoff.No Lean/server/buildbyreviewers.','status':'Freshcurrentpublishedcomputationalfrontierobservations;not full8byteexactsnapshot orwholeoriginalgoalcompletion.'}
(area/'results-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');(area/'registration-proposal.json').write_text(json.dumps({'guardedRegression':'Environmentmetadata/identity/errororderkernelguards are standalone testdriver,notnewproductionroot.','modules':[{'path':'tests/directruntime-20261104/native-browser/environment/MetadataControls.lean','role':'15metadatafoils/siblings/errorpriority/signatures/axioms','centralAction':'Proposal only;no sharedgeneratedroot edits'}]},indent=2)+'\n')
with (root/'docs/feature-work/directruntime-native-browser.md').open('a') as f:f.write('''

## Authenticated environment source and published guard theorem

The coordinator source archive6e53ff49…6646ac and ticketcd333e5e…35f645 were
verified and safely extracted into coordinator inputs. All8frontier snapshots
and all12coordinator source/control/manifest entries match their hashes. The
assigned branch fast-forwarded to published mastere0f4251ff before further work.
Seven current frontier files match byte-for-byte;Translate35d642 contains exactly
the delivered90479 definitions plus a37-line standalone guard-inversion theorem.
Removing only that theorem/doc for comparison reproduces90479 exactly. The
published proof is retained. This is not eight-file byte identity or a claim of
binary/source equivalence;actualcurrent hashes and limits are recorded in the
[results manifest](../../tests/directruntime-20261104/native-browser/environment/results-manifest.json).

Fresh native and real Chromium requests use the current published source build
4d7285b80e89741e9da8cb49ce7ab8b62a828a72. All16source-level box/diamond cases
match8proved,4refuted,4unsupported perbackend,plus2positive guards. Actual compiler
function IDs select each request and match each reply. Unsupported block.number
and tx.origin retain exact unknown-name diagnostics;wrong value/time assertions
refute. Eight box annotations erase to the exactc6b4f237 source. Fifteen metadata
foils,three supportedkeys,two unsupportedsiblings andbase-first error priority
pass per-file guards. The helper prints no axioms;the published guard theorem
prints propext/Quot.sound,not compileridentity orworldadequacy assumptions.

Thirteen per-file diagnostics and retained decoder/model controls pass. Fresh
address16,stategap,fixed-byte20,C13,A8,B84 and83functional observations match their
unchanged expectations on native/browser. Identitydiamond succeeds in both
compiler modes;four storage-diamond cases remainpending. Native negatives/UI
pass;browser negatives remain13/14 with invariant stack overflow. Complete
selected-C/object/import/export inventory and optional-kernel-helper exclusion
are limited executable evidence,not universal purity orsource/ABI/native proofs.
All original stack/performance/build-cost STOPs remain;no stopped benchmark was
rerun andRUNTIME_GATE_PASS stayspending.

The exact producer AST/evidence archive remain undelivered. A fresh independent
compiler run uses the authenticated source and producer arguments,with an
explicit expected-hash comparison;it is not labelled producer delivery or used
to replace a historical journal. Actualfixture/source/compiler/binary identities
are retained separately. Bulk data stays offGit withper-file indexes/SHA256.
Local registration proposal:environment/MetadataControls.lean is a standalone
per-file driver;no generatedroot addition. Verified32-artifact incrementalcache
is coordinatorpending;no ship-cache orH88coherence success is inferred.
''')
print(str(area/'results-manifest.json'))
