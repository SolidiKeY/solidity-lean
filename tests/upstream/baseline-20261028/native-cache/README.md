# Native cache diagnosis and diagnostic follow-up

The native diagnostic adapter was already reusable. **No project-module build was run.** A mixed preflight had conflated the76-module Upstream branch with the257-module Testing proof branch. Lake-native hashes verified every narrow source/olean against its trace, recorded imports match current bytes, and the narrower no-build preflight succeeded.

StatePartsScoped was successfully built in the retained900-second attempt; its earlier active snapshot was not a semantic failure or terminal blocker. Testing's current direct ProveChunked import is absent from its saved setup. The stale proof branch remains separate; no retry or increased limits were used.

Actual native results: {'typedImportModes': 40, 'replayModes': 38, 'replayStatuses': {'broken': 12, 'working': 26}, 'matchingRuntimeObservations': 122, 'wrongExpectedValueControls': 2, 'productionProvenanceRefusals': 4, 'internalAbiEntryRefusals': 2, 'typedOnlyModes': 2}. Broken replay batches retain named import refusals; their positive functions were not silently executed. The isolated companion inputs are separate. The deliberate expected8control observes7 and is correctly rejected.

Both modes now observe Panic0x01, Panic0x11 and rollback to counter3; scoped identifiers, scalar wrappers, type bounds, hashes/concats and other selected scalar controls match. Malformed NatSpec is refused through production callbacks. UDVT struct fields, pushed-member postfix increment and try-nested loop jumps retain exact native refusals.

A real state-mutating receiver compound/store control returns107then207, superseding the blanket receiver-call/mutation refusal. This does not admit every pushed-member form. Exact rethrow produces[1,2]; wrong-offset assembly remains excluded.

**nativeValidationComplete remains false:** unchanged replay fixes default msg.value0, so nonzero payment rejection is untested. The Testing proof listing/search frontend remains stale; no proof listing, new semantic theorem or generated EVM observation is claimed. Historical cold timeout and warm-unrun remain unchanged.

Reproduce with `bash scripts/run-solidity-baseline-native.sh /workspace/solidity-lean/.lake/FRESH_NATIVE_OUTPUT`; it validates cache identities before any native preflight, contains no build command and never edits config. Read-only archive/index validation: `python3 scripts/solidity-baseline-native-index.py --check`.

Extract `evidence.tar.gz` into this directory for raw case links. All original baseline and prior diagnostic evidence remains unchanged.

| Feature | Native disposition | Assessment |
|---|---|---|
| identifiers | inventory-evidence-discrepancy | Scoped shadowing returns7, and existing SourceIdentifiers controls typed-import and execute in both modes. No new identifier defect is established by these bounded controls. |
| comments | inventory-evidence-discrepancy | Production specification callbacks now run: nested-comment specification imports and executes; malformed BadClause is refused with solidity.specificationSyntax. Ordinary UTF8/CRLF controls execute. No comment-stripping defect established. |
| pragmaVersion | inventory-evidence-discrepancy | Pinned-compiler accepted source imports natively; production importer refuses mismatched compiler/pragma records. Prior >=0.9 rejection is compiler evidence. No authentication of arbitrary consistent handwritten JSON is claimed. |
| wrapUnwrap | inventory-evidence-discrepancy | Unsigned, bool/address and signed-minus-one wrapper controls typed-import and execute in both modes. UDVT struct-field refusal remains a separately named aggregate dependency gap. |
| typeBounds | inventory-evidence-discrepancy | uint8 max returns255 while int8 min and enum max assertions pass; false max254 emits Panic0x01. Signed enum conversion remains causally separate. |
| numericLiterals | inventory-evidence-discrepancy | Exact-rational/extreme literal controls execute; literals() returns1. Generated runtime ERC7201 overflow remains a separate arithmetic-folding gap, not a literal attribution. |
| unicodeLiterals | inventory-evidence-discrepancy | Unicode byte length4 and existing byte-sequence assertions execute in both modes; no UTF8-specific defect is established. |
| addressLiterals | inventory-evidence-discrepancy | Packed-address and array address-kind controls execute; prior pinned compiler checksum rejection remains compiler evidence, not a valid-source defect. |
| visibility | inventory-evidence-discrepancy | Public entry returns7, internal helper imports as internal, and unchanged external replay refuses checkedHelper(uint8) as no imported ABI entry. This does not certify the full lifetime action set. |
| addressTypes | inventory-evidence-discrepancy | Concrete payable/address conversion returns7 and bool/address wrapper assertions execute in both modes. Native carrier versus source160-bit premise remains declared policy. |
| unaryArithmetic | inventory-evidence-discrepancy | Narrow signed negation returns5 and existing signed literal assertions execute; no new unary source failure established. |
| bitwise | inventory-evidence-discrepancy | Fixed-byte complement returns0 and signed bitwise literal assertions execute; no recursive-resource failure is attributed to bitwise lowering. |
| shifts | inventory-evidence-discrepancy | Signed int8 right shift returns ABI word -4, and huge-count literal controls execute. Existing general lowering proof scope is not promoted. |
| comparisons | inventory-evidence-discrepancy | Signed comparison returns1 and enum/integer bound assertions execute. Unsupported structural aggregate equality is not invented as a missing Solidity shape. |
| shortCircuit | inventory-evidence-discrepancy | The Boolean expression containing a failing die() helper returns1 without failure in both modes; this is bounded lazy-evaluation evidence, not universal source correspondence. |
| blocks | inventory-evidence-discrepancy | Nested declaration-ID shadowing returns outer value7 and localMagic assertions execute; scoped native elaboration succeeds. |
| uncheckedBlock | inventory-evidence-discrepancy | Local uint8 increment wraps to0; a checked helper called from unchecked fails with exact Panic0x11. Both modes preserve the lexical caller/callee distinction. |
| expressionStatements | inventory-evidence-discrepancy | Discarded increment returns counter1; postfix capture returns4 after asserting old3. False assertions produce exact Panic0x01, not a proved false property. |
| deleteExpression | inventory-evidence-discrepancy | Legal array delete executes and returns length0. Prior storage-pointer delete is compiler-invalid and remains excluded from implementation-gap evidence. |
| assertBuiltin | inventory-evidence-discrepancy | False-bound and write-fail assertions emit exact36-byte Panic0x01; the failed write rolls back so later counter read is3. Existing guard lemmas have standard axioms only. |
| keccakBuiltin | named-proof-interface-limit | Equal-content Keccak control returns1. The existing64-literal-byte content closer remains a named proof-automation boundary, not a runtime hash defect or injectivity axiom. |
| sha256Builtin | named-proof-interface-limit | Equal-content SHA256 control returns1. Shared literal-content closer limits and existing same-content interfaces remain distinct from runtime execution. |
| ripemd160Builtin | named-proof-interface-limit | Equal-content RIPEMD160 control returns1. Symbolic/literal-content proof limits do not establish missing executable hash semantics. |
| thisAddress | inventory-evidence-discrepancy | Self identity returns1 under the adapter transaction. The existing160-bit source premise is policy; this observation is not a new proof of that environment bound. |
| uncheckedArithmetic | inventory-evidence-discrepancy | Narrow arithmetic wraps to0 in unchecked; called checked helper preserves Panic0x11. No checked ERC7201 folding failure is reassigned here. |
| hexLiterals | inventory-evidence-discrepancy | Explicit bytes2 hex array returns291; exact hex/Unicode byte controls execute. Raw inferred string[2] hex array was rejected by solc, not Lean. |
| freeFunctions | inventory-evidence-discrepancy | Resolved plusOne free call returns5 in both modes; conditional function-value admission remains separate from ordinary free-function identity lookup. |
| valueTypeDeclarations | observed-native-import-refusal | A memory struct with scalar UDVT field Ticket is refused in member-type dependency lookup; scalar wrappers and fixed UDVT arrays execute. |
| fixedArrays | named-proof-interface-limit | Storage-to-memory fixed-array snapshot returns7 after source storage mutation. Generic fixedCopy/fixedCopyMem exclusion in the verified EVM fragment remains a named compiler-interface limit. |
| valueTypes | observed-native-import-refusal | UDVT struct member lookup is refused; scalar/fixed-array wrapper controls execute. This is a specific nominal field shape. |
| increments | observed-native-import-refusal | Postfix a.push().x++ is refused during production source/native import, even for a pure array receiver; plain member increment companion executes. |
| compoundAssignment | inventory-documentation-discrepancy | State-mutating receiver().push().x += 7 and constant member store both execute, yielding107/207 in each mode. The old blanket receiver-call/mutation refusal is too broad; postfix pushed-member increment remains separately refused. |
| structConstruction | inventory-evidence-discrepancy | Ordinary scalar-member construction returns7. The nominal companion fails during UDVT member-type lookup, not a newly demonstrated construction rule defect. |
| doWhileStatement | observed-native-import-refusal | Continue inside try inside a do-loop is refused by the exact loop jump gate; ordinary do/continue executes. |
| continueStatement | observed-native-import-refusal | The try-inside-loop jump gate refuses continue; the standalone ordinary continuation control returns2. |
| canonicalRethrow | inventory-evidence-discrepancy | Exact whole-buffer rethrow executes with exact[1,2]bytes; wrong offset remains profile-excluded. General assembly and computed-data formula limitations are not promoted. |
| bytesConcat | named-proof-interface-limit | Concatenated bytes length2 and both byte-content assertions execute; general symbolic heap-writing loop summaries remain the named proof-interface limit. |
| stringConcat | named-proof-interface-limit | Byte length of concatenated string returns2; this is concrete runtime evidence, not a general symbolic constructed-content theorem. |
| danglingReferences | named-model-assumption-limit | The selected recycled-slot model path returns5. This is not generated EVM evidence or a portable all-version definedness guarantee; clean-tail/callback premises remain explicit. |
| nonpayableEntry | diagnostic-capability-limit | Ordinary zero-value public entry executes; internal helper is not an imported ABI entry. Nonzero msg.value external-entry rejection remains untested because unchanged replay fixes default msgValue0. |

## Per-case evidence

| Case | Mode | Typed report | Replay |
|---|---|---|---|
| [BadClause](runs/BadClause/legacy/record.json) | legacy | retained | broken |
| [BadClause](runs/BadClause/viaIR/record.json) | viaIR | retained | broken |
| [CommentRanges](runs/CommentRanges/legacy/record.json) | legacy | retained | working |
| [CommentRanges](runs/CommentRanges/viaIR/record.json) | viaIR | retained | working |
| [CommentSpecPositive](runs/CommentSpecPositive/legacy/record.json) | legacy | retained | working |
| [CommentSpecPositive](runs/CommentSpecPositive/viaIR/record.json) | viaIR | retained | working |
| [ComputedRevert](runs/ComputedRevert/legacy/record.json) | legacy | retained | typed only |
| [ComputedRevert](runs/ComputedRevert/viaIR/record.json) | viaIR | retained | typed only |
| [ConstantsEnums](runs/ConstantsEnums/legacy/record.json) | legacy | retained | working |
| [ConstantsEnums](runs/ConstantsEnums/viaIR/record.json) | viaIR | retained | working |
| [ExactRethrow](runs/ExactRethrow/legacy/record.json) | legacy | retained | working |
| [ExactRethrow](runs/ExactRethrow/viaIR/record.json) | viaIR | retained | working |
| [HexArrayExplicit](runs/HexArrayExplicit/legacy/record.json) | legacy | retained | working |
| [HexArrayExplicit](runs/HexArrayExplicit/viaIR/record.json) | viaIR | retained | working |
| [NativePositive](runs/NativePositive/legacy/record.json) | legacy | retained | working |
| [NativePositive](runs/NativePositive/viaIR/record.json) | viaIR | retained | working |
| [NominalStruct](runs/NominalStruct/legacy/record.json) | legacy | retained | broken |
| [NominalStruct](runs/NominalStruct/viaIR/record.json) | viaIR | retained | broken |
| [PushedMember](runs/PushedMember/legacy/record.json) | legacy | retained | broken |
| [PushedMember](runs/PushedMember/viaIR/record.json) | viaIR | retained | broken |
| [PushedMemberMutation](runs/PushedMemberMutation/legacy/record.json) | legacy | retained | working |
| [PushedMemberMutation](runs/PushedMemberMutation/viaIR/record.json) | viaIR | retained | working |
| [PushedMemberPositive](runs/PushedMemberPositive/legacy/record.json) | legacy | retained | working |
| [PushedMemberPositive](runs/PushedMemberPositive/viaIR/record.json) | viaIR | retained | working |
| [ScalarMatrixValid](runs/ScalarMatrixValid/legacy/record.json) | legacy | retained | working |
| [ScalarMatrixValid](runs/ScalarMatrixValid/viaIR/record.json) | viaIR | retained | working |
| [SourceIdentifiers](runs/SourceIdentifiers/legacy/record.json) | legacy | retained | working |
| [SourceIdentifiers](runs/SourceIdentifiers/viaIR/record.json) | viaIR | retained | working |
| [SourceLiterals](runs/SourceLiterals/legacy/record.json) | legacy | retained | working |
| [SourceLiterals](runs/SourceLiterals/viaIR/record.json) | viaIR | retained | working |
| [SourceTypes](runs/SourceTypes/legacy/record.json) | legacy | retained | working |
| [SourceTypes](runs/SourceTypes/viaIR/record.json) | viaIR | retained | working |
| [SpecBindings](runs/SpecBindings/legacy/record.json) | legacy | retained | broken |
| [SpecBindings](runs/SpecBindings/viaIR/record.json) | viaIR | retained | broken |
| [TryContinue](runs/TryContinue/legacy/record.json) | legacy | retained | broken |
| [TryContinue](runs/TryContinue/viaIR/record.json) | viaIR | retained | broken |
| [TryContinuePositive](runs/TryContinuePositive/legacy/record.json) | legacy | retained | working |
| [TryContinuePositive](runs/TryContinuePositive/viaIR/record.json) | viaIR | retained | working |
| [WrongRethrow](runs/WrongRethrow/legacy/record.json) | legacy | retained | broken |
| [WrongRethrow](runs/WrongRethrow/viaIR/record.json) | viaIR | retained | broken |

## Historical snapshots

The gap index at66629757, attribution index at13edcbe4 and reader-only matrix atc4a5a2f1 remain unchanged snapshot evidence. Their documentary hashes refer to those checkpoints; later documentation appendices legitimately differ. Replay their generators against the recorded checkpoint, not current appended prose. This milestone validates preserved bytes and the new native index; it does not silently regenerate those reports.

## Next waves

- diagnostic-capability-limit: nonpayableEntry.
- inventory-documentation-discrepancy: compoundAssignment.
- inventory-evidence-discrepancy: identifiers, comments, pragmaVersion, wrapUnwrap, typeBounds, numericLiterals, unicodeLiterals, addressLiterals, visibility, addressTypes, unaryArithmetic, bitwise, shifts, comparisons, shortCircuit, blocks, uncheckedBlock, expressionStatements, deleteExpression, assertBuiltin, thisAddress, uncheckedArithmetic, hexLiterals, freeFunctions, structConstruction, canonicalRethrow.
- named-model-assumption-limit: danglingReferences.
- named-proof-interface-limit: keccakBuiltin, sha256Builtin, ripemd160Builtin, fixedArrays, bytesConcat, stringConcat.
- observed-native-import-refusal: valueTypeDeclarations, valueTypes, increments, doWhileStatement, continueStatement.

Existing named memory/hash/compiler-fragment limits remain declaration-backed limits, not universal missing-proof demands. Inventory evidence recommendations do not promote statuses. See matrix.json for exact controls, historical declaration links and the rejected original-variant association candidates.
