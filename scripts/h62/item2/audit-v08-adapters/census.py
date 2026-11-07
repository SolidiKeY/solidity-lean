#!/usr/bin/env python3
"""Conservative frozen-source census. Lexical candidates are NOT Lean certificates.
All theorem tokens outside comments/strings are retained, including controls and
premise-free statements, so a heuristic never silently excludes an obligation.
Bulk results belong outside Git. Run from any directory with --repo and --out.
"""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
MAP = "docs/module-map/v08-adapters.md"

# Q-WORLD-AUDIT-RAWINT (#54): fixed, whole-file reviewed correspondences.
# Kinds: 1=mapFree argument/binder; 2=change-step && _; 3=lit_ok _ _;
# 4=empty cursor field. Additional forms below require the separate #55 trace rule.
# All rows cite the reviewed VY5 integration; kind 4 also cites its origin.
VY5_INTEGRATION = "e8247d9277190b71488387dac594e82b2b191942"
CURSOR_ORIGIN = "d83228dae5e6d141cd1ff454c75d544fc7f7cb60"
BASELINE_CORRESPONDENCE = {
    'Solidity/Backend/CalldataPackets/RawAddress/Controls.lean': (4,),
    'Solidity/Backend/CalldataPackets/RawInt/Execution.lean': (2,),
    'Solidity/Backend/CalldataPackets/RawUintN/Execution.lean': (1, 2),
    'Solidity/Backend/Executable/ConstructorArgumentObservations.lean': (1,),
    'Solidity/Backend/Executable/ConstructorLocalArguments.lean': (1,),
    'Solidity/Backend/PrimitivePackets/Comparisons/Controls.lean': (4,),
    'Solidity/Frontend/Admission/ModifierRoots.lean': (1,),
    'Solidity/Frontend/Admission/TypedExpressionPolicy.lean': (1,),
    'Solidity/Frontend/Admission/TypedObservationPolicy.lean': (1,),
    'Solidity/Lowering/V08/CallableMetadata.lean': (1,),
    'Solidity/Lowering/V08/LiteralFailureConvertedFields.lean': (1,),
    'Solidity/Lowering/V08/LiteralFailureCopySequence.lean': (1,),
    'Solidity/Lowering/V08/LiteralFailureMixedCustomError.lean': (1,),
    'Solidity/Lowering/V08/MetadataControls.lean': (1,),
    'Solidity/Lowering/V08/SourceCustomErrorFailures.lean': (1,),
    'Solidity/Source/Preservation/AllocatingFragment.lean': (1,),
    'Solidity/Source/Preservation/AllocationBodyControls.lean': (1,),
    'Solidity/Source/Preservation/EncodingVariants.lean': (1,),
    'Solidity/Source/Preservation/MemoryBodies.lean': (1,),
    'Solidity/Source/Preservation/MemoryExpressions.lean': (1,),
    'Solidity/Source/Preservation/ReferenceArguments.lean': (1,),
    'Solidity/Source/Preservation/ValueConversions.lean': (1,),
    'Solidity/Source/Progress/AllocationReturns.lean': (1,),
    'Solidity/Source/Progress/ArithmeticBuiltins.lean': (1,),
    'Solidity/Source/Progress/BoundParents.lean': (1,),
    'Solidity/Source/Progress/BuiltinAdmission.lean': (1,),
    'Solidity/Source/Progress/BuiltinStatements.lean': (1,),
    'Solidity/Source/Progress/EffectBodies.lean': (1,),
    'Solidity/Source/Progress/ForwardingChain.lean': (1,),
    'Solidity/Source/Progress/ForwardingControls.lean': (1,),
    'Solidity/Source/Progress/ForwardingReturns.lean': (1,),
    'Solidity/Source/Progress/ParentArguments.lean': (1,),
    'Solidity/Source/Progress/ReadyArguments.lean': (1,),
    'Solidity/Source/Progress/ReadyBodies.lean': (1,),
    'Solidity/Source/Progress/ReadyExpressions.lean': (1,),
    'Solidity/Source/Progress/ReadyProgram.lean': (1,),
    'Solidity/Source/Progress/ReadyProgramControls.lean': (1,),
    'Solidity/Source/Progress/ReadyReturns.lean': (1,),
    'Solidity/Source/Progress/RecoveryBuiltin.lean': (1,),
}
# Q-WORLD-VY5-OTHER-HUNKS (#55) supersedes the hunk-kind restriction for
# these exact 79 files. Each tuple lists verified on-master history/introducer
# commits; the complete per-hunk replay and blame evidence remains off Git.
MASTER_TRACE_CORRESPONDENCE = {
    'Solidity/Lowering/G19/AssignmentBlocks.lean': ('066f26a388d383c4e8704da5b8af7a3d86fce1c3', '1a226a21efc90a3138e084af91246630f97e3ea4', 'b046da6c672eb7a9100d72a7c98a079e49594a5e'),
    'Solidity/Lowering/G19/AssignmentDoWhileBreak.lean': ('066f26a388d383c4e8704da5b8af7a3d86fce1c3', '1a226a21efc90a3138e084af91246630f97e3ea4', 'b046da6c672eb7a9100d72a7c98a079e49594a5e'),
    'Solidity/Lowering/G19/AssignmentDoWhileBreakControls.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '66960116ca1628603b9a8e32de9a9c53112d06d7', 'b046da6c672eb7a9100d72a7c98a079e49594a5e'),
    'Solidity/Lowering/G19/AssignmentDoWhileContinue.lean': ('066f26a388d383c4e8704da5b8af7a3d86fce1c3', '1a226a21efc90a3138e084af91246630f97e3ea4', 'b046da6c672eb7a9100d72a7c98a079e49594a5e'),
    'Solidity/Lowering/G19/AssignmentDoWhileContinueControls.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '66960116ca1628603b9a8e32de9a9c53112d06d7', 'b046da6c672eb7a9100d72a7c98a079e49594a5e'),
    'Solidity/Lowering/G19/AssignmentDoWhileReturn.lean': ('066f26a388d383c4e8704da5b8af7a3d86fce1c3', '1a226a21efc90a3138e084af91246630f97e3ea4', 'b046da6c672eb7a9100d72a7c98a079e49594a5e'),
    'Solidity/Lowering/G19/AssignmentDoWhileReturnControls.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '66960116ca1628603b9a8e32de9a9c53112d06d7', 'b046da6c672eb7a9100d72a7c98a079e49594a5e'),
    'Solidity/Lowering/G19/AssignmentForBreak.lean': ('066f26a388d383c4e8704da5b8af7a3d86fce1c3', '1a226a21efc90a3138e084af91246630f97e3ea4', 'b046da6c672eb7a9100d72a7c98a079e49594a5e'),
    'Solidity/Lowering/G19/AssignmentForBreakControls.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '66960116ca1628603b9a8e32de9a9c53112d06d7', 'b046da6c672eb7a9100d72a7c98a079e49594a5e'),
    'Solidity/Lowering/G19/AssignmentReturnFlag.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', 'b628f5b1f2dccdd8108e19942902c52d11688ff5'),
    'Solidity/Lowering/G19/AssignmentWhileBreak.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '7ce2f385de297f91742df3ebad9f74668deb0d2d', '84ec7ed1e78ed4b0a3e689468f97e56f0c84ac6c', 'b046da6c672eb7a9100d72a7c98a079e49594a5e'),
    'Solidity/Lowering/G19/AssignmentWhileReset.lean': ('066f26a388d383c4e8704da5b8af7a3d86fce1c3', '1a226a21efc90a3138e084af91246630f97e3ea4', 'b046da6c672eb7a9100d72a7c98a079e49594a5e'),
    'Solidity/Lowering/G19/ConditionalSequence.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '2eb354bb091065537cff94b20f737a7ed391c534', 'd83228dae5e6d141cd1ff454c75d544fc7f7cb60'),
    'Solidity/Lowering/G19/ConditionalStatement.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', 'a454a8723a044d8fc0978bb91429267871004c2b', 'e5fabb4ef81bf11893bd72afb3d678fb9a3a639b'),
    'Solidity/Lowering/G19/ReturnTail.lean': ('0eea935ba7d475200ca1e248c9bee1253c73c4c7', '1a226a21efc90a3138e084af91246630f97e3ea4', 'b046da6c672eb7a9100d72a7c98a079e49594a5e'),
    'Solidity/Lowering/G19/WhileReturn.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '674cc1797b911fbf5bf3d626cc4a44e2af949ec1'),
    'Solidity/Lowering/V08/ConstructorScalarTransport.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/EnvironmentProjection.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/LibraryPremises.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4', '7ce2f385de297f91742df3ebad9f74668deb0d2d'),
    'Solidity/Lowering/V08/LiteralFailureBoolPrefixControls.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '7ce2f385de297f91742df3ebad9f74668deb0d2d', '84ec7ed1e78ed4b0a3e689468f97e56f0c84ac6c'),
    'Solidity/Lowering/V08/LiteralFailureCalldataCopyControls.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '7ce2f385de297f91742df3ebad9f74668deb0d2d', '84ec7ed1e78ed4b0a3e689468f97e56f0c84ac6c'),
    'Solidity/Lowering/V08/LiteralFailureMixedCustomErrorControls.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '7ce2f385de297f91742df3ebad9f74668deb0d2d', '84ec7ed1e78ed4b0a3e689468f97e56f0c84ac6c'),
    'Solidity/Lowering/V08/LiteralFailureNestedSlice.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '7ce2f385de297f91742df3ebad9f74668deb0d2d', 'fb43ae8609fed20157756800113fffff668d8a4c'),
    'Solidity/Lowering/V08/LiteralFailureSliceChain.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '7ce2f385de297f91742df3ebad9f74668deb0d2d', 'ecda06166e5cf1d15713656ed407472163c18724'),
    'Solidity/Lowering/V08/LiteralFailureSliceEncoding.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '7ce2f385de297f91742df3ebad9f74668deb0d2d', '84ec7ed1e78ed4b0a3e689468f97e56f0c84ac6c'),
    'Solidity/Lowering/V08/LiteralFailureStringInterleavingControls.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '7ce2f385de297f91742df3ebad9f74668deb0d2d', '84ec7ed1e78ed4b0a3e689468f97e56f0c84ac6c'),
    'Solidity/Lowering/V08/LiteralFailureStringPrefixControls.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '7ce2f385de297f91742df3ebad9f74668deb0d2d', '84ec7ed1e78ed4b0a3e689468f97e56f0c84ac6c'),
    'Solidity/Lowering/V08/LiteralFailureTypedFieldsControls.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '7ce2f385de297f91742df3ebad9f74668deb0d2d', '84ec7ed1e78ed4b0a3e689468f97e56f0c84ac6c'),
    'Solidity/Lowering/V08/LocalCallableTransport.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4', '2a2cf593a91d40a427b55a3e14b6e2c15d996a19', '2eb354bb091065537cff94b20f737a7ed391c534'),
    'Solidity/Lowering/V08/ProjectionControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SliceFailureLowering.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '2eb354bb091065537cff94b20f737a7ed391c534', '3e1a17f4267af1e323e3495cee2c66b2716be3b3'),
    'Solidity/Lowering/V08/SourceAbiControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4', '7256a1ad97227e488b1b8fa1fcd4263077f47e53'),
    'Solidity/Lowering/V08/SourceCallableControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4', 'e1db8b99d604e9c93557c7aba3345ac3b7485f86'),
    'Solidity/Lowering/V08/SourceConstructorArgumentsControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourceCustomErrorControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4', 'e1db8b99d604e9c93557c7aba3345ac3b7485f86'),
    'Solidity/Lowering/V08/SourceCustomErrorFailureControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4', 'e1db8b99d604e9c93557c7aba3345ac3b7485f86'),
    'Solidity/Lowering/V08/SourceDeploymentControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourceDeploymentSessionControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourceDispatchControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4', 'e1db8b99d604e9c93557c7aba3345ac3b7485f86'),
    'Solidity/Lowering/V08/SourceEmitControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4', 'e1db8b99d604e9c93557c7aba3345ac3b7485f86'),
    'Solidity/Lowering/V08/SourceEnvironmentControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4', 'e1db8b99d604e9c93557c7aba3345ac3b7485f86'),
    'Solidity/Lowering/V08/SourceFailedDeploymentControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourceMemoryKeccak.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourcePayableDeploymentControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourcePrefixedRethrowControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourceRethrowControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourceSessionCreditControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourceStandardRethrowControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourceTransactionControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourceTransientBytesEmitControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourceTransientEmitControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourceTransientEmitPanicControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourceTransientErrorCallerRollback.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourceTransientInnerRollbackOuterCommit.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourceTransientMixedRethrowControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourceTransientOwnerCommit.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourceTransientOwnerRollback.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourceTransientReachedPayment.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourceTransientReentry.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourceTransientRejectedPayment.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourceTransientRethrowControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/SourceTransientSameOwnerPayment.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/WorldCatalogueControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Lowering/V08/WorldImageAccess.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '2eb354bb091065537cff94b20f737a7ed391c534', '7ce2f385de297f91742df3ebad9f74668deb0d2d', '84ec7ed1e78ed4b0a3e689468f97e56f0c84ac6c'),
    'Solidity/Lowering/V08/WorldImageAccessControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4', '7ce2f385de297f91742df3ebad9f74668deb0d2d', 'e1db8b99d604e9c93557c7aba3345ac3b7485f86', 'fb43ae8609fed20157756800113fffff668d8a4c'),
    'Solidity/Lowering/V08/WorldResetControls.lean': ('046292ee61fc6967311bbb1ddec44505ed698481', '1a226a21efc90a3138e084af91246630f97e3ea4'),
    'Solidity/Source/Preservation/Combinators.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '2eb354bb091065537cff94b20f737a7ed391c534', '3e1a17f4267af1e323e3495cee2c66b2716be3b3'),
    'Solidity/Source/Preservation/MemoryBodyCalls.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '7ce2f385de297f91742df3ebad9f74668deb0d2d', 'fb43ae8609fed20157756800113fffff668d8a4c'),
    'Solidity/Source/Preservation/MemoryProgramControls.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '7ce2f385de297f91742df3ebad9f74668deb0d2d', 'ecda06166e5cf1d15713656ed407472163c18724'),
    'Solidity/Source/Preservation/Reads.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '2eb354bb091065537cff94b20f737a7ed391c534', '3449b61d4bdd1b1e8670182ebb6553894251173c'),
    'Solidity/Source/Preservation/ReferenceReturns.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '7ce2f385de297f91742df3ebad9f74668deb0d2d', '84ec7ed1e78ed4b0a3e689468f97e56f0c84ac6c'),
    'Solidity/Source/Progress/AggregateReturnControls.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '7ce2f385de297f91742df3ebad9f74668deb0d2d', 'ecda06166e5cf1d15713656ed407472163c18724'),
    'Solidity/Source/Progress/AllocationBodyCallControls.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '7ce2f385de297f91742df3ebad9f74668deb0d2d', 'ecda06166e5cf1d15713656ed407472163c18724'),
    'Solidity/Source/Progress/BoundCatalogueParentControls.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '4ffa5a674d1593680d63442a2128d2b45407ab5c', '7ce2f385de297f91742df3ebad9f74668deb0d2d'),
    'Solidity/Source/Progress/BoundParentControls.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '7ce2f385de297f91742df3ebad9f74668deb0d2d', 'ecda06166e5cf1d15713656ed407472163c18724'),
    'Solidity/Source/Progress/BoundParentPanicControls.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '7ce2f385de297f91742df3ebad9f74668deb0d2d', 'ecda06166e5cf1d15713656ed407472163c18724'),
    'Solidity/Source/Progress/CallComposition.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '7256a1ad97227e488b1b8fa1fcd4263077f47e53', '7ce2f385de297f91742df3ebad9f74668deb0d2d', 'ecda06166e5cf1d15713656ed407472163c18724'),
    'Solidity/Source/Progress/ParentArgumentControls.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '7ce2f385de297f91742df3ebad9f74668deb0d2d', 'ecda06166e5cf1d15713656ed407472163c18724'),
    'Solidity/Source/Progress/ReadyReturnControls.lean': ('1a226a21efc90a3138e084af91246630f97e3ea4', '4ffa5a674d1593680d63442a2128d2b45407ab5c', '7256a1ad97227e488b1b8fa1fcd4263077f47e53', '7ce2f385de297f91742df3ebad9f74668deb0d2d'),
}
BASELINE_OVERRIDES = {path: VY5_INTEGRATION
    for path in (*BASELINE_CORRESPONDENCE, *MASTER_TRACE_CORRESPONDENCE)}

def correspondence_notes():
    notes = {path: dict(basis="reviewed-four-kinds", kinds=kinds,
        citations=[VY5_INTEGRATION] + ([CURSOR_ORIGIN] if 4 in kinds else []))
        for path, kinds in BASELINE_CORRESPONDENCE.items()}
    notes.update({path: dict(basis="master-hunk-trace-issue-55",
        citations=[VY5_INTEGRATION, *commits])
        for path, commits in MASTER_TRACE_CORRESPONDENCE.items()})
    return notes

def frozen_blobs(repo):
    tracked = subprocess.check_output(["git", "ls-tree", "-rz", BASE], cwd=repo)
    frozen = {}
    for record in tracked.split(b"\0"):
        if not record: continue
        metadata, path = record.split(b"\t", 1)
        frozen[path.decode()] = metadata.split()[2].decode()
    for path, revision in BASELINE_OVERRIDES.items():
        frozen[path] = subprocess.check_output(
            ["git", "rev-parse", revision + ":" + path], cwd=repo, text=True).strip()
    return frozen

def verify_frozen(repo, frozen, path):
    data = (repo/path).read_bytes()
    blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
    if frozen.get(path) != blob: raise SystemExit("Frozen-source mismatch: " + path)


def sha(data):
    return hashlib.sha256(data).hexdigest()

def mask(source):
    """Preserve offsets/newlines; mask nested Lean comments and string literals."""
    out = list(source)
    i = 0
    depth = 0
    string = False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                out[i:i+2] = "  "; depth += 1; i += 2
            elif source.startswith("-/", i):
                out[i:i+2] = "  "; depth -= 1; i += 2
            else:
                if source[i] != "\n": out[i] = " "
                i += 1
        elif string:
            if source[i] == "\\":
                out[i] = " "; i += 1
                if i < len(source):
                    if source[i] != "\n": out[i] = " "
                    i += 1
            else:
                if source[i] == '\"': string = False
                if source[i] != "\n": out[i] = " "
                i += 1
        elif source.startswith("--", i):
            while i < len(source) and source[i] != "\n": out[i] = " "; i += 1
        elif source.startswith("/-", i):
            out[i:i+2] = "  "; depth = 1; i += 2
        elif source[i] == "'" and i + 2 < len(source) and source[i+2] == "'":
            # Single-character literals (including a double quote) are not strings.
            out[i:i+3] = "   "; i += 3
        elif source[i] == '\"':
            out[i] = " "; string = True; i += 1
        else:
            i += 1
    if depth or string: raise ValueError("unterminated comment/string")
    return "".join(out)

def expand(path):
    m = re.search(r"\{([^{}]*)\}", path)
    if not m: return [path]
    return [p for choice in m[1].split(",")
            for p in expand(path[:m.start()] + choice + path[m.end():])]

def resolve(repo, ref, directory=""):
    if directory and "/" not in ref: ref = directory + "/" + ref
    candidates = [ref, "Solidity/" + ref, "Bridge/" + ref]
    if "*" in ref:
        return sorted({str(p.relative_to(repo)) for pattern in candidates
                       for p in repo.glob(pattern) if p.is_file()})
    return [p for p in candidates if (repo/p).is_file()]

def signature_end(code, start, limit):
    stack = []
    close = {")": "(", "]": "[", "}": "{"}
    for i in range(start, limit):
        ch = code[i]
        if not stack and code.startswith(":=", i): return i
        if not stack and ch == "\n":
            tail = code[i+1:limit]
            # Equation-style declarations have no := before their clauses.
            if re.match(r"[ \t]*\|(?![|>])", tail):
                # A match in the result TYPE also has | branches. Leave these
                # ambiguous declarations unsupported rather than truncate them.
                if re.search(r"\bmatch\b", code[start:i]): return None
                return i
            # Never swallow the next declaration as a proof boundary.
            if re.match(r"\s*(?:(?:private|protected|noncomputable)\s+)?(?:def|abbrev|theorem|lemma|structure|inductive|namespace|end)\b", tail):
                return None
        if ch in "([{": stack.append(ch)
        elif ch in close:
            if stack and stack[-1] == close[ch]: stack.pop()
    return None

def scan(source, path):
    code = mask(source)
    events = re.compile(r"(?m)^\s*(namespace|section|end)\b([^\n]*)")
    declarations = list(re.finditer(r"\btheorem\s+([^\s({:]+)", code))
    result = []
    scopes = []
    prior = 0

    for index, match in enumerate(declarations):
        for event in events.finditer(code, prior, match.start()):
            kind, rest = event[1], event[2].strip()
            if kind in ("namespace", "section"):
                scopes.append((kind, rest.split()[0] if rest else ""))
            elif scopes: scopes.pop()
        prior = match.start()
        name = match[1]
        if name.startswith("«"):
            end_name = code.find("»", match.start(1))
            if end_name != -1: name = source[match.start(1):end_name+1]
        prefix = ".".join(value for kind, value in scopes if kind == "namespace")
        qualified = name[len("_root_."):] if name.startswith("_root_.") else ".".join(filter(None, [prefix, name]))
        limit = declarations[index+1].start() if index+1 < len(declarations) else len(code)
        stop = signature_end(code, match.end(), limit)
        signature = source[match.start():stop] if stop is not None else None
        line_start = code.rfind("\n", 0, match.start())+1
        visibility = "private" if re.search(r"\bprivate\s+$",code[line_start:match.start()]) else "public_or_protected"
        result.append(dict(id=f"{path}:{source.count(chr(10),0,match.start())+1}:{name}",
            name_candidate=qualified, visibility=visibility, file=path, line=source.count(chr(10),0,match.start())+1,
            signature_source=signature, signature_sha256=sha(signature.encode()) if signature else None,
            module_context_requires_elaboration=True,
            witness_status="UNCOVERED", statement_fidelity="UNELABORATED",
            owner_status="UNCONFIRMED", owner_relay="area producer; H55-G49 if applicable"))
    return result

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    repo = args.repo.resolve(); out = args.out.resolve()
    if out == repo or repo in out.parents: raise SystemExit("Bulk output must be outside repository")
    frozen = frozen_blobs(repo)
    def verify(path):
        verify_frozen(repo, frozen, path)
    verify(MAP)
    text = (repo/MAP).read_text()
    references = []
    for line_number, line in enumerate(text.splitlines(), 1):
        if not line.startswith("|"): continue
        directory = ""
        for ref in re.findall(r"`([^`]*\.lean)`", line.split("|")[1]):
            for expanded in expand(ref):
                if "/" in expanded: directory = expanded.rsplit("/",1)[0]
                references.append(dict(reference=expanded, map_line=line_number,
                    resolution="contextual_glob" if "*" in expanded else "explicit_or_same_row_directory",
                    resolved=resolve(repo, expanded, directory)))
                if "(+`Controls`)" in line or "(+Controls)" in line:
                    control = expanded.removesuffix(".lean") + "Controls.lean"
                    resolved = resolve(repo, control, directory)
                    if resolved: references.append(dict(reference=control,map_line=line_number,
                        resolution="parenthetical_controls",resolved=resolved))
    files = sorted({p for ref in references for p in ref["resolved"]})
    declarations = []
    modules = []
    for path in files:
        verify(path)
        data = (repo/path).read_bytes(); source = data.decode()
        rows = scan(source, path); declarations.extend(rows)
        modules.append(dict(file=path, sha256=sha(data), theorem_candidates=len(rows)))
    ids = [r["id"] for r in declarations]
    if len(ids) != len(set(ids)): raise SystemExit("Duplicate declaration identifiers")
    summary = dict(base=BASE, baseline_overrides=BASELINE_OVERRIDES, baseline_correspondence=correspondence_notes(), map=MAP, map_sha256=sha((repo/MAP).read_bytes()),
        references=len(references), unique_files=len(files), theorem_candidates=len(declarations),
        unresolved_references=[r for r in references if not r["resolved"]],
        unterminated_signatures=[r["id"] for r in declarations if r["signature_source"] is None],
        uncovered=len(declarations), simultaneous_witnesses_verified=0,
        statement_fidelity="PENDING LEAN ELABORATION", owner_confirmation="PENDING", frozen_source_verified=True, complete_interface_inventory=False,
        limitations=["Lexical census; inherited variables are not elaborated.",
          "All theorem candidates retained; interface/hypothesis classification pending.",
          "Theorem-only source inventory omits structure proof projections and predicate definitions; these require the all-kind kernel census.",
          "Map shorthand (+Controls) requires manual reconciliation.",
          "Namespace reconstruction is a candidate, not kernel name validation."])
    out.mkdir(parents=True, exist_ok=True)
    for name, value in [("census.json",dict(summary=summary,modules=modules,references=references,declarations=declarations)),
                        ("summary.json",summary)]:
        (out/name).write_text(json.dumps(value,ensure_ascii=False,sort_keys=True,indent=2)+"\n")
    print(json.dumps(summary,ensure_ascii=False,sort_keys=True,indent=2))

if __name__ == "__main__": main()
