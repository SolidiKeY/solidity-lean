-- The root of the `SolidityCorpus` library: solkey's example suites, ported
-- by `scripts/solkey-port.mjs` (generated; do not edit).
import Solidity.Corpus.Basic
import Solidity.Corpus.Imported
import Solidity.Corpus.TestSuite
import Solidity.Corpus.SolcExpressions
import Solidity.Corpus.SolcStructs
import Solidity.Corpus.SolcArrays
import Solidity.Corpus.SolcMemory
import Solidity.Corpus.SolcMappings
import Solidity.Corpus.SolcControlFlow
import Solidity.Examples.Tactics.Net

-- Handwritten .key proof mappings are checked by this library too.
#check Solidity.Examples.Tactics.Net.netSendSimple
#check Solidity.Examples.Tactics.Net.netTransferCapturedAmount
#check Solidity.Examples.Tactics.Net.netTransferStorageReceiver
#check Solidity.Examples.Tactics.Net.netTransferSimple
