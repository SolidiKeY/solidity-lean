import Solidity.Calculus.DecideEval.Readers
import Solidity.Calculus.DecideEval.Storages
import Solidity.Calculus.DecideEval.Memory

/-!
# The elimination keeps what a term reads

`LTm.elim` (`Calculus/Decide.lean`) is the typed Theory read symbolically;
here each of its parts is shown to read what the Theory's operation reads
(`Theory/Typed/Obs.lean`), and the elimination of a term to read what the
term reads (`LTm.elim_eval`, an equality).  The proofs follow the
definitions: a symbolic path names the reference its keys evaluate to
(`SPath.eval`), `relSegs` is `Path.strip?` (`relSegs_sound`), each reader
reads the observations of the value it stands for (`VRd.Rep`), and each
storage operation's reader those of the storage it leaves (`SRd.Rep`,
through the bridges `Storage.obs_write`, `obs_delete`, `obs_push`, …).

The module is split by topic, each piece importing the one before
(`Calculus/DecideEval/Readers.lean`, `Calculus/DecideEval/Storages.lean`, `Calculus/DecideEval/Memory.lean`);
this module imports them all.
-/
