import Solidity.Theory.Typed.Obs.Paths
import Solidity.Theory.Typed.Obs.Values
import Solidity.Theory.Typed.Obs.Ops

/-!
# The Theory, typed: a value is its observations

KeY's storage theory (`structRules.key`) read on typed locations.  A value
of a sort is what its reads show (`Obs`): the word at every primitive
location below it, the live length of every dynamic array, and whether a
location is there at all.  So the Theory's equality is `=`: two values with
the same observations are one value, and the laws need no equivalence to be
stated up to.

**One structure for every location family.**  `Obs L` is generic in the
locations `L : Ty → Type`, a location being typed by what it holds: `TVal T`
(`Obs (Path T)`, a stored value, read below it), `TSto C` (`Obs (SLoc C)`, a
storage, read at a state variable's path or at a dangling one).  A location
family appends a path and strips a prefix (`ObsLoc`), and every operation
(`find`, `save`, `delAt`, `copyTo`, `push`, `pop`, …) and every law is
stated once, over any of them.

**Total.**  A write is total (`save` at a path not there makes it there), so
`findOnSave`/`findOnSaveFrame` (solkey's `selectOnSaveCons`) hold with no
premise that the write lands.  A location not there reads the default word, length `0`, and
`has = false`.

**From the type.**  What a delete, a copy and a push do below the location
they act on is computed from the location's type and the value's
observations (`TVal.del`, `TVal.overlay`, `TVal.strip`, `TVal.pushA`), as
the interpreter does it on a typed value (`SVal.defaultOf`, `SVal.overlay`,
`SVal.strip`, `Storage.push`): no lazy leaf, no node kind.

**The bridge.**  A typed value is read here by `SVal.obs`, a storage by
`Storage.obs`; each operation of the interpreter is, read so, the
operation of this module (`SVal.obs_save`, `SVal.obs_overlay`, …).

The module is split by topic, each piece importing the one before
(`Theory/Typed/Obs/Paths.lean`, `Theory/Typed/Obs/Values.lean`, `Theory/Typed/Obs/Ops.lean`);
this module imports them all.
-/
