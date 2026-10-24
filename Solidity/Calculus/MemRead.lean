import Solidity.Calculus.MemRead.Spine
import Solidity.Calculus.MemRead.Laws
import Solidity.Calculus.MemRead.Ok
import Solidity.Calculus.MemRead.Pass

/-!
# Reading memory as solkey reads it

The memory clauses of `sol_decide`, each the transcription of the solkey
taclets named on it (`memoryRules.key`, `structMemoryRules.key`;
`docs/lean-key-rule-map.md` has the rows), proved on the typed heap
(`Theory/Typed/Mem.lean`).

A memory term of the reduction is the tree of its writes and allocations,
as the program built it: `write(m, a, v)`, `addM(m, R)` with its root
`alloc(m, R)`, `copySt(m, S)` with its root `copy(m, S)`.  A read
(`read(M, b)`, `iread(M, b)`, `size(M, i)`) walks the tree from the newest
node down (`LTm.memRes`), comparing addresses without running anything:

* **readOnWrite**: the address written reads what was written;
  **readOnWriteFrame**: an address apart from it reads below
  (`LTm.apart?`: two members, a member and an element, two literal
  indices of one identity).
* **readOnAddMFrame**: an address whose object is older than an
  allocation (`LTm.boundedIn`: allocated on the spine below it, or read out
  of a memory there) reads below it; **readOnAddM** with **initMember**
  and **defaultValueInt**/**defaultValueBool**: an address at a member path
  of the fresh root reads its default.
* **readFromCopyToStorage**: a member of a copy of storage reads the
  storage there, its read eliminated as the storage reads are
  (`LTm.elim`).
* **readFromCopyToStorageIdentity**, and **readFromCopyToStorage** below
  the root (KeY's `idC(idp, fxs)`): an identity member of a copy's object,
  read at the copy, stays that read and holds the storage member
  (`copyObjN`); a word of such an object, or an element of a copied
  storage array (Lean only), reads the storage copied (`copyPathRd?`), and
  the object is fresh over the memory the copy grows (`LTm.copyFresh?`).
  Sound by `Theory/Typed/MemMirror.lean`.

A read whose address's object is guarded (`if (c) then o else err`, `d;
o`: a read walked before it) is read with the guards out (`LTm.hoistA`,
`wrapG`), each guard once; the addresses a write compares are read so too.

Each rewrite is an equation of reads (`LTm.memRes_eval`): it keeps what
the term reads in every state, a halting term halting.

The module is split by topic, each piece importing the one before
(`Calculus/MemRead/Spine.lean`, `Calculus/MemRead/Laws.lean`, `Calculus/MemRead/Ok.lean`, `Calculus/MemRead/Pass.lean`);
this module imports them all.
-/
