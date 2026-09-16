import Solidity.Examples.Common
import Solidity.DecEq

/-!
# The calculus's worked examples — cross-domain copies

Section 8 of `Examples/Derivations/Paper.lean`: the storage-to-memory and
memory-to-storage copies, where the calculus needs its identity layer and the
Lean rule states one `alloc`/`copyMem` element.  The conventions are that
file's docstring; the example-by-example map is `docs/paper-parity.md`.
-/

namespace Solidity.Examples.Paper

open Rules StandardExample SoliditySyntax Solidity.Examples Semantics

set_option maxHeartbeats 8000000

section
variable (φ : WrappedExpr)

/-! ## 8 · Cross-domain copies

Where the calculus needs its identity layer — a freshness premise
`new(mem, r) →`, the identity constructor `idC`, and the lazy `copySt` view —
Lean's rule states one `alloc` element: a memory declaration initialised from
a storage path.  The chains below therefore end one line earlier than the
calculus's, and the difference is the header's point 4, not a disagreement
about the program.  The premise itself is not an assumption here: the term
algebra has `new` and `idC` (`Theory/Memory.lean`) and `denoteMem_new` proves
the root a rule invents really is fresh. -/

/-! ### `Token memory t = alice.account.token;` — storage to memory
The source path is captured into a storage alias first, exactly as the
calculus does, and the declaration then allocates from it. -/

sol_derivation storageToMemoryNonsimplePath :
    => <[ Token memory mv3 = alice.account.token ]>(φ)
  ~*> => { sp@Account := path(alice.account) }
          { alloc(Token, mv3, sp@Account.token) } (φ)

/-! ### `alice.age = 25; Person memory carol = alice; v = carol.age;`
Six lines upstream, three rules here: the calculus spells out the `readCopySt`
resolution and the read-over-write that the terminal memory read already
performs. -/

sol_derivation storageToMemoryRootCopy :
    => <[ alice.age = 34; Person memory mv2 = alice; v = mv2@Person.age ]>(φ)
  ~*> => { storage := save(alice.age, 34) } { alloc(Person, mv2, alice) }
          { v := mv2@Person.age } (φ)

/-! ### the same at a *member* source, which needs the storage alias first -/

sol_derivation storageToMemoryMemberCopy :
    => <[ alice.account.balance = 10; Account memory mv = alice.account;
          v = mv@Account.balance ]>(φ)
  ~*> => { rv@uint := default(uint) } { rv@uint := 10 }
          { sp@Account := path(alice.account) }
          { storage := save(sp@Account.balance, rv@uint) }
          { alloc(Account, mv, alice.account) } { v := mv@Account.balance } (φ)

/-! ### `carol.age = 42; alice = carol; v = alice.age;` — memory to storage
The other direction, where the calculus's lazy `copyMem` view is one element
here. -/

sol_derivation memoryToStorageRootCopy :
    => <[ carol.age = 34; alice = carol; v = alice.age ]>(φ)
  ~*> => { memory := write(carol.age, 34) } { storage := copyMem(alice, carol) }
          { v := alice.age } (φ)

/-! ### the same from an alias, at a storage *field* target -/

sol_derivation memoryToStorageFromAlias :
    => <[ mv@Account.balance = 10; alice.account = mv@Account;
          v = alice.account.balance ]>(φ)
  ~*> => { memory := write(mv@Account.balance, 10) }
          { storage := copyMem(alice.account, mv@Account) }
          { sp@Account := path(alice.account) } { v := sp@Account.balance } (φ)

/-! ### `carol.account.balance = 50; alice.account = carol.account; v = …`
A memory *member* as the source of a storage write.  The calculus says no
alias is introduced; Lean captures the member into `pv` first, and the copy
then reads that identity — the same `copyMem` view, one binding earlier. -/

sol_derivation memoryToStorageFromMemberSource :
    => <[ carol.account.balance = 50; alice.account = carol.account;
          v = alice.account.balance ]>(φ)
  ~*> => { rv@uint := default(uint) } { rv@uint := 50 }
          { mv@Account := ref(carol.account) }
          { memory := write(mv@Account.balance, rv@uint) }
          { pv@Account := ref(carol.account) }
          { storage := copyMem(alice.account, pv@Account) }
          { sp@Account := path(alice.account) } { v := sp@Account.balance } (φ)

/-! ### `carolToken.value = 99; alice.account.token = carolToken; v = …`
The target is the nonsimple path this time, so it is the *target* that needs
the storage alias; the memory source is already simple and needs none. -/

sol_derivation memoryToStorageNonsimplePath :
    => <[ mv3@Token.value = 99; alice.account.token = mv3@Token;
          v = alice.account.token.value ]>(φ)
  ~*> => { memory := write(mv3@Token.value, 99) }
          { sp@Account := path(alice.account) }
          { storage := copyMem(sp@Account.token, mv3@Token) }
          { sp@Token := path(alice.account.token) } { v := sp@Token.value } (φ)

end

end Solidity.Examples.Paper
