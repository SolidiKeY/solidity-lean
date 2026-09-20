import Solidity.Tactics.Derivation
import Solidity.Semantics.DecEq

/-!
# The calculus's worked examples — memory

Sections 5–7 of `Examples/Derivations/Paper.lean`: memory aliasing and
writes, memory `delete`, and memory arrays and allocation.  The conventions
the chains are written in are that file's docstring; which paper example each
chain is, and which ones have no chain, is `docs/paper-parity.md`.
-/

namespace Solidity.Examples.Paper

open Rules StandardExample SoliditySyntax Solidity.Examples Semantics

set_option maxHeartbeats 8000000

section
variable (φ : WrappedExpr)

/-! ## 5 · Memory

A memory alias is a *reference*: the alias update binds the identity the path
reads (`ref`), not a copy of the value, so a write through the alias and a
write through the original path are the same write.  That is the whole point
of the calculus's memory-aliasing example, and it is what makes the second
update below a `write` at `mv`'s identity rather than at `carol`'s. -/

/-! ### `Account memory carolAcc = carol.account; carolAcc.balance = 100;`
The calculus starts this one with `Person memory carol;`, which allocates a
fresh identity; `carol` is already a memory root here, so the chain starts
after the declaration. -/

sol_derivation memoryAliasWrite :
    => <[ Account memory mv = carol.account; mv@Account.balance = 100 ]>(φ)
  ~*> => { mv@Account := ref(carol.account) }
          { memory := write(memory, mv@Account.balance, 100) } (φ)

/-! ### `carol.account = david.account;`
A reference-valued field assignment: the source is *aliased*, not snapshotted,
so both fields end up at one identity.  `writeRef`, not `write`. -/

sol_derivation memoryFieldCopy :
    => <[ carol.account = david.account ]>(φ)
  ~*> => { pv@Account := ref(david.account) }
          { memory := write(memory, carol.account, image(pv@Account)) } (φ)

/-! ### `carol.account.balance = 10;` — the memory twin of the headline
Written with the middle line the storage chain has, so the two can be read
side by side: the same freeze, the same capture, and only the last element
differs — `memory := write` at an identity where storage has `storage := save`
at a path. -/

sol_derivation memoryDeepFieldWrite :
    => <[ carol.account.balance = 10 ]>(φ)
  ~*> => { rv@uint := default(uint) } { rv@uint := 10 }
          <[ Account memory mv = carol.account;
             mv@Account.balance = rv@uint ]>(φ)
  ~*> => { rv@uint := default(uint) } { rv@uint := 10 }
          { mv@Account := ref(carol.account) }
          { memory := write(memory, mv@Account.balance, rv@uint) } (φ)

/-! ### `v = carol.account.balance;` — the memory twin of the read -/

sol_derivation memoryDeepFieldRead :
    => <[ v = carol.account.balance ]>(φ)
  ~*> => { mv@Account := ref(carol.account) } { v := mv@Account.balance } (φ)

/-! ### `Person memory carolAlias = carol;` — aliasing by declaration drop
One update and no heap write at all: an alias shares the identity. -/

sol_derivation memoryDeclAlias :
    => <[ Person memory mv2 = carol ]>(φ)
  ~*> => { mv2@Person := ref(carol) } (φ)

/-! ### `Token memory t = carol.account.token;`
The memory twin of the declaration drop, one selector deeper: two `ref`
bindings and still no heap write. -/

sol_derivation memoryDeclDeepAlias :
    => <[ Token memory mv3 = carol.account.token ]>(φ)
  ~*> => { mv@Account := ref(carol.account) }
          { mv3@Token := ref(mv@Account.token) } (φ)

/-! ### `carolAcc = david.account;`
A memory field on the right is **not** captured as an expression: the root is
rebound to the identity the read yields, and the heap is untouched. -/

sol_derivation memoryRootRebind :
    => <[ mv@Account = david.account ]>(φ)
  ~*> => { mv@Account := ref(david.account) } (φ)

/-! ### `v = carol;` and `carol = david;`
A memory root read binds an identity, and a root *assignment* is a rebinding
of exactly the same kind — the heap is untouched in both. -/

sol_derivation memoryRootRead :
    => <[ mv2@Person = carol ]>(φ)
  ~> => { mv2@Person := ref(carol) } (φ)

sol_derivation memoryRootAssign :
    => <[ carol = david ]>(φ)
  ~> => { carol := ref(david) } (φ)

/-! ### `carol.age = a + b;` — a computed value into a memory field
The operand is frozen into `pv` before the write, exactly as a storage field
write freezes it.  The two vacuous lines are `binopAssignment`'s `\else`
branch, which every operator produces and `+` cannot take (see
`fieldCompoundAssign`). -/

sol_derivation memoryFieldWriteCapturedRhs :
    => <[ carol.age = a + b ]>(φ)
  ~*> [ => { pv@uint := default(uint) } { pv@uint := (a + b) }
          { memory := write(memory, carol.age, pv@uint) } (φ),
        { pv@uint := default(uint) } ¬⊤ => { pv@uint := default(uint) } ⊤,
        { pv@uint := default(uint) } ¬⊤ => { pv@uint := default(uint) } ⊥ ]

/-! ## 6 · Memory delete

The calculus's point: `delete carol` resets the *identity's* members, so an
alias taken beforehand observes the reset.  Both chains read the value back
**twice**, through the alias and through the path, because that pair is the
claim: the two reads agree, which is what "the alias observes the reset"
means.  The chains stay stacked: the merge law has no reader for a `read` over
a `clear`. -/

sol_derivation memoryDeleteRoot :
    => <[ Person memory mv2 = carol; carol.age = 33; delete carol;
          oldAge = mv2@Person.age; newAge = carol.age ]>(φ)
  ~*> => { mv2@Person := ref(carol) } { memory := write(memory, carol.age, 33) }
          { clear(carol) } { oldAge := mv2@Person.age }
          { newAge := carol.age } (φ)

sol_derivation memoryDeleteField :
    => <[ Account memory mv = carol.account; mv@Account.balance = 100;
          delete carol.account; oldBal = mv@Account.balance;
          newBal = carol.account.balance ]>(φ)
  ~*> => { mv@Account := ref(carol.account) }
          { memory := write(memory, mv@Account.balance, 100) }
          { clear(carol.account) } { oldBal := mv@Account.balance }
          { mv@Account := ref(carol.account) }
          { newBal := mv@Account.balance } (φ)

/-! ### `delete carolValues[i];` and `delete carolTokens[i];`
A memory index delete is **not** bounds-guarded: one rule, one `clear` element,
whatever the index.  The element default is manufactured on the next read,
which is what makes the guard unnecessary (`Theory/Memory.lean`'s
`readOnAddM`). -/

sol_derivation memoryIndexDeletePrimitive :
    => <[ delete mv@UintArray[i] ]>(φ)
  ~> => { clear(mv@UintArray[i]) } (φ)

sol_derivation memoryIndexDeleteReference :
    => <[ delete mv2@TokenArray[i] ]>(φ)
  ~> => { clear(mv2@TokenArray[i]) } (φ)

/-! ### `delete carol.account.tokens[i];` — under a nested path
Two `ref` bindings to reach the array, and then the same single `clear`. -/

sol_derivation memoryIndexDeleteNonsimplePath :
    => <[ delete carol.account.tokens[i] ]>(φ)
  ~*> => { mv@Account := ref(carol.account) }
          { mv@TokenArray := ref(mv@Account.tokens) }
          { clear(mv@TokenArray[i]) } (φ)

/-! ## 7 · Memory arrays and allocation

A memory index access is bounds-guarded exactly as a storage one is, and a
nested path is two `ref` bindings before the write.  The calculus's auxiliary
arrays are the scratch aliases named in the header. -/

/-! ### `UintArray memory mv;` — the allocation the other chains start after
One rule, one element, and no heap write to a member: `addM` adds the root and
every member of it is manufactured on read (`Theory/Memory.lean`'s
`readOnAddM` and `defaultDefIdentity`).  The calculus writes the same line with
its freshness premise `new(mem, r) →` in front; here the root a rule invents
really is fresh, and that is `Update/Theory.lean`'s `denoteMem_new` rather than
an assumption carried along. -/

sol_derivation memoryArrayAlloc :
    => <[ UintArray memory mv ]>(φ)
  ~> => { mv := freshId(alloc(UintArray)) ‖ memory := alloc(UintArray) } (φ)

sol_derivation memoryArrayReadBox :
    => [ v = mv@UintArray[i] ](φ)
  ~*> [ inBounds(mv@UintArray[i]) => { v := mv@UintArray[i] } [ ](φ),
        ¬inBounds(mv@UintArray[i]) => ⊤ ]

sol_derivation memoryArrayWriteBox :
    => [ mv@UintArray[i] = 100 ](φ)
  ~*> [ inBounds(mv@UintArray[i]) =>
          { memory := write(memory, mv@UintArray[i], 100) } [ ](φ),
        ¬inBounds(mv@UintArray[i]) => ⊤ ]

/-! ### `carol.account.values[i] = 42;` — a nested memory path under an index -/

sol_derivation memoryNestedArrayWrite :
    => [ carol.account.values[i] = 42 ](φ)
  ~*> [ { rv@uint := default(uint) } { rv@uint := 42 }
          { mv@Account := ref(carol.account) }
          { mv@UintArray := ref(mv@Account.values) } inBounds(mv@UintArray[i]) =>
          { rv@uint := default(uint) } { rv@uint := 42 }
          { mv@Account := ref(carol.account) }
          { mv@UintArray := ref(mv@Account.values) }
          { memory := write(memory, mv@UintArray[i], rv@uint) } [ ](φ),
        { rv@uint := default(uint) } { rv@uint := 42 }
          { mv@Account := ref(carol.account) }
          { mv@UintArray := ref(mv@Account.values) } ¬inBounds(mv@UintArray[i]) =>
          { rv@uint := default(uint) } { rv@uint := 42 }
          { mv@Account := ref(carol.account) }
          { mv@UintArray := ref(mv@Account.values) } ⊤ ]

/-! ### `v = carolValues[++i];` — an impure index
The index is frozen into `idx` before the bounds goal is read, which is what
the `{…}` prefix on the antecedent says; the increment itself is the pair
`bump` names. -/

sol_derivation memoryArrayIncIndexRead :
    => [ v = mv@UintArray[++i] ](φ)
  ~*> [ { idx@uint := default(uint) } { bump(++i) ‖ idx@uint := ++i }
          inBounds(mv@UintArray[idx@uint]) =>
          { idx@uint := default(uint) } { bump(++i) ‖ idx@uint := ++i }
          { v := mv@UintArray[idx@uint] } [ ](φ),
        { idx@uint := default(uint) } { bump(++i) ‖ idx@uint := ++i }
          ¬inBounds(mv@UintArray[idx@uint]) =>
          { idx@uint := default(uint) } { bump(++i) ‖ idx@uint := ++i } ⊤ ]

/-! ### `carolValues[++i] = val;` — the write twin of the impure index
The value is frozen *before* the index is captured, and the receiver is bound
to itself first: the rule aliases the receiver whether or not it is already an
alias, which is what makes the capture order the same for every receiver. -/

sol_derivation memoryArrayIncIndexWrite :
    => [ mv@UintArray[++i] = amount ](φ)
  ~*> [ { rv@uint := default(uint) } { rv@uint := amount }
          { mv@UintArray := ref(mv@UintArray) }
          { idx@uint := default(uint) } { bump(++i) ‖ idx@uint := ++i }
          inBounds(mv@UintArray[idx@uint]) =>
          { rv@uint := default(uint) } { rv@uint := amount }
          { mv@UintArray := ref(mv@UintArray) }
          { idx@uint := default(uint) } { bump(++i) ‖ idx@uint := ++i }
          { memory := write(memory, mv@UintArray[idx@uint], rv@uint) } [ ](φ),
        { rv@uint := default(uint) } { rv@uint := amount }
          { mv@UintArray := ref(mv@UintArray) }
          { idx@uint := default(uint) } { bump(++i) ‖ idx@uint := ++i }
          ¬inBounds(mv@UintArray[idx@uint]) =>
          { rv@uint := default(uint) } { rv@uint := amount }
          { mv@UintArray := ref(mv@UintArray) }
          { idx@uint := default(uint) } { bump(++i) ‖ idx@uint := ++i } ⊤ ]

/-! ### `carolTokens[i] = david.account.token;`
A reference-valued element written from a memory path: the source is read to
an identity and that identity is stored, so this is `writeRef` and the two
slots alias. -/

sol_derivation memoryArrayWriteRefSource :
    => [ mv2@TokenArray[i] = david.account.token ](φ)
  ~*> [ { mv@Account := ref(david.account) } { pv@Token := ref(mv@Account.token) }
          inBounds(mv2@TokenArray[i]) =>
          { mv@Account := ref(david.account) } { pv@Token := ref(mv@Account.token) }
          { memory := write(memory, mv2@TokenArray[i], image(pv@Token)) } [ ](φ),
        { mv@Account := ref(david.account) } { pv@Token := ref(mv@Account.token) }
          ¬inBounds(mv2@TokenArray[i]) =>
          { mv@Account := ref(david.account) }
          { pv@Token := ref(mv@Account.token) } ⊤ ]

/-! ### `carol.account.token = davidTokens[i];` — the other direction
The element is read first, so the bounds goal is the *first* thing the line
carries and the capture that follows it is under no prefix at all. -/

sol_derivation memoryFieldWriteFromArrayElem :
    => [ carol.account.token = mv2@TokenArray[i] ](φ)
  ~*> [ inBounds(mv2@TokenArray[i]) =>
          { pv@Token := ref(mv2@TokenArray[i]) } { mv@Account := ref(carol.account) }
          { memory := write(memory, mv@Account.token, image(pv@Token)) } [ ](φ),
        ¬inBounds(mv2@TokenArray[i]) => ⊤ ]

/-! ### `Token memory tok = carol.account.tokens[i];`
A declaration from an array element under a nested path: two `ref` bindings to
reach the array, then a third to bind the element — and still no heap write,
because a memory declaration from a memory source aliases. -/

sol_derivation memoryDeclFromNestedArrayElem :
    => [ Token memory mv3 = carol.account.tokens[i] ](φ)
  ~*> [ { mv@Account := ref(carol.account) }
          { mv@TokenArray := ref(mv@Account.tokens) } inBounds(mv@TokenArray[i]) =>
          { mv@Account := ref(carol.account) }
          { mv@TokenArray := ref(mv@Account.tokens) }
          { mv3@Token := ref(mv@TokenArray[i]) } [ ](φ),
        { mv@Account := ref(carol.account) }
          { mv@TokenArray := ref(mv@Account.tokens) } ¬inBounds(mv@TokenArray[i]) =>
          { mv@Account := ref(carol.account) }
          { mv@TokenArray := ref(mv@Account.tokens) } ⊤ ]

/-! ### `Token memory tok = carolTokens[++i];`
The same declaration with an impure index: the index is frozen into `idx`
before the bounds goal is read, and the element the alias binds is the one
that index named. -/

sol_derivation memoryDeclFromIncIndexElem :
    => [ Token memory mv3 = mv2@TokenArray[++i] ](φ)
  ~*> [ { idx@uint := default(uint) } { bump(++i) ‖ idx@uint := ++i }
          inBounds(mv2@TokenArray[idx@uint]) =>
          { idx@uint := default(uint) } { bump(++i) ‖ idx@uint := ++i }
          { mv3@Token := ref(mv2@TokenArray[idx@uint]) } [ ](φ),
        { idx@uint := default(uint) } { bump(++i) ‖ idx@uint := ++i }
          ¬inBounds(mv2@TokenArray[idx@uint]) =>
          { idx@uint := default(uint) } { bump(++i) ‖ idx@uint := ++i } ⊤ ]

end

end Solidity.Examples.Paper
