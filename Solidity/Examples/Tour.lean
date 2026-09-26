import Solidity.Calculus.Close

/-!
# A tour: everything on a few programs

Open this file in the editor and put the cursor after each `apply`: the goal
is printed in the calculus's notation, as the sequent `dl{ Γ ⟹ [ … ] φ }`
(mini-solkey's `Examples/Tour.lean`, less its EVM part: this package has no
compiler).

1. The running example, a write to `alice.account.balance` read
   back: by hand, one taclet at a time, and by the strategy.
2. Aliasing: a write through a `storage` local is visible through the root.
3. Frames: a mapping write does not disturb another key, and a write under a
   mapping of structs reads back.
4. What elaboration rejects.

A proof by hand starts with `apply Proves.valid`, which turns `⊨ φ` into the
judgement `⊢ φ` (`Calculus/Logic.lean`); each `apply` then checks that its rule
matches the first statement and replaces the goal by the rule's premise.  A
read whose receiver is not simple is unfolded by `storageFieldRead_unfold_rightFst`,
whose conclusion `Hole.fill lhs …` does not unify by name
(`StorageSteps.lean`'s docstring), so those steps take the strategy's rule,
`(Stmt.step _ _ _).taclet`, and the comment names it.
-/

namespace Solidity.Examples.Tour

open Proves

local instance : InContract := ⟨StandardExample⟩

/-! ## 1. The running example -/

/-- `alice.account.balance = 10; uint x = alice.account.balance;`, one taclet at
a time. -/
theorem runningExample_byHand :
    ⊨ dl!{ [ alice.account.balance = 10; uint x = alice.account.balance; ] x == 10 } := by
  apply Proves.valid
  -- Step 2: the receiver `alice.account` is not simple; capture source, then receiver
  apply unfold .storageFieldWrite_unfold_leftFst
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign  -- { se1 := 10 }
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot  -- { sp1 := alice.account }
  -- Step 3: all parts simple, generate the update
  apply update .storageFieldWriteSave  -- { storage := save(storage, sp1.balance, se1) }
  -- the read: Step 1 captures the receiver (`storageFieldRead_unfold_rightFst`) …
  apply unfold .localValueDeclInitDrop
  apply unfold (Stmt.step _ _ _).taclet
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  -- … and Step 3 reads with `find`
  apply update .storageFieldReadFind  -- { x := find(storage, sp2.balance) }
  apply empty
  -- first order: apply the updates, then read back what was written
  apply close
  sol_symex
  sol_close

/-- The same, with the strategy choosing the rules. -/
theorem runningExample :
    ⊨ dl!{ [ alice.account.balance = 10; uint x = alice.account.balance; ] x == 10 } := by
  sol_symex
  sol_close

/-! ## 2. Aliasing -/

/-- `Account storage p = alice.account; p.balance = 7; uint x = alice.account.balance;`
— the alias is a path, so the write through it is a write to `alice`. -/
theorem aliasing :
    ⊨ dl!{ [ Account storage p = alice.account; p.balance = 7;
             uint x = alice.account.balance; ] x == 7 } := by
  apply Proves.valid
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot  -- { p := alice.account }
  apply update .storageFieldWriteSave
  apply unfold .localValueDeclInitDrop
  -- Step 1, `storageFieldRead_unfold_rightFst`
  apply unfold (Stmt.step _ _ _).taclet
  apply unfold .storageLocalDeclInitDrop
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldReadFind
  apply empty
  apply close
  sol_symex
  sol_close

/-! ## 3. Frames -/

/-- `uint z = balances[b]; balances[a] += 5; uint y = balances[b];` — another
mapping key is untouched, given that the keys differ. -/
theorem mappingFrame :
    ⊨ dl!{ a != b → [ uint z = balances[b]; balances[a] += 5; uint y = balances[b]; ]
             y == z } := by
  apply Proves.valid
  apply intro
  apply unfold .localValueDeclInitDrop
  apply update .storageIndexReadMappingFind
  apply update .storageIndexMappingOpAssign
  apply unfold .localValueDeclInitDrop
  apply update .storageIndexReadMappingFind
  apply empty
  apply close
  sol_symex
  sol_close

/-- `folks[k].account.balance = total; uint y = folks[k].account.balance;` — a
mapping of structs, written through a receiver two selectors deep, from a
root read; the source is read first. -/
theorem nested :
    ⊨ dl!{ [ folks[k].account.balance = total; uint y = folks[k].account.balance; ]
           y == total } := by
  apply Proves.valid
  apply unfold .storageFieldWrite_unfold_leftFst
  apply unfold .localValueDeclInitDrop
  apply update .storageRootReadSelect
  apply unfold .storageLocalDeclInitDrop
  -- Step 1 on the alias's target `folks[k].account` (`storageFieldRead_unfold_rightFst`)
  apply unfold (Stmt.step _ _ _).taclet
  apply unfold .storageLocalDeclInitDrop
  apply update .storageIndexReadMappingBindLocalRoot
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldWriteSave
  apply unfold .localValueDeclInitDrop
  -- Step 1 twice on the read, `storageFieldRead_unfold_rightFst`
  apply unfold (Stmt.step _ _ _).taclet
  apply unfold .storageLocalDeclInitDrop
  apply unfold (Stmt.step _ _ _).taclet
  apply unfold .storageLocalDeclInitDrop
  apply update .storageIndexReadMappingBindLocalRoot
  apply update .storageFieldReadBindLocalRoot
  apply update .storageFieldReadFind
  apply empty
  apply close
  sol_symex
  sol_close

/-! ## 4. What elaboration rejects

A statement no rule can run cannot be written (`Syntax.lean`). -/

/-- error: Solidity elaboration failed: a value where a storage reference is expected -/
#guard_msgs in
#check (sol{ alice = 1; } : Prog StandardExample)

/-- error: Solidity elaboration failed: struct Person has no member salary -/
#guard_msgs in
#check (sol{ alice.salary = 1; } : Prog StandardExample)

/-- error: Solidity elaboration failed: a storage copy of a type that holds a mapping -/
#guard_msgs in
#check (sol{ wallet = wallet; } : Prog StandardExample)

end Solidity.Examples.Tour
