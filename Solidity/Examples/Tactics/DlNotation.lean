import Solidity.Calculus.Notation
import Solidity.Calculus.Delab
import Solidity.Calculus.Surface

/-!
# `dl!{ … }` pinned: today's reading and the scoped one

`Calculus/SurfaceNotation.lean`'s reader (`dl[C]{ φ }`, `dl!{ φ }`,
`dl![m]{ φ }`) on one contract: every formula reads as the scoped
`Fml C []`, with or without a modality (`Calculus/Notation.lean`'s
`elabDlAuto`, decision 11; W9.4 for one with none), its parameters bound by
hidden binders.  Moved out of `Calculus/SurfaceNotation.lean`
at W8.2, which cannot read a modality scoped (the reader is above it) nor
print a scoped formula (`Calculus/Delab.lean`).
-/

namespace Solidity

section Examples

open Semantics

local instance : InContract := ⟨StandardExample⟩

/-- A declaration's local is in scope in the postcondition. -/
example : Fml StandardExample [] := dl[StandardExample]{ ⟨ uint x = 10; ⟩ x == 10 }

/-- A write, then a read of it into a local, under the box. -/
example : Fml StandardExample [] := dl!{ [ alice.age = 10; uint y = alice.age; ] y == 10 }

/-- `a` and `x` are bound by nothing: parameters, `uint` locals. -/
example : Fml StandardExample [] := dl!{ a == 1 → ⟨ x = a; ⟩ x == 1 }

/-- `==` on program expressions is `=` on their lowerings. -/
example : dl!{ alice.age == 10 } = dl!{ find(storage, alice.age) = 10 } := rfl

/-- An update: a local and the storage, in parallel. -/
example : Fml StandardExample [] :=
  dl!{ { x := 10 ‖ storage := save(storage, alice.age, 10) } find(storage, alice.age) = x }

/-- An alias bound by an update is an alias under it, in a program too. -/
example : Fml StandardExample [] := dl!{ { p := alice } ⟨ p.age = 3; ⟩ p.age == 3 }

/-- `x := unset` binds a storage alias to no path (`storageLocalDeclSkip`);
a value local, a memory local or a state variable is refused.  The scoped
reading asks what `p` is (`where`). -/
example : Fml StandardExample [] := dl!{ { p := unset } true where Person storage p }

/-- error: Solidity elaboration failed: `v := unset` binds a storage alias; `v` is a value local -/
#guard_msgs in #check dl!{ [ uint v = 1; ] { v := unset } v == 1 }

/-- error: Solidity elaboration failed: `age := unset` binds a storage alias; `age` is a state variable -/
#guard_msgs in #check dl!{ { age := unset } true }

/-- A push, in nested `save`s, reads back as one. -/
example : dl!{ { storage := save(save(storage, values[values.length], 7), values.length,
    values.length + 1) } true } =
    (Fml.upd .diamond (Upd.nil.snoc (.storage (Tms.STerm.push Tms.STerm.storage
      (Tms.PTerm.root "values" rfl) (Tms.SValT.val (Tms.Term.lit (p := .uint) ⟨7, rfl⟩))))) .tt :
      Fml StandardExample []) := rfl

/-- info: dl{ ⟨ uint x = 10; ⟩ x = 10 } : Fml StandardExample [] -/
#guard_msgs in #check dl!{ ⟨ uint x = 10; ⟩ x == 10 }

/--
info: dl{ { x := 10 ‖ storage := save(storage, alice.age, 10) } find(storage, alice.age) = x } : Fml StandardExample []
-/
#guard_msgs in
#check dl!{ { x := 10 ‖ storage := save(storage, alice.age, 10) } find(storage, alice.age) = x }

/-- A capture takes the least index the formula's fresh variables leave. -/
example : dl!{ ⟨ values[total + 1] += 2; ⟩ ie1 == 0 } =
    dl!{ ⟨ uint ie2 = total + 1; values[ie2] += 2; ⟩ ie1 == 0 } := rfl
example : dl!{ ⟨ values[total + 1] += 2; ⟩ ie3 == 0 } =
    dl!{ ⟨ uint ie1 = total + 1; values[ie1] += 2; ⟩ ie3 == 0 } := rfl

/-- `∨`, `↔` and `∃` are the connectives they stand for, and print back. -/
example : dl!{ a == 1 ∨ a == 2 } = dl!{ ¬(¬a == 1 ∧ ¬a == 2) } := rfl
example : dl!{ a == 1 ↔ b == 1 } = dl!{ (a == 1 → b == 1) ∧ (b == 1 → a == 1) } := rfl
example : dl!{ ∃ uint y; y == a } = dl!{ ¬(∀ uint y; ¬y == a) } := rfl

/-- info: dl{ a = 1 ∨ a = 2 ↔ ¬b = 1 } : Fml StandardExample [] -/
#guard_msgs in #check dl!{ a == 1 ∨ a == 2 ↔ ¬b == 1 }

/-- info: dl{ ∃ uint y; y = a } : Fml StandardExample [] -/
#guard_msgs in #check dl!{ ∃ uint y; y == a }

/-- `=` is `==`'s equation; `≐` the total one, and `defined` is its own atom. -/
example : dl!{ a = 1 } = (Fml.bind .box (.user "a") (.val .uint)
    (.eqD (.pvV .here) (Tms.Term.lit (p := .uint) ⟨1, rfl⟩)) : Fml StandardExample []) := rfl
example : dl!{ a ≐ 1 } = (Fml.bind .box (.user "a") (.val .uint)
    (.eq (.pvV .here) (Tms.Term.lit (p := .uint) ⟨1, rfl⟩)) : Fml StandardExample []) := rfl

/-- info: dl{ (defined(a) ∧ a ≐ 1) → a = 1 } : Fml StandardExample [] -/
#guard_msgs in #check dl!{ defined(a) ∧ a ≐ 1 → a = 1 }

/-- info: dl{ a = 1 } : Fml StandardExample [] -/
#guard_msgs in #check (Fml.bind .box (.user "a") (.val .uint)
  (Fml.eqD (.pvV .here) (Tms.Term.lit (p := .uint) ⟨1, rfl⟩)) : Fml StandardExample [])

/-- info: dl{ ¬a = 1 ∧ a < 2 } : Fml StandardExample [] -/
#guard_msgs in #check dl!{ a != 1 ∧ a < 2 }

/-- error: Solidity elaboration failed: unknown name y -/
#guard_msgs in #check dl!{ ⟨ uint y = 1; ⟩ true ∧ y == 1 }

/-! ### Memory objects -/

/--
info: dl{
  { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
    ⟨ carol.age = 5; ⟩ true } : Fml StandardExample []
-/
#guard_msgs in
#check dl!{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
  ⟨ carol.age = 5; ⟩ true }

/-- A dropped memory declaration: `carolAcc` is typed from `carol.account`
(`scopeHints`), and a read of a reference binds a memory local. -/
example : Fml StandardExample [] :=
  dl!{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
       ⟨ carolAcc = carol.account; carolAcc.balance = 1; ⟩ true }
example : Fml StandardExample [] :=
  dl!{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
       { carolAcc := read(memory, carol.account) } ⟨ carolAcc.balance = 1; ⟩ true }

/-- … with the memory locals the program declares before it, in a branch too. -/
example : Fml StandardExample [] :=
  dl!{ ⟨ Person memory d; if (a == 1) { acc = d.account; } else { acc = d.account; }; acc.balance = 1; ⟩
       true }

/-- A name the program declares is left to its declaration. -/
example : Fml StandardExample [] :=
  dl!{ { carol := freshId(addM(memory, Person)) ‖ memory := addM(memory, Person) }
       ⟨ Person memory d; d = carol; ⟩ true }

/-- info: dl{ { ts := freshId(addM(memory, Token[3])) ‖ memory := addM(memory, Token[3]) } true } : Fml StandardExample [] -/
#guard_msgs in
#check dl!{ { ts := freshId(addM(memory, Token[3])) ‖ memory := addM(memory, Token[3]) } true }

/--
info: dl{
  { xs := freshId(copySt(memory, newArr(uint[], 3))) ‖ memory := copySt(memory, newArr(uint[], 3)) }
    true } : Fml StandardExample []
-/
#guard_msgs in
#check dl!{ { xs := freshId(copySt(memory, newArr(uint[], 3))) ‖ memory := copySt(memory, newArr(uint[], 3)) }
  true }

-- A `where` clause: the memory local a copy out of storage binds, its
-- declaration dropped, prints as the clause that reads it back.
/-- info: dl{ ⟨ carol = alice; carol.age = 1; ⟩ true where Person memory carol } : Fml StandardExample [] -/
#guard_msgs in
#check dl!{ ⟨ carol = alice; carol.age = 1; ⟩ true where Person memory carol }

/--
info: dl{
  { sp2 := alice.account } ⟨ acc = sp2; ⟩ read(memory, acc.balance) = 1 where
    Account memory acc } : Fml StandardExample []
-/
#guard_msgs in #check dl!{ { sp2 := alice.account } ⟨ acc = sp2; ⟩ acc.balance == 1
  where Account memory acc }

-- An allocation reads back at a struct or an array only.
/-- error: Solidity elaboration failed: `addM(m, T)`: a value type is not allocated in memory -/
#guard_msgs in #check dl!{ { memory := addM(memory, uint) } true }

/--
error: Solidity elaboration failed: `addM(m)` does not say what it allocates: write `addM(m, T)` for a type `T`
-/
#guard_msgs in #check dl!{ { memory := addM(memory) } true }

/-! ### At a modality: `dl![m]{ … }` -/

/-- `⟨[ P ]⟩` at a constructor is its bracket. -/
example : dl![.box]{ ⟨[ alice.age = 10; ]⟩ alice.age == 10 } =
    dl!{ [ alice.age = 10; ] alice.age == 10 } := rfl
example : dl[StandardExample, .diamond]{ ⟨[ x = 1; ]⟩ x == 1 } = dl!{ ⟨ x = 1; ⟩ x == 1 } := rfl

/-- A modality under the update still decides. -/
example : dl![.diamond]{ { x := 1 } [ x = 2; ] x == 2 } = dl!{ { x := 1 } [ x = 2; ] x == 2 } := rfl

/-- info: dl{ ⟨[ x = 1; ]⟩ x = 1 } : Fml StandardExample [] -/
#guard_msgs in
variable (m : Modality) in
#check dl![m]{ ⟨[ x = 1; ]⟩ x == 1 }

/--
error: `⟨[ … ]⟩` is either modality: read the formula at one, `dl![m]{ … }`, or write `⟨ … ⟩` or `[ … ]`
-/
#guard_msgs in #check dl!{ ⟨[ x = 1; ]⟩ x == 1 }

/-! ### A Lean formula where a formula stands -/

/-- A name is a Lean formula: the postcondition `φ`, at the context of
the place it stands in. -/
example (φ : Fml StandardExample [.val .uint]) :
    dl!{ { x := 1 } φ } =
      Fml.upd .diamond (Upd.nil.decl (.user "x") (.val (Tms.Term.lit (p := .uint) ⟨1, rfl⟩))) φ := rfl

/-- So is `‹t›`; `true` stays the keyword. -/
example (φ ψ : Fml StandardExample []) : dl!{ ‹φ› ∧ ψ ∧ true } = Fml.and φ (Fml.and ψ .tt) := rfl

-- A name nothing binds is refused, not bound as a new variable of the
-- signature (`autoImplicit`): here a misspelt `true`.
/-- error: a name where a formula stands is a Lean formula (φ : Post C Γ): unknown `ture` -/
#guard_msgs in
example : dl!{ ⟨ x = 1; ⟩ ture } = dl!{ ⟨ x = 1; ⟩ true } := rfl

/-- info: fun m φ => dl{ ⟨[ x = 1; ]⟩ φ } : Modality → Post StandardExample [LTy.val PrimTy.uint] → Fml StandardExample [] -/
#guard_msgs in
#check fun (m : Modality) (φ : Post StandardExample [.val .uint]) => dl![m]{ ⟨[ x = 1; ]⟩ φ }

-- An inaccessible name prints escaped: bare, it would read back as another.
/--
trace: φ✝ : Post StandardExample [LTy.val PrimTy.uint]
⊢ dl{ ⟨ x = 1; ⟩ ‹↑φ✝› } = dl{ ⟨ x = 1; ⟩ ‹↑φ✝› }
-/
#guard_msgs in
example : ∀ φ : Post StandardExample [.val .uint], dl!{ ⟨ x = 1; ⟩ φ } = dl!{ ⟨ x = 1; ⟩ φ } := by
  intro
  trace_state
  rfl

-- `⊨` and `⊧` of a name alone are Lean's to print.
/-- info: fun φ => (⊨ φ) ∧ ∀ (σ : State StandardExample []), σ ⊧ φ : Fml StandardExample [] → Prop -/
#guard_msgs in #check fun (φ : Fml StandardExample []) => (⊨ φ) ∧ ∀ σ, σ ⊧ φ

/-! ### Chain-only spellings -/

/-- A sequent line is its formula: its antecedents imply its succedent. -/
example : dl!{ 5 <= selfBalance ⟹ ⟨ to.transfer(5); ⟩ true } =
    dl!{ 5 <= selfBalance → ⟨ to.transfer(5); ⟩ true } := rfl
example : dl!{ a == 1, b == 2 ⟹ a == b } = dl!{ a == 1 → b == 2 → a == b } := rfl

/-- The two goals of a split, and a line at a modality. -/
example : dl!{ (a == 1 ⟹ ⟨ x = 1; ⟩ true) ∧ (¬a == 1, b == 1 ⟹ false) } =
    dl!{ (a == 1 → ⟨ x = 1; ⟩ true) ∧ (¬a == 1 → b == 1 → false) } := rfl
example (m : Modality) : dl![m]{ a == 1 ⟹ ⟨[ x = 1; ]⟩ true } =
    dl![m]{ a == 1 → ⟨[ x = 1; ]⟩ true } := rfl

-- It prints as the formula it is.
/-- info: dl{ 5 <= selfBalance → ⟨ to .transfer(5); ⟩ true } : Fml StandardExample [] -/
#guard_msgs in #check dl!{ 5 <= selfBalance ⟹ ⟨ to.transfer(5); ⟩ true }

/-- `0 <= se <= selfBalance`, and the read of the ledger. -/
example : dl!{ 0 <= 5 <= selfBalance } = dl!{ 0 <= 5 ∧ 5 <= selfBalance } := rfl
example : dl!{ { net := store(net, at(to), select(net, at(to)) - 5) } select(net, at(to)) = x } =
    dl!{ { net := store(net, at(to), net(to) - 5) } net(to) = x } := rfl

end Examples

end Solidity
