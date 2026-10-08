import Solidity.Calculus.Close

/-!
# `sol_close` past `{havoc}`

`{havoc} φ` is KeY's anonymising update `{storage := storageSk ‖ net :=
netSk}`, fresh skolem constants for what a callee leaves: `φ` holds for
every storage `st` and ledger `nt` put in the state (`State.havoc`).  The
closer reads it so: `holds_havoc` names the two as universally bound
variables, and `State.havoc_eq_mk` writes the state they make as the
structure, so that `Close.getEnv_mk`, `Close.readAddr_mk` and their kin
read its locals and heap as before, while a read of its storage or ledger
reads `st` or `nt`, of which nothing is known.  A snapshot taken before it
(`{old := storage ‖ oldNet := net}`, a function contract's "post") is a
local, so `find(old, …)` still reads the storage the snapshot took.

The set is `close_rw`'s; a module that leaves `{havoc}` at a leaf imports
this one (`Calculus/Core/FunContract.lean`).
-/

namespace Solidity

open Semantics

namespace Close

variable {C : Contract} {σ : State}

/-- `{havoc} φ`: `φ` for every storage and ledger the callee may leave. -/
theorem holds_havoc (φ : Fml C) : holds σ (.havoc φ) ↔ ∀ st nt, holds (σ.havoc st nt) φ :=
  Iff.rfl

/-- The state a `{havoc}` leaves, as the structure: its locals, heap,
funds and transaction `σ`'s. -/
theorem State.havoc_eq_mk (σ : State) (st : List (Name × SVal)) (nt : List (Int × Int)) :
    σ.havoc st nt = State.mk st σ.heap σ.nextId σ.env nt σ.selfBalance σ.tx := rfl

end Close

attribute [close_rw] Close.holds_havoc Close.State.havoc_eq_mk

end Solidity
