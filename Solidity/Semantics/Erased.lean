import Solidity.Semantics
import Solidity.Syntax.Quote

/-!
# The erased state

What the closer's untyped terms read (`docs/intrinsic.md`, M3, decision 40):
a state carries the locals of its context `Γ`, `Env C Γ`, a type computed
from `Γ` (`Unit`, then one component per local, innermost first), beside
`Semantics.lean`'s untyped global part (`State.glob`).  A typed state erases
to one (`State.erase`, `Semantics/State.lean`), and an update's result is
one (decision U1, W9.6.0).  The terms read a local's binding through
`aliasPath` and `memRef`; no program is evaluated here, nor anywhere on the
erasure: the typed run (`Semantics/Run.lean`) is the only run, and the
rules' soundness reads it against the terms (`Calculus/LowerRun.lean`).

Where the kernel evaluates: `Env`'s functions recurse on `Idx`/`Ext` by
`casesOn` (Gate G0, condition 1).
-/

namespace Solidity

open Semantics (Value SVal Seg Res)

variable {C : Contract}

/-! ## Locals -/

/-- What a local of type `t` holds: a value, the storage path an alias is
bound to (`none` while unset), a memory object's identity (`none` while
unset: only a hidden binder leaves one so, decision 17'), a whole storage
(`old`) or ledger (`oldNet`).  Reducible, so a local's value finds the instances of its type. -/
@[reducible] def LTy.Denote (_C : Contract) : LTy → Type
  | .val _ => Value
  | .alias _ => Option (Name × List Seg)
  | .mem _ => Option Nat
  | .old => List (Name × SVal)
  | .oldNet => List (Int × Int)

/-- The locals of `Γ`, innermost first: a type computed from `Γ`, not an
inductive family (condition 4). -/
def Env (C : Contract) : Ctx → Type
  | [] => Unit
  | t :: Γ => t.Denote C × Env C Γ

namespace Env

/-- The local at a position. -/
def get : {Γ : Ctx} → {t : LTy} → Idx Γ t → Env C Γ → t.Denote C
  | _, _, i => Idx.casesOn (motive := fun Γ t _ => Env C Γ → t.Denote C) i (fun e => e.1)
      (fun i e => Env.get i e.2)
  termination_by structural _ _ i => i

/-- The local at a position, set. -/
def set : {Γ : Ctx} → {t : LTy} → Idx Γ t → t.Denote C → Env C Γ → Env C Γ
  | _, _, i => Idx.casesOn (motive := fun Γ t _ => t.Denote C → Env C Γ → Env C Γ) i
      (fun w e => (w, e.2)) (fun i w e => (e.1, Env.set i w e.2))
  termination_by structural _ _ i => i

/-- The locals a suffix pushed, popped. -/
def drop {Γ : Ctx} : {Δ : Ctx} → Ext Γ Δ → Env C Δ → Env C Γ
  | _, h => Ext.casesOn (motive := fun Δ _ => Env C Δ → Env C Γ) h (fun e => e)
      (fun h e => Env.drop h e.2)
  termination_by structural _ h => h

/-- The locals `ρ` on top of `Γ`'s. -/
def append {Γ : Ctx} : (ρ : Ctx) → Env C ρ → Env C Γ → Env C (ρ ++ Γ)
  | [], _, e => e
  | _ :: ρ, r, e => (r.1, Env.append ρ r.2 e)

/-- The top `ρ` of the locals. -/
def take {Γ : Ctx} : (ρ : Ctx) → Env C (ρ ++ Γ) → Env C ρ
  | [], _ => ()
  | _ :: ρ, e => (e.1, Env.take ρ e.2)

theorem get_set {Γ : Ctx} {t : LTy} (i : Idx Γ t) (v : t.Denote C) (e : Env C Γ) :
    Env.get i (Env.set i v e) = v := by
  induction i with
  | here => rfl
  | there i ih => exact ih v e.2

theorem take_append {Γ : Ctx} (ρ : Ctx) (r : Env C ρ) (e : Env C Γ) :
    Env.take ρ (Env.append ρ r e) = r := by
  induction ρ with
  | nil => rfl
  | cons t ρ ih => show (r.1, Env.take ρ (Env.append ρ r.2 e)) = r; rw [ih]; rfl

theorem drop_append {Γ : Ctx} (ρ : Ctx) (r : Env C ρ) (e : Env C Γ) :
    Env.drop (Ext.append Γ ρ) (Env.append ρ r e) = e := by
  induction ρ with
  | nil => rfl
  | cons t ρ ih => exact ih r.2

end Env

/-! ## States -/

/-- A state in the context `Γ`: `Semantics.State`'s parts, the locals typed
by `Γ`. -/
structure EState (C : Contract) (Γ : Ctx) where
  storage : List (Name × SVal)
  heap : List (Nat × Semantics.MObj) := []
  nextId : Nat := 0
  env : Env C Γ
  net : List (Int × Int) := []
  selfBalance : Int := 0
  tx : Semantics.TxEnv := {}

namespace EState

/-- Everything but the locals, as `Semantics.lean`'s operations take it. -/
def glob {Γ : Ctx} (σ : EState C Γ) : Semantics.State :=
  { storage := σ.storage, heap := σ.heap, nextId := σ.nextId, net := σ.net,
    selfBalance := σ.selfBalance, tx := σ.tx }

/-- A global part with locals. -/
def ofGlob {Γ : Ctx} (τ : Semantics.State) (e : Env C Γ) : EState C Γ :=
  { storage := τ.storage, heap := τ.heap, nextId := τ.nextId, env := e, net := τ.net,
    selfBalance := τ.selfBalance, tx := τ.tx }

/-- The global part replaced. -/
def withGlob {Γ : Ctx} (σ : EState C Γ) (τ : Semantics.State) : EState C Γ := ofGlob τ σ.env

/-- The locals replaced, in another context. -/
def withEnv {Γ Δ : Ctx} (σ : EState C Γ) (e : Env C Δ) : EState C Δ :=
  { storage := σ.storage, heap := σ.heap, nextId := σ.nextId, env := e, net := σ.net,
    selfBalance := σ.selfBalance, tx := σ.tx }

/-- A local declared. -/
def push {Γ : Ctx} {t : LTy} (σ : EState C Γ) (v : t.Denote C) : EState C (t :: Γ) :=
  σ.withEnv (v, σ.env)

/-- A local set. -/
def setLocal {Γ : Ctx} {t : LTy} (σ : EState C Γ) (i : Idx Γ t) (v : t.Denote C) : EState C Γ :=
  σ.withEnv (Env.set i v σ.env)

/-- A scope's locals popped. -/
def drop {Γ Δ : Ctx} (h : Ext Γ Δ) (σ : EState C Δ) : EState C Γ := σ.withEnv (Env.drop h σ.env)

/-- A global state with no locals. -/
def ofSem (τ : Semantics.State) : EState C [] := EState.ofGlob τ ()

end EState

/-! ## A local's binding -/

section Eval

variable {Γ : Ctx}

/-- The path an alias is bound to; an unset one reverts. -/
def aliasPath (σ : EState C Γ) {R : RefTy} (i : Idx Γ (.alias R)) : Res (Name × List Seg) :=
  match (Env.get i σ.env : Option (Name × List Seg)) with
  | some p => pure p
  | none => .error .revert

/-- The object a memory local names; an unset one reverts, as an unset
alias does (decision 17'). -/
def memRef (σ : EState C Γ) {R : RefTy} (i : Idx Γ (.mem R)) : Res Nat :=
  match (Env.get i σ.env : Option Nat) with
  | some id => pure id
  | none => .error .revert

end Eval

/-! ## Examples

Scoped programs the typed run's examples run (`Semantics/Run.lean`). -/

section Examples

def guardLowCore := sol[StandardExample]{ require(age > 3); }
def assertLowCore := sol[StandardExample]{ assert(age > 3); }
def incOrderCore := sol[TestSuite]{ uint i = 1; uint x = i++ + i; assert(x == 2); assert(i == 2); }
def indexOrderCore := sol[TestSuite]{ uint i = 0; values.push(100);
  values.push(100); values.push(100); values[++i] = ++i; assert(values[2] == 1); }

end Examples

end Solidity
