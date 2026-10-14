import Solidity.Typing.HeredRun

/-!
# What every reachable storage satisfies beyond its types

A typed storage has its roots, its structs their members, its words in
range and its fixed-size arrays their lengths, by its types
(`Semantics/Storage.lean`).  What else every reachable storage satisfies is
a property of its values, `SVal.Canon` (`canonH`): a mapping's keys are
**unique** (they only grow by `setBy`), and its default is **the** type's
default (`save` and `delete` never touch it), at every node, the slots a
`pop` recycled and a mapping's default included.  Then a storage whose
mapping default is not the default (`map_default_not_reachable`) or whose
mapping repeats a key (`map_dup_key_not_reachable`) is not `Reachable`.

`Prog.run_canon` is the preservation theorem (the typed run keeps
`heredInv C canonH`, `Typing/HeredRun.lean`: each storage operation keeps
the node conditions, `canonH_run`), `reachable_canon` its corollary from a
contract's initial state (`Reachable`: a scoped program `Prog C [] Γ'` runs
there by the typed interpreter).

The converse is `Typing/Constructibility.lean`: canonical is not enough, and
canonical and tight (`SVal.Tight`) is exactly reachable for a storage that
fits (`reachable_iff`), with no premise on the storage under `FixedFits`
(`reachable_iff_fits`, `Typing/Fits.lean`).
-/

namespace Solidity

open Semantics (structDef lookupBy setBy nodupKeysB)

variable {C : Contract}

/-! ## The canonical values -/

/-- A canonical node: a mapping's keys distinct and its default the type's
default. -/
def canonH : Hered where
  arr _ _ := True
  fix _ _ := True
  map _ := fun {V} m d => nodupKeysB m.toList = true ∧ d = SVal.dflt V

/-- `v` is canonical: every mapping in it has distinct keys and the
default default, recursively (recycled array slots included). -/
abbrev SVal.Canon {T : Ty} (v : SVal T) : Prop := v.All canonH

/-- Every root canonical. -/
abbrev Storage.Canon (st : Storage C) : Prop := st.All canonH

/-- A default is canonical. -/
theorem SVal.dflt_canon (T : Ty) : (SVal.dflt T).Canon :=
  SVal.dflt_all (P := canonH) (fun _ => trivial) (fun _ _ => trivial)
    (fun _ _ => ⟨by rw [SMap.toList_nil]; rfl, rfl⟩) T

/-- **Every storage operation keeps the nodes canonical**: a key written by
`setBy` is written once, and nothing writes a mapping's default. -/
theorem canonH_run : HeredRun canonH (fun _ => True) where
  save _ _ _ _ _ _ _ _ := trivial
  map _ _ _ _ _ h := ⟨by rw [SMap.toList_ofList]; exact nodupKeysB_setBy' h.1, h.2⟩
  strip _ _ _ _ := trivial
  del _ _ _ _ := trivial
  ov _ _ _ _ _ _ _ _ _ := trivial
  push _ _ _ _ _ _ _ _ _ := trivial
  pop _ _ _ _ _ _ _ _ _ := trivial
  dflt := SVal.dflt_canon
  plain v _ h := SVal.all_mono' (P := canonH) (Q := plainH) (fun _ _ _ _ => trivial) (fun _ _ _ => trivial)
    (fun _ _ h => h.elim) v h

/-- The storage a contract starts with is canonical. -/
theorem Storage.init_canon : (Storage.init C).Canon :=
  SFields.dflt_all (P := canonH) (fun _ => trivial) (fun _ _ => trivial)
    (fun _ _ => ⟨by rw [SMap.toList_nil]; rfl, rfl⟩) C.vars

/-! ## The run keeps the storage canonical -/

/-- What a run keeps beyond its types: canonical storage (and aliases along
keys a program writes). -/
abbrev canonInv (C : Contract) : RunInv C := heredInv C canonH

/-- **Canonicity**: a block run by the typed run from a state whose storage
is canonical, its aliases bound along keys a program writes, ends, if in a
state, in one whose storage is canonical: after `alice.age = 3;` every
mapping still has distinct keys, after `balances[7] += 1;` key `7` is there
once. -/
theorem Prog.run_canon {Γ Γ' : Ctx} (P : Prog C Γ Γ') {σ : State C Γ} {o : Out C σ.H Γ'}
    (hσ : (canonInv C).HoldsT σ) (h : P.run σ = .ok o) : o.st.storage.Canon :=
  Prog.run_all canonH_run (fun _ => trivial) P hσ h

/-! ## Reachable storages -/

/-- A storage is reachable when a scoped program runs, by the typed
interpreter (`Prog.run`, `Semantics/Run.lean`), from the contract's initial
state (`State.init`: every root at its default, no locals, no memory) to a
state with that storage.  A `bool` mapping key is hashed as `0`/`1`
(decisions 10 and 14). -/
def Reachable (C : Contract) (st : Storage C) : Prop :=
  ∃ (Γ' : Ctx) (P : Prog C [] Γ') (o : Out C (State.init C).H Γ'),
    P.run (State.init C) = .ok o ∧ o.st.storage = st

/-- The initial state satisfies a hereditary invariant its default storage
does: it has no locals. -/
theorem heredInv.init {P : Hered} (h : (Storage.init C).All P) :
    (heredInv C P).HoldsT (State.init C) :=
  ⟨h, trivial⟩

/-- What every run from the initial state keeps holds of every reachable
storage. -/
theorem Reachable.all {P : Hered} {G : Ty → Prop} (hP : HeredRun P G)
    (hG : ∀ {U : Ty}, SRef C U → G U) (hi : (Storage.init C).All P) {st : Storage C}
    (h : Reachable C st) : st.All P := by
  obtain ⟨Γ', P', o, hrun, rfl⟩ := h
  exact Prog.run_all hP hG P' (heredInv.init hi) hrun

/-- **Reachable ⇒ canonical.**  Every storage a scoped program reaches from
`C`'s initial state has distinct keys and the default default in every
mapping. -/
theorem reachable_canon {st : Storage C} (h : Reachable C st) : st.Canon :=
  Reachable.all canonH_run (fun _ => trivial) Storage.init_canon h

/-! ## What is not reachable

Two storages the types admit and no scoped program reaches (`Reachable`).
A third, a struct missing a member, the types no longer admit
(`SFields (structDef s)`). -/

section Witnesses

/-- One mapping root. -/
def Balances : Contract := contract!{ mapping(uint => uint) balances; }

/-- `balances` with absent keys reading `5`. -/
def Balances.five : Storage Balances :=
  .cons (.map .nil (.prim (PrimTy.ofLit .uint 5 rfl))) .nil

/-- `balances` with key `1` twice. -/
def Balances.dup : Storage Balances :=
  .cons (.map (.cons (PrimTy.ofLit .uint 1 rfl) (.prim (PrimTy.ofLit .uint 0 rfl))
    (.cons (PrimTy.ofLit .uint 1 rfl) (.prim (PrimTy.ofLit .uint 1 rfl)) .nil))
    (.prim (PrimTy.dflt .uint))) .nil

/-- A mapping whose absent keys read `5`: typed, not reachable, since every
mapping's default is its type's default. -/
theorem map_default_not_reachable : ¬ Reachable Balances Balances.five := by
  intro h
  have hc := reachable_canon h
  simp only [Balances.five, SFields.All, SVal.All] at hc
  have hd := hc.1.1.2
  rw [SVal.dflt_prim] at hd
  cases hd

/-- A mapping with key `1` twice: typed, not reachable, since keys only grow
by `setBy`. -/
theorem map_dup_key_not_reachable : ¬ Reachable Balances Balances.dup := by
  intro h
  have hc := reachable_canon h
  simp only [Balances.dup, SFields.All, SVal.All] at hc
  exact absurd hc.1.1.1 (by simp only [SMap.toList]; decide)

end Witnesses

end Solidity
