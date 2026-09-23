import Solidity.Update.Step
import Solidity.Update.LowerLaws

/-!
# Lowering a line's reads onto the storage theory

After the calculus has run a program, a line reads

    {storage := save(storage, ledger.nonce, 5)} … {n := find(storage, ledger.nonce)} (φ)

and the paper keeps going: the read is a term of `structRules.key`'s signature
over the storage the line started from, `findSt(save(storage, …), …)`, and the
theories rewrite it to `5`.  `lowerLine` is that step.  It walks the stack,
keeping the storage writes it has seen as a term of `Theory/Storage.lean` over
the pre-state leaf `Theory.Struct.cur`, and replaces each read it can by a
**rigid read** (`Sequent.rigid`) of that term.  The frontier then *contains*
`findSt (save (cur []) [ledger, nonce] 5) [ledger, nonce]`, and `theory_rw`
rewrites it with the theory's own equations.

`lowerLine_upd` is why that is a merge line and not a leap: the lowered line
denotes the same update.  The work is `LowerLaws.Sim` — the interpreter's
storage and the theory term agree on every read the term answers with a literal
or with the untouched pre-state — carried through the stack.  A read the term
answers otherwise (a member of a deleted struct the program never wrote, where
the interpreter's lazy `delete` and the theory's eager one part) is left where
it is.

**What it handles.**  One storage root, the first the stack names; writes of a
literal at a nested place; deletes; and any binding, tracked when it is a
literal or a path alias.  It stops at the first update it does not know, and
leaves the rest of the stack alone.
-/

namespace Solidity
namespace Update

open Semantics SemanticsProperties Wp Rules Theory Theory.StValue

/-! ## The storage term, as data -/

/-- The writes seen so far, as data: the tactic needs a term it can compute
with (`seq_lower` reduces it) without computing the theory's `save`. -/
inductive TTerm where
  | cur
  | save (t : TTerm) (p : List Seg) (v : PrimVal)
  | delAt (t : TTerm) (p : List Seg)
  deriving Repr, DecidableEq

/-- The theory term it stands for. -/
def TTerm.toStruct : TTerm -> Struct
  | .cur => Struct.cur []
  | .save t p v => Theory.StValue.save t.toStruct p (prim v)
  | .delAt t p => Theory.StValue.delAt t.toStruct p

/-- A rigid read of it.  Irreducible, so `seq_lower` can normalise a frontier
without evaluating the read; `simp only [TTerm.read, TTerm.toStruct]` then
spells it as the theory term `theory_rw` works on. -/
@[irreducible] def TTerm.read (t : TTerm) (p : List Seg) : StValue := findSt t.toStruct p

/-- The theory answers with something the interpreter can be held to. -/
def claimOk : StValue -> Bool
  | prim _ => true
  | st (Struct.cur _) => true
  | _ => false

/-! ## What the walk knows -/

/-- A name the stack has bound: to a literal, to a path below the root, or to
something the walk does not follow. -/
inductive Known where
  | lit (v : Value)
  | path (r : List Seg)
  | unknown
  deriving Repr, DecidableEq

/-- An index the walk can read: a literal, or a stack variable bound to one. -/
def intOf (σ : List (Name × Known)) : WrappedExpr -> Option Int
  | WrappedExpr.intLit _ i => some i
  | WrappedExpr.var Kind.stack _ fld =>
      match lookupBy fld.name σ with
      | some (Known.lit (Value.int i)) => some i
      | _ => none
  | _ => none

/-- A value the walk can read, likewise. -/
def valOf (σ : List (Name × Known)) : Sym -> Option Value
  | Sym.read (WrappedExpr.intLit _ i) => some (Value.int i)
  | Sym.read (WrappedExpr.bool b) => some (Value.bool b)
  | Sym.read (WrappedExpr.var Kind.stack _ fld) =>
      match lookupBy fld.name σ with
      | some (Known.lit v) => some v
      | _ => none
  | Sym.deflt ty => some (defaultValue ty)
  | _ => none

/-- A place's path below the root `R`: `R` itself as a state variable, an
alias the walk has seen bound, then fields and readable indices. -/
def pathOf (R : Name) (σ : List (Name × Known)) : WrappedExpr -> Option (List Seg)
  | WrappedExpr.var _ _ fld =>
      match lookupBy fld.name σ with
      | some (Known.path r) => some r
      | some _ => none
      | none => if fld.name = R ∧ fld.origin = some StorageOrigin.global then some [] else none
  | WrappedExpr.field _ _ base f => (pathOf R σ base).map (· ++ [Seg.field f.name])
  | WrappedExpr.index _ _ base ix =>
      pathOf R σ base >>= fun r => (intOf σ ix).map fun i => r ++ [Seg.at i]
  | _ => none

/-- A write's target: a nested place (a bare root is written by origin, not
through `varPath`, so it would not be the root the reads see). -/
def targetOf (R : Name) (σ : List (Name × Known)) : WrappedExpr -> Option (List Seg)
  | e@(WrappedExpr.field _ _ _ _) => pathOf R σ e
  | e@(WrappedExpr.index _ _ _ _) => pathOf R σ e
  | _ => none

/-- A read the walk can lower: a storage place below the root. -/
def readOf (R : Name) (σ : List (Name × Known)) : WrappedExpr -> Option (List Seg)
  | e@(WrappedExpr.var Kind.storage _ _) => pathOf R σ e
  | e@(WrappedExpr.field Kind.storage _ _ _) => pathOf R σ e
  | e@(WrappedExpr.index Kind.storage _ _ _) => pathOf R σ e
  | _ => none

/-- What a binding tells the walk. -/
def knownOf (R : Name) (σ : List (Name × Known)) : BindRhs -> Known
  | BindRhs.val t => match valOf σ t with
      | some v => Known.lit v
      | none => Known.unknown
  | BindRhs.path src => match pathOf R σ src with
      | some r => Known.path r
      | none => Known.unknown
  | _ => Known.unknown

/-- One step of the walk. -/
inductive LStep where
  | stop
  | keep (σ : List (Name × Known)) (X : TTerm)
  | rigid (n : Name) (ty : Ty) (p : List Seg) (σ : List (Name × Known))

def lstep (R : Name) (σ : List (Name × Known)) (X : TTerm) : UpdTerm -> LStep
  | [UpdElem.storage (StTerm.save StTerm.cur tgt (StVal.sym t))] =>
      match targetOf R σ tgt, valOf σ t with
      | some r, some v => .keep σ (.save X (Seg.field R :: r) v)
      | _, _ => .stop
  | [UpdElem.storage (StTerm.delAt StTerm.cur tgt)] =>
      match pathOf R σ tgt with
      | some r => .keep σ (.delAt X (Seg.field R :: r))
      | none => .stop
  | [UpdElem.bind n rhs] =>
      if n = R then .stop
      else match rhs with
        | BindRhs.val (Sym.read e) =>
            match readOf R σ e with
            | some r =>
                if claimOk (findSt X.toStruct (Seg.field R :: r)) then
                  .rigid n e.ty (Seg.field R :: r) (setBy n Known.unknown σ)
                else .keep (setBy n (knownOf R σ rhs) σ) X
            | none => .keep (setBy n (knownOf R σ rhs) σ) X
        | _ => .keep (setBy n (knownOf R σ rhs) σ) X
  | _ => .stop

/-- A rigid read, one update further from the one before it. -/
def bumpRigid : List (Nat × Name × Ty × TTerm × List Seg) -> List (Nat × Name × Ty × TTerm × List Seg)
  | [] => []
  | (k, e) :: rs => (k + 1, e) :: rs

/-- The walk: the stack left, and the rigid reads to weave into it. -/
def lowerGo (R : Name) :
    List (Name × Known) -> TTerm -> List UpdTerm ->
      List UpdTerm × List (Nat × Name × Ty × TTerm × List Seg)
  | _, _, [] => ([], [])
  | σ, X, u :: us =>
      match lstep R σ X u with
      | .stop => (u :: us, [])
      | .keep σ' X' =>
          let r := lowerGo R σ' X' us
          (u :: r.1, bumpRigid r.2)
      | .rigid n ty p σ' =>
          let r := lowerGo R σ' X us
          (r.1, (0, n, ty, X, p) :: r.2)

/-- The root a stack writes under: the first storage place it names. -/
def placeRoot : WrappedExpr -> Option Name
  | WrappedExpr.var Kind.storage _ fld => some fld.name
  | WrappedExpr.field _ _ base _ => placeRoot base
  | WrappedExpr.index _ _ base _ => placeRoot base
  | _ => none

def firstRoot : List UpdTerm -> Option Name
  | [] => none
  | [UpdElem.storage (StTerm.save StTerm.cur tgt _)] :: us => (placeRoot tgt).orElse fun _ => firstRoot us
  | [UpdElem.storage (StTerm.delAt StTerm.cur tgt)] :: us => (placeRoot tgt).orElse fun _ => firstRoot us
  | _ :: us => firstRoot us

def toRigid (rs : List (Nat × Name × Ty × TTerm × List Seg)) :
    List (Nat × Name × Ty × Theory.StValue) :=
  rs.map fun (k, n, ty, t, p) => (k, n, ty, t.read p)

/-- Lower one line.  A line that already has rigid reads is left alone. -/
def lowerLine (q : Sequent) : Sequent :=
  match q.rigid, firstRoot q.upds with
  | [], some R =>
      let r := lowerGo R [] .cur q.upds
      { q with upds := r.1, rigid := toRigid r.2 }
  | _, _ => q

def lowerFrontier (f : Frontier) : Frontier := f.map lowerLine

/-! ## Soundness -/

section Soundness

/-- What a binding the walk tracks says about the state. -/
def KnownOk (s : State) (R n : Name) : Known -> Prop
  | .lit v => lookupBy n s.env = some (Binding.val v)
  | .path r => ∃ ρ : Name × List Seg, varPath s (rootField R) = .ok ρ ∧
      lookupBy n s.env = some (Binding.spath ρ.1 (ρ.2 ++ r))
  | .unknown => True

/-- The walk's invariant: the root is not rebound, the tracked bindings hold,
and the storage term simulates the storage. -/
structure Inv (s0 : State) (R : Name) (σ : List (Name × Known)) (X : TTerm) (s : State) : Prop where
  root : lookupBy R s.env = lookupBy R s0.env
  known : ∀ n k, lookupBy n σ = some k -> KnownOk s R n k
  sim : Sim X.toStruct R (storageAt s0 R) (storageAt s R)

theorem varPath_congr {s t : State} {f g : Field} (hn : f.name = g.name)
    (ho : f.origin = g.origin) (he : lookupBy f.name s.env = lookupBy f.name t.env) :
    varPath s f = varPath t g := by
  unfold varPath
  rw [he, hn, ho]

theorem toUpd_bind (n : Name) (rhs : BindRhs) (s : State) :
    UpdTerm.toUpd [UpdElem.bind n rhs] s = (bindRhs rhs s).map fun b => s.setEnv n b := by
  simp only [UpdTerm.toUpd, UpdTerm.toPar, List.flatMap_cons, List.flatMap_nil, elemPar,
    List.append_nil]
  exact Upd.toUpd_env n _ s

theorem toUpd_storageElem (t : StTerm) (s : State) :
    UpdTerm.toUpd [UpdElem.storage t] s = (storageRhs t s).map fun g => { s with storage := g } := by
  simp only [UpdTerm.toUpd, UpdTerm.toPar, List.flatMap_cons, List.flatMap_nil, elemPar,
    List.append_nil]
  exact Upd.toUpd_storage _ s

variable {s0 : State} {R : Name}

theorem intOf_sound {σ : List (Name × Known)} {X : TTerm} {s : State} {ix : WrappedExpr} {i : Int}
    (hI : Inv s0 R σ X s) (h : intOf σ ix = some i) :
    simpleInt s ix = .ok i ∧ (readTerm s ix >>= Value.asInt) = .ok i := by
  unfold intOf at h
  split at h
  · cases h
    simp [simpleInt, simpleVal, readTerm, readVal, bind, Except.bind, Value.asInt]
  · rename_i fld
    split at h
    · rename_i i' hk
      cases h
      have := hI.known _ _ hk
      simp only [KnownOk] at this
      simp [simpleInt, simpleVal, readTerm, readVal, stackVal, this, bind, Except.bind,
        Value.asInt]
    · cases h
  · cases h

theorem valOf_sound {σ : List (Name × Known)} {X : TTerm} {s : State} {t : Sym} {v : Value}
    (hI : Inv s0 R σ X s) (h : valOf σ t = some v) : Sym.eval s t = .ok v := by
  unfold valOf at h
  split at h
  · cases h; simp [Sym.eval, readTerm, readVal]
  · cases h; simp [Sym.eval, readTerm, readVal]
  · rename_i fld
    split at h
    · rename_i v' hk
      cases h
      have := hI.known _ _ hk
      simp only [KnownOk] at this
      simp [Sym.eval, readTerm, readVal, stackVal, this]
    · cases h
  · cases h; rfl
  · cases h

theorem pathOf_sound {σ : List (Name × Known)} {X : TTerm} {s : State} (hI : Inv s0 R σ X s) :
    ∀ {e : WrappedExpr} {r : List Seg}, pathOf R σ e = some r ->
      placePath s e = (varPath s (rootField R)).map fun ρ => (ρ.1, ρ.2 ++ r)
  | WrappedExpr.var k ty fld, r, h => by
      unfold pathOf at h
      split at h
      · rename_i r' hk
        cases h
        obtain ⟨ρ, hρ, hn⟩ := hI.known _ _ hk
        simp only [placePath, hρ]
        simp [varPath, hn, Except.map]
      · cases h
      · rename_i hnone
        split at h
        · rename_i hc
          cases h
          have hv : varPath s fld = varPath s (rootField R) :=
            varPath_congr hc.1 hc.2 rfl
          simp only [placePath, hv]
          cases varPath s (rootField R) <;> simp [Except.map]
        · cases h
  | WrappedExpr.field k ty base f, r, h => by
      unfold pathOf at h
      cases hb : pathOf R σ base with
      | none => rw [hb] at h; cases h
      | some rb =>
          rw [hb] at h
          cases h
          simp only [placePath, pathOf_sound hI hb]
          cases varPath s (rootField R) <;> simp [Except.map, bind, Except.bind]
  | WrappedExpr.index k ty base ix, r, h => by
      unfold pathOf at h
      cases hb : pathOf R σ base with
      | none => rw [hb] at h; cases h
      | some rb =>
          cases hi : intOf σ ix with
          | none => rw [hb] at h; simp [hi, bind, Option.bind] at h
          | some i =>
              rw [hb] at h
              simp [hi, bind, Option.bind] at h
              subst h
              simp only [placePath, pathOf_sound hI hb, (intOf_sound hI hi).1]
              cases varPath s (rootField R) <;> simp [Except.map, bind, Except.bind]
  | WrappedExpr.pushPlace _, _, h | WrappedExpr.bool _, _, h | WrappedExpr.intLit _ _, _, h
  | Typed.WrappedExpr.mkCall _ _ _ _, _, h | Typed.WrappedExpr.mkBinop _ _ _, _, h
  | Typed.WrappedExpr.mkUnop _ _, _, h | Typed.WrappedExpr.mkIncDec _ _, _, h
  | Typed.WrappedExpr.mkTernary _ _ _, _, h => by simp [pathOf] at h

theorem storageAt_congr {s t : State} (he : lookupBy R s.env = lookupBy R t.env)
    (hst : s.storage = t.storage) : storageAt s R = storageAt t R := by
  funext r
  unfold storageAt State.findStorage
  rw [varPath_congr rfl rfl he, hst]

theorem storageAt_eq_find {s : State} {ρ : Name × List Seg} {old : SVal}
    (hρ : varPath s (rootField R) = .ok ρ) (hv : lookupBy ρ.1 s.storage = some old) :
    storageAt s R = fun r => old.find (ρ.2 ++ r) := by
  funext r
  simp [storageAt, hρ, State.findStorage, hv, bind, Except.bind]

theorem KnownOk.congr {s t : State} {n : Name} {k : Known}
    (hR : lookupBy R s.env = lookupBy R t.env) (hn : lookupBy n s.env = lookupBy n t.env)
    (h : KnownOk s R n k) : KnownOk t R n k := by
  cases k with
  | lit v => simpa [KnownOk, hn] using h
  | path r =>
      obtain ⟨ρ, hρ, hl⟩ := h
      exact ⟨ρ, by rw [← varPath_congr rfl rfl hR]; exact hρ, by rw [← hn]; exact hl⟩
  | unknown => trivial

/-- A binding the walk steps over keeps the invariant, the bound name now
known as `k`. -/
theorem Inv.setEnv {σ : List (Name × Known)} {X : TTerm} {s : State} {n : Name} {b : Binding}
    {k : Known} (hI : Inv s0 R σ X s) (hn : n ≠ R) (hk : KnownOk (s.setEnv n b) R n k) :
    Inv s0 R (setBy n k σ) X (s.setEnv n b) := by
  have hR : lookupBy R s.env = lookupBy R (s.setEnv n b).env := by
    simp [State.setEnv, lookupBy_setBy_ne (Ne.symm hn)]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hR]; exact hI.root
  · intro m k' hm
    by_cases hmn : m = n
    · subst hmn
      rw [lookupBy_setBy_self] at hm
      cases hm
      exact hk
    · rw [lookupBy_setBy_ne hmn] at hm
      exact (hI.known m k' hm).congr hR (by simp [State.setEnv, lookupBy_setBy_ne hmn])
  · rw [← storageAt_congr hR rfl]; exact hI.sim

/-- A storage write keeps the tracked bindings. -/
theorem Inv.withStorage {σ : List (Name × Known)} {X X' : TTerm} {s : State}
    {g : List (Name × SVal)} (hI : Inv s0 R σ X s)
    (hsim : Sim X'.toStruct R (storageAt s0 R) (storageAt { s with storage := g } R)) :
    Inv s0 R σ X' { s with storage := g } :=
  ⟨hI.root, fun n k h => (hI.known n k h).congr rfl rfl, hsim⟩

theorem Value.toSVal_eq (v : Value) : v.toSVal = SVal.prim v := by
  cases v <;> rfl

/-- The storage a successful write at a resolved path installs. -/
theorem saveStorage_ok {s s' : State} {root : Name} {segs : List Seg} {new : SVal}
    (h : s.saveStorage root segs new = .ok s') :
    ∃ old upd, lookupBy root s.storage = some old ∧ old.save segs new = .ok upd ∧
      s' = { s with storage := setBy root upd s.storage } := by
  unfold State.saveStorage at h
  cases hv : lookupBy root s.storage with
  | none => simp [hv] at h
  | some old =>
      simp only [hv] at h
      cases hs : old.save segs new with
      | error e => rw [hs] at h; cases h
      | ok upd =>
          rw [hs] at h
          cases h
          exact ⟨old, upd, rfl, hs, rfl⟩

theorem storageAt_after {s : State} {ρ : Name × List Seg} {upd : SVal}
    (hρ : varPath s (rootField R) = .ok ρ) :
    storageAt { s with storage := setBy ρ.1 upd s.storage } R = fun r => upd.find (ρ.2 ++ r) :=
  storageAt_eq_find (s := { s with storage := setBy ρ.1 upd s.storage })
    (by rw [← hρ]; exact varPath_congr rfl rfl rfl) (lookupBy_setBy_self _ _ _)

theorem locPath_of_target {σ : List (Name × Known)} {X : TTerm} {s : State}
    {tgt : WrappedExpr} {r : List Seg} (hI : Inv s0 R σ X s) (ht : targetOf R σ tgt = some r) :
    locPath s tgt = (varPath s (rootField R)).map fun ρ => (ρ.1, ρ.2 ++ r) := by
  cases tgt <;> simp only [targetOf] at ht <;> first | cases ht | exact pathOf_sound hI ht

/-- **A write of a literal**, kept in the stack: the term grows by the same
`save`. -/
theorem step_save {σ : List (Name × Known)} {X : TTerm} {s s' : State}
    {tgt : WrappedExpr} {t : Sym} {r : List Seg} {v : Value}
    (hI : Inv s0 R σ X s) (ht : targetOf R σ tgt = some r) (hv : valOf σ t = some v)
    (h : UpdTerm.toUpd [UpdElem.storage (StTerm.save StTerm.cur tgt (StVal.sym t))] s = .ok s') :
    Inv s0 R σ (.save X (Seg.field R :: r) v) s' := by
  rw [toUpd_storageElem, storageRhs_save_cur] at h
  simp only [stVal, valOf_sound hI hv] at h
  rw [show Except.map Value.toSVal (Except.ok v) >>= storageSave s tgt
      = storageSave s tgt v.toSVal from rfl] at h
  simp only [storageSave, locPath_of_target hI ht] at h
  cases hρ : varPath s (rootField R) with
  | error e => simp [hρ, Except.map, bind, Except.bind] at h
  | ok ρ =>
      cases hs : s.saveStorage ρ.1 (ρ.2 ++ r) v.toSVal with
      | error e => simp [hρ, hs, Upd.saveSt, Except.map, bind, Except.bind] at h
      | ok s1 =>
          simp [hρ, hs, Upd.saveSt, Except.map, bind, Except.bind] at h
          subst h
          obtain ⟨old, upd, hold, hsave, rfl⟩ := saveStorage_ok hs
          refine hI.withStorage ?_
          rw [storageAt_after hρ]
          have hsim := hI.sim
          rw [storageAt_eq_find hρ hold] at hsim
          rw [Value.toSVal_eq] at hsave
          exact sim_save hsim hsave

/-- `delAtOn`'s path is the place's path below the root, index or not. -/
theorem delAtOn_eq {σ : List (Name × Known)} {X : TTerm} {s : State}
    {tgt : WrappedExpr} {r : List Seg} (hI : Inv s0 R σ X s) (hp : pathOf R σ tgt = some r)
    (g : List (Name × SVal)) :
    delAtOn s g tgt =
      (varPath s (rootField R) >>= fun ρ =>
        { s with storage := g }.findStorage ρ.1 (ρ.2 ++ r) >>= fun c =>
          ({ s with storage := g }.saveStorage ρ.1 (ρ.2 ++ r) c.defaultOf).map State.storage) := by
  have hpl := pathOf_sound hI hp
  unfold delAtOn
  cases tgt with
  | index k ty base ix =>
      unfold pathOf at hp
      cases hb : pathOf R σ base with
      | none => rw [hb] at hp; cases hp
      | some rb =>
          cases hi : intOf σ ix with
          | none => rw [hb] at hp; simp [hi, bind, Option.bind] at hp
          | some i =>
              rw [hb] at hp
              simp [hi, bind, Option.bind] at hp
              subst hp
              have hbase := pathOf_sound hI hb
              have hix := (intOf_sound hI hi).2
              simp only [hbase]
              cases varPath s (rootField R) with
              | error e => rfl
              | ok ρ =>
                  simp only [Except.map, bind, Except.bind] at hix ⊢
                  simp only [List.append_assoc]
                  split at hix <;> simp_all
  | var k ty fld =>
      simp only [deletePath, hpl]
      cases varPath s (rootField R) <;> rfl
  | field k ty base f =>
      simp only [deletePath, hpl]
      cases varPath s (rootField R) <;> rfl
  | pushPlace _ => simp [pathOf] at hp
  | bool _ => simp [pathOf] at hp
  | intLit _ _ => simp [pathOf] at hp
  | mkCall _ _ _ _ => simp [pathOf] at hp
  | mkBinop _ _ _ => simp [pathOf] at hp
  | mkUnop _ _ => simp [pathOf] at hp
  | mkIncDec _ _ => simp [pathOf] at hp
  | mkTernary _ _ _ => simp [pathOf] at hp

/-- **A delete**, kept in the stack: the term grows by the same `delAt`. -/
theorem step_delAt {σ : List (Name × Known)} {X : TTerm} {s s' : State}
    {tgt : WrappedExpr} {r : List Seg}
    (hI : Inv s0 R σ X s) (hp : pathOf R σ tgt = some r)
    (h : UpdTerm.toUpd [UpdElem.storage (StTerm.delAt StTerm.cur tgt)] s = .ok s') :
    Inv s0 R σ (.delAt X (Seg.field R :: r)) s' := by
  rw [toUpd_storageElem, storageRhs_delAt_cur, delAtOn_eq hI hp] at h
  have heta : ({ s with storage := s.storage } : State) = s := rfl
  rw [heta] at h
  cases hρ : varPath s (rootField R) with
  | error e => simp [hρ, Except.map, bind, Except.bind] at h
  | ok ρ =>
      cases hf : s.findStorage ρ.1 (ρ.2 ++ r) with
      | error e => simp [hρ, hf, Except.map, bind, Except.bind] at h
      | ok c =>
          cases hs : s.saveStorage ρ.1 (ρ.2 ++ r) c.defaultOf with
          | error e => simp [hρ, hf, hs, Except.map, bind, Except.bind] at h
          | ok s1 =>
              simp [hρ, hf, hs, Except.map, bind, Except.bind] at h
              subst h
              obtain ⟨old, upd, hold, hsave, rfl⟩ := saveStorage_ok hs
              have hc : old.find (ρ.2 ++ r) = .ok c := by
                simpa [State.findStorage, hold] using hf
              refine hI.withStorage ?_
              rw [storageAt_after hρ]
              have hsim := hI.sim
              rw [storageAt_eq_find hρ hold] at hsim
              exact sim_delAt hsim hc hsave

/-- **A binding**, kept in the stack: the walk records what it can of it. -/
theorem step_bind {σ : List (Name × Known)} {X : TTerm} {s s' : State}
    {n : Name} {rhs : BindRhs} (hI : Inv s0 R σ X s) (hn : n ≠ R)
    (h : UpdTerm.toUpd [UpdElem.bind n rhs] s = .ok s') :
    Inv s0 R (setBy n (knownOf R σ rhs) σ) X s' := by
  rw [toUpd_bind] at h
  cases hb : bindRhs rhs s with
  | error e => simp [hb, Except.map] at h
  | ok b =>
      simp [hb, Except.map] at h
      subst h
      refine hI.setEnv hn ?_
      have hself : lookupBy n (s.setEnv n b).env = some b := by simp [State.setEnv]
      cases rhs with
      | val t =>
          cases hv : valOf σ t with
          | some v =>
              simp only [knownOf, hv]
              simp only [bindRhs, valOf_sound hI hv, Except.map] at hb
              cases hb
              exact hself
          | none => simp only [knownOf, hv]; trivial
      | path src =>
          cases hr : pathOf R σ src with
          | some r =>
              simp only [knownOf, hr]
              simp only [bindRhs, pathOf_sound hI hr] at hb
              cases hρ : varPath s (rootField R) with
              | error e => simp [hρ, Except.map] at hb
              | ok ρ =>
                  simp [hρ, Except.map] at hb
                  subst hb
                  refine ⟨ρ, ?_, hself⟩
                  rw [← hρ]
                  exact varPath_congr rfl rfl
                    (by simp [State.setEnv, rootField, lookupBy_setBy_ne (Ne.symm hn)])
          | none => simp only [knownOf, hr]; trivial
      | pushSlot _ => trivial
      | mref _ => trivial
      | freshId _ => trivial

/-- A read the walk can lower is the interpreter's read of the root's
storage. -/
theorem readOf_sound {σ : List (Name × Known)} {X : TTerm} {s : State}
    {e : WrappedExpr} {r : List Seg} (hI : Inv s0 R σ X s) (h : readOf R σ e = some r) :
    readTerm s e = storageAt s R r >>= SVal.asValue := by
  have key : ∀ e', pathOf R σ e' = some r ->
      (placePath s e' >>= fun p => s.findStorage p.1 p.2 >>= SVal.asValue) =
        storageAt s R r >>= SVal.asValue := by
    intro e' he
    rw [pathOf_sound hI he]
    unfold storageAt
    cases varPath s (rootField R) <;> rfl
  cases e with
  | var k ty fld =>
      cases k <;> simp only [readOf] at h <;> first | cases h | exact key _ h
  | field k ty base f =>
      cases k <;> simp only [readOf] at h <;> first | cases h | exact key _ h
  | index k ty base ix =>
      cases k <;> simp only [readOf] at h <;> first | cases h | exact key _ h
  | _ => simp [readOf] at h

/-- The claim a lowered read rests on: what the theory answers is what the
interpreter reads. -/
theorem claim_sound {X : TTerm} {s : State} {r : List Seg}
    (hsim : Sim X.toStruct R (storageAt s0 R) (storageAt s R))
    (hc : claimOk (findSt X.toStruct (Seg.field R :: r)) = true) :
    storageAt s R r >>= SVal.asValue = rigidVal s0 (X.read (Seg.field R :: r)) := by
  unfold TTerm.read
  obtain ⟨hp, hv⟩ := hsim r
  cases hX : findSt X.toStruct (Seg.field R :: r) with
  | prim l =>
      rw [hp l hX]
      cases l <;> rfl
  | st S =>
      cases S with
      | cur p' =>
          obtain ⟨rfl, heq⟩ := hv p' hX
          rw [heq]
          rfl
      | _ => rw [hX] at hc; simp [claimOk] at hc

/-- A binding the walk forgets. -/
theorem step_bind_unknown {σ : List (Name × Known)} {X : TTerm} {s s' : State}
    {n : Name} {rhs : BindRhs} (hI : Inv s0 R σ X s) (hn : n ≠ R)
    (h : UpdTerm.toUpd [UpdElem.bind n rhs] s = .ok s') :
    Inv s0 R (setBy n Known.unknown σ) X s' := by
  rw [toUpd_bind] at h
  cases hb : bindRhs rhs s with
  | error e => simp [hb, Except.map] at h
  | ok b =>
      simp [hb, Except.map] at h
      subst h
      exact hI.setEnv hn trivial

/-- What one step of the walk promises. -/
def LStep.Sound (s0 : State) (R : Name) (X : TTerm) (u : UpdTerm) (s : State) : LStep -> Prop
  | .stop => True
  | .keep σ' X' => ∀ s', UpdTerm.toUpd u s = .ok s' -> Inv s0 R σ' X' s'
  | .rigid n _ p σ' => UpdTerm.toUpd u s = rigidBind s0 n (X.read p) s ∧
      ∀ s', UpdTerm.toUpd u s = .ok s' -> Inv s0 R σ' X s'

theorem lstep_sound {σ : List (Name × Known)} {X : TTerm} {s : State} (u : UpdTerm)
    (hI : Inv s0 R σ X s) : (lstep R σ X u).Sound s0 R X u s := by
  unfold lstep
  split
  · split
    · rename_i r v ht hv
      exact fun s' h => step_save hI ht hv h
    · trivial
  · split
    · rename_i r hp
      exact fun s' h => step_delAt hI hp h
    · trivial
  · rename_i n rhs
    split
    · trivial
    · rename_i hn
      split
      · rename_i e
        split
        · rename_i r hr
          split
          · rename_i hc
            refine ⟨?_, fun s' h => step_bind_unknown hI hn h⟩
            funext
            rw [toUpd_bind]
            unfold rigidBind
            simp only [bindRhs, Sym.eval]
            rw [readOf_sound hI hr, claim_sound hI.sim hc]
            cases rigidVal s0 (X.read (Seg.field R :: r)) <;> rfl
          · exact fun s' h => step_bind hI hn h
        · exact fun s' h => step_bind hI hn h
      · exact fun s' h => step_bind hI hn h
  · trivial

theorem weave_bump (s0 : State) (u : UpdTerm) (us : List UpdTerm)
    (rs : List (Nat × Name × Ty × TTerm × List Seg)) :
    weaveUpd s0 (u :: us) (toRigid (bumpRigid rs)) =
      Upd.seq (UpdTerm.toUpd u) (weaveUpd s0 us (toRigid rs)) := by
  cases rs with
  | nil => rfl
  | cons e rest =>
      obtain ⟨k, n, ty, t, p⟩ := e
      simp only [bumpRigid, toRigid, List.map_cons, weaveUpd, List.take_succ_cons,
        List.drop_succ_cons, stackUpd_cons, Upd.seq_assoc]

theorem weave_zero (s0 : State) (us : List UpdTerm) (n : Name) (ty : Ty) (v : Theory.StValue)
    (rs : List (Nat × Name × Ty × Theory.StValue)) :
    weaveUpd s0 us ((0, n, ty, v) :: rs) = Upd.seq (rigidBind s0 n v) (weaveUpd s0 us rs) := by
  simp [weaveUpd]

theorem Inv.start (s0 : State) (R : Name) : Inv s0 R [] .cur s0 :=
  ⟨rfl, fun _ _ h => (by cases h), sim_start R _⟩

/-- **The walk denotes the stack it walked.** -/
theorem lowerGo_sound (s0 : State) (R : Name) :
    ∀ (us : List UpdTerm) (σ : List (Name × Known)) (X : TTerm) (s : State),
      Inv s0 R σ X s ->
      stackUpd us s = weaveUpd s0 (lowerGo R σ X us).1 (toRigid (lowerGo R σ X us).2) s
  | [], _, _, _, _ => rfl
  | u :: us, σ, X, s, hI => by
      have hs := lstep_sound u hI
      simp only [lowerGo]
      revert hs
      cases lstep R σ X u with
      | stop => intro _; rfl
      | keep σ' X' =>
          intro hs
          rw [weave_bump]
          show (UpdTerm.toUpd u s >>= stackUpd us) = (UpdTerm.toUpd u s >>= _)
          cases h : UpdTerm.toUpd u s with
          | error e => rfl
          | ok s' => exact lowerGo_sound s0 R us σ' X' s' (hs s' h)
      | rigid n ty p σ' =>
          intro hs
          simp only [toRigid, List.map_cons] at hs ⊢
          rw [weave_zero]
          show (UpdTerm.toUpd u s >>= stackUpd us) = (rigidBind s0 n (X.read p) s >>= _)
          rw [← hs.1]
          cases h : UpdTerm.toUpd u s with
          | error e => rfl
          | ok s' => exact lowerGo_sound s0 R us σ' X s' (hs.2 s' h)

theorem Sequent.upd_eq_weave (q : Sequent) :
    q.upd = fun s0 => weaveUpd s0 q.upds q.rigid s0 := by
  unfold Sequent.upd
  split
  · rename_i h; rw [h]; rfl
  · rename_i h; rw [h]

/-- **Lowering is a merge line**: the lowered line denotes the same update. -/
theorem lowerLine_upd (q : Sequent) : (lowerLine q).upd = q.upd := by
  unfold lowerLine
  split
  · rename_i R hr _
    rw [Sequent.upd_eq_weave, Sequent.upd_eq_weave, hr]
    funext s0
    exact (lowerGo_sound s0 R q.upds [] .cur s0 (Inv.start s0 R)).symm
  · rfl

theorem lowerLine_ante (q : Sequent) : (lowerLine q).ante = q.ante := by
  unfold lowerLine; split <;> rfl

theorem lowerLine_goal (q : Sequent) : (lowerLine q).goal = q.goal := by
  unfold lowerLine; split <;> rfl

theorem lowerFrontier_equiv : ∀ f : Frontier, Frontier.Equiv f (lowerFrontier f)
  | [] => trivial
  | q :: rest =>
      ⟨⟨(lowerLine_ante q).symm, (lowerLine_goal q).symm, (lowerLine_upd q).symm⟩,
        lowerFrontier_equiv rest⟩

/-! ## Raising a literal back

Once `theory_rw` has taken a rigid read to a literal, the literal is an
ordinary binding again, `{v := 0}`, and the line can be written in the `seq!`
notation. -/

/-- The literal a read of type `ty` writes. -/
def litOf (ty : Ty) : PrimVal -> WrappedExpr
  | .int v => WrappedExpr.intLit ty v
  | .bool b => WrappedExpr.bool b

/-- The stack with every rigid read, if each is a literal, written back where
it sits. -/
def raiseUpds : List UpdTerm -> List (Nat × Name × Ty × Theory.StValue) -> Option (List UpdTerm)
  | us, [] => some us
  | us, (k, n, ty, prim p) :: rs =>
      (raiseUpds (us.drop k) rs).map fun tail =>
        us.take k ++ [UpdElem.bind n (BindRhs.val (Sym.read (litOf ty p)))] :: tail
  | _, _ => none

def raiseLine (q : Sequent) : Sequent :=
  match raiseUpds q.upds q.rigid with
  | some us => { q with upds := us, rigid := [] }
  | none => q

def raiseFrontier (f : Frontier) : Frontier := f.map raiseLine

theorem toUpd_lit (s0 : State) (n : Name) (ty : Ty) (p : PrimVal) :
    UpdTerm.toUpd [UpdElem.bind n (BindRhs.val (Sym.read (litOf ty p)))] =
      rigidBind s0 n (prim p) := by
  funext s
  rw [toUpd_bind]
  cases p <;> rfl

theorem raiseUpds_sound (s0 : State) :
    ∀ (rs : List (Nat × Name × Ty × Theory.StValue)) (us us' : List UpdTerm),
      raiseUpds us rs = some us' -> stackUpd us' = weaveUpd s0 us rs
  | [], us, us', h => by cases h; rfl
  | (k, n, ty, prim p) :: rs, us, us', h => by
      simp only [raiseUpds] at h
      cases ht : raiseUpds (us.drop k) rs with
      | none => rw [ht] at h; cases h
      | some tail =>
          rw [ht] at h
          cases h
          simp only [weaveUpd, stackUpd_append, stackUpd_cons, toUpd_lit s0,
            raiseUpds_sound s0 rs _ _ ht]
  | (_, _, _, st _) :: _, _, _, h => by simp [raiseUpds] at h

theorem raiseLine_upd (q : Sequent) : (raiseLine q).upd = q.upd := by
  unfold raiseLine
  split
  · rename_i us h
    rw [Sequent.upd_eq_weave, Sequent.upd_eq_weave]
    funext s0
    show stackUpd us s0 = _
    rw [raiseUpds_sound s0 _ _ _ h]
  · rfl

theorem raiseFrontier_equiv : ∀ f : Frontier, Frontier.Equiv f (raiseFrontier f)
  | [] => trivial
  | q :: rest =>
      ⟨⟨by unfold raiseLine; split <;> rfl, by unfold raiseLine; split <;> rfl,
          (raiseLine_upd q).symm⟩,
        raiseFrontier_equiv rest⟩

end Soundness

end Update
end Solidity
