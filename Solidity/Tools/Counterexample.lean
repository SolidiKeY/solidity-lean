import Solidity.Calculus.SolSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.SoundLoops
import Solidity.Semantics.RunFuel
import Solidity.Tools.Common

/-!
# Counterexamples: scoped formulas evaluated in a typed state

`holds σ φ` (`Calculus/Logic.lean`) is a `Prop`: a quantifier ranges
over `2^256` values, an update over the typed states it lands on, `{havoc}` over every storage, so it cannot be computed.
`Fml.eval3` is its three-valued shadow over the typed state
(`State`): terms are read by the typed readers and updates computed
(`Upd.applyV`), the programs under a
modality are run by the typed run with fuel (`Prog.runF`,
`Semantics/RunFuel.lean`: a loop entered at most `loopFuel`
iterations, `unknown` past them), a quantifier and a hidden binder are
tried on a finite domain (`ff` as soon as one instance is), an update is
read in the one typed state its end lifts to (`State.lift?`: the heap
empty, the storage and the transaction its own), and the connectives are
Kleene's.  An answer is never wrong, only sometimes missing:
`Fml.eval3_tt` and `Fml.eval3_ff` say that `tt` implies `holds σ φ` and
`ff` implies `¬ holds σ φ`.

A counterexample to a specification (`refuteSpec`) is a state in
which the stated premises (`I ∧ requires`) evaluate to `tt` and a
conjunct after the call to `ff`.  The premises that are true by
construction (`R`, `L`, `msg.value`, `Calculus/SurfaceSpec.lean`) are not
evaluated but made true by the generator: arguments are drawn in their
type's range, storages are canonical (`Typing/Reachability.lean`: every
struct member present in order, a mapping's keys unique and its default the
type's), their words in range, and `msg.value` is `0` for a function that
is not `payable`.  The candidate is untyped data (`Cand`), read as a typed
state by `State.ofSem?` (the storage decoded at the contract's types).

The search is testing: small pools of values per primitive type (the
bounds, `0`, `1`, `2`, and the spec's own literals), all-default storages
over every combination of arguments first, then random states
(`GenSpec.sval` of `Tools/Common.lean` over the pools, seeded, so the result
is the same on every run).  A witness found is shrunk before it is shown
(Shrinking, below).

A witness is **certified** when the kernel checks `¬ ⊨ φ` of the scoped
formula from it: `Fml.not_valid_of_eval3Peel` applied to
`Fml.eval3Peel dom vals σ₀ φ = .ff`, `φ` with its leading parameters bound
to the witness's arguments `vals` (`Fml.peel`), which the kernel decides by
evaluating `peel`, `eval3`, the typed run and the decoding of the
candidate's storage on closed terms (`certifyRefl`).  That needs every
premise to evaluate to `tt` in `σ₀`, and so fails when one is quantified
over a `uint`, as the layout premise of a mapping is; the witness is then
only **tested**.  What the kernel runs is written by the recursor
(`Fml.eval3`, `Fml.peel`, `Prog.runF`; Gate G0 conditions 1 and 2), each
with a compiled `match` twin the search runs (`Fml.eval3C`, `Fml.peelC`,
`Prog.runFC`) and a theorem that they agree.
-/

namespace Solidity.Tools

/-! ## Three truth values -/

/-- Kleene's truth values: `unknown` where a finite evaluation cannot
decide. -/
inductive Tri where
  | tt
  | ff
  | unknown
  deriving DecidableEq, Repr, Inhabited

namespace Tri

/-- Negation. -/
def not : Tri → Tri
  | tt => ff
  | ff => tt
  | unknown => unknown

/-- Conjunction: `ff` wins over `unknown`. -/
def and : Tri → Tri → Tri
  | ff, _ => ff
  | _, ff => ff
  | tt, tt => tt
  | _, _ => unknown

/-- Implication: `ff → _` and `_ → tt` are `tt` whatever the other side. -/
def imp : Tri → Tri → Tri
  | ff, _ => tt
  | _, tt => tt
  | tt, ff => ff
  | _, _ => unknown

end Tri

end Solidity.Tools

namespace Solidity

open Solidity.Tools (Tri)
open Semantics (Value)

variable {C : Contract}

/-! ## The typed state of a candidate

An untyped storage read at the contract's types: kernel-reducible, by
recursion on a depth `k` (a struct's members, an array's elements and a
mapping's values one level down), each list by its own recursion. -/

/-- Exactly `n` values, each decoded by `f`. -/
def SVec.decode {E : Ty} (f : Semantics.SVal → Option (SVal E)) :
    (n : Nat) → List Semantics.SVal → Option (SVec E n)
  | 0, [] => some .nil
  | n + 1, v :: vs => do pure (.cons (← f v) (← SVec.decode f n vs))
  | _, _ => none

/-- A list of values, each decoded by `f`. -/
def SList.decode {E : Ty} (f : Semantics.SVal → Option (SVal E)) :
    List Semantics.SVal → Option (SList E)
  | [] => some .nil
  | v :: vs => do pure (.cons (← f v) (← SList.decode f vs))

/-- A mapping's entries, each value decoded by `f`. -/
def SMap.decode {V : Ty} (f : Semantics.SVal → Option (SVal V)) :
    List (Int × Semantics.SVal) → Option (SMap V)
  | [] => some .nil
  | (k, v) :: es => do pure (.cons k (← f v) (← SMap.decode f es))

/-- A struct's members, by name and in order, each decoded at its type by `f`. -/
def SFields.decode (f : (T : Ty) → Semantics.SVal → Option (SVal T)) :
    (fs : List (Name × Ty)) → List (Name × Semantics.SVal) → Option (SFields fs)
  | [], [] => some .nil
  | (n, T) :: fs, (n', v) :: vs =>
    if n = n' then do pure (.cons (← f T v) (← SFields.decode f fs vs)) else none
  | _, _ => none

/-- An untyped storage value read at the type `T`, at most `k` levels deep:
`none` where it has another shape (a value out of its type's range among
them). -/
def SVal.decodeN : Nat → (T : Ty) → Semantics.SVal → Option (SVal T)
  | 0, _, _ => none
  | _ + 1, .prim p, .prim v => (PrimTy.ofValue? p v).map .prim
  | k + 1, .ref (.struct s), .struct fs =>
    (SFields.decode (SVal.decodeN k) (Semantics.structDef s) fs).map .struct
  | k + 1, .ref (.array E), .array es sh false =>
    if h : es.length < 2 ^ 256 then do
      pure (.array (← SVec.decode (SVal.decodeN k E) es.length es)
        (← SList.decode (SVal.decodeN k E) sh) h)
    else none
  | k + 1, .ref (.fixed E n), .array es [] true =>
    (SVec.decode (SVal.decodeN k E) n es).map .fixed
  | k + 1, .ref (.mapping _ V), .map es d => do
    pure (.map (← SMap.decode (SVal.decodeN k V) es) (← SVal.decodeN k V d))
  | _ + 1, _, _ => none

/-- An untyped storage read at the contract's types. -/
def Storage.decode (C : Contract) (st : List (Name × Semantics.SVal)) : Option (Storage C) :=
  SFields.decode (SVal.decodeN 32) C.vars st

/-- **The typed state of an untyped one**, with no locals: the storage
decoded, the words of the transaction and the funds read as `uint`s. -/
def State.ofSem? (C : Contract) (s : Semantics.State) : Option (State C []) := do
  let u (n : Int) : Option PrimTy.uint.Denote := PrimTy.ofValue? .uint (.int n)
  let st ← Storage.decode C s.storage
  let bal ← u s.selfBalance
  let sender ← u s.tx.msgSender
  let self ← u s.tx.selfAddress
  let value ← u s.tx.msgValue
  let time ← u s.tx.timestamp
  pure { storage := st, H := [], heap := Heap.empty, env := (), net := s.net,
         selfBalance := bal,
         tx := { msgSender := sender, selfAddress := self, msgValue := value, timestamp := time,
                 ext := s.tx.ext } }

/-- `State.ofSem?`, the initial state where it fails. -/
def State.ofSemD (C : Contract) (s : Semantics.State) : State C [] :=
  (State.ofSem? C s).getD (State.init C)

/-! ## Comparing untyped storages in the kernel

`Semantics.SVal`'s `DecidableEq` (a nested inductive's, written by hand) does
not reduce in the kernel; `SVal.beqK` is a structural Boolean equality that
does, and implies equality (`SVal.eq_of_beqK`). -/

mutual
/-- Boolean equality of untyped storage values, structural. -/
def _root_.Solidity.Semantics.SVal.beqK : Semantics.SVal → Semantics.SVal → Bool
  | .prim a, .prim b => decide (a = b)
  | .struct fs, .struct gs => Semantics.SVal.fieldsBeqK fs gs
  | .array es sh f, .array es' sh' f' =>
    Semantics.SVal.listBeqK es es' && Semantics.SVal.listBeqK sh sh' && f == f'
  | .map es d, .map es' d' => Semantics.SVal.entriesBeqK es es' && Semantics.SVal.beqK d d'
  | _, _ => false
  termination_by structural a => a

/-- Members, by name and value. -/
def _root_.Solidity.Semantics.SVal.fieldsBeqK :
    List (Name × Semantics.SVal) → List (Name × Semantics.SVal) → Bool
  | [], [] => true
  | (n, v) :: fs, (n', v') :: gs =>
    decide (n = n') && Semantics.SVal.beqK v v' && Semantics.SVal.fieldsBeqK fs gs
  | _, _ => false
  termination_by structural a => a

/-- Elements. -/
def _root_.Solidity.Semantics.SVal.listBeqK : List Semantics.SVal → List Semantics.SVal → Bool
  | [], [] => true
  | v :: vs, v' :: vs' => Semantics.SVal.beqK v v' && Semantics.SVal.listBeqK vs vs'
  | _, _ => false
  termination_by structural a => a

/-- Entries, by key and value. -/
def _root_.Solidity.Semantics.SVal.entriesBeqK :
    List (Int × Semantics.SVal) → List (Int × Semantics.SVal) → Bool
  | [], [] => true
  | (k, v) :: es, (k', v') :: es' =>
    decide (k = k') && Semantics.SVal.beqK v v' && Semantics.SVal.entriesBeqK es es'
  | _, _ => false
  termination_by structural a => a
end

mutual
theorem _root_.Solidity.Semantics.SVal.eq_of_beqK : (a b : Semantics.SVal) →
    Semantics.SVal.beqK a b = true → a = b
  | .prim a, .prim b, h => by
    simp only [Semantics.SVal.beqK, decide_eq_true_eq] at h
    rw [h]
  | .struct fs, .struct gs, h => by
    simp only [Semantics.SVal.beqK] at h
    rw [Semantics.SVal.eq_of_fieldsBeqK fs gs h]
  | .array es sh f, .array es' sh' f', h => by
    simp only [Semantics.SVal.beqK, Bool.and_eq_true, beq_iff_eq] at h
    rw [Semantics.SVal.eq_of_listBeqK es es' h.1.1, Semantics.SVal.eq_of_listBeqK sh sh' h.1.2,
      h.2]
  | .map es d, .map es' d', h => by
    simp only [Semantics.SVal.beqK, Bool.and_eq_true] at h
    rw [Semantics.SVal.eq_of_entriesBeqK es es' h.1, Semantics.SVal.eq_of_beqK d d' h.2]
  | .prim _, .struct _, h | .prim _, .array .., h | .prim _, .map .., h
  | .struct _, .prim _, h | .struct _, .array .., h | .struct _, .map .., h
  | .array .., .prim _, h | .array .., .struct _, h | .array .., .map .., h
  | .map .., .prim _, h | .map .., .struct _, h | .map .., .array .., h => by
    simp only [Semantics.SVal.beqK, Bool.false_eq_true] at h

theorem _root_.Solidity.Semantics.SVal.eq_of_fieldsBeqK :
    (a b : List (Name × Semantics.SVal)) → Semantics.SVal.fieldsBeqK a b = true → a = b
  | [], [], _ => rfl
  | (n, v) :: fs, (n', v') :: gs, h => by
    simp only [Semantics.SVal.fieldsBeqK, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1.1, Semantics.SVal.eq_of_beqK v v' h.1.2, Semantics.SVal.eq_of_fieldsBeqK fs gs h.2]
  | [], _ :: _, h | _ :: _, [], h => by
    simp only [Semantics.SVal.fieldsBeqK, Bool.false_eq_true] at h

theorem _root_.Solidity.Semantics.SVal.eq_of_listBeqK :
    (a b : List Semantics.SVal) → Semantics.SVal.listBeqK a b = true → a = b
  | [], [], _ => rfl
  | v :: vs, v' :: vs', h => by
    simp only [Semantics.SVal.listBeqK, Bool.and_eq_true] at h
    rw [Semantics.SVal.eq_of_beqK v v' h.1, Semantics.SVal.eq_of_listBeqK vs vs' h.2]
  | [], _ :: _, h | _ :: _, [], h => by
    simp only [Semantics.SVal.listBeqK, Bool.false_eq_true] at h

theorem _root_.Solidity.Semantics.SVal.eq_of_entriesBeqK :
    (a b : List (Int × Semantics.SVal)) → Semantics.SVal.entriesBeqK a b = true → a = b
  | [], [], _ => rfl
  | (k, v) :: es, (k', v') :: es', h => by
    simp only [Semantics.SVal.entriesBeqK, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1.1, Semantics.SVal.eq_of_beqK v v' h.1.2, Semantics.SVal.eq_of_entriesBeqK es es' h.2]
  | [], _ :: _, h | _ :: _, [], h => by
    simp only [Semantics.SVal.entriesBeqK, Bool.false_eq_true] at h
end

/-! ## The typed state an update ends in

An update leaves a global part and the locals' values (`Upd.applyV`), and
what follows it is read in every typed state with them (`holds`,
`Upd.afterT_applyV`).  One of them is enough to refute it: `State.lift?`
reads them back as a typed state where the heap is empty and the storage
and the transaction are the starting state's (a snapshot `old := storage`
is that storage), every local a value of its type, an unset alias or
memory local, a ledger. -/

/-- The locals' values, typed over the heap typing `H`: `none` where a
memory local's identity is no object of its type there. -/
def TEnv.liftV? (H : HTy) : (Δ : Ctx) → LocsV C Δ → Option (TEnv C H Δ)
  | [], _ => some ()
  | .val _ :: Δ, ℓ => do pure (ℓ _ .here, ← TEnv.liftV? H Δ fun _ i => ℓ _ (.there i))
  | .alias _ :: Δ, ℓ => do pure (ℓ _ .here, ← TEnv.liftV? H Δ fun _ i => ℓ _ (.there i))
  | .mem R :: Δ, ℓ => match (ℓ _ .here : Option Nat) with
    | none => do pure (none, ← TEnv.liftV? H Δ fun _ i => ℓ _ (.there i))
    | some id => do
      pure (some (← HRef.ofId? H R id), ← TEnv.liftV? H Δ fun _ i => ℓ _ (.there i))
  | .old :: Δ, ℓ => do pure (ℓ _ .here, ← TEnv.liftV? H Δ fun _ i => ℓ _ (.there i))
  | .oldNet :: Δ, ℓ => do pure (ℓ _ .here, ← TEnv.liftV? H Δ fun _ i => ℓ _ (.there i))
  | .kint :: Δ, ℓ => do pure (ℓ _ .here, ← TEnv.liftV? H Δ fun _ i => ℓ _ (.there i))

theorem TEnv.liftV?_get (H : HTy) : (Δ : Ctx) → (ℓ : LocsV C Δ) → (e' : TEnv C H Δ) →
    TEnv.liftV? H Δ ℓ = some e' → ∀ {t : LTy} (i : Idx Δ t),
      LTy.VDen.ofT t (TEnv.get i e') = ℓ t i
  | [], _, (), _, _, i => nomatch i
  | .val _ :: Δ, ℓ, e', h, t, i | .alias _ :: Δ, ℓ, e', h, t, i | .old :: Δ, ℓ, e', h, t, i
  | .oldNet :: Δ, ℓ, e', h, t, i | .kint :: Δ, ℓ, e', h, t, i => by
    simp only [TEnv.liftV?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨e'', he, rfl⟩ := h
    cases i with
    | here => rfl
    | there j => exact TEnv.liftV?_get H Δ _ e'' he j
  | .mem R :: Δ, ℓ, e', h, t, i => by
    simp only [TEnv.liftV?] at h
    split at h
    · rename_i hn
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨e'', he, rfl⟩ := h
      cases i with
      | here => rw [hn]; rfl
      | there j => exact TEnv.liftV?_get H Δ _ e'' he j
    · rename_i id hn
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨r, hr, e'', he, rfl⟩ := h
      cases i with
      | here =>
        rw [hn]
        show Option.map (·.id) (some r) = some id
        unfold HRef.ofId? at hr
        split at hr
        · cases hr; rfl
        · cases hr
      | there j => exact TEnv.liftV?_get H Δ _ e'' he j

/-- **A typed state with the global part and the locals `q`**: `none`
where a memory local's identity is no object of its type in the global
part's heap. -/
def State.lift? {Γ Δ : Ctx} (σ : State C Γ) (q : GlobT C σ.H × LocsV C Δ) :
    Option (State C Δ) := do
  let g := q.1.1
  let env ← TEnv.liftV? g.H Δ q.2
  pure { storage := g.storage, H := g.H, heap := g.heap, env, net := g.net,
         selfBalance := g.selfBalance, tx := g.tx }

theorem State.lift?_spec {Γ Δ : Ctx} {σ : State C Γ} {q : GlobT C σ.H × LocsV C Δ}
    {σ' : State C Δ} (h : σ.lift? q = some σ') :
    σ'.glob = q.1.1 ∧ (∀ {t : LTy} (i : Idx Δ t), σ'.getV i = q.2 t i) := by
  unfold State.lift? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨env, hlift, rfl⟩ := h
  exact ⟨rfl, fun i => TEnv.liftV?_get _ Δ q.2 env hlift i⟩

/-! ## Evaluation -/

/-- The values a quantifier over each primitive type is tried on. -/
abbrev TDom := (p : PrimTy) → List p.Denote

/-- The iterations a loop is run for, at most, each time it is entered. -/
def loopFuel : Nat := 1000

/-- The values a hidden binder of type `t` is tried on in `σ`: the domain
for a value, unset for an alias or a memory local, `σ`'s storage and ledger
for a snapshot. -/
def TDom.bind {Γ : Ctx} (dom : TDom) (σ : State C Γ) : (t : LTy) → List (t.TDenote C σ.H)
  | .val p => dom p
  | .alias _ => [none]
  | .mem _ => [none]
  | .old => [σ.storage]
  | .oldNet => [σ.net]
  | .kint => (dom .int).map (·.1)

/-- What a modality says of a typed run: of the state it ends in, a halt as
`Modality.onTHalt` says, `ff` on a panic, `unknown` on `diverge` (a loop
past `loopFuel` iterations is one). -/
def Tri.afterT {α : Type} (m : Modality) (k : α → Tri) : TRes α → Tri
  | .ok a => k a
  | .error .panic => .ff
  | .error .diverge => .unknown
  | .error .exhausted => .tt
  | .error .revert => match m with
    | .box => .tt
    | .diamond => .ff

/-- The program, then its frames, run with fuel (`Prog.runFrames`). -/
def Prog.runFramesF {Γ Γ₁ Γ₀ : Ctx} (n : Nat) (σ : State C Γ) (P : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) : TRes (State C Γ₀) := do
  let o ← Prog.runF n P σ
  let o' ← Frames.runF n o.st κ
  pure o'.st

theorem Prog.runFramesF_approx {Γ Γ₁ Γ₀ : Ctx} (n : Nat) (σ : State C Γ) (P : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) : TRes.Approx (Prog.runFramesF n σ P κ) (Prog.runFrames σ P κ) :=
  (Prog.runF_approx n P σ).bind fun o => (Frames.runF_approx n o.st κ).bind fun _ => .refl _

/-- **`holds`, evaluated**, compiled: `dom p` is the finite domain a
quantifier over `p` is tried on.  The twin of `Fml.eval3` (`Fml.eval3_eq`). -/
def Fml.eval3C (dom : TDom) : {Γ : Ctx} → State C Γ → Fml C Γ → Tri
  | _, _, .tt => .tt
  | _, σ, .eq a b =>
    (a.eval σ).elim .unknown fun x => (b.eval σ).elim .unknown fun y => if x = y then .tt else .ff
  | _, σ, .defined t => (t.eval σ).elim .ff fun _ => .tt
  | _, σ, .not φ => (φ.eval3C dom σ).not
  | _, σ, .and φ ψ => (φ.eval3C dom σ).and (ψ.eval3C dom σ)
  | _, σ, .imp φ ψ => (φ.eval3C dom σ).imp (ψ.eval3C dom σ)
  | _, σ, .upd m U φ =>
    (U.applyV σ).elim (if m = .box || U.exh σ then .tt else .ff) fun τ =>
      (σ.lift? τ).elim .unknown fun σ' => if φ.eval3C dom σ' = .ff then .ff else .unknown
  | _, σ, .modal m P κ φ => Tri.afterT m (fun τ => φ.eval3C dom τ) (Prog.runFramesF loopFuel σ P κ)
  | _, σ, .havoc φ =>
    if φ.eval3C dom σ = .ff || φ.eval3C dom (σ.havoc σ.storage []) = .ff then .ff else .unknown
  | _, σ, .all _ p φ =>
    if (dom p).any fun v => φ.eval3C dom (σ.push (t := .val p) v) = .ff then .ff else .unknown
  | _, σ, .bind _ _ t φ =>
    if (dom.bind σ t).any fun v => φ.eval3C dom (σ.push v) = .ff then .ff else .unknown
  | _, σ, .anon xs φ =>
    if φ.eval3C dom (σ.anon xs fun x => TEnv.get x.2 σ.env) = .ff then .ff else .unknown

theorem Fml.eval3C_sound (dom : TDom) : {Γ : Ctx} → (φ : Fml C Γ) → ∀ σ : State C Γ,
    (φ.eval3C dom σ = .tt → holds σ φ) ∧ (φ.eval3C dom σ = .ff → ¬ holds σ φ)
  | _, .tt, _ => ⟨fun _ => trivial, nofun⟩
  | _, .eq a b, σ => by
    simp only [Fml.eval3C, holds]
    cases ha : a.eval σ with
    | none => simp only [Option.elim, reduceCtorEq, false_implies, and_self]
    | some x =>
    cases hb : b.eval σ with
    | none => simp only [Option.elim, reduceCtorEq, false_implies, and_self]
    | some y =>
      simp only [Option.elim]
      have hda : a.denote σ = .prim (PrimTy.erase x) := Tm.denote_eval σ a x ha
      have hdb : b.denote σ = .prim (PrimTy.erase y) := Tm.denote_eval σ b y hb
      rw [hda, hdb, Theory.StValue.Equiv.prim_iff]
      by_cases hxy : x = y
      · subst hxy
        simp only [if_true, reduceCtorEq, false_implies, and_true]
        exact fun _ => trivial
      · simp only [hxy, if_false, reduceCtorEq, false_implies, true_and]
        exact fun _ h => hxy (PrimTy.erase_injective (Theory.StValue.prim.inj h))
  | _, .defined t, σ => by
    simp only [Fml.eval3C, holds]
    cases h : t.eval σ <;> simp only [Option.elim, ne_eq, reduceCtorEq, not_false_eq_true,
      imp_self, not_true_eq_false, and_self, implies_true, false_implies, true_implies]
  | _, .not φ, σ => by
    have ih := Fml.eval3C_sound dom φ σ
    simp only [Fml.eval3C, holds]
    cases h : φ.eval3C dom σ <;> simp_all only [Tri.not, reduceCtorEq, false_implies, forall_const,
      true_and, and_true, and_self, implies_true, not_true_eq_false, not_false_eq_true,
      Classical.not_not]
  | _, .and φ ψ, σ => by
    have ih₁ := Fml.eval3C_sound dom φ σ
    have ih₂ := Fml.eval3C_sound dom ψ σ
    simp only [Fml.eval3C, holds]
    cases h₁ : φ.eval3C dom σ <;> cases h₂ : ψ.eval3C dom σ <;>
      simp_all only [Tri.and, reduceCtorEq, false_implies, forall_const, true_and, and_true,
        and_false, false_and, and_self, implies_true, not_true_eq_false, not_false_eq_true, not_and]
  | _, .imp φ ψ, σ => by
    have ih₁ := Fml.eval3C_sound dom φ σ
    have ih₂ := Fml.eval3C_sound dom ψ σ
    simp only [Fml.eval3C, holds]
    cases h₁ : φ.eval3C dom σ <;> cases h₂ : ψ.eval3C dom σ <;>
      simp_all only [Tri.imp, reduceCtorEq, false_implies, forall_const, true_and, and_true,
        and_self, implies_true, not_true_eq_false, not_false_eq_true, not_imp]
  | _, .upd m U φ, σ => by
    simp only [Fml.eval3C]
    show (_ → U.afterT m σ (holds · φ)) ∧ (_ → ¬ U.afterT m σ (holds · φ))
    rw [Upd.afterT_applyV]
    cases hU : U.applyV σ with
    | none =>
      cases m <;> cases U.exh σ <;> simp only [Option.elim, Modality.onHalt, reduceCtorEq, imp_self,
        not_true_eq_false, not_false_eq_true, and_self, true_implies, false_implies, if_true,
        if_false, Bool.or_true, Bool.or_false, Bool.true_or, Bool.false_or, decide_true,
        decide_false, true_or, or_true, false_or, or_false, Bool.false_eq_true, ↓reduceIte,
        not_false_eq_true, Tri.noConfusion, implies_true]
    | some τ =>
      simp only [Option.elim]
      cases hl : σ.lift? τ with
      | none => exact ⟨fun h => Tri.noConfusion h, fun h => Tri.noConfusion h⟩
      | some σ' =>
        simp only
        split
        · rename_i hff
          obtain ⟨hg, hl'⟩ := State.lift?_spec hl
          exact ⟨fun h => Tri.noConfusion h,
            fun _ hall => (Fml.eval3C_sound dom φ σ').2 hff (hall σ' hg hl')⟩
        · exact ⟨fun h => Tri.noConfusion h, fun h => Tri.noConfusion h⟩
  | _, .modal m P κ φ, σ => by
    simp only [Fml.eval3C, holds]
    have happ := Prog.runFramesF_approx loopFuel σ P κ
    cases hr : Prog.runFramesF loopFuel σ P κ with
    | ok τ =>
      rw [hr] at happ
      rw [← happ.eq nofun]
      have ih := Fml.eval3C_sound dom φ τ
      simp only [Tri.afterT, Modality.afterRunTR]
      exact ⟨fun h => ⟨ih.1 h, nofun⟩, fun h hh => ih.2 h hh.1⟩
    | error e =>
      rw [hr] at happ
      cases e with
      | diverge => exact ⟨nofun, nofun⟩
      | panic =>
        rw [← happ.eq nofun]
        simp only [Tri.afterT, Modality.afterRunTR, reduceCtorEq, ne_eq,
          not_true_eq_false, and_false, not_false_eq_true, imp_self, and_self]
      | exhausted =>
        rw [← happ.eq nofun]
        cases m <;> simp only [Tri.afterT, Modality.afterRunTR, Modality.onTHalt, ne_eq,
          Except.error.injEq, reduceCtorEq, not_false_eq_true, and_self, implies_true,
          false_implies]
      | revert =>
        rw [← happ.eq nofun]
        cases m <;> simp only [Tri.afterT, Modality.afterRunTR, Modality.onTHalt, ne_eq,
          Except.error.injEq, reduceCtorEq, not_false_eq_true, and_self, implies_true,
          and_true, not_true_eq_false, imp_self]
  | _, .havoc φ, σ => by
    simp only [Fml.eval3C, holds]
    split
    · rename_i h
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      refine ⟨nofun, fun _ hall => ?_⟩
      rcases h with h | h
      · exact (Fml.eval3C_sound dom φ σ).2 h
          (by simpa only [State.havoc_self] using hall σ.storage σ.net)
      · exact (Fml.eval3C_sound dom φ _).2 h (hall _ _)
    · exact ⟨nofun, nofun⟩
  | _, .all _ p φ, σ => by
    simp only [Fml.eval3C, holds]
    split
    · rename_i h
      obtain ⟨v, _, hff⟩ := List.any_eq_true.mp h
      exact ⟨nofun, fun _ hall => (Fml.eval3C_sound dom φ _).2 (of_decide_eq_true hff) (hall v)⟩
    · exact ⟨nofun, nofun⟩
  | _, .bind m _ t φ, σ => by
    simp only [Fml.eval3C, holds]
    split
    · rename_i h
      obtain ⟨v, _, hff⟩ := List.any_eq_true.mp h
      exact ⟨nofun, fun _ hall => (Fml.eval3C_sound dom φ _).2 (of_decide_eq_true hff) (hall v)⟩
    · exact ⟨nofun, nofun⟩
  | _, .anon xs φ, σ => by
    simp only [Fml.eval3C, holds]
    split
    · rename_i h
      exact ⟨nofun, fun _ hall => (Fml.eval3C_sound dom φ _).2 h (hall _)⟩
    · exact ⟨nofun, nofun⟩

/-- **`holds`, evaluated**, by its recursor (Gate G0 conditions 1 and 2):
what the kernel runs in a certificate.  Compiled as `Fml.eval3C`. -/
@[implemented_by Fml.eval3C]
def Fml.eval3 (dom : TDom) {Γ : Ctx} (σ : State C Γ) (φ : Fml C Γ) : Tri :=
  Fml.rec (motive := fun Γ _ => State C Γ → Tri)
    (fun _ => .tt)
    (fun a b σ => (a.eval σ).elim .unknown fun x =>
      (b.eval σ).elim .unknown fun y => if x = y then .tt else .ff)
    (fun t σ => (t.eval σ).elim .ff fun _ => .tt)
    (fun _ ih σ => (ih σ).not)
    (fun _ _ ih₁ ih₂ σ => (ih₁ σ).and (ih₂ σ))
    (fun _ _ ih₁ ih₂ σ => (ih₁ σ).imp (ih₂ σ))
    (fun m U _ ih σ => (U.applyV σ).elim (if m = .box || U.exh σ then .tt else .ff) fun τ =>
      (σ.lift? τ).elim .unknown fun σ' => if ih σ' = .ff then .ff else .unknown)
    (fun m P κ _ ih σ => Tri.afterT m (fun τ => ih τ) (Prog.runFramesF loopFuel σ P κ))
    (fun _ ih σ => if ih σ = .ff || ih (σ.havoc σ.storage []) = .ff then .ff else .unknown)
    (fun _ p _ ih σ =>
      if (dom p).any fun v => ih (σ.push (t := .val p) v) = .ff then .ff else .unknown)
    (fun _ _ t _ ih σ => if (dom.bind σ t).any fun v => ih (σ.push v) = .ff then .ff else .unknown)
    (fun xs _ ih σ =>
      if ih (σ.anon xs fun x => TEnv.get x.2 σ.env) = .ff then .ff else .unknown)
    φ σ

theorem Fml.eval3_eq (dom : TDom) : {Γ : Ctx} → (φ : Fml C Γ) → ∀ σ : State C Γ,
    φ.eval3 dom σ = φ.eval3C dom σ
  | _, .tt, _ | _, .eq .., _ | _, .defined _, _ => rfl
  | _, .not φ, _ => by simp only [Fml.eval3C, ← Fml.eval3_eq dom φ]; rfl
  | _, .and φ ψ, _ => by simp only [Fml.eval3C, ← Fml.eval3_eq dom φ, ← Fml.eval3_eq dom ψ]; rfl
  | _, .imp φ ψ, _ => by simp only [Fml.eval3C, ← Fml.eval3_eq dom φ, ← Fml.eval3_eq dom ψ]; rfl
  | _, .upd _ _ φ, _ => by simp only [Fml.eval3C, ← Fml.eval3_eq dom φ]; rfl
  | _, .modal _ _ _ φ, _ => by simp only [Fml.eval3C, ← Fml.eval3_eq dom φ]; rfl
  | _, .havoc φ, _ => by simp only [Fml.eval3C, ← Fml.eval3_eq dom φ]; rfl
  | _, .all _ _ φ, _ => by simp only [Fml.eval3C, ← Fml.eval3_eq dom φ]; rfl
  | _, .bind _ _ _ φ, _ => by simp only [Fml.eval3C, ← Fml.eval3_eq dom φ]; rfl
  | _, .anon _ φ, _ => by simp only [Fml.eval3C, ← Fml.eval3_eq dom φ]; rfl

theorem Fml.eval3_sound (dom : TDom) {Γ : Ctx} (φ : Fml C Γ) (σ : State C Γ) :
    (φ.eval3 dom σ = .tt → holds σ φ) ∧ (φ.eval3 dom σ = .ff → ¬ holds σ φ) := by
  rw [Fml.eval3_eq]
  exact Fml.eval3C_sound dom φ σ

/-- **A `tt` is a truth**: `φ` holds in `σ`. -/
theorem Fml.eval3_tt {dom : TDom} {Γ : Ctx} {σ : State C Γ} {φ : Fml C Γ}
    (h : φ.eval3 dom σ = .tt) : holds σ φ :=
  (Fml.eval3_sound dom φ σ).1 h

/-- **An `ff` is a counterexample**: `φ` does not hold in `σ`. -/
theorem Fml.eval3_ff {dom : TDom} {Γ : Ctx} {σ : State C Γ} {φ : Fml C Γ}
    (h : φ.eval3 dom σ = .ff) : ¬ holds σ φ :=
  (Fml.eval3_sound dom φ σ).2 h

end Solidity

namespace Solidity.Tools

open Semantics

variable {C : Contract}

/-! ## The values tried -/

/-- The integer literals a clause mentions. -/
def specNums : SpecExpr → List Int
  | .num n => [n]
  | .old e | .net e | .field e _ | .unop _ e | .all _ _ e | .ex _ _ e => specNums e
  | .index a b | .binop _ a b | .imp a b | .iff a b => specNums a ++ specNums b
  | .bool _ | .name _ | .result => []

/-- The integer literals a location's keys mention. -/
def locNums : SpecLoc → List Int
  | .root _ => []
  | .field l _ | .all l => locNums l
  | .index l e => locNums l ++ specNums e

/-- The `uint`s tried: `0`, `1`, `2`, each literal `n` of the specification
with `n ± 1`, and the two largest, in that order: a combination of small
arguments is tried first. -/
def uintPool (lits : List Int) : List Int :=
  (([0, 1, 2] ++ lits.flatMap (fun n => [n, n + 1, n - 1]) ++ [uintBound - 1, uintBound - 2]).filter
    fun n => decide (0 ≤ n ∧ n < uintBound)).eraseDups

/-- The `int`s tried: `0`, `±1`, the bounds, and each literal with its
negation and neighbours. -/
def intPool (lits : List Int) : List Int :=
  (([0, 1, -1] ++ lits.flatMap (fun n => [n, -n, n + 1, n - 1]) ++ [-intBound, intBound - 1]).filter
    fun n => decide (-intBound ≤ n ∧ n < intBound)).eraseDups

/-- The pool arguments and stored words are drawn from. -/
def poolVals (lits : List Int) : PrimTy → List Value
  | .bool => [.bool true, .bool false]
  | .uint => (uintPool lits).map .int
  | .int => (intPool lits).map .int

/-! ## Random states -/

/-- How a search draws a storage: every word from `vals`, a mapping's keys
from `keys`, up to `3` entries, arrays of fewer than `3` elements. -/
def pooledGen (vals : PrimTy → List Value) (keys : PrimTy → List Int) : GenSpec where
  prim p := pickD (PrimTy.default p) (vals p)
  key K := some (pickD 0 (keys K))
  entries := 4
  length := 3

/-- Every combination, the first list's element first. -/
def products {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: rest => xs.flatMap fun x => (products rest).map (x :: ·)

/-- A candidate: the storage, the arguments, the transaction, the ledger
and the funds a call starts from. -/
structure Cand where
  st : List (Name × Semantics.SVal)
  args : List (String × Value)
  tx : TxEnv := { msgSender := 1 }
  net : List (Int × Int) := []
  bal : Int := 0

/-- The state a candidate starts in: the arguments bound as locals. -/
def Cand.state [FreshNames] (c : Cand) : Semantics.State :=
  { storage := c.st, env := c.args.map fun (n, v) => (Var.ofName n, .val v), tx := c.tx,
    net := c.net, selfBalance := c.bal }

/-- A random candidate: arguments of the types `ps`, a sender, a storage of
`C`'s layout whose mapping keys include the arguments and the sender. -/
def genCandidate (C : Contract) (lits : List Int) (ps : List (String × PrimTy))
    (payable : Bool) : Gen Cand := do
  let dom := poolVals lits
  let args ← ps.mapM fun (n, p) => do pure (n, ← pickD (PrimTy.default p) (dom p))
  let sender ← pickD 1 ([1, 2] ++ uintPool lits)
  let argInts := args.filterMap fun (_, v) => match v with
    | .int n => some n
    | .bool _ => none
  let keys : PrimTy → List Int := fun
    | .bool => [0, 1]
    | .uint => (uintPool lits ++ (sender :: argInts).filter (0 ≤ ·)).eraseDups
    | .int => (intPool lits ++ sender :: argInts).eraseDups
  let st ← (pooledGen dom keys).storage C
  let value ← if payable then pickD 0 (uintPool lits) else pure 0
  let time ← pickD 0 (uintPool lits)
  let paid ← pickD 0 (uintPool lits)
  let net ← pickD [] [[], [(sender, paid)]]
  let bal ← pickD 0 [0, 1, uintBound - 1]
  pure { st, args, tx := { msgSender := sender, msgValue := value, timestamp := time }, net, bal }

/-! ## Shrinking

A witness found at random is shrunk before it is shown: the ledger emptied,
the funds and the timestamp zeroed, the sender `1`, a state variable reset to its default,
a mapping entry dropped, and a large number renamed to a small one unused
elsewhere, everywhere it occurs (arguments, sender, keys, words), so that
the equalities the witness relies on survive.  A step is kept when the
candidate is still a counterexample. -/

/-- The integers a storage value holds, keys included. -/
partial def SVal.ints : Semantics.SVal → List Int
  | .prim (.int n) => [n]
  | .prim (.bool _) => []
  | .struct fs => fs.flatMap fun (_, v) => SVal.ints v
  | .array es sh _ => (es ++ sh).flatMap SVal.ints
  | .map es d => es.flatMap (fun (k, v) => k :: SVal.ints v) ++ SVal.ints d

/-- `v` renamed `s`, keys and words alike. -/
partial def SVal.rename (v s : Int) : Semantics.SVal → Semantics.SVal
  | .prim (.int n) => .prim (.int (if n = v then s else n))
  | .prim (.bool b) => .prim (.bool b)
  | .struct fs => .struct (fs.map fun (f, x) => (f, SVal.rename v s x))
  | .array es sh fx => .array (es.map (SVal.rename v s)) (sh.map (SVal.rename v s)) fx
  | .map es d => .map (es.map fun (k, x) => (if k = v then s else k, SVal.rename v s x))
    (SVal.rename v s d)

/-- The integers a candidate mentions. -/
def Cand.ints (c : Cand) : List Int :=
  (c.args.filterMap (fun (_, v) => match v with | .int n => some n | .bool _ => none) ++
    c.tx.msgSender :: c.st.flatMap (fun (_, v) => SVal.ints v)).eraseDups

/-- `v` renamed `s` everywhere in a candidate. -/
def Cand.rename (c : Cand) (v s : Int) : Cand :=
  let r (n : Int) : Int := if n = v then s else n
  { c with
    st := c.st.map fun (x, sv) => (x, SVal.rename v s sv)
    args := c.args.map fun (x, a) => (x, match a with | .int n => .int (r n) | .bool b => .bool b)
    tx := { c.tx with msgSender := r c.tx.msgSender }
    net := c.net.map fun (a, b) => (r a, b) }

/-- The candidates one shrinking step away, simplest first. -/
def Cand.shrinks (C : Contract) (c : Cand) : List Cand :=
  let small : List Int := [0, 1, 2, 3]
  let ints := c.ints
  let renames := (ints.filter (fun v => !small.contains v)).flatMap fun v =>
    (small.filter (!ints.contains ·)).map (c.rename v)
  let resets := C.vars.filterMap fun (r, T) =>
    if lookupBy r c.st == some (defaultForTy T) then none
    else some { c with st := setBy r (defaultForTy T) c.st }
  let drops := c.st.flatMap fun (r, v) => match v with
    | .map es d => (List.range es.length).map fun i =>
      { c with st := setBy r (.map (es.eraseIdx i) d) c.st }
    | _ => []
  (if c.net.isEmpty then [] else [{ c with net := [] }]) ++
  (if c.bal = 0 then [] else [{ c with bal := 0 }]) ++
  (if c.tx.timestamp = 0 then [] else [{ c with tx := { c.tx with timestamp := 0 } }]) ++
  (if c.tx.msgValue = 0 then [] else [{ c with tx := { c.tx with msgValue := 0 } }]) ++
  (if c.tx.msgSender = 1 then [] else [{ c with tx := { c.tx with msgSender := 1 } }]) ++
  resets ++ drops ++ renames

/-- **Shrink** `c` while `ok` holds of it, one step at a time, at most
`fuel` steps. -/
def Cand.shrink (C : Contract) (ok : Cand → Bool) : Nat → Cand → Cand
  | 0, c => c
  | fuel + 1, c =>
    match (c.shrinks C).find? ok with
    | some c' => Cand.shrink C ok fuel c'
    | none => c


/-- **The domain a quantifier and a hidden binder are tried on**: the pools
of `lits` (`uintPool`, `intPool`) read at their types. -/
def poolDom (lits : List Int) : TDom
  | .bool => [true, false]
  | .uint => (uintPool lits).filterMap fun n => PrimTy.ofValue? .uint (.int n)
  | .int => (intPool lits).filterMap fun n => PrimTy.ofValue? .int (.int n)

end Solidity.Tools

/-! ## Reading a scoped formula against a candidate -/

namespace Solidity

open Solidity.Tools (Tri)
open Semantics (Value)

variable {C : Contract}

/-- The leading parameters of a scoped formula, outermost first: its `∀`s
and the hidden binders of value type in front of it (a specification's
parameters, `Calculus/Spec.lean`). -/
def Fml.params : {Γ : Ctx} → Fml C Γ → List (Var × PrimTy)
  | _, .all x p φ => (x, p) :: Fml.params φ
  | _, .bind _ x (.val p) φ => (x, p) :: Fml.params φ
  | _, _ => []

/-- A state and a formula under it, at some context. -/
abbrev Peeled (C : Contract) := (Δ : Ctx) × State C Δ × Fml C Δ

/-- The leading parameters bound to `vals`, by name, as far as each is
given: the state and the formula under them.  Compiled; the twin of
`Fml.peel` (`Fml.peel_eq`). -/
def Fml.peelC (vals : List (Var × Value)) : {Γ : Ctx} → State C Γ → Fml C Γ → Peeled C
  | _, σ, .all x p φ => match (vals.lookup x).bind (PrimTy.ofValue? p) with
    | some w => Fml.peelC vals (σ.push (t := .val p) w) φ
    | none => ⟨_, σ, .all x p φ⟩
  | _, σ, .bind m x (.val p) φ => match (vals.lookup x).bind (PrimTy.ofValue? p) with
    | some w => Fml.peelC vals (σ.push (t := .val p) w) φ
    | none => ⟨_, σ, .bind m x (.val p) φ⟩
  | _, σ, φ => ⟨_, σ, φ⟩

/-- The leading parameters bound to `vals`, by the recursor (Gate G0
conditions 1 and 2): what a certificate peels in the kernel.  Compiled as
`Fml.peelC`. -/
@[implemented_by Fml.peelC]
def Fml.peel (vals : List (Var × Value)) {Γ : Ctx} (σ : State C Γ) (φ : Fml C Γ) :
    Peeled C :=
  Fml.rec (motive := fun Γ _ => State C Γ → Peeled C)
    (fun σ => ⟨_, σ, .tt⟩) (fun a b σ => ⟨_, σ, .eq a b⟩) (fun t σ => ⟨_, σ, .defined t⟩)
    (fun φ _ σ => ⟨_, σ, .not φ⟩) (fun φ ψ _ _ σ => ⟨_, σ, .and φ ψ⟩)
    (fun φ ψ _ _ σ => ⟨_, σ, .imp φ ψ⟩) (fun m U φ _ σ => ⟨_, σ, .upd m U φ⟩)
    (fun m P κ φ _ σ => ⟨_, σ, .modal m P κ φ⟩) (fun φ _ σ => ⟨_, σ, .havoc φ⟩)
    (fun x p φ ih σ => match (vals.lookup x).bind (PrimTy.ofValue? p) with
      | some w => ih (σ.push (t := .val p) w)
      | none => ⟨_, σ, .all x p φ⟩)
    (fun {Γ} m x t φ ih σ =>
      LTy.casesOn (motive := fun t => Fml C (t :: Γ) → (State C (t :: Γ) → Peeled C) → Peeled C) t
        (fun p φ ih => match (vals.lookup x).bind (PrimTy.ofValue? p) with
          | some w => ih (σ.push (t := .val p) w)
          | none => ⟨_, σ, .bind m x (.val p) φ⟩)
        (fun r φ _ => ⟨_, σ, .bind m x (.alias r) φ⟩) (fun r φ _ => ⟨_, σ, .bind m x (.mem r) φ⟩)
        (fun φ _ => ⟨_, σ, .bind m x .old φ⟩) (fun φ _ => ⟨_, σ, .bind m x .oldNet φ⟩)
        (fun φ _ => ⟨_, σ, .bind m x .kint φ⟩) φ ih)
    (fun xs φ _ σ => ⟨_, σ, .anon xs φ⟩)
    φ σ

theorem Fml.peel_eq (vals : List (Var × Value)) : {Γ : Ctx} → (φ : Fml C Γ) →
    ∀ σ : State C Γ, Fml.peel vals σ φ = Fml.peelC vals σ φ
  | _, .all _ _ φ, _ => by simp only [Fml.peelC, ← Fml.peel_eq vals φ]; rfl
  | _, .bind _ _ (.val _) φ, _ => by simp only [Fml.peelC, ← Fml.peel_eq vals φ]; rfl
  | _, .bind _ _ (.alias _) _, _ | _, .bind _ _ (.mem _) _, _ | _, .bind _ _ .old _, _
  | _, .bind _ _ .oldNet _, _ | _, .bind _ _ .kint _, _ | _, .tt, _ | _, .eq .., _
  | _, .defined _, _ | _, .not _, _ | _, .and .., _ | _, .imp .., _ | _, .upd .., _
  | _, .modal .., _ | _, .havoc _, _ | _, .anon .., _ => rfl

/-- What fails under the peeled binders fails under the binders: each is a
`∀` (or a hidden binder, read as one) of the values it is peeled at. -/
theorem Fml.not_holds_of_peelC (vals : List (Var × Value)) : {Γ : Ctx} → (σ : State C Γ) →
    (φ : Fml C Γ) → ¬ holds (Fml.peelC vals σ φ).2.1 (Fml.peelC vals σ φ).2.2 → ¬ holds σ φ
  | _, σ, .all x p φ, h => by
    cases hw : (vals.lookup x).bind (PrimTy.ofValue? p) with
    | none => rw [Fml.peelC, hw] at h; exact h
    | some w =>
      rw [Fml.peelC, hw] at h
      exact fun hall => Fml.not_holds_of_peelC vals _ φ h (hall w)
  | _, σ, .bind m x (.val p) φ, h => by
    cases hw : (vals.lookup x).bind (PrimTy.ofValue? p) with
    | none => rw [Fml.peelC, hw] at h; exact h
    | some w =>
      rw [Fml.peelC, hw] at h
      exact fun hall => Fml.not_holds_of_peelC vals _ φ h (hall w)
  | _, _, .bind _ _ (.alias _) _, h | _, _, .bind _ _ (.mem _) _, h | _, _, .bind _ _ .old _, h
  | _, _, .bind _ _ .oldNet _, h | _, _, .bind _ _ .kint _, h | _, _, .tt, h | _, _, .eq .., h
  | _, _, .defined _, h
  | _, _, .not _, h | _, _, .and .., h | _, _, .imp .., h | _, _, .upd .., h
  | _, _, .modal .., h | _, _, .havoc _, h | _, _, .anon .., h => h

/-- `φ` read under its leading parameters bound to `vals` (`Fml.peel`). -/
def Fml.eval3Peel (dom : TDom) (vals : List (Var × Value)) {Γ : Ctx} (σ : State C Γ)
    (φ : Fml C Γ) : Tri :=
  match Fml.peel vals σ φ with
  | ⟨_, σ', ψ⟩ => ψ.eval3 dom σ'

/-- **A certificate**: a typed state where `φ`, its leading parameters bound
to `vals`, evaluates to `ff` refutes `⊨ φ`. -/
theorem Fml.not_valid_of_eval3Peel {dom : TDom} (vals : List (Var × Value)) (σ : State C [])
    {φ : Fml C []} (h : Fml.eval3Peel dom vals σ φ = .ff) : ¬ Valid φ := by
  intro hv
  have key := Fml.not_holds_of_peelC vals σ φ
  rw [← Fml.peel_eq] at key
  unfold Fml.eval3Peel at h
  generalize Fml.peel vals σ φ = q at h key
  obtain ⟨_, σ', ψ⟩ := q
  exact key (Fml.eval3_ff h) (hv σ)

/-- The first `n` conjuncts of `φ₁ ∧ (φ₂ ∧ …)`, the last one the rest
(`Fml.conj`'s shape). -/
def Fml.conjN {Γ : Ctx} : Nat → Fml C Γ → List (Fml C Γ)
  | 0, _ => []
  | 1, φ => [φ]
  | n + 2, .and φ ψ => φ :: Fml.conjN (n + 1) ψ
  | _ + 2, φ => [φ]

/-- What the run in front of a formula leaves, for the report: the storage
it ends with, or how it halts; under implications, a binder at its first
value, an update in the typed state it lifts to.  `none` where the run is
past its fuel or the update lifts to no typed state. -/
def Fml.outcome (dom : TDom) : {Γ : Ctx} → State C Γ →
    Fml C Γ → Option (Except Semantics.Halt (List (Name × Semantics.SVal)))
  | _, σ, .imp _ ψ => Fml.outcome dom σ ψ
  | _, σ, .all _ p ψ => match dom p with
    | v :: _ => Fml.outcome dom (σ.push (t := .val p) v) ψ
    | [] => none
  | _, σ, .bind _ _ t ψ => match dom.bind σ t with
    | v :: _ => Fml.outcome dom (σ.push v) ψ
    | [] => none
  | _, σ, .upd _ U ψ => match U.applyV σ with
    | none => some (.error .revert)
    | some τ => match σ.lift? τ with
      | some σ' => match Fml.outcome dom σ' ψ with
        | some r => some r
        | none => some (.ok σ'.storage.erase)
      | none => none
  | _, σ, .modal _ P κ _ => match Prog.runFramesF loopFuel σ P κ with
    | .ok τ => some (.ok τ.storage.erase)
    | .error .diverge => none
    | .error e => some (.error e.erase)
  | _, _, _ => none

/-- A specification's body `{U} [ P ] (φ₁ ∧ … ∧ φₙ)` read in `σ`: the halt
the run ends in, or the indices of the conjuncts that evaluate to `ff`
where it ends; `none` where the run is past its fuel or the update lifts to
no typed state. -/
def Fml.postFails (dom : TDom) (n : Nat) : {Γ : Ctx} → State C Γ →
    Fml C Γ → Option (Option Semantics.Halt × List Nat)
  | _, σ, .upd _ U ψ => match U.applyV σ with
    | none => some (some .revert, [])
    | some τ => match σ.lift? τ with
      | some σ' => Fml.postFails dom n σ' ψ
      | none => none
  | _, σ, .modal _ P κ φ => match Prog.runFramesF loopFuel σ P κ with
    | .ok τ =>
      some (none, ((List.range n).zip (Fml.conjN n φ)).filterMap fun (i, ψ) =>
        if ψ.eval3 dom τ = .ff then some i else none)
    | .error .diverge => none
    | .error e => some (some e.erase, [])
  | _, _, _ => none

end Solidity

namespace Solidity.Tools

open Semantics

variable {C : Contract}

/-! ## The search -/

/-- **A counterexample**: the state the call starts in (its storage, the
arguments bound as locals, the transaction, the ledger), the arguments, the
storage the typed run ends with or how it halts (`none` for a formula with
no run in front), and the indices of the conjuncts after the call that
evaluate to `ff`. -/
structure Witness where
  state : Semantics.State
  args : List (String × Value)
  outcome : Option (Except Halt (List (Name × Semantics.SVal)))
  failing : List Nat

/-- What a search found, among how many candidates, of which how many met
the stated premises. -/
structure Search where
  witness : Option Witness
  tried : Nat
  admitted : Nat

/-- The integers a candidate's arguments are, first in its domain: a
binder tries them before the pools. -/
def Cand.argInts (c : Cand) : List Int :=
  c.args.filterMap fun (_, v) => match v with
    | .int n => some n
    | .bool _ => none

section Search

variable [FreshNames]

/-- The arguments of a candidate by variable, as `Fml.peel` binds them. -/
def Cand.vals (c : Cand) : List (Var × Value) := c.args.map fun (n, v) => (Var.ofName n, v)

/-- The typed state a candidate starts in, with no locals: its parameters are
the formula's binders. -/
def Cand.tstate (C : Contract) (c : Cand) : State C [] := State.ofSemD C c.state

/-- The obligation of `f` in pieces, and what the search needs of `f`: its
declaration, the scoped obligation, how many premises are met by
construction and how many stated, the conjuncts after the call (today's,
as the specification writes them), its parameters of value type, the
literals of the clauses. -/
structure SpecProblem (C : Contract) where
  decl : FunDecl
  fml : Fml C []
  assumed : Nat
  checked : Nat
  posts : List (NRead C)
  params : List (String × PrimTy)
  payable : Bool
  lits : List Int

/-- The problem of `f`: `specPieces`, the scoped obligation, the
parameters, the literals. -/
def SpecProblem.of (C : Contract) (f : String) : Except String (SpecProblem C) := do
  let (assumed, checked, _, _, posts) ← specPieces C f
  let fml ← specObligation C f
  let some d := lookupBy f C.funs | throw s!"{f} is not a function of the contract"
  let params := d.params.filterMap fun (n, T) => match T with
    | .prim p => some (n, p)
    | _ => none
  let lits := (C.inv ++ d.spec.requires ++ d.spec.ensures).flatMap specNums ++
    (d.spec.assignable.getD []).flatMap locNums
  pure { decl := d, fml, assumed := assumed.length, checked := checked.length, posts, params,
         payable := d.payable, lits }

/-- The literals a candidate's domain is drawn from: its arguments, then
the specification's. -/
def SpecProblem.domLits (P : SpecProblem C) (c : Cand) : List Int := c.argInts ++ P.lits

/-- A candidate tried: `none` unless the stated premises evaluate to `tt`;
then the conjuncts that evaluate to `ff`, if any.  A run that panics (an
`assert` failed) refutes the box whatever follows it, so it is a
counterexample with no conjunct blamed: the witness's outcome names it.
The update and the call run once (the typed run, with fuel), and each
conjunct is read in the state they leave. -/
def SpecProblem.try (P : SpecProblem C) (c : Cand) : Option (Option Witness) :=
  let dom := poolDom (P.domLits c)
  let ⟨_, σ, ψ⟩ := Fml.peel c.vals (c.tstate C) P.fml
  match ψ with
  | .imp pre body =>
    let pres := (Fml.conjN (P.assumed + P.checked) pre).drop P.assumed
    if !pres.all (fun φ => φ.eval3 dom σ = .tt) then none else
    match Fml.postFails dom P.posts.length σ body with
    | none => some none
    | some (some .panic, _) =>
      some (some { state := c.state, args := c.args, failing := [],
                   outcome := some (.error .panic) })
    | some (some _, _) => some none
    | some (none, []) => some none
    | some (none, failing) =>
      some (some { state := c.state, args := c.args, failing,
                   outcome := Fml.outcome dom σ body })
  | _ => none

/-- Whether a candidate is a counterexample. -/
def SpecProblem.refutes (P : SpecProblem C) (c : Cand) : Bool :=
  match P.try c with
  | some (some _) => true
  | _ => false

/-- **The search for a counterexample to `f`'s specification**: the
all-default storage with every combination of pooled arguments first (when
there are at most half the budget of them), then random candidates up to
`budget`; what is found is shrunk. -/
def SpecProblem.search (P : SpecProblem C) (budget : Nat) : Search := Id.run do
  let dom := poolVals P.lits
  let combos := products (P.params.map fun (_, p) => dom p)
  let combos := if combos.length * 2 ≤ budget then combos else []
  let cands := combos.map fun vs =>
    ({ st := C.initStorage, args := P.params.map (·.1) |>.zip vs } : Cand)
  let mut admitted := 0
  let mut tried := 0
  let mut g := mkStdGen 2026
  let mut found : Option Cand := none
  for c in cands do
    tried := tried + 1
    match P.try c with
    | none => pure ()
    | some none => admitted := admitted + 1
    | some (some _) => found := some c; break
  if found.isNone then
    for _ in [0:budget - tried] do
      let (c, g') := (genCandidate C P.lits P.params P.payable).run g
      g := g'
      tried := tried + 1
      match P.try c with
      | none => pure ()
      | some none => admitted := admitted + 1
      | some (some _) => found := some c; break
  let some c := found | return { witness := none, tried, admitted }
  let c := c.shrink C P.refutes 64
  return { witness := (P.try c).join, tried, admitted := admitted + 1 }

/-- **A counterexample to a closed scoped formula**: its parameters bound to
pooled `uint`s (every combination first), the storage all-default, then
random storages of `C`'s layout; what is found is shrunk.  A candidate is
one where the formula under its arguments evaluates to `ff`. -/
def searchFml (C : Contract) (φ : Fml C []) (budget : Nat := 2000) : Search := Id.run do
  let ps := (Fml.params φ).filterMap fun (x, p) => match x with
    | .user n => some (n, p)
    | .fresh .. => none
  -- the candidate's arguments bound, so that the witness is what refutes
  let refutes (c : Cand) : Bool :=
    Fml.eval3Peel (poolDom c.argInts) c.vals (c.tstate C) φ = .ff
  let combos := products (ps.map fun (_, p) => poolVals [] p)
  let combos := if combos.length * 2 ≤ budget then combos else []
  let mut tried := 0
  let mut g := mkStdGen 2026
  let mut found : Option Cand := none
  for vs in combos do
    tried := tried + 1
    let c : Cand := { st := C.initStorage, args := ps.map (·.1) |>.zip vs }
    if refutes c then found := some c; break
  if found.isNone then
    for _ in [0:budget - tried] do
      let (c, g') := (genCandidate C [] ps true).run g
      g := g'
      tried := tried + 1
      if refutes c then found := some c; break
  let some c := found | return { witness := none, tried, admitted := tried }
  let c := c.shrink C refutes 64
  let ⟨_, σ, ψ⟩ := Fml.peel c.vals (c.tstate C) φ
  return { witness := some { state := c.state, args := c.args, failing := [],
                             outcome := Fml.outcome (poolDom c.argInts) σ ψ },
           tried, admitted := tried }

/-! ## Printing a witness -/

/-- A witness, one fact per line: the arguments and the transaction
(`fmtTx`), the storage before, and after the run (or how it halted). -/
def Witness.lines (C : Contract) (w : Witness) : List String :=
  let σ := w.state
  let args := w.args.map fun (n, v) => s!"{n} = {Value.fmt v}"
  let after := match w.outcome with
    | none => []
    | some (.error h) => [s!"after: {fmtHalt h}"]
    | some (.ok st) => ["after: " ++ fmtStorageLine C st]
  [", ".intercalate (args ++ fmtTx σ), "before: " ++ fmtStorageLine C σ.storage] ++ after

/-! ## Certificates -/

section Meta

open Lean Meta

deriving instance ToExpr for Semantics.SVal
deriving instance ToExpr for Semantics.MVal
deriving instance ToExpr for Semantics.MObj
deriving instance ToExpr for Semantics.Seg
deriving instance ToExpr for Semantics.Binding
deriving instance ToExpr for Semantics.ExtKey
deriving instance ToExpr for Semantics.ExtResult
deriving instance ToExpr for Semantics.TxEnv
deriving instance ToExpr for Semantics.State

/-- **The certificate**: the kernel checks `¬ ⊨ φ` of the scoped `φ` as
`Fml.not_valid_of_eval3Peel` at the typed state of `σ`
(`State.ofSemD`), its leading parameters bound to the witness's arguments
`vals` (`Fml.peel`, as the search read it), deciding
`Fml.eval3Peel (poolDom lits) vals _ φ = .ff` by evaluation: the decoding
of `σ`'s storage, the typed run and the formula under the parameters.  The
kernel runs under `heartbeats` (thousands), half the default, and the
declaration is checked, never added. -/
def certifyRefl (cE φE : Expr) (lits : List Int) (vals : List (Var × Value))
    (σ : Semantics.State) (heartbeats : Nat := 100000) : MetaM Bool := do
  let domE := mkApp (mkConst ``poolDom) (toExpr lits)
  let σE := mkApp2 (mkConst ``State.ofSemD) cE (toExpr σ)
  let valsE := toExpr vals
  let ev ← mkAppM ``Fml.eval3Peel #[domE, valsE, σE, φE]
  let eq ← mkEq ev (mkConst ``Tri.ff)
  let h ← mkDecideProof eq
  let type := mkNot (← mkAppM ``Valid #[φE])
  let value ← mkAppM ``Fml.not_valid_of_eval3Peel #[valsE, σE, h]
  let decl := Declaration.thmDecl {
    name := `_counterexample_certificate, levelParams := [], type, value }
  let opts := maxHeartbeats.set (← getOptions) heartbeats
  match Kernel.Environment.addDecl (← getEnv).toKernelEnv opts decl with
  | .ok _ => pure true
  | .error _ => pure false

/-- A refutation: the witness, whether the kernel certified it, and the
conjuncts it fails. -/
structure Refutation where
  witness : Witness
  certified : Bool
  fails : List MessageData

/-- The `i`-th conjunct owed after the call of `d`, `φ`: an invariant or an
`ensures` as written, a conjunct of the frame of `assignable` as the
formula it is, read where the snapshots `old` and `oldNet` are in scope
and closed over them by hidden binders (quoted against the contract `cE`). -/
def postLabel (C : Contract) (d : FunDecl) (cE : Expr) (i : Nat) (φ : NRead C) : MessageData :=
  if h : i < C.inv.length then m!"invariant {SpecExpr.fmt C.inv[i]}"
  else if h' : i - C.inv.length < d.spec.ensures.length then
    m!"ensures {SpecExpr.fmt d.spec.ensures[i - C.inv.length]}"
  else
    let locs := (d.spec.assignable.getD []).map SpecLoc.fmt
    let Γ : NCtx := [(oldNetVar, .oldNet), (oldVar, .old)]
    let shown : MessageData := match φ Γ with
      | .ok ψ => m!"{Fml.quote cE (Fml.closeN false Γ ψ)}"
      | .error e => m!"{e}"
    m!"assignable {if locs.isEmpty then "\\nothing" else ", ".intercalate locs}: {shown}"

/-- **Refute `f`'s specification**: search, then certify what was found
against the scoped obligation.  `n` names the contract `C`. -/
def refuteSpec (n : Lean.Name) (C : Contract) (f : String) (budget : Nat := 2000) :
    MetaM (Except String (Search × Option Refutation)) := do
  match SpecProblem.of C f with
  | .error e => pure (.error e)
  | .ok P =>
    let s := P.search budget
    let some w := s.witness | pure (.ok (s, none))
    let cE := mkConst n
    let c : Cand := { st := w.state.storage, args := w.args }
    let lits := P.domLits c
    -- the kernel is asked only what the evaluator already answered
    let certified ← if Fml.eval3Peel (poolDom lits) c.vals (State.ofSemD C w.state)
        P.fml = .ff then certifyRefl cE (Fml.quote cE P.fml) lits c.vals w.state
      else pure false
    let fails := w.failing.map fun i => postLabel C P.decl cE i (P.posts.getD i NRead.tt)
    pure (.ok (s, some { witness := w, certified, fails }))

/-- The report of a refutation: the witness and the conjuncts it fails. -/
def Refutation.lines (C : Contract) (r : Refutation) : List MessageData :=
  (r.witness.lines C).map toMessageData ++ r.fails.map fun l => m!"fails: {l}"

/-- The head line of a refutation of `f`, as `#verify` and
`#counterexample` print it: `✗ f (certified):`. -/
def Refutation.head (f : String) (r : Refutation) : MessageData :=
  m!"✗ {f} ({if r.certified then "certified" else "tested"}):"

/-- The report of the search for a counterexample to `f`'s specification. -/
def searchReport (C : Contract) (f : String) : Search × Option Refutation → MessageData
  | (_, some r) => reportMsg (r.head f) (r.lines C)
  | (s, none) =>
    m!"no counterexample to {f} found in {s.tried} candidates ({s.admitted} met the premises)"

end Meta

end Search

/-! ## `#counterexample` -/

/-- `#counterexample C.f`: a counterexample to the specification of the
function `f` of the contract `C`; `#counterexample C`: to each of its
functions with an obligation; `#counterexample φ`: to the closed scoped
formula `φ : Fml C []` (`dl!{ … }` under `open scoped
Solidity.Scoped`, or `cdl!{ … }`). -/
syntax (name := counterexampleCmd) "#counterexample " term : command

open Lean Elab Command Term Meta in
/-- `#counterexample`: a function's specification, a contract's, or a
formula. -/
@[command_elab counterexampleCmd]
def elabCounterexample : Lean.Elab.Command.CommandElab := fun stx => liftTermElabM do
  let t := stx[1]
  let target ← if t.isIdent then resolveTarget? "#counterexample" t.getId else pure none
  let one (c : Lean.Name) (C : Contract) (f : String) : TermElabM Unit := do
    match ← refuteSpec c C f with
    | .error e => throwError "#counterexample: {e}"
    | .ok r => logInfo (searchReport C f r)
  match target with
  | some (.function c C f) => one c C f
  | some (.contract c C) =>
    let fs := C.funs.filter fun (_, d) => hasObligation C d
    if fs.isEmpty then logInfo m!"{c} has no function with a specification"
    for (f, _) in fs do one c C f
  | none =>
    let φE ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    let φE ← instantiateMVars φE
    let ty ← whnf (← inferType φE)
    unless ty.isAppOfArity ``Fml 2 && (← whnfR ty.appArg!).isAppOf ``List.nil do
      throwError "#counterexample: not a closed scoped formula `Fml C []` (`cdl!\{ … }`, or \
        `dl!\{ … }` under `open scoped Solidity.Scoped`){indentExpr φE}"
    if φE.hasFVar || φE.hasMVar then
      throwError "#counterexample: the formula is not closed{indentExpr φE}"
    let cE := ty.appFn!.appArg!
    unless (← whnfR cE).isConst do throwError "#counterexample: not a named contract: {cE}"
    let C ← unsafe evalExpr Contract (Lean.mkConst ``Contract) cE
    let φ ← unsafe evalExpr (Fml C []) ty φE
    let s := searchFml C φ
    let some w := s.witness
      | logInfo m!"no counterexample found in {s.tried} candidates"
    let c : Cand := { st := w.state.storage, args := w.args }
    let certified ← if Fml.eval3Peel (poolDom c.argInts) c.vals
        (State.ofSemD C w.state) φ = .ff then certifyRefl cE φE c.argInts c.vals w.state
      else pure false
    logReport m!"counterexample ({if certified then "certified" else "tested"}):"
      ((w.lines C).map toMessageData)

end Solidity.Tools
