import Solidity.Semantics.IntrinsicStorage.Layout
import Solidity.Semantics.ContractWorld
import Solidity.Semantics.RunFuel

/-! Structural preimages of actual dependent storage. Coverage quantifies over
all addresses and mapping defaults. A finite universe of bounded preimages
makes the specification a list without evaluating the address or key domains. -/
namespace Solidity.Semantics.IntrinsicStorage

open Solidity.Storage

/-- A stored field with its full-word offset, including every represented field. -/
inductive FieldCell : {fs : List (Name × Ty)} → SFields fs → Nat → {T : Ty} → SVal T → Prop
  | head {f T fs} (v : SVal T) (vs : SFields fs) : FieldCell (.cons (f := f) v vs) 0 v
  | tail {f T fs U} (v : SVal T) (vs : SFields fs) {o : Nat} {w : SVal U}
      (h : FieldCell vs o w) : FieldCell (.cons (f := f) v vs) (size T + o) w

/-- One concrete storage edge. Shadows and overwritten explicit map entries
remain represented; fallback edges cover exactly the keys using the default. -/
inductive Child : {T : Ty} → SVal T → Storage.Loc → {U : Ty} → SVal U → Storage.Loc → Prop
  | field {s U} (fs : SFields (structDef s)) {o : Nat} {v : SVal U}
      (h : FieldCell fs o v) (l : Storage.Loc) : Child (.struct fs) l v (l.add o)
  | live {E n} (vs : SVec E n) (sh : SList E) (hn : n < 2 ^ 256)
      {i : Nat} {v : SVal E} (h : vs.toList[i]? = some v) (l : Storage.Loc) :
      Child (.array vs sh hn) l v (.data l (i * size E))
  | shadow {E n} (vs : SVec E n) (sh : SList E) (hn : n < 2 ^ 256)
      {i : Nat} {v : SVal E} (h : sh.toList[i]? = some v) (l : Storage.Loc) :
      Child (.array vs sh hn) l v (.data l ((n + i) * size E))
  | fixed {E n} (vs : SVec E n) {i : Nat} {v : SVal E}
      (h : vs.toList[i]? = some v) (l : Storage.Loc) :
      Child (.fixed vs) l v (l.add (i * size E))
  | entry {K V} (vs : SMap K V) (d : SVal V) {k : K.Denote} {v : SVal V}
      (h : (k, v) ∈ vs.toList) (l : Storage.Loc) :
      Child (.map vs d) l v (.hash (keyWord k) l 0)
  | fallback {K V} (vs : SMap K V) (d : SVal V) (k : K.Denote)
      (h : lookupBy k vs.toList = none) (l : Storage.Loc) :
      Child (.map vs d) l d (.hash (keyWord k) l 0)

theorem fieldCell_get {fs : List (Name × Ty)} (vs : SFields fs) {f : Name} {T : Ty}
    (h : lookupBy f fs = some T) : FieldCell vs (offsetIn fs f) (vs.get h) := by
  cases vs with
  | nil => simp only [lookupBy] at h; cases h
  | @cons g U fs v rest =>
    by_cases e : f = g
    · have ht := SFields.lookupBy_cons_pos e h
      subst ht
      simpa only [offsetIn, e, if_true, SFields.get_cons, dif_pos] using FieldCell.head v rest
    · simpa only [offsetIn, e, if_false, SFields.get_cons, dif_neg] using
        FieldCell.tail v rest (fieldCell_get rest (SFields.lookupBy_cons_neg e h))

theorem child_array {E : Ty} {n : Nat} (vs : SVec E n) (sh : SList E)
    (hn : n < 2 ^ 256) {i : Nat} {v : SVal E}
    (h : (vs.toList ++ sh.toList)[i]? = some v) (l : Storage.Loc) :
    Child (.array vs sh hn) l v (.data l (i * size E)) := by
  by_cases hi : i < n
  · rw [List.getElem?_append_left (by simpa only [SVec.length_toList] using hi)] at h
    exact .live vs sh hn h l
  · rw [List.getElem?_append_right (by simpa only [SVec.length_toList] using Nat.le_of_not_gt hi),
      SVec.length_toList] at h
    have he : n + (i - n) = i := by omega
    simpa only [he] using Child.shadow vs sh hn h l

theorem Child.bounded {T U : Ty} {v : SVal T} {w : SVal U} {l m : Storage.Loc}
    (h : Child v l w m) (hl : BoundedKeys l) : BoundedKeys m := by
  cases h with
  | field fs h l => simpa only [boundedKeys_add] using hl
  | live => exact hl
  | shadow => exact hl
  | fixed => simpa only [boundedKeys_add] using hl
  | entry vs d h l => exact ⟨keyWord_lt _, hl⟩
  | fallback vs d k h l => exact ⟨keyWord_lt k, hl⟩

/-- Finite ancestry within the actual value, with no imposed depth cutoff. -/
inductive Below : {T : Ty} → SVal T → Storage.Loc → {U : Ty} → SVal U → Storage.Loc → Prop
  | refl {T} (v : SVal T) (l : Storage.Loc) : Below v l v l
  | step {T U V} {v : SVal T} {w : SVal U} {x : SVal V} {l m n : Storage.Loc}
      (head : Child v l w m) (tail : Below w m x n) : Below v l x n

theorem Below.bounded {T U : Ty} {v : SVal T} {w : SVal U} {l m : Storage.Loc}
    (h : Below v l w m) (hl : BoundedKeys l) : BoundedKeys m := by
  induction h with
  | refl => exact hl
  | step head tail ih => exact ih (head.bounded hl)

theorem Below.trans {T U V : Ty} {v : SVal T} {w : SVal U} {x : SVal V}
    {l m n : Storage.Loc} (h : Below v l w m) (g : Below w m x n) : Below v l x n := by
  induction h with
  | refl => exact g
  | step head tail ih => exact .step head (ih g)

/-- Actual successful lookup reaches the same typed value at the canonical
location. Failed lookups are handled separately by execution observations. -/
theorem below_find {T U : Ty} (p : Path T U) (v : SVal T) {w : SVal U}
    (h : v.find p = some w) (l : Storage.Loc) : Below v l w (locate p l) := by
  induction p generalizing l with
  | nil =>
    rw [SVal.find_nil] at h
    cases h
    exact .refl v l
  | field hf p ih =>
    cases v with
    | struct fs =>
      rw [SVal.find_field] at h
      exact .step (.field fs (fieldCell_get fs hf) l) (ih _ h _)
  | «at» i p ih =>
    cases v with
    | array vs sh hn =>
      rw [SVal.find_at] at h
      split at h
      next x hx => exact .step (child_array vs sh hn hx l) (ih x h _)
      next => cases h
  | atF i p ih =>
    cases v with
    | fixed vs =>
      rw [SVal.find_atF] at h
      split at h
      next x hx => exact .step (.fixed vs hx l) (ih x h _)
      next => cases h
  | key k p ih =>
    cases v with
    | map vs d =>
      rw [SVal.find_key] at h
      split at h
      next x hx => exact .step (.entry vs d (lookupBy_eq_some_mem hx) l) (ih x h _)
      next hx => exact .step (.fallback vs d k hx l) (ih d h _)

/-- An empty dynamic array still has a data origin; inline primitives only
inherit their ancestors. Mapping keys enter through actual Child edges. -/
inductive LocalInput : {T : Ty} → SVal T → Storage.Loc → Pre → Prop
  | ancestor {T} (v : SVal T) (l : Storage.Loc) {p : Pre}
      (h : p ∈ ancestry l) : LocalInput v l p
  | data {E n} (vs : SVec E n) (sh : SList E) (hn : n < 2 ^ 256) (l : Storage.Loc) :
      LocalInput (.array vs sh hn) l (.data (l.word (2 ^ 256) keccakH))

def ValueInput {T : Ty} (v : SVal T) (l : Storage.Loc) (p : Pre) : Prop :=
  ∃ (U : Ty) (w : SVal U) (m : Storage.Loc), Below v l w m ∧ LocalInput w m p

theorem ValueInput.words {T : Ty} {v : SVal T} {l : Storage.Loc} {p : Pre}
    (h : ValueInput v l p) (hl : BoundedKeys l) : p.Words := by
  obtain ⟨U, w, m, below, input⟩ := h
  cases input with
  | ancestor w m hp => exact ancestry_words m (below.bounded hl) p hp
  | data => exact word_lt _

theorem ValueInput.child {T U : Ty} {v : SVal T} {w : SVal U} {l m : Storage.Loc}
    (h : Child v l w m) {p : Pre} (hp : ValueInput w m p) : ValueInput v l p := by
  obtain ⟨V, x, n, below, input⟩ := hp
  exact ⟨V, x, n, .step h below, input⟩

def StoredInput {C : Contract} (st : Solidity.Storage C) (p : Pre) : Prop :=
  ∃ (T : Ty) (v : SVal T) (o : Nat), FieldCell st o v ∧ ValueInput v (.root o) p

/-- No caller-supplied account support: every actual address is quantified. -/
def WorldInput {K : Type} {contracts : K → Contract} (w : ContractWorld.World contracts)
    (p : Pre) : Prop :=
  ∃ (a : ContractWorld.Address) (k : K) (st : Solidity.Storage (contracts k)),
    w.accounts a = some ⟨k, st⟩ ∧ StoredInput st p

theorem WorldInput.words {K : Type} {contracts : K → Contract}
    {w : ContractWorld.World contracts} {p : Pre} (h : WorldInput w p) : p.Words := by
  obtain ⟨a, k, st, ha, T, v, o, hv, hp⟩ := h
  exact hp.words True.intro

/-- A mathematical finite universe, never enumerated by the checks. -/
def preUniverse : List Pre :=
  ((List.finRange (2 ^ 256)).map (fun w => Pre.data w.val)) ++
  ((List.finRange (2 ^ 256)).flatMap (fun k =>
    (List.finRange (2 ^ 256)).map (fun w => Pre.entry k.val w.val)))

private theorem in_finRange {n : Nat} (i : Fin n) : i ∈ List.finRange n :=
  List.mem_ofFn.mpr ⟨i, rfl⟩

theorem mem_preUniverse {p : Pre} (hp : p.Words) : p ∈ preUniverse := by
  cases p with
  | data w =>
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨⟨w, hp⟩, in_finRange _, rfl⟩
  | entry k w =>
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    exact ⟨⟨k, hp.1⟩, in_finRange _,
      List.mem_map.mpr ⟨⟨w, hp.2⟩, in_finRange _, rfl⟩⟩

/-- Choice decides occurrence, not which accounts or defaults to omit. -/
noncomputable def stored {K : Type} {contracts : K → Contract}
    (w : ContractWorld.World contracts) : List (List UInt8) := by
  classical
  exact (preUniverse.filter (fun p => decide (WorldInput w p))).map encoded

theorem mem_stored {K : Type} {contracts : K → Contract}
    (w : ContractWorld.World contracts) (b : List UInt8) :
    b ∈ stored w ↔ ∃ p, WorldInput w p ∧ encoded p = b := by
  classical
  constructor
  · intro h
    obtain ⟨p, hp, hb⟩ := List.mem_map.mp h
    exact ⟨p, of_decide_eq_true (List.mem_filter.mp hp).2, hb⟩
  · rintro ⟨p, hp, rfl⟩
    apply List.mem_map.mpr
    exact ⟨p, List.mem_filter.mpr ⟨mem_preUniverse hp.words, decide_eq_true hp⟩, rfl⟩

theorem read_stored {K : Type} {contracts : K → Contract}
    (w : ContractWorld.World contracts) (a : ContractWorld.Address) (k : K)
    (st : Solidity.Storage (contracts k)) (ha : w.accounts a = some ⟨k, st⟩)
    {T : Ty} (r : SRef (contracts k) T) {v : SVal T} (hv : st.find r = some v)
    {p : Pre} (hp : p ∈ ancestry (reference r)) : encoded p ∈ stored w := by
  apply (mem_stored w _).mpr
  refine ⟨p, ⟨a, k, st, ha, r.ty, st.get r.hroot, offsetIn _ r.root,
    fieldCell_get st r.hroot, T, v, reference r, ?_, ?_⟩, rfl⟩
  · exact below_find r.path _ hv _
  · exact .ancestor v _ hp


/-- Structural inputs of an actual aggregate operand at its reached location. -/
noncomputable def valueInputs {T : Ty} (v : SVal T) (l : Storage.Loc) : List (List UInt8) := by
  classical
  exact (preUniverse.filter (fun p => decide (ValueInput v l p))).map encoded

theorem valueInputs_covers {T : Ty} (v : SVal T) (l : Storage.Loc) (hl : BoundedKeys l)
    {p : Pre} (hp : ValueInput v l p) : encoded p ∈ valueInputs v l := by
  classical
  exact List.mem_map.mpr ⟨p,
    List.mem_filter.mpr ⟨mem_preUniverse (hp.words hl), decide_eq_true hp⟩, rfl⟩

/-- Observations are outside the result so a failing bind cannot erase them. -/
structure Inputs where
  slots : List (List UInt8) := []
  ordinary : List (List UInt8) := []

namespace Inputs

def append (a b : Inputs) : Inputs := ⟨a.slots ++ b.slots, a.ordinary ++ b.ordinary⟩
def hashed (a : Inputs) : List (List UInt8) := a.slots ++ a.ordinary

theorem slot_hashed (a : Inputs) {b : List UInt8} (h : b ∈ a.slots) : b ∈ a.hashed :=
  List.mem_append_left _ h

end Inputs

structure Audit (α : Type) where
  result : TRes α
  inputs : Inputs := {}

namespace Audit

def pure (x : α) : Audit α := ⟨.ok x, {}⟩
def lift (x : TRes α) : Audit α := ⟨x, {}⟩
def bind (x : Audit α) (f : α → Audit β) : Audit β :=
  match x.result with
  | .error e => ⟨.error e, x.inputs⟩
  | .ok a => let y := f a; ⟨y.result, x.inputs.append y.inputs⟩
/-- Case analysis on a result retains the prefix, including a caught error. -/
def follow (x : Audit α) (f : TRes α → Audit β) : Audit β :=
  let y := f x.result
  ⟨y.result, x.inputs.append y.inputs⟩

@[simp] theorem result_follow (x : Audit α) (f : TRes α → Audit β) :
    (follow x f).result = (f x.result).result := rfl

theorem follow_slots (x : Audit α) (f : TRes α → Audit β) {b : List UInt8}
    (h : b ∈ x.inputs.slots) : b ∈ (follow x f).inputs.slots := List.mem_append_left _ h

def map (f : α → β) (x : Audit α) : Audit β := ⟨x.result.map f, x.inputs⟩

instance : Monad Audit where
  pure := pure
  bind := bind
  map := map

@[simp] theorem result_pure (a : α) :
    (Pure.pure a : Audit α).result = (Pure.pure a : TRes α) := rfl
@[simp] theorem result_lift (a : TRes α) : (lift a).result = a := rfl
@[simp] theorem result_bind (a : Audit α) (f : α → Audit β) :
    (a >>= f).result = a.result >>= fun x => (f x).result := by
  cases a with
  | mk result inputs => cases result <;> rfl
@[simp] theorem result_map (f : α → β) (a : Audit α) :
    (f <$> a).result = a.result.map f := rfl

@[simp] theorem result_map_direct (f : α → β) (a : Audit α) :
    (Audit.map f a).result = a.result.map f := rfl

theorem result_mapM (f : α → Audit β) (xs : List α) :
    (xs.mapM f).result = xs.mapM (fun x => (f x).result) := by
  have go : ∀ xs acc, (List.mapM.loop f xs acc).result =
      List.mapM.loop (fun x => (f x).result) xs acc := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons x xs ih =>
      intro acc
      simp only [List.mapM.loop, result_bind, ih]
  exact go xs []

theorem failed_bind (a : Audit α) (f : α → Audit β) {e : THalt}
    (h : a.result = .error e) : (a >>= f).inputs = a.inputs := by
  change (bind a f).inputs = _
  simp only [bind, h]

theorem bind_slots_left (a : Audit α) (f : α → Audit β) {b : List UInt8}
    (h : b ∈ a.inputs.slots) : b ∈ (a >>= f).inputs.slots := by
  change b ∈ (bind a f).inputs.slots
  unfold bind
  cases a.result with
  | error e => exact h
  | ok x => exact List.mem_append_left _ h

theorem bind_slots_right (a : Audit α) (f : α → Audit β) {x : α}
    (hx : a.result = .ok x) {b : List UInt8} (h : b ∈ (f x).inputs.slots) :
    b ∈ (a >>= f).inputs.slots := by
  change b ∈ (bind a f).inputs.slots
  simp only [bind, hx, Inputs.append]
  exact List.mem_append_right _ h

noncomputable def atRef {C : Contract} {T : Ty} (r : SRef C T) (a : TRes α) : Audit α :=
  ⟨a, ⟨(ancestry (reference r)).map encoded, []⟩⟩

@[simp] theorem result_atRef {C : Contract} {T : Ty} (r : SRef C T) (a : TRes α) :
    (atRef r a).result = a := rfl

noncomputable def read {C : Contract} {T : Ty} (st : Solidity.Storage C) (r : SRef C T) :
    Audit (SVal T) :=
  ⟨TRes.ofOpt (st.find r), ⟨(ancestry (reference r)).map encoded ++
    (match st.find r with | none => [] | some v => valueInputs v (reference r)), []⟩⟩

@[simp] theorem result_read {C : Contract} {T : Ty} (st : Solidity.Storage C) (r : SRef C T) :
    (read st r).result = TRes.ofOpt (st.find r) := rfl

noncomputable def write {C : Contract} {T : Ty} (st : Solidity.Storage C) (r : SRef C T)
    (v : SVal T) : Audit (Solidity.Storage C) :=
  ⟨TRes.ofOpt (st.write r v), ⟨(ancestry (reference r)).map encoded ++
    valueInputs v (reference r) ++
    (match st.find r with | none => [] | some old => valueInputs old (reference r)), []⟩⟩

@[simp] theorem result_write {C : Contract} {T : Ty} (st : Solidity.Storage C)
    (r : SRef C T) (v : SVal T) : (write st r v).result = TRes.ofOpt (st.write r v) := rfl

/-- The data region is reached by a push, or by a nonempty pop. The choice
uses the actual pre-operation array, not the post-rollback world. -/
noncomputable def arrayOp {C : Contract} {E : Ty} (st : Solidity.Storage C)
    (r : SRef C (.ref (.array E))) (pop : Bool) (a : TRes α) : Audit α :=
  ⟨a, ⟨(ancestry (reference r)).map encoded ++
    (match st.find r with
    | none => []
    | some v => if pop && decide ((SVal.view v : ArrView E).n = 0) then []
      else valueInputs v (reference r) ++
        [encoded (.data ((reference r).word (2 ^ 256) keccakH))]), []⟩⟩

@[simp] theorem result_arrayOp {C : Contract} {E : Ty} (st : Solidity.Storage C)
    (r : SRef C (.ref (.array E))) (pop : Bool) (a : TRes α) :
    (arrayOp st r pop a).result = a := rfl

/-- Include the actual old destination, whose nested cells may be cleared. -/
noncomputable def touch {C : Contract} {T : Ty} (st : Solidity.Storage C)
    (r : SRef C T) (a : TRes α) : Audit α :=
  ⟨a, (read st r).inputs⟩

@[simp] theorem result_touch {C : Contract} {T : Ty} (st : Solidity.Storage C)
    (r : SRef C T) (a : TRes α) : (touch st r a).result = a := rfl

/-- A pushed aggregate is accounted at its new destination, not its source. -/
noncomputable def push {C : Contract} {E : Ty} (st : Solidity.Storage C)
    (r : SRef C (.ref (.array E))) (val : SVal E → Option (SVal E)) :
    Audit (Solidity.Storage C) :=
  let a := arrayOp st r false (TRes.ofOpt (st.push r val))
  ⟨a.result, ⟨a.inputs.slots ++ (match st.find r with
    | none => []
    | some v =>
      let w : ArrView E := SVal.view v
      match val (pushSlot E w.shadow.toList).1 with
      | none => []
      | some x => valueInputs x (.data (reference r) (w.n * size E))), []⟩⟩

@[simp] theorem result_push {C : Contract} {E : Ty} (st : Solidity.Storage C)
    (r : SRef C (.ref (.array E))) (val : SVal E → Option (SVal E)) :
    (push st r val).result = TRes.ofOpt (st.push r val) := rfl

noncomputable def place {C : Contract} {E : Ty} (st : Solidity.Storage C)
    (r : SRef C (.ref (.array E))) : Audit (Solidity.Storage C × PrimTy.uint.Denote) :=
  ⟨TRes.ofOpt (st.pushPlace r), (push st r some).inputs⟩

@[simp] theorem result_place {C : Contract} {E : Ty} (st : Solidity.Storage C)
    (r : SRef C (.ref (.array E))) : (place st r).result = TRes.ofOpt (st.pushPlace r) := rfl

theorem read_value {C : Contract} {T : Ty} (st : Solidity.Storage C) (r : SRef C T)
    {v : SVal T} (hv : st.find r = some v) {p : Pre}
    (hp : ValueInput v (reference r) p) : encoded p ∈ (read st r).inputs.slots := by
  simp only [read, hv]
  exact List.mem_append_right _ (valueInputs_covers v _ (reference_bounded r) hp)

theorem write_value {C : Contract} {T : Ty} (st : Solidity.Storage C) (r : SRef C T)
    (v : SVal T) {p : Pre} (hp : ValueInput v (reference r) p) :
    encoded p ∈ (write st r v).inputs.slots := by
  exact List.mem_append_left _ (List.mem_append_right _
    (valueInputs_covers v _ (reference_bounded r) hp))

theorem write_old {C : Contract} {T : Ty} (st : Solidity.Storage C) (r : SRef C T)
    (v : SVal T) {old : SVal T} (hv : st.find r = some old) {p : Pre}
    (hp : ValueInput old (reference r) p) : encoded p ∈ (write st r v).inputs.slots := by
  simp only [write, hv]
  exact List.mem_append_right _ (valueInputs_covers old _ (reference_bounded r) hp)

def hashing {C : Contract} {Γ : Ctx} {R : RefTy} (σ : State C Γ)
    (k : HashKind) (r : HRef σ.H R) : Audit PrimTy.uint.Denote :=
  ⟨.ok (σ.heap.hash k r), ⟨[], match k with
    | .keccak => [(MObj.words R (σ.heap.get r)).map (fun n => UInt8.ofNat n.toNat)]
    | _ => []⟩⟩

@[simp] theorem result_hashing {C : Contract} {Γ : Ctx} {R : RefTy} (σ : State C Γ)
    (k : HashKind) (r : HRef σ.H R) : (hashing σ k r).result = .ok (σ.heap.hash k r) := rfl

end Audit

namespace Observe

open Audit (lift atRef)
variable {C : Contract} {Γ : Ctx}

mutual
noncomputable def path (σ : State C Γ) : {T : Ty} → SPath C Γ T → Audit (SRef C T)
  | _, .alias i => lift (SPath.resolveT σ (.alias i))
  | _, .loc l => loc σ l

noncomputable def loc (σ : State C Γ) : {T : Ty} → Loc C Γ T → Audit (SRef C T)
  | _, .root r h => pure (SRef.ofRoot r h)
  | _, .field b _ h => do
    let r ← path σ b
    pure (r.field h)
  | _, .index it b i => do
    let r ← path σ b
    let k ← value σ i
    atRef r (TRes.ofOpt (σ.storage.checkIndex r it k))
    atRef (r.index it k) (.ok (r.index it k))

noncomputable def memoryPath (σ : State C Γ) : {T : Ty} → MPath C Γ T → Audit (MVal σ.H T)
  | _, .var i h => lift (MPath.mvalT σ (.var i h))
  | _, .loc l => do lift (TRes.ofOpt (σ.heap.readAddr (← memoryLoc σ l)))

noncomputable def memoryLoc (σ : State C Γ) : {T : Ty} → MLoc C Γ T → Audit (MAddr σ.H T)
  | _, .field b _ h => do
    let r ← memoryPath σ b
    pure (.field r h)
  | _, .index a b i => do
    let r ← memoryPath σ b
    let k ← value σ i
    pure (.index r a k)

noncomputable def value (σ : State C Γ) : {p : PrimTy} → Val C Γ p → Audit p.Denote
  | _, .simple s => pure (s.evalT σ)
  | _, .read l => do
    let r ← loc σ l
    let v ← Audit.read σ.storage r
    pure v.view
  | _, .binop op h hq a b => do
    let x ← value σ a
    match op.shortT x with
    | some y => pure (hq ▸ y)
    | none => do
      let y ← value σ b
      lift (hq ▸ TRes.ofOpt (op.evalT h x y))
  | _, .unop op h hq a => do
    let x ← value σ a
    lift (hq ▸ TRes.ofOpt (op.evalT h x))
  | _, .ternary c a b => do
    let v ← value σ c
    if boolT v then value σ a else value σ b
  | _, .readMem l => do lift (TRes.ofOpt (σ.heap.readAddr (← memoryLoc σ l)))
  | _, .len b hp => do
    let r ← path σ b
    let n ← atRef r (TRes.ofOpt (σ.storage.len r))
    pure (hp ▸ n)
  | _, .mlen b hp => do
    let r ← memoryPath σ b
    pure (hp ▸ σ.heap.lenU r)
  | _, .modular op a b k => do
    let x ← value σ a
    let y ← value σ b
    let m ← value σ k
    lift (TRes.ofOpt (op.evalT x y m))
  | _, .hash k b hp => do
    let r ← memoryPath σ b
    let w ← Audit.hashing σ k r
    pure (hp ▸ w)
end


mutual
theorem path_result (σ : State C Γ) : {T : Ty} → (p : SPath C Γ T) →
    (path σ p).result = p.resolveT σ
  | _, .alias _ => rfl
  | _, .loc l => loc_result σ l

theorem loc_result (σ : State C Γ) : {T : Ty} → (l : Loc C Γ T) →
    (loc σ l).result = l.resolveT σ
  | _, .root _ _ => rfl
  | _, .field b f h => by
    simp only [loc, Audit.result_bind, Audit.result_pure, path_result σ b, Loc.resolveT]
  | _, .index it b i => by
    simp only [loc, Audit.result_bind, Audit.result_atRef, path_result σ b,
      value_result σ i, Loc.resolveT]
    rfl

theorem memoryPath_result (σ : State C Γ) : {T : Ty} → (p : MPath C Γ T) →
    (memoryPath σ p).result = p.mvalT σ
  | _, .var _ _ => rfl
  | _, .loc l => by
    simp only [memoryPath, Audit.result_bind, Audit.result_lift, memoryLoc_result σ l,
      MPath.mvalT]

theorem memoryLoc_result (σ : State C Γ) : {T : Ty} → (l : MLoc C Γ T) →
    (memoryLoc σ l).result = l.addrT σ
  | _, .field b f h => by
    simp only [memoryLoc, Audit.result_bind, Audit.result_pure, memoryPath_result σ b,
      MLoc.addrT]
  | _, .index a b i => by
    simp only [memoryLoc, Audit.result_bind, Audit.result_pure, memoryPath_result σ b,
      value_result σ i, MLoc.addrT]

theorem value_result (σ : State C Γ) : {p : PrimTy} → (v : Val C Γ p) →
    (value σ v).result = v.evalT σ
  | _, .simple _ => rfl
  | _, .read l => by
    simp only [value, Audit.result_bind, Audit.result_read, Audit.result_pure,
      loc_result σ l, Val.evalT]
  | _, .binop op h hq a b => by
    subst hq
    simp only [value, Audit.result_bind, value_result σ a, Val.evalT]
    congr 1
    funext x
    cases op.shortT x <;>
      simp only [Audit.result_bind, Audit.result_pure, Audit.result_lift, value_result σ b]
  | _, .unop op h hq a => by
    subst hq
    simp only [value, Audit.result_bind, Audit.result_lift, value_result σ a, Val.evalT]
  | _, .ternary c a b => by
    simp only [value, Audit.result_bind, value_result σ c, Val.evalT]
    congr 1
    funext x
    cases x <;> first | exact value_result σ b | exact value_result σ a
  | _, .readMem l => by
    simp only [value, Audit.result_bind, Audit.result_lift, memoryLoc_result σ l, Val.evalT]
  | _, .len b hp => by
    subst hp
    simp only [value, Audit.result_bind, Audit.result_atRef, Audit.result_pure,
      path_result σ b, Val.evalT]
  | _, .mlen b hp => by
    subst hp
    simp only [value, Audit.result_bind, Audit.result_pure, memoryPath_result σ b, Val.evalT]
  | _, .modular op a b k => by
    simp only [value, Audit.result_bind, Audit.result_lift, value_result σ a,
      value_result σ b, value_result σ k, Val.evalT]
  | _, .hash k b hp => by
    subst hp
    simp only [value, Audit.result_bind, Audit.result_pure, Audit.result_hashing,
      memoryPath_result σ b, Val.evalT]
    rfl
end


noncomputable def source (σ : State C Γ) {T : Ty} : Src C Γ T → Audit (SVal T)
  | .val v => do pure (.prim (← value σ v))
  | .copy p _ => do
    let r ← path σ p
    Audit.read σ.storage r
  | .fixedCopy p shape _ => do
    let r ← path σ p
    let v ← Audit.read σ.storage r
    pure (shape.apply v)
  | .copyMem p => do pure (MVal.copyMToSt σ.heap (← memoryPath σ p))
  | .fixedCopyMem p shape => do pure (shape.apply (MVal.copyMToSt σ.heap (← memoryPath σ p)))

noncomputable def memorySource (σ : State C Γ) {T : Ty} : MSrc C Γ T → Audit (MVal σ.H T)
  | .val v => value σ v
  | .ref p => memoryPath σ p

noncomputable def aliasRhs (σ : State C Γ) {R : RefTy} :
    ARhs C Γ R → Audit (Solidity.Storage C × SRef C (.ref R))
  | .path p => do pure (σ.storage, ← path σ p)
  | .push b _ => do
    let r ← path σ b
    let _ ← atRef r (.ok ())
    if σ.storage.full r then lift (.error .exhausted) else
    let (st, n) ← Audit.place σ.storage r
    atRef (r.index (.arr .dyn) n) (.ok (st, r.index (.arr .dyn) n))

noncomputable def memoryRhs (σ : State C Γ) {R : RefTy} :
    MRhs C Γ R → Audit (Grew C Γ σ.H (HRef · R))
  | .alias p => do
    let r ← memoryPath σ p
    pure ⟨σ, List.prefix_refl _, r⟩
  | .copy p hm => do
    let r ← path σ p
    let sv ← Audit.read σ.storage r
    let g := σ.copyStToMG sv hm
    pure ⟨g.st, g.ext, g.val⟩
  | .newArr n h => lift (MRhs.evalT σ (.newArr n h))

noncomputable def args (σ : State C Γ) : {ps : Ctx} → Args C Γ ps → Audit (TEnv C σ.H ps)
  | _, as => Args.casesOn (motive := fun ps _ => Audit (TEnv C σ.H ps)) as (pure ())
      (fun as _ _ e => do
        let r ← args σ as
        let v ← value σ e
        pure (v, r))
      (fun as _ _ e => do
        let r ← args σ as
        let v ← path σ e
        pure (some v, r))
      (fun as _ _ e => do
        let r ← args σ as
        let v ← memoryPath σ e
        pure (some v, r))
  termination_by structural _ as => as

theorem source_result (σ : State C Γ) {T : Ty} (s : Src C Γ T) :
    (source σ s).result = s.valueT σ := by
  cases s <;> simp only [source, Src.valueT, Audit.result_bind, Audit.result_pure,
    Audit.result_read, value_result, path_result, memoryPath_result]

theorem memorySource_result (σ : State C Γ) {T : Ty} (s : MSrc C Γ T) :
    (memorySource σ s).result = s.mvalT σ := by
  cases s <;> first | exact value_result σ _ | exact memoryPath_result σ _

theorem aliasRhs_result (σ : State C Γ) {R : RefTy} (r : ARhs C Γ R) :
    (aliasRhs σ r).result = r.evalT σ := by
  cases r with
  | path p => simp only [aliasRhs, ARhs.evalT, Audit.result_bind, Audit.result_pure, path_result]
  | push b h =>
    simp only [aliasRhs, ARhs.evalT, Audit.result_bind, Audit.result_atRef, path_result]
    congr 1
    funext ref
    simp only [Solidity.ok_bind]
    split <;> simp only [Audit.result_lift, Audit.result_bind, Audit.result_atRef] <;> rfl

theorem memoryRhs_result (σ : State C Γ) {R : RefTy} (r : MRhs C Γ R) :
    (memoryRhs σ r).result = r.evalT σ := by
  cases r <;> simp only [memoryRhs, MRhs.evalT, Audit.result_bind, Audit.result_pure,
    Audit.result_read, Audit.result_lift, path_result, memoryPath_result]

theorem args_result (σ : State C Γ) : {ps : Ctx} → (a : Args C Γ ps) →
    (args σ a).result = a.evalT σ
  | _, .nil => rfl
  | _, .snoc as x h e => by
    rw [args, Args.evalT]
    simp only [Audit.result_bind, Audit.result_pure, args_result σ as, value_result]
  | _, .snocStorage as x h e => by
    rw [args, Args.evalT]
    simp only [Audit.result_bind, Audit.result_pure, args_result σ as, path_result]
  | _, .snocMemory as x h e => by
    rw [args, Args.evalT]
    simp only [Audit.result_bind, Audit.result_pure, args_result σ as, memoryPath_result]


noncomputable def storeOp (σ : State C Γ) (op : BinOp) : {p : PrimTy} →
    OpLoc C Γ p → p.Denote → Audit (Out C σ.H Γ)
  | _, .local i, v => lift (OpLoc.storeT σ op (.local i) v)
  | _, .root r h, v => atRef (SRef.ofRoot r h) (opStoreT σ op (SRef.ofRoot r h) v)
  | _, .field b f h, v => do
    let r ← loc σ (.field b f h)
    atRef r (opStoreT σ op r v)
  | _, .index it b i, v => do
    let r ← loc σ (.index it b (.simple i))
    atRef r (opStoreT σ op r v)
  | _, .mfield b f h, v => do lift (opMemT σ op (← memoryLoc σ (.field b f h)) v)
  | _, .mindex a b i, v => do lift (opMemT σ op (← memoryLoc σ (.index a b (.simple i))) v)

noncomputable def bumpOp (σ : State C Γ) (op : IncDec) : {p : PrimTy} →
    OpLoc C Γ p → Audit (Out C σ.H Γ × p.Denote)
  | _, .local i => lift (OpLoc.bumpT σ op (.local i))
  | _, .root r h => atRef (SRef.ofRoot r h) (bumpStoreT σ op (SRef.ofRoot r h))
  | _, .field b f h => do
    let r ← loc σ (.field b f h)
    atRef r (bumpStoreT σ op r)
  | _, .index it b i => do
    let r ← loc σ (.index it b (.simple i))
    atRef r (bumpStoreT σ op r)
  | _, .mfield b f h => do lift (bumpMemT σ op (← memoryLoc σ (.field b f h)))
  | _, .mindex a b i => do lift (bumpMemT σ op (← memoryLoc σ (.index a b (.simple i))))

theorem storeOp_result (σ : State C Γ) (op : BinOp) {p : PrimTy}
    (l : OpLoc C Γ p) (v : p.Denote) : (storeOp σ op l v).result = l.storeT σ op v := by
  cases l <;> simp only [storeOp, OpLoc.storeT, Audit.result_lift, Audit.result_atRef,
    Audit.result_bind, loc_result, memoryLoc_result]

theorem bumpOp_result (σ : State C Γ) (op : IncDec) {p : PrimTy}
    (l : OpLoc C Γ p) : (bumpOp σ op l).result = l.bumpT σ op := by
  cases l <;> simp only [bumpOp, OpLoc.bumpT, Audit.result_lift, Audit.result_atRef,
    Audit.result_bind, loc_result, memoryLoc_result]

abbrev Step (C : Contract) (Γ Δ : Ctx) := (σ : State C Γ) → Audit (Out C σ.H Δ)

namespace Run

noncomputable def assign {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) : Step C Γ Γ := fun σ => do
  let sv ← source σ r
  let ref ← loc σ l
  let st ← Audit.write σ.storage ref sv
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

noncomputable def rebind {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R) : Step C Γ Γ :=
  fun σ => do
    let (st, ref) ← aliasRhs σ r
    pure ⟨(σ.withStorage st).setLocal i (some ref), List.prefix_refl _⟩

noncomputable def assignLocal {p : PrimTy} (i : Idx Γ (.val p)) (r : Val C Γ p) : Step C Γ Γ :=
  fun σ => do pure ⟨σ.setLocal i (← value σ r), List.prefix_refl _⟩

noncomputable def declLocal (p : PrimTy) (init : Option (Val C Γ p)) : Step C Γ (.val p :: Γ) :=
  fun σ => do
    let v ← match init with | none => pure (PrimTy.dflt p) | some e => value σ e
    pure ⟨σ.push (t := .val p) v, List.prefix_refl _⟩

noncomputable def declStorage (R : RefTy) (init : Option (ARhs C Γ R)) : Step C Γ (.alias R :: Γ) :=
  fun σ => match init with
  | none => pure ⟨σ.push (t := .alias R) none, List.prefix_refl _⟩
  | some r => do
    let (st, ref) ← aliasRhs σ r
    pure ⟨(σ.withStorage st).push (t := .alias R) (some ref), List.prefix_refl _⟩

noncomputable def opAssign {p : PrimTy} (op : BinOp) (l : OpLoc C Γ p) (r : Val C Γ p) :
    Step C Γ Γ := fun σ => do storeOp σ op l (← value σ r)

noncomputable def incDec {p : PrimTy} (op : IncDec) (l : OpLoc C Γ p) : Step C Γ Γ :=
  fun σ => do pure (← bumpOp σ op l).1

noncomputable def assignIncDec {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec)
    (l : OpLoc C Γ p) : Step C Γ Γ := fun σ => do
  let (o, v) ← bumpOp σ op l
  pure ⟨o.st.setLocal i v, o.ext⟩

noncomputable def push {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E)) :
    Step C Γ Γ := fun σ => do
  let ref ← path σ b
  let x ← match v with
    | none => pure none
    | some r => do pure (some (← source σ r).strip)
  if σ.storage.full ref then atRef ref (.error .exhausted) else
  let st ← Audit.push σ.storage ref (fun slot => some (x.getD slot))
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

noncomputable def assignLocalPush {p : PrimTy} (i : Idx Γ (.val p))
    (b : SPath C Γ (.array (.prim p))) : Step C Γ Γ := fun σ => do
  let o ← push b none σ
  pure ⟨o.st.setLocal i (PrimTy.dflt p), o.ext⟩

noncomputable def pushOpAssign {p : PrimTy} (op : BinOp) (b : SPath C Γ (.array (.prim p)))
    (rhs : Val C Γ p) : Step C Γ Γ := fun σ => do
  let v ← value σ rhs
  let ref ← path σ b
  if σ.storage.full ref then atRef ref (.error .exhausted) else
  let (st, i) ← Audit.place σ.storage ref
  atRef (ref.index (.arr .dyn) i) (opStoreT (σ.withStorage st) op (ref.index (.arr .dyn) i) v)

noncomputable def pushIncDec {p : PrimTy} (op : IncDec) (b : SPath C Γ (.array (.prim p))) :
    Step C Γ Γ := fun σ => do
  let ref ← path σ b
  if σ.storage.full ref then atRef ref (.error .exhausted) else
  let (st, i) ← Audit.place σ.storage ref
  pure (← atRef (ref.index (.arr .dyn) i) (bumpStoreT (σ.withStorage st) op
    (ref.index (.arr .dyn) i))).1

noncomputable def pop {E : Ty} (b : SPath C Γ (.array E)) : Step C Γ Γ := fun σ => do
  let ref ← path σ b
  let st ← Audit.arrayOp σ.storage ref true (TRes.ofOpt (σ.storage.pop E.isMapping ref))
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

noncomputable def transfer (r a : Val C Γ .uint) : Step C Γ Γ := fun σ => do
  let addr ← value σ r
  let amt ← value σ a
  if σ.canPay addr amt then pure ⟨σ.pay addr amt.1, List.prefix_refl _⟩
  else lift (.error .revert)

noncomputable def send (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) : Step C Γ Γ := fun σ => do
  let addr ← value σ r
  let amt ← value σ a
  pure (sendT σ pv addr amt)

noncomputable def declMem (R : RefTy) (init : Option (MRhs C Γ R))
    (hm : (Ty.ref R).mapFree = true) : Step C Γ (.mem R :: Γ) := fun σ => match init with
  | none =>
    let g := σ.allocDefaultG R hm
    pure ⟨g.st.push (t := .mem R) (some g.val), g.ext⟩
  | some r => do
    let g ← memoryRhs σ r
    pure ⟨g.st.push (t := .mem R) (some g.val), g.ext⟩

noncomputable def rebindMem {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) : Step C Γ Γ :=
  fun σ => do
    let g ← memoryRhs σ r
    pure ⟨g.st.setLocal i (some g.val), g.ext⟩

noncomputable def assignFromMem {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
    Step C Γ Γ := fun σ => do
  let m ← memoryPath σ p
  let ref ← loc σ l
  let st ← Audit.write σ.storage ref (MVal.copyMToSt σ.heap m)
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

noncomputable def assignMem {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) : Step C Γ Γ := fun σ => do
  let mv ← memorySource σ r
  let a ← memoryLoc σ l
  let hp ← lift (TRes.ofOpt (σ.heap.writeAddr a mv))
  pure ⟨σ.withHeap hp, List.prefix_refl _⟩

noncomputable def delete {T : Ty} (l : Loc C Γ T) : Step C Γ Γ := fun σ => do
  let ref ← loc σ l
  let st ← Audit.touch σ.storage ref (TRes.ofOpt (σ.storage.delete ref))
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

noncomputable def deleteMem {T : Ty} (p : MPath C Γ T) : Step C Γ Γ := fun σ => match p with
  | .var i hm => lift (TRun.deleteMem (.var i hm) σ)
  | .loc l => do lift (TRun.clearT σ (← memoryLoc σ l) l.mapFree)

noncomputable def assignNew {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint)
    (h : R.newArrOk = true) : Step C Γ Γ := fun σ =>
  let g := σ.copyStToMG (newArrT R (n.evalT σ) h) (RefTy.mapFree_of_newArrOk h)
  match l with
  | .store l => do
    let ref ← loc g.st l
    let st ← Audit.write g.st.storage ref (MVal.copyMToSt g.st.heap g.val)
    pure ⟨g.st.withStorage st, g.ext⟩
  | .mem l => do
    let a ← memoryLoc g.st l
    let hp ← lift (TRes.ofOpt (g.st.heap.writeAddr a g.val))
    pure ⟨g.st.withHeap hp, g.ext⟩

noncomputable def require (c : Val C Γ .bool) : Step C Γ Γ := fun σ => do
  let v ← value σ c
  if boolT v then pure ⟨σ, List.prefix_refl _⟩ else lift (.error .revert)

noncomputable def assert (c : Val C Γ .bool) : Step C Γ Γ := fun σ => do
  let v ← value σ c
  if boolT v then pure ⟨σ, List.prefix_refl _⟩ else lift (.error .panic)


noncomputable def ite {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (h₁ : Ext Γ Γ₁)
    (thn : Step C Γ Γ₁) (h₂ : Ext Γ Γ₂) (els : Step C Γ Γ₂) : Step C Γ Γ := fun σ => do
  let v ← value σ c
  if boolT v then (thn σ).map fun o => ⟨o.st.drop h₁, o.ext⟩
  else (els σ).map fun o => ⟨o.st.drop h₂, o.ext⟩

noncomputable def call {Γ' ps rs Γf : Ctx} (a : Args C Γ ps) (ret : CallRet Γ rs Γ')
    (hb : Ext (rs ++ ps) Γf) (body : Step C (rs ++ ps) Γf) : Step C Γ Γ' := fun σ => do
  let a ← args σ a
  let o₁ := ret.enterT (σ.withEnv a)
  let o ← body o₁.st
  let e : σ.H <+: o.st.H := o₁.ext.trans o.ext
  pure ⟨o.st.withEnv
    (ret.leaveT (TEnv.wk e Γ σ.env) (TEnv.take rs (TEnv.drop hb o.st.env))), e⟩

noncomputable def receiverOp {E : Ty} (op : ReceiverOp C Γ E)
    (b : SPath C Γ (.array E)) : Step C Γ Γ := match op with
  | .push v _ => push b v
  | .pop => pop b

noncomputable def callReceiver {ps Γf : Ctx} {E : Ty} (a : Args C Γ ps) (r : Var)
    (h : Ext ([.alias (.array E)] ++ ps) Γf)
    (body : Step C ([.alias (.array E)] ++ ps) Γf) (op : ReceiverOp C Γ E) :
    Step C Γ Γ := fun σ => do
  let o ← call a (.storage (.array E) r) h body σ
  let o' ← receiverOp (op.wk (.drop .refl)) (.alias .here) o.st
  pure ⟨o'.st.drop (.push .refl), o.ext.trans o'.ext⟩

noncomputable def pushAfterPrefix {Γv : Ctx} {E : Ty} (h : Ext Γ Γv) (code : Step C Γ Γv)
    (v : Src C Γv E) (ref : SRef C (.ref (.array E))) : Step C Γ Γ := fun σ => do
  let a ← code σ
  let v ← source a.st v
  if a.st.storage.full ref then atRef ref (.error .exhausted) else
  let st ← Audit.push a.st.storage ref (fun _ => some v.strip)
  pure ⟨(a.st.withStorage st).drop h, a.ext⟩

noncomputable def afterReceiverPrefix {Γv : Ctx} {E : Ty} (he : Ext Γ Γv)
    (code : Step C Γ Γv) (v : Src C Γv E) : Step C (.alias (.array E) :: Γ) Γ := fun σ => do
  let ref ← path σ (.alias .here)
  pushAfterPrefix he code v ref (σ.drop (.push .refl))

noncomputable def callReceiverPush {ps Γf Γv : Ctx} {E : Ty} (a : Args C Γ ps) (r : Var)
    (hb : Ext ([.alias (.array E)] ++ ps) Γf) (body : Step C ([.alias (.array E)] ++ ps) Γf)
    (he : Ext Γ Γv) (code : Step C Γ Γv) (v : Src C Γv E) : Step C Γ Γ := fun σ => do
  let a ← call a (.storage (.array E) r) hb body σ
  (afterReceiverPrefix he code v a.st).map fun b => ⟨b.st, a.ext.trans b.ext⟩

noncomputable def tryCall {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} (ec : ExtCall C Γ) (rets : Binders ρ)
    (h₁ : Ext (ρ ++ Γ) Γ₁) (ok : Step C (ρ ++ Γ) Γ₁)
    (h₂ : Ext Γ Γ₂) (err : Step C Γ Γ₂) (code : CodeBinder κ)
    (h₃ : Ext (κ ++ Γ) Γ₃) (pnc : Step C (κ ++ Γ) Γ₃)
    (h₄ : Ext Γ Γ₄) (other : Step C Γ Γ₄) (sargs : Args C Γ ps)
    (hs : Ext (ρ ++ ps) Γf) (sbody : Step C (ρ ++ ps) Γf) (self : Bool) : Step C Γ Γ := fun σ =>
  if (ec.addr.evalT σ).1 = 0 then lift (.error .revert) else
  if self && decide ((ec.addr.evalT σ).1 = σ.tx.selfAddress.1) then
    Audit.follow (call sargs (.rets rets.toRet) hs sbody σ) fun res => match res with
    | .ok o => (ok o.st).map fun o' =>
      ⟨o'.st.drop ((Ext.append Γ ρ).trans h₁), o.ext.trans o'.ext⟩
    | .error .revert => (other σ).map fun o => ⟨o.st.drop h₄, o.ext⟩
    | .error (.revertWith d) =>
      match Semantics.decodeError d with
      | some _ => (err σ).map fun o => ⟨o.st.drop h₂, o.ext⟩
      | none => match Semantics.decodePanic d with
        | some c => (pnc (σ.withEnv (TEnv.append κ (code.decodeT (H := σ.H) c) σ.env))).map
            fun o => ⟨o.st.drop ((Ext.append Γ κ).trans h₃), o.ext⟩
        | none => (other σ).map fun o => ⟨o.st.drop h₄, o.ext⟩
    | .error .panic =>
      (pnc (σ.withEnv (TEnv.append κ (code.decodeT (H := σ.H) (TRun.selfPanicCode ec σ)) σ.env))).map
        fun o => ⟨o.st.drop ((Ext.append Γ κ).trans h₃), o.ext⟩
    | .error e => lift (.error e)
  else match lookupBy (ec.keyT σ) σ.tx.ext with
  | none => lift (.error .revert)
  | some (.ok vs) => do
    let (r, _) ← lift (rets.decodeT (H := σ.H) vs)
    (ok (σ.withEnv (TEnv.append ρ r σ.env))).map fun o =>
      ⟨o.st.drop ((Ext.append Γ ρ).trans h₁), o.ext⟩
  | some (.error _) => (err σ).map fun o => ⟨o.st.drop h₂, o.ext⟩
  | some (.panic c) =>
    (pnc (σ.withEnv (TEnv.append κ (code.decodeT (H := σ.H) c) σ.env))).map
      fun o => ⟨o.st.drop ((Ext.append Γ κ).trans h₃), o.ext⟩
  | some (.other _) => (other σ).map fun o => ⟨o.st.drop h₄, o.ext⟩

/-- Finite observed loop prefixes use exactly the existing loop-fuel convention. -/
def iterate (body : α → Audit α) (cond : α → Audit Bool) : Nat → α → Audit α
  | 0, _ => lift (.error .diverge)
  | n + 1, σ => do
    let b ← cond σ
    if b then iterate body cond n (← body σ) else pure σ

noncomputable def loop {Γ₁ : Ctx} (n : Nat) (c : Val C Γ .bool) (h : Ext Γ Γ₁)
    (body : Step C Γ Γ₁) : Step C Γ Γ := fun σ => iterate
  (fun o : Out C σ.H Γ => (body o.st).map fun o' => ⟨o'.st.drop h, o.ext.trans o'.ext⟩)
  (fun o => value o.st c) n ⟨σ, List.prefix_refl _⟩

def block {Γ₁ : Ctx} (h : Ext Γ Γ₁) (body : Step C Γ Γ₁) : Step C Γ Γ := fun σ =>
  (body σ).map fun o => ⟨o.st.drop h, o.ext⟩

def seq {Γ₁ Γ₂ : Ctx} (s : Step C Γ Γ₁) (p : Step C Γ₁ Γ₂) : Step C Γ Γ₂ := fun σ => do
  let o ← s σ
  (p o.st).map fun o' => ⟨o'.st, o.ext.trans o'.ext⟩

def nil : Step C Γ Γ := fun σ => pure ⟨σ, List.prefix_refl _⟩

noncomputable def revPart (σ : State C Γ) : RevPart C Γ → Audit (List UInt8)
  | .word v => do
    let x ← value σ v
    pure (Semantics.wordBytes (PrimTy.toWord x).1.toNat)
  | .bytes bs => lift (RevPart.evalT σ (.bytes bs))
  | .sel sig => ⟨RevPart.evalT σ (.sel sig), ⟨[], [sig.toUTF8.data.toList]⟩⟩
  | .mem kind src => lift (RevPart.evalT σ (.mem kind src))

noncomputable def revertData (d : List (RevPart C Γ)) : Step C Γ Γ := fun σ => do
  let bs ← d.mapM (revPart σ)
  lift (.error (THalt.ofData bs.flatten))

noncomputable def litWrites {Γ₁ : Ctx} : List UInt8 → Nat →
    Step C (.mem bytesR :: Γ) Γ₁ → Step C (.mem bytesR :: Γ) Γ₁
  | [], _, k => k
  | b :: bs, i, k => if hi : i < 2 ^ 256 then
      seq (assignMem (litLoc i hi) (litSrc b)) (litWrites bs (i + 1) k)
    else k

noncomputable def litBytes {Γ₁ : Ctx} (bs : List UInt8)
    (k : Step C (.mem bytesR :: Γ) Γ₁) : Step C Γ Γ₁ :=
  if hn : bs.length < 2 ^ 256 then
    seq (declMem bytesR (some (.newArr (.lit (bs.length : Int) (PrimTy.inRange_uint_of_lt hn)) rfl)) rfl)
      (litWrites bs 0 k)
  else seq (declMem bytesR none rfl) k

noncomputable def catchBytes {ρ ps Γf : Ctx} (ec : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (hs : Ext (ρ ++ ps) Γf) (sbody : Step C (ρ ++ ps) Γf)
    (self : Bool) (σ : State C Γ) : Audit (List UInt8) :=
  if (ec.addr.evalT σ).1 = 0 then lift (.error .revert) else
  if self && decide ((ec.addr.evalT σ).1 = σ.tx.selfAddress.1) then
    Audit.follow (call sargs (.rets rets.toRet) hs sbody σ) fun res => match res with
    | .ok _ => lift (.error .revert)
    | .error .revert => pure []
    | .error (.revertWith d) => pure d
    | .error .panic => pure (Semantics.encodePanic (TRun.selfPanicCode ec σ).1.toNat)
    | .error e => lift (.error e)
  else lift (TRun.catchBytes ec rets sargs hs (fun σ => (sbody σ).result) self σ)

noncomputable def catchData {ρ ps Γf Γ₁ : Ctx} (ec : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (hs : Ext (ρ ++ ps) Γf) (sbody : Step C (ρ ++ ps) Γf)
    (self : Bool) (kind : CatchKind) (h₁ : Ext (.mem bytesR :: Γ) Γ₁)
    (body : Step C (.mem bytesR :: Γ) Γ₁) : Step C Γ Γ := fun σ => do
  let d ← catchBytes ec rets sargs hs sbody self σ
  match kind.decode d with
  | none => lift (.error .revert)
  | some bs => (litBytes bs body σ).map fun o => ⟨o.st.drop ((Ext.push .refl).trans h₁), o.ext⟩


def project {Γ Δ : Ctx} (s : Step C Γ Δ) : TStep C Γ Δ := fun σ => (s σ).result

theorem iterate_result (body : α → Audit α) (cond : α → Audit Bool) (n : Nat) (σ : α) :
    (iterate body cond n σ).result =
      TLoop.runF (fun x => (body x).result) (fun x => (cond x).result) n σ := by
  induction n generalizing σ with
  | zero => rfl
  | succ n ih =>
    simp only [iterate, Audit.result_bind]
    cases hc : (cond σ).result with
    | error e => simp only [hc, Solidity.error_bind, TLoop.runF, TLoop.iterN, TLoop.step]
    | ok b =>
      cases b with
      | false =>
        simp only [hc, Solidity.ok_bind, Bool.false_eq_true, ↓reduceIte,
          Audit.result_pure, TLoop.runF, TLoop.iterN, TLoop.step]
        rfl
      | true =>
        simp only [Solidity.ok_bind, ↓reduceIte, Audit.result_bind, ih]
        cases hb : (body σ).result <;>
          simp only [hb, Solidity.ok_bind, Solidity.error_bind, TLoop.runF,
            TLoop.iterN, TLoop.step, hc]

theorem assign_result {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) (σ : State C Γ) :
    (assign l r σ).result = TRun.assign l r σ := by
  simp only [assign, TRun.assign, Audit.result_bind, Audit.result_pure,
    Audit.result_write,
    source_result, loc_result]

theorem rebind_result {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R) (σ : State C Γ) :
    (rebind i r σ).result = TRun.rebind i r σ := by
  simp only [rebind, TRun.rebind, Audit.result_bind, Audit.result_pure,
    aliasRhs_result]

theorem assignLocal_result {p : PrimTy} (i : Idx Γ (.val p)) (r : Val C Γ p) (σ : State C Γ) :
    (assignLocal i r σ).result = TRun.assignLocal i r σ := by
  simp only [assignLocal, TRun.assignLocal, Audit.result_bind, Audit.result_pure,
    value_result]

theorem declLocal_result (p : PrimTy) (init : Option (Val C Γ p)) (σ : State C Γ) :
    (declLocal p init σ).result = TRun.declLocal p init σ := by
  cases init <;>
  simp only [declLocal, TRun.declLocal, Audit.result_bind, Audit.result_pure,
    value_result]

theorem declStorage_result (R : RefTy) (init : Option (ARhs C Γ R)) (σ : State C Γ) :
    (declStorage R init σ).result = TRun.declStorage R init σ := by
  cases init <;>
  simp only [declStorage, TRun.declStorage, Audit.result_bind, Audit.result_pure,
    aliasRhs_result]

theorem opAssign_result {p : PrimTy} (op : BinOp) (l : OpLoc C Γ p) (r : Val C Γ p) (σ : State C Γ) :
    (opAssign op l r σ).result = TRun.opAssign op l r σ := by
  simp only [opAssign, TRun.opAssign, Audit.result_bind,
    value_result,
    storeOp_result]

theorem incDec_result {p : PrimTy} (op : IncDec) (l : OpLoc C Γ p) (σ : State C Γ) :
    (incDec op l σ).result = TRun.incDec op l σ := by
  simp only [incDec, TRun.incDec, Audit.result_bind, Audit.result_pure,
    bumpOp_result]

theorem assignIncDec_result {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec)
    (l : OpLoc C Γ p) (σ : State C Γ) :
    (assignIncDec i op l σ).result = TRun.assignIncDec i op l σ := by
  simp only [assignIncDec, TRun.assignIncDec, Audit.result_bind, Audit.result_pure,
    bumpOp_result]

theorem push_result {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E)) (σ : State C Γ) :
    (push b v σ).result = TRun.push b v σ := by
  cases v <;>
  simp only [push, TRun.push, Audit.result_bind, Audit.result_pure,
    Audit.result_atRef,
    Audit.result_push, source_result, path_result,
    apply_ite Audit.result]

theorem assignLocalPush_result {p : PrimTy} (i : Idx Γ (.val p))
    (b : SPath C Γ (.array (.prim p))) (σ : State C Γ) :
    (assignLocalPush i b σ).result = TRun.assignLocalPush i b σ := by
  simp only [assignLocalPush, TRun.assignLocalPush, push_result, Audit.result_bind, Audit.result_pure]

theorem pushOpAssign_result {p : PrimTy} (op : BinOp) (b : SPath C Γ (.array (.prim p)))
    (rhs : Val C Γ p) (σ : State C Γ) :
    (pushOpAssign op b rhs σ).result = TRun.pushOpAssign op b rhs σ := by
  simp only [pushOpAssign, TRun.pushOpAssign, Audit.result_bind,
    Audit.result_atRef,
    Audit.result_place, value_result, path_result,
    apply_ite Audit.result]

theorem pushIncDec_result {p : PrimTy} (op : IncDec) (b : SPath C Γ (.array (.prim p))) (σ : State C Γ) :
    (pushIncDec op b σ).result = TRun.pushIncDec op b σ := by
  simp only [pushIncDec, TRun.pushIncDec, Audit.result_bind, Audit.result_pure,
    Audit.result_atRef,
    Audit.result_place, path_result,
    apply_ite Audit.result]

theorem pop_result {E : Ty} (b : SPath C Γ (.array E)) (σ : State C Γ) :
    (pop b σ).result = TRun.pop b σ := by
  simp only [pop, TRun.pop, Audit.result_bind, Audit.result_pure,
    Audit.result_arrayOp, path_result]

theorem transfer_result (r a : Val C Γ .uint) (σ : State C Γ) :
    (transfer r a σ).result = TRun.transfer r a σ := by
  simp only [transfer, TRun.transfer, Audit.result_bind, Audit.result_pure,
    Audit.result_lift,
    value_result,
    apply_ite Audit.result]
  rfl

theorem send_result (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) (σ : State C Γ) :
    (send pv r a σ).result = TRun.send pv r a σ := by
  simp only [send, TRun.send, Audit.result_bind, Audit.result_pure,
    value_result]

theorem declMem_result (R : RefTy) (init : Option (MRhs C Γ R))
    (hm : (Ty.ref R).mapFree = true) (σ : State C Γ) :
    (declMem R init hm σ).result = TRun.declMem R init hm σ := by
  cases init <;>
  simp only [declMem, TRun.declMem, Audit.result_bind, Audit.result_pure,
    memoryRhs_result]

theorem rebindMem_result {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) (σ : State C Γ) :
    (rebindMem i r σ).result = TRun.rebindMem i r σ := by
  simp only [rebindMem, TRun.rebindMem, Audit.result_bind, Audit.result_pure,
    memoryRhs_result]

theorem assignFromMem_result {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) (σ : State C Γ) :
    (assignFromMem l p σ).result = TRun.assignFromMem l p σ := by
  simp only [assignFromMem, TRun.assignFromMem, Audit.result_bind, Audit.result_pure,
    Audit.result_write,
    loc_result,
    memoryPath_result]

theorem assignMem_result {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) (σ : State C Γ) :
    (assignMem l r σ).result = TRun.assignMem l r σ := by
  simp only [assignMem, TRun.assignMem, Audit.result_bind, Audit.result_pure,
    Audit.result_lift,
    memorySource_result, memoryLoc_result]

theorem delete_result {T : Ty} (l : Loc C Γ T) (σ : State C Γ) :
    (delete l σ).result = TRun.delete l σ := by
  simp only [delete, TRun.delete, Audit.result_bind, Audit.result_pure,
    Audit.result_touch, loc_result]

theorem deleteMem_result {T : Ty} (p : MPath C Γ T) (σ : State C Γ) :
    (deleteMem p σ).result = TRun.deleteMem p σ := by
  cases p <;>
  simp only [deleteMem, TRun.deleteMem, Audit.result_bind,
    Audit.result_lift,
    memoryLoc_result]

theorem assignNew_result {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint)
    (h : R.newArrOk = true) (σ : State C Γ) :
    (assignNew l n h σ).result = TRun.assignNew l n h σ := by
  cases l <;>
  simp only [assignNew, TRun.assignNew, Audit.result_bind, Audit.result_pure,
    Audit.result_lift, Audit.result_write,
    loc_result,
    memoryLoc_result]

theorem require_result (c : Val C Γ .bool) (σ : State C Γ) :
    (require c σ).result = TRun.require c σ := by
  simp only [require, TRun.require, Audit.result_bind, Audit.result_pure,
    Audit.result_lift,
    value_result,
    apply_ite Audit.result]

theorem assert_result (c : Val C Γ .bool) (σ : State C Γ) :
    (assert c σ).result = TRun.assert c σ := by
  simp only [assert, TRun.assert, Audit.result_bind, Audit.result_pure,
    Audit.result_lift,
    value_result,
    apply_ite Audit.result]

theorem ite_result {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (h₁ : Ext Γ Γ₁)
    (thn : Step C Γ Γ₁) (h₂ : Ext Γ Γ₂) (els : Step C Γ Γ₂) (σ : State C Γ) :
    (ite c h₁ thn h₂ els σ).result = TRun.ite c h₁ (project thn) h₂ (project els) σ := by
  simp only [ite, TRun.ite, Audit.result_bind, Audit.result_map_direct, value_result, apply_ite Audit.result, project]

theorem call_result {Γ' ps rs Γf : Ctx} (a : Args C Γ ps) (ret : CallRet Γ rs Γ')
    (hb : Ext (rs ++ ps) Γf) (body : Step C (rs ++ ps) Γf) (σ : State C Γ) :
    (call a ret hb body σ).result = TRun.call a ret hb (project body) σ := by
  simp only [call, TRun.call, Audit.result_bind, Audit.result_pure, args_result, project]

theorem receiverOp_result {E : Ty} (op : ReceiverOp C Γ E)
    (b : SPath C Γ (.array E)) (σ : State C Γ) :
    (receiverOp op b σ).result = TRun.receiverOp op b σ := by
  cases op <;>
  simp only [receiverOp, TRun.receiverOp, push_result, pop_result]

theorem callReceiver_result {ps Γf : Ctx} {E : Ty} (a : Args C Γ ps) (r : Var)
    (h : Ext ([.alias (.array E)] ++ ps) Γf)
    (body : Step C ([.alias (.array E)] ++ ps) Γf) (op : ReceiverOp C Γ E) (σ : State C Γ) :
    (callReceiver a r h body op σ).result = TRun.callReceiver a r h (project body) op σ := by
  simp only [callReceiver, TRun.callReceiver, Audit.result_bind, Audit.result_pure, call_result, receiverOp_result]

theorem pushAfterPrefix_result {Γv : Ctx} {E : Ty} (h : Ext Γ Γv) (code : Step C Γ Γv)
    (v : Src C Γv E) (ref : SRef C (.ref (.array E))) (σ : State C Γ) :
    (pushAfterPrefix h code v ref σ).result = TRun.pushAfterPrefix h (project code) v ref σ := by
  simp only [pushAfterPrefix, TRun.pushAfterPrefix, Audit.result_bind, Audit.result_pure, Audit.result_atRef, Audit.result_push, source_result, apply_ite Audit.result, project]

theorem afterReceiverPrefix_result {Γv : Ctx} {E : Ty} (he : Ext Γ Γv)
    (code : Step C Γ Γv) (v : Src C Γv E) (σ : State C (.alias (.array E) :: Γ)) :
    (afterReceiverPrefix he code v σ).result = TRun.afterReceiverPrefix he (project code) v σ := by
  simp only [afterReceiverPrefix, TRun.afterReceiverPrefix, Audit.result_bind, path_result, pushAfterPrefix_result]

theorem callReceiverPush_result {ps Γf Γv : Ctx} {E : Ty} (a : Args C Γ ps) (r : Var)
    (hb : Ext ([.alias (.array E)] ++ ps) Γf) (body : Step C ([.alias (.array E)] ++ ps) Γf)
    (he : Ext Γ Γv) (code : Step C Γ Γv) (v : Src C Γv E) (σ : State C Γ) :
    (callReceiverPush a r hb body he code v σ).result = TRun.callReceiverPush a r hb (project body) he (project code) v σ := by
  simp only [callReceiverPush, TRun.callReceiverPush, Audit.result_bind, Audit.result_map_direct, call_result, afterReceiverPrefix_result]

theorem tryCall_result {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} (ec : ExtCall C Γ) (rets : Binders ρ)
    (h₁ : Ext (ρ ++ Γ) Γ₁) (ok : Step C (ρ ++ Γ) Γ₁)
    (h₂ : Ext Γ Γ₂) (err : Step C Γ Γ₂) (code : CodeBinder κ)
    (h₃ : Ext (κ ++ Γ) Γ₃) (pnc : Step C (κ ++ Γ) Γ₃)
    (h₄ : Ext Γ Γ₄) (other : Step C Γ Γ₄) (sargs : Args C Γ ps)
    (hs : Ext (ρ ++ ps) Γf) (sbody : Step C (ρ ++ ps) Γf) (self : Bool) (σ : State C Γ) :
    (tryCall ec rets h₁ ok h₂ err code h₃ pnc h₄ other sargs hs sbody self σ).result = TRun.tryCall ec rets h₁ (project ok) h₂ (project err) code h₃ (project pnc) h₄ (project other) sargs hs (project sbody) self σ := by
  simp only [tryCall, TRun.tryCall, Audit.result_lift, Audit.result_follow, apply_ite Audit.result, call_result, project]
  all_goals
    repeat first | simp_all only [Audit.result_map_direct, Audit.result_lift, Audit.result_bind] | split

theorem loop_result {Γ₁ : Ctx} (n : Nat) (c : Val C Γ .bool) (h : Ext Γ Γ₁)
    (body : Step C Γ Γ₁) (σ : State C Γ) :
    (loop n c h body σ).result = TRun.loopF n c h (project body) σ := by
  simp only [loop, TRun.loopF, Audit.result_map_direct, value_result, iterate_result, project]

theorem block_result {Γ₁ : Ctx} (h : Ext Γ Γ₁) (body : Step C Γ Γ₁) (σ : State C Γ) :
    (block h body σ).result = TRun.block h (project body) σ := by
  simp only [block, TRun.block, Audit.result_map_direct, project]

theorem seq_result {Γ₁ Γ₂ : Ctx} (s : Step C Γ Γ₁) (p : Step C Γ₁ Γ₂) (σ : State C Γ) :
    (seq s p σ).result = TRun.seq (project s) (project p) σ := by
  simp only [seq, TRun.seq, Audit.result_bind, Audit.result_map_direct, project]
  cases (s σ).result <;> rfl

theorem nil_result (σ : State C Γ) :
    (nil  σ).result = TRun.nil  σ := by
  simp only [nil, TRun.nil, Audit.result_pure]
  rfl


theorem revPart_result (σ : State C Γ) (p : RevPart C Γ) :
    (revPart σ p).result = p.evalT σ := by
  cases p <;> simp only [revPart, RevPart.evalT, Audit.result_bind,
    Audit.result_pure, Audit.result_lift, value_result]

theorem revertData_result (d : List (RevPart C Γ)) (σ : State C Γ) :
    (revertData d σ).result = TRun.revertData d σ := by
  simp only [revertData, TRun.revertData, Audit.result_bind, Audit.result_mapM,
    revPart_result, Audit.result_lift]

theorem litWrites_result {Γ₁ : Ctx} (bs : List UInt8) (i : Nat)
    (k : Step C (.mem bytesR :: Γ) Γ₁) (σ : State C (.mem bytesR :: Γ)) :
    (litWrites bs i k σ).result = TRun.litWritesT bs i (project k) σ := by
  induction bs generalizing i σ with
  | nil => rfl
  | cons b bs ih =>
    rw [litWrites, TRun.litWritesT]
    split
    · rw [seq_result]
      simp only [TRun.seq, project, assignMem_result, ih]
    · rfl

theorem litBytes_result {Γ₁ : Ctx} (bs : List UInt8)
    (k : Step C (.mem bytesR :: Γ) Γ₁) (σ : State C Γ) :
    (litBytes bs k σ).result = TRun.litBytesT bs (project k) σ := by
  unfold litBytes TRun.litBytesT
  split <;> rw [seq_result] <;>
    simp only [TRun.seq, project, declMem_result, litWrites_result]

theorem catchBytes_result {ρ ps Γf : Ctx} (ec : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (hs : Ext (ρ ++ ps) Γf) (sbody : Step C (ρ ++ ps) Γf)
    (self : Bool) (σ : State C Γ) :
    (catchBytes ec rets sargs hs sbody self σ).result =
      TRun.catchBytes ec rets sargs hs (project sbody) self σ := by
  unfold catchBytes
  split
  · simp only [Audit.result_lift, TRun.catchBytes, * , ↓reduceIte]
  · split
    · simp only [Audit.result_follow, call_result, TRun.catchBytes, *, ↓reduceIte]
      repeat first | simp_all only [Audit.result_lift, Audit.result_pure] | split | rfl
    · rfl

theorem catchData_result {ρ ps Γf Γ₁ : Ctx} (ec : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (hs : Ext (ρ ++ ps) Γf) (sbody : Step C (ρ ++ ps) Γf)
    (self : Bool) (kind : CatchKind) (h₁ : Ext (.mem bytesR :: Γ) Γ₁)
    (body : Step C (.mem bytesR :: Γ) Γ₁) (σ : State C Γ) :
    (catchData ec rets sargs hs sbody self kind h₁ body σ).result =
      TRun.catchData ec rets sargs hs (project sbody) self kind h₁ (project body) σ := by
  simp only [catchData, TRun.catchData, Audit.result_bind, catchBytes_result]
  congr 1
  funext d
  split <;> simp_all only [Audit.result_lift, Audit.result_map_direct, litBytes_result]

end Run

mutual

/-- The compiled typed run with fuel of a statement. -/
noncomputable def statement (n : Nat) : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Step C Γ Γ'
  | _, _, .assign l r => Run.assign l r
  | _, _, .rebind i r => Run.rebind i r
  | _, _, .assignLocal i r => Run.assignLocal i r
  | _, _, .declLocal p _ init => Run.declLocal p init
  | _, _, .declStorage R _ init => Run.declStorage R init
  | _, _, .opAssign op _ _ l r => Run.opAssign op l r
  | _, _, .incDec op _ l => Run.incDec op l
  | _, _, .pushOpAssign op _ _ b r => Run.pushOpAssign op b r
  | _, _, .pushIncDec op _ b => Run.pushIncDec op b
  | _, _, .assignIncDec i op _ l _ => Run.assignIncDec i op l
  | _, _, .assignLocalPush i b => Run.assignLocalPush i b
  | _, _, .push b v _ => Run.push b v
  | _, _, .pop b => Run.pop b
  | _, _, .transfer r a => Run.transfer r a
  | _, _, .send pv r a _ => Run.send pv r a
  | _, _, .declMem R _ init _ hm => Run.declMem R init hm
  | _, _, .rebindMem i r => Run.rebindMem i r
  | _, _, .assignFromMem l p => Run.assignFromMem l p
  | _, _, .assignMem l r => Run.assignMem l r
  | _, _, .delete l => Run.delete l
  | _, _, .deleteMem p _ => Run.deleteMem p
  | _, _, .assignNew l n' h => Run.assignNew l n' h
  | _, _, .ite c thn els => Run.ite c thn.ext (program n thn) els.ext (program n els)
  | _, _, .require c => Run.require c
  | _, _, .assert c => Run.assert c
  | _, _, .revert => fun _ => Audit.lift (.error .revert)
  | _, _, .assumeFalse => fun _ => Audit.lift (.error .exhausted)
  | _, _, .call _ args ret body => Run.call args ret body.ext (program n body)
  | _, _, .callReceiver _ args r body op =>
    Run.callReceiver args r body.ext (program n body) op
  | _, _, .callReceiverPush _ args r body code value =>
    Run.callReceiverPush args r body.ext (program n body)
      code.ext (program n code) value
  | _, _, .tryCall call rets ok err code pnc other sargs sbody self =>
    Run.tryCall call rets ok.ext (program n ok) err.ext (program n err) code pnc.ext
      (program n pnc) other.ext (program n other) sargs sbody.ext (program n sbody) self
  | _, _, .loop _ c body => Run.loop n c body.ext (program n body)
  | _, _, .block body => Run.block body.ext (program n body)
  | _, _, .callRec _ _ args ret body =>
    Run.call args ret (body ()).ext (program n (body ()))
  | _, _, .revertData d => Run.revertData d
  | _, _, .catchData c rets sargs sbody self kind _ body =>
    Run.catchData c rets sargs sbody.ext (program n sbody) self kind body.ext (program n body)

/-- The compiled typed run with fuel of a sequence. -/
noncomputable def program (n : Nat) : {Γ Γ' : Ctx} → Prog C Γ Γ' → Step C Γ Γ'
  | _, _, .nil => Run.nil
  | _, _, .cons s P => Run.seq (statement n s) (program n P)

end


mutual

theorem statement_project (n : Nat) : {Γ Δ : Ctx} → (s : Stmt C Γ Δ) →
    Run.project (statement n s) = s.runFC n
  | _, _, .assign l r => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.assign_result]
  | _, _, .rebind i r => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.rebind_result]
  | _, _, .assignLocal i r => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.assignLocal_result]
  | _, _, .declLocal p _ init => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.declLocal_result]
  | _, _, .declStorage R _ init => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.declStorage_result]
  | _, _, .opAssign op _ _ l r => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.opAssign_result]
  | _, _, .incDec op _ l => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.incDec_result]
  | _, _, .pushOpAssign op _ _ b r => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.pushOpAssign_result]
  | _, _, .pushIncDec op _ b => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.pushIncDec_result]
  | _, _, .assignIncDec i op _ l _ => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.assignIncDec_result]
  | _, _, .assignLocalPush i b => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.assignLocalPush_result]
  | _, _, .push b v _ => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.push_result]
  | _, _, .pop b => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.pop_result]
  | _, _, .transfer r a => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.transfer_result]
  | _, _, .send pv r a _ => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.send_result]
  | _, _, .declMem R _ init _ hm => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.declMem_result]
  | _, _, .rebindMem i r => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.rebindMem_result]
  | _, _, .assignFromMem l p => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.assignFromMem_result]
  | _, _, .assignMem l r => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.assignMem_result]
  | _, _, .delete l => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.delete_result]
  | _, _, .deleteMem p _ => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.deleteMem_result]
  | _, _, .assignNew l n' h => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.assignNew_result]
  | _, _, .ite c thn els => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.ite_result, program_project]
  | _, _, .require c => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.require_result]
  | _, _, .assert c => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.assert_result]
  | _, _, .revert => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Audit.result_lift]
  | _, _, .assumeFalse => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Audit.result_lift]
  | _, _, .call _ args ret body => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.call_result, program_project]
  | _, _, .callReceiver _ args r body op => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.callReceiver_result, program_project]
  | _, _, .callReceiverPush _ args r body code value => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.callReceiverPush_result, program_project]
  | _, _, .tryCall call rets ok err code pnc other sargs sbody self => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.tryCall_result, program_project]
  | _, _, .loop _ c body => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.loop_result, program_project]
  | _, _, .block body => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.block_result, program_project]
  | _, _, .callRec _ _ args ret body => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.call_result, program_project]
  | _, _, .revertData d => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.revertData_result]
  | _, _, .catchData c rets sargs sbody self kind _ body => by
    funext σ
    change (statement n _ σ).result = _
    rw [statement, Stmt.runFC]
    simp only [Run.catchData_result, program_project]

theorem program_project (n : Nat) : {Γ Δ : Ctx} → (p : Prog C Γ Δ) →
    Run.project (program n p) = p.runFC n
  | _, _, .nil => funext Run.nil_result
  | _, _, .cons s p => by
    funext σ
    change (program n (.cons s p) σ).result = _
    rw [program, Prog.runFC, Run.seq_result]
    rw [statement_project, program_project]

end

theorem program_result (n : Nat) {Γ Δ : Ctx} (p : Prog C Γ Δ) (σ : State C Γ) :
    (program n p σ).result = p.runFC n σ := congrFun (program_project n p) σ


/-- Every finite observation projects to the unchanged actual run, or reports
that its loop prefix has not yet finished. This includes actual error results. -/
theorem program_approx (n : Nat) {Γ Δ : Ctx} (p : Prog C Γ Δ) (σ : State C Γ) :
    TRes.Approx (program n p σ).result (p.run σ) := by
  rw [program_result, ← Prog.runF_eq]
  exact Prog.runF_approx n p σ

theorem program_agrees (n : Nat) {Γ Δ : Ctx} (p : Prog C Γ Δ) (σ : State C Γ)
    (finished : (program n p σ).result ≠ .error .diverge) :
    (program n p σ).result = p.run σ := (program_approx n p σ).eq finished

/-- A later halt cannot erase a previously reached statement's slot inputs. -/
theorem cons_slots {Γ Δ Ξ : Ctx} (n : Nat) (s : Stmt C Γ Δ) (p : Prog C Δ Ξ)
    (σ : State C Γ) {b : List UInt8} (h : b ∈ (statement n s σ).inputs.slots) :
    b ∈ (program n (.cons s p) σ).inputs.slots :=
  Audit.bind_slots_left _ _ h

end Observe


namespace Frame

open ContractWorld
variable {K : Type} [DecidableEq K] {contracts : K → Contract}

/-- The actual guarded callee frame, with observations retained independently
of its result. Only loop observation is bounded; entry and settlement are unchanged. -/
noncomputable def callFrame (n : Nat) (w : World contracts) {k : K} {α : Type}
    (r : Handle k) (entry : Entry (contracts k) α) (ctx : Context) :
    Audit (World contracts × State (contracts k) entry.locals) := do
  if w.isLibrary k || (ctx.isStatic && !(emptyBody entry.body)) then
    Audit.lift (.error .revert)
  else
    let st ← Audit.lift (TRes.ofOpt (w.storage? r))
    let σ ← Audit.lift (w.enter r.address ctx st entry.payable)
    let o ← Observe.program n entry.body σ
    let next ← Audit.lift (w.finish r.address o.st)
    pure (next, o.st)

theorem callFrame_approx (n : Nat) (w : World contracts) {k : K} {α : Type}
    (r : Handle k) (entry : Entry (contracts k) α) (ctx : Context) :
    TRes.Approx (callFrame n w r entry ctx).result (w.callFrame r entry ctx) := by
  unfold callFrame World.callFrame
  split
  · exact .refl _
  · simp only [Audit.result_bind, Audit.result_lift, Audit.result_pure]
    apply TRes.Approx.bind (.refl _)
    intro st
    apply TRes.Approx.bind (.refl _)
    intro σ
    apply TRes.Approx.bind (Observe.program_approx n entry.body σ)
    intro o
    exact .refl _

noncomputable def call (n : Nat) (w : World contracts) {k : K} {α : Type}
    (r : Handle k) (entry : Entry (contracts k) α) (ctx : Context) :
    Audit (World contracts × α) := do
  let (next, σ) ← callFrame n w r entry ctx
  let result ← Audit.lift (entry.result σ)
  pure (next, result)

theorem call_approx (n : Nat) (w : World contracts) {k : K} {α : Type}
    (r : Handle k) (entry : Entry (contracts k) α) (ctx : Context) :
    TRes.Approx (call n w r entry ctx).result (w.call r entry ctx) := by
  simp only [call, World.call, Audit.result_bind, Audit.result_lift, Audit.result_pure]
  exact TRes.Approx.bind (callFrame_approx n w r entry ctx) (fun _ => .refl _)


noncomputable def create (n : Nat) (w : World contracts) (k : K) (self : Address)
    (ctor : Prog (contracts k) [] []) (ctx : Context) : Audit (World contracts × Handle k) :=
  if w.isLibrary k then Audit.lift (.error .revert) else do
    if (w.accounts self).isSome || decide (self = ctx.sender) || ctx.isStatic then
      Audit.lift (.error .revert)
    else
      let σ ← Audit.lift (w.enter self ctx (Storage.init (contracts k))
        (((contracts k).ctor.map (·.payable)).getD false))
      let o ← Observe.program n ctor σ
      let next ← Audit.lift (w.finish self o.st)
      pure (next, ⟨self⟩)

omit [DecidableEq K] in
theorem create_approx (n : Nat) (w : World contracts) (k : K) (self : Address)
    (ctor : Prog (contracts k) [] []) (ctx : Context) :
    TRes.Approx (create n w k self ctor ctx).result (w.create k self ctor ctx) := by
  unfold create World.create
  split
  · exact .refl _
  · change TRes.Approx _ (if (w.accounts self).isSome || decide (self = ctx.sender) || ctx.isStatic
      then .error .revert else do
        let σ ← w.enter self ctx (Storage.init (contracts k))
          (((contracts k).ctor.map (·.payable)).getD false)
        let o ← ctor.run σ
        let next ← w.finish self o.st
        pure (next, (⟨self⟩ : Handle k)))
    split
    · exact .refl _
    · simp only [Audit.result_bind, Audit.result_lift, Audit.result_pure]
      apply TRes.Approx.bind (.refl _)
      intro σ
      apply TRes.Approx.bind (Observe.program_approx n ctor σ)
      intro o
      exact .refl _

/-- Atomic rollback changes the returned world, never the observed inputs. -/
def atomic (w : World contracts) (a : Audit (World contracts × α)) :
    (World contracts × TRes α) × Inputs := (ContractWorld.atomic w a.result, a.inputs)

omit [DecidableEq K] in
theorem atomic_failed (w : World contracts) (a : Audit (World contracts × α))
    {e : THalt} (h : a.result = .error e) :
    atomic w a = ((w, .error e), a.inputs) := by
  simp only [atomic, h, ContractWorld.atomic]

end Frame

end Solidity.Semantics.IntrinsicStorage
