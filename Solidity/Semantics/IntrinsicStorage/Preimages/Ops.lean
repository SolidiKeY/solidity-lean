import Solidity.Semantics.IntrinsicStorage.Preimages.Frames
import Solidity.Semantics.RunFuel

/-! Audited storage operations and observers preserve actual results, including failures. -/
namespace Solidity.Semantics.IntrinsicStorage

open Solidity.Storage

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

end Observe

end Solidity.Semantics.IntrinsicStorage
