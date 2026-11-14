import Solidity.Semantics.Panic.Origins
import Solidity.Semantics.Panic.Result

namespace Solidity.Semantics.Panic

open Solidity.Panic

/-- Translate the original intrinsic sites into the result interface's codes. -/
def siteCode : Site → Code
  | .assertion => .assert
  | .arithmetic => .arithmetic
  | .zeroDivisor => .divZero
  | .enumConversion => .enumConv
  | .storageEncoding => .storageEncoding
  | .emptyPop => .popEmpty
  | .bounds => .index
  | .allocation => .alloc
  | .zeroInternalFunction => .zeroFn

theorem siteCode_code (site : Site) : (siteCode site).code = site.code := by
  cases site <;> rfl

/-- The finite family of result types of intrinsic producers. This keeps
heterogeneous typed operands in Type without erasing them into an existential proof. -/
inductive ValueKind where
  | unit | nat | prim (p : PrimTy) | storage (C : Contract) | memory (H : HTy) (E : Ty)

def ValueKind.Denote : ValueKind → Type
  | .unit => Unit
  | .nat => Nat
  | .prim p => p.Denote
  | .storage C => Storage C
  | .memory H E => MVal H E

/-- Retain the actual typed producer, operands and failed-branch evidence. -/
structure Raised where
  kind : ValueKind
  producer : Producer kind.Denote
  site : Site
  failed : Origin producer site

def Raised.ofOrigin {α : Type} (p : Producer α) (site : Site) (h : Origin p site) : Raised :=
  match p with
  | .assertion b => ⟨.unit, .assertion b, site, h⟩
  | .binary op ty accepts x y => ⟨.prim (op.op.ret ty), .binary op ty accepts x y, site, h⟩
  | .modular op x y k => ⟨.prim .uint, .modular op x y k, site, h⟩
  | .neg x => ⟨.prim .int, .neg x, site, h⟩
  | .enumConversion n x => ⟨.prim .uint, .enumConversion n x, site, h⟩
  | .storageEncoding word => ⟨.nat, .storageEncoding word, site, h⟩
  | .pop st keep ref => ⟨.storage _, .pop st keep ref, site, h⟩
  | .index hp ref array i => ⟨.memory _ _, .index hp ref array i, site, h⟩
  | .storageIndex st ref array i => ⟨.unit, .storageIndex st ref array i, site, h⟩
  | .allocation input used size => ⟨.nat, .allocation input used size, site, h⟩
  | .internalFunction tag => ⟨.prim .uint, .internalFunction tag, site, h⟩

abbrev EvalResult (α : Type) := Result Raised α

/-- Unclassified failures remain ordinary reverts. In particular this bridge
never guesses an intrinsic origin from a V1 halt or external revert bytes. -/
def evalProducer {α : Type} (producer : Producer α) : EvalResult α :=
  match h : producer.run with
  | .ok value => .ok value
  | .error none => .error .revert
  | .error (some site) =>
      .error (.intrinsic (siteCode site) (Raised.ofOrigin producer site h))

/-- Every typed origin raises its own code, retaining its failure witness. -/
theorem evalProducer_origin {α : Type} (producer : Producer α) (site : Site)
    (h : Origin producer site) :
    evalProducer producer = .error (.intrinsic (siteCode site) (Raised.ofOrigin producer site h)) := by
  unfold evalProducer
  split <;> rename_i he <;> have e := h.symm.trans he <;> cases e <;> rfl

theorem evalProducer_success {α : Type} (producer : Producer α) (value : α)
    (h : producer.run = .ok value) : evalProducer producer = .ok value := by
  unfold evalProducer
  split <;> rename_i he <;> have e := h.symm.trans he <;> cases e <;> rfl

theorem evalProducer_unclassified {α : Type} (producer : Producer α)
    (h : producer.run = .error none) : evalProducer producer = .error .revert := by
  unfold evalProducer
  split <;> rename_i he <;> have e := h.symm.trans he <;> cases e <;> rfl

/-- V1's assertion/allocation sites use panic; expression helpers use revert.
This classifier is local to these producers, never a whole-run erasure. -/
def producerV1 (_ : Code) (origin : Raised) : THalt :=
  match origin.site with
  | .assertion | .allocation => .panic
  | _ => .revert

/-- Local assertion behavior, including the successful unit value. -/
theorem assertion_project (value : Bool) :
    (evalProducer (.assertion value)).toV1With producerV1 =
      (if value then .ok () else .error .panic : TRes Unit) := by
  cases value <;> rfl

/-- A successful checked operator retains exactly the existing result. -/
theorem binary_success (op : Checked) (p : PrimTy)
    (h : op.op.accepts p = true) (x y : p.Denote) (value : (op.op.ret p).Denote)
    (success : op.op.evalT h x y = some value) :
    evalProducer (.binary op p h x y) = .ok value :=
  evalProducer_success _ _ (Solidity.Panic.binary_success op p h x y value success)


/-- Expression failures project locally to V1's ordinary revert. -/
def erase {α : Type} (result : EvalResult α) : TRes α :=
  result.toV1With (fun _ _ => .revert)

def ofOpt {α : Type} : Option α → EvalResult α
  | some value => .ok value
  | none => .error .revert

theorem erase_ofOpt {α : Type} (value : Option α) :
    erase (ofOpt value) = TRes.ofOpt value := by
  cases value <;> rfl

theorem erase_bind_congr {α β : Type} {x : EvalResult α} {y : TRes α}
    {f : α → EvalResult β} {g : α → TRes β}
    (h : erase x = y) (next : ∀ a, erase (f a) = g a) :
    erase (x >>= f) = (y >>= g) := by
  subst y
  rw [erase, Result.toV1With_bind]
  congr 1
  funext a
  exact next a

theorem erase_evalProducer {α : Type} (producer : Producer α) :
    erase (evalProducer producer) =
      match producer.run with
      | .ok value => .ok value
      | .error _ => .error .revert := by
  unfold evalProducer
  split <;> rename_i he <;> simp only [he, erase, Result.toV1With, Halt.toV1With]

theorem erase_checked {α : Type} (site : Option Site) (value : Option α) :
    (match checked site value with
      | .ok value => .ok value
      | .error _ => .error .revert : TRes α) = TRes.ofOpt value := by
  cases value <;> rfl

def binary (op : BinOp) {p : PrimTy} (h : op.accepts p = true) (x y : p.Denote) :
    EvalResult (op.ret p).Denote :=
  match op with
  | .add => evalProducer (.binary .add p h x y)
  | .sub => evalProducer (.binary .sub p h x y)
  | .mul => evalProducer (.binary .mul p h x y)
  | .pow => evalProducer (.binary .pow p h x y)
  | .div => evalProducer (.binary .div p h x y)
  | .mod => evalProducer (.binary .mod p h x y)
  | op => ofOpt (op.evalT h x y)

theorem binary_erase (op : BinOp) {p : PrimTy} (h : op.accepts p = true) (x y : p.Denote) :
    erase (binary op h x y) = TRes.ofOpt (op.evalT h x y) := by
  cases op <;> simp only [binary, erase_ofOpt, erase_evalProducer, Producer.run,
    erase_checked, Checked.op]

def unary (op : UnOp) {p : PrimTy} (h : op.accepts p = true) (x : p.Denote) :
    EvalResult (op.ret p).Denote :=
  match op, p with
  | .neg, .int => evalProducer (.neg x)
  | op, _ => ofOpt (op.evalT h x)

theorem unary_erase (op : UnOp) {p : PrimTy} (h : op.accepts p = true) (x : p.Denote) :
    erase (unary op h x) = TRes.ofOpt (op.evalT h x) := by
  cases op <;> cases p <;> simp only [unary, erase_ofOpt, erase_evalProducer,
    Producer.run, erase_checked]

def modular (op : ModOp) (x y k : PrimTy.uint.Denote) : EvalResult PrimTy.uint.Denote :=
  evalProducer (.modular op x y k)

theorem modular_erase (op : ModOp) (x y k : PrimTy.uint.Denote) :
    erase (modular op x y k) = TRes.ofOpt (op.evalT x y k) := by
  simp only [modular, erase_evalProducer, Producer.run, erase_checked]

variable {C : Contract} {Γ : Ctx}

def storageIndex {R : RefTy} {k : PrimTy} {V : Ty} (st : Storage C)
    (r : SRef C (.ref R)) (it : IndexTy R k V) (i : k.Denote) : EvalResult Unit :=
  match it with
  | .arr array => evalProducer (.storageIndex st r array i)
  | .map => ofOpt (st.checkIndex r .map i)

theorem storageIndex_erase {R : RefTy} {k : PrimTy} {V : Ty} (st : Storage C)
    (r : SRef C (.ref R)) (it : IndexTy R k V) (i : k.Denote) :
    erase (storageIndex st r it i) = TRes.ofOpt (st.checkIndex r it i) := by
  cases it with
  | map => exact erase_ofOpt _
  | arr array =>
    simp only [storageIndex, erase_evalProducer, Producer.run, Storage.checkIndex]
    cases st.find r with
    | none => rfl
    | some receiver => exact erase_checked _ _

def memoryRead {H : HTy} (hp : Heap H) {T : Ty} : MAddr H T → EvalResult (MVal H T)
  | .field r h => .ok (hp.field r h)
  | .index r a i => evalProducer (.index hp r a i)

theorem memoryRead_erase {H : HTy} (hp : Heap H) {T : Ty} (addr : MAddr H T) :
    erase (memoryRead hp addr) = TRes.ofOpt (hp.readAddr addr) := by
  cases addr with
  | field => rfl
  | index => simp only [memoryRead, erase_evalProducer, Producer.run, erase_checked,
      Heap.readAddr]


mutual

def path (σ : State C Γ) : {T : Ty} → SPath C Γ T → EvalResult (SRef C T)
  | _, .alias i => ofOpt (TEnv.get i σ.env)
  | _, .loc l => loc σ l

def loc (σ : State C Γ) : {T : Ty} → Loc C Γ T → EvalResult (SRef C T)
  | _, .root r h => .ok (SRef.ofRoot r h)
  | _, .field b _ h => do
    let r ← path σ b
    pure (r.field h)
  | _, .index it b i => do
    let r ← path σ b
    let k ← value σ i
    let _ ← storageIndex σ.storage r it k
    pure (r.index it k)

def mpath (σ : State C Γ) : {T : Ty} → MPath C Γ T → EvalResult (MVal σ.H T)
  | _, .var i _ => ofOpt (TEnv.get i σ.env)
  | _, .loc l => do memoryRead σ.heap (← mloc σ l)

def mloc (σ : State C Γ) : {T : Ty} → MLoc C Γ T → EvalResult (MAddr σ.H T)
  | _, .field b _ h => do
    let r ← mpath σ b
    pure (.field r h)
  | _, .index a b i => do
    let r ← mpath σ b
    let k ← value σ i
    pure (.index r a k)

def value (σ : State C Γ) : {p : PrimTy} → Val C Γ p → EvalResult p.Denote
  | _, .simple s => .ok (s.evalT σ)
  | _, .read l => do
    let r ← loc σ l
    let v ← ofOpt (σ.storage.find r)
    pure v.view
  | _, .binop op h hq a b => do
    let x ← value σ a
    match op.shortT x with
    | some y => pure (hq ▸ y)
    | none => do
      let y ← value σ b
      hq ▸ binary op h x y
  | _, .unop op h hq a => do
    let x ← value σ a
    hq ▸ unary op h x
  | _, .ternary c a b => do
    let test ← value σ c
    if boolT test then value σ a else value σ b
  | _, .readMem l => do memoryRead σ.heap (← mloc σ l)
  | _, .len b hp => do
    let r ← path σ b
    let n ← ofOpt (σ.storage.len r)
    pure (hp ▸ n)
  | _, .mlen b hp => do
    let r ← mpath σ b
    pure (hp ▸ σ.heap.lenU r)
  | _, .modular op a b k => do
    let x ← value σ a
    let y ← value σ b
    let m ← value σ k
    modular op x y m
  | _, .hash k b hp => do
    let r ← mpath σ b
    pure (hp ▸ σ.heap.hash k r)

end

mutual

theorem path_erase (σ : State C Γ) : {T : Ty} → (b : SPath C Γ T) →
    erase (path σ b) = b.resolveT σ
  | _, .alias i => by
      simp only [path, SPath.resolveT, erase_ofOpt, TRes.ofOpt]
      cases TEnv.get i σ.env <;> rfl
  | _, .loc l => loc_erase σ l

theorem loc_erase (σ : State C Γ) : {T : Ty} → (l : Loc C Γ T) →
    erase (loc σ l) = l.resolveT σ
  | _, .root .. => rfl
  | _, .field b _ _ => erase_bind_congr (path_erase σ b) fun _ => rfl
  | _, .index _ b i => erase_bind_congr (path_erase σ b) fun _ =>
      erase_bind_congr (value_erase σ i) fun _ =>
        erase_bind_congr (storageIndex_erase _ _ _ _) fun _ => rfl

theorem mpath_erase (σ : State C Γ) : {T : Ty} → (b : MPath C Γ T) →
    erase (mpath σ b) = b.mvalT σ
  | _, .var i _ => by
      simp only [mpath, MPath.mvalT, erase_ofOpt, TRes.ofOpt]
      cases TEnv.get i σ.env <;> rfl
  | _, .loc l => erase_bind_congr (mloc_erase σ l) fun _ => memoryRead_erase _ _

theorem mloc_erase (σ : State C Γ) : {T : Ty} → (l : MLoc C Γ T) →
    erase (mloc σ l) = l.addrT σ
  | _, .field b _ _ => erase_bind_congr (mpath_erase σ b) fun _ => rfl
  | _, .index _ b i => erase_bind_congr (mpath_erase σ b) fun _ =>
      erase_bind_congr (value_erase σ i) fun _ => rfl

theorem value_erase (σ : State C Γ) : {p : PrimTy} → (v : Val C Γ p) →
    erase (value σ v) = v.evalT σ
  | _, .simple _ => rfl
  | _, .read l => erase_bind_congr (loc_erase σ l) fun _ =>
      erase_bind_congr (erase_ofOpt _) fun _ => rfl
  | _, .binop op _ hq a b => by
    subst hq
    refine erase_bind_congr (value_erase σ a) fun x => ?_
    cases op.shortT x with
    | some _ => rfl
    | none => exact erase_bind_congr (value_erase σ b) fun _ => binary_erase _ _ _ _
  | _, .unop _ _ hq a => by
    subst hq
    exact erase_bind_congr (value_erase σ a) fun _ => unary_erase _ _ _
  | _, .ternary c a b => erase_bind_congr (value_erase σ c) fun test => by
      cases test with
      | false => exact value_erase σ b
      | true => exact value_erase σ a
  | _, .readMem l => erase_bind_congr (mloc_erase σ l) fun _ => memoryRead_erase _ _
  | _, .len b _ => erase_bind_congr (path_erase σ b) fun _ =>
      erase_bind_congr (erase_ofOpt _) fun _ => rfl
  | _, .mlen b _ => erase_bind_congr (mpath_erase σ b) fun _ => rfl
  | _, .modular _ a b k => erase_bind_congr (value_erase σ a) fun _ =>
      erase_bind_congr (value_erase σ b) fun _ =>
        erase_bind_congr (value_erase σ k) fun _ => modular_erase _ _ _ _
  | _, .hash _ b _ => erase_bind_congr (mpath_erase σ b) fun _ => rfl

end

/-- Exact successful values can be recovered from the projection without
assuming any invariant on the state. -/
theorem value_of_ok (σ : State C Γ) {p : PrimTy} (v : Val C Γ p) (a : p.Denote)
    (h : v.evalT σ = .ok a) : value σ v = .ok a := by
  have he := value_erase σ v
  rw [h] at he
  cases hv : value σ v with
  | ok b => rw [hv] at he; cases he; rfl
  | error halt => rw [hv] at he; cases he

/-- Typed sources keep expression/path provenance while preserving V1 copies. -/
def source (σ : State C Γ) {T : Ty} : Src C Γ T → EvalResult (SVal T)
  | .val v => do pure (.prim (← value σ v))
  | .copy p _ => do
    let r ← path σ p
    ofOpt (σ.storage.find r)
  | .fixedCopy p shape _ => do
    let r ← path σ p
    let v ← ofOpt (σ.storage.find r)
    pure (shape.apply v)
  | .copyMem p => do pure (MVal.copyMToSt σ.heap (← mpath σ p))
  | .fixedCopyMem p shape => do
    pure (shape.apply (MVal.copyMToSt σ.heap (← mpath σ p)))

/-- Source evaluation projects to the complete V1 value, including copies. -/
theorem source_erase (σ : State C Γ) {T : Ty} : (src : Src C Γ T) →
    erase (source σ src) = src.valueT σ
  | .val v => erase_bind_congr (value_erase σ v) fun _ => rfl
  | .copy p _ => erase_bind_congr (path_erase σ p) fun _ => erase_ofOpt _
  | .fixedCopy p _ _ => erase_bind_congr (path_erase σ p) fun _ =>
      erase_bind_congr (erase_ofOpt _) fun _ => rfl
  | .copyMem p => erase_bind_congr (mpath_erase σ p) fun _ => rfl
  | .fixedCopyMem p _ => erase_bind_congr (mpath_erase σ p) fun _ => rfl

/-- A memory assignment source is evaluated before its target address. -/
def msource (σ : State C Γ) {T : Ty} : MSrc C Γ T → EvalResult (MVal σ.H T)
  | .val v => value σ v
  | .ref p => mpath σ p

theorem msource_erase (σ : State C Γ) {T : Ty} (src : MSrc C Γ T) :
    erase (msource σ src) = src.mvalT σ := by
  cases src with
  | val v => exact value_erase σ v
  | ref p => exact mpath_erase σ p



/-- The pop helper agrees even on missing paths and empty arrays. -/
theorem pop_erase {E : Ty} (st : Storage C) (keep : Bool)
    (ref : SRef C (.ref (.array E))) :
    erase (evalProducer (.pop st keep ref)) = TRes.ofOpt (st.pop keep ref) := by
  rw [erase_evalProducer]
  cases found : st.find ref with
  | none => simp only [Producer.run, Storage.pop, found]; rfl
  | some value =>
    simp only [Producer.run, found]
    by_cases empty : (SVal.view value).elems.toList.isEmpty = true
    · simp only [if_pos empty]
      have nil := List.isEmpty_iff.mp empty
      simp only [Storage.pop, found, bind, Option.bind, nil, List.reverse_nil, TRes.ofOpt]
    · simp only [if_neg empty]
      cases st.pop keep ref <;> rfl

/-- Allocation retains the existing ABI success value and panic failure. -/
theorem allocation_project (input : AbiEntry.Input) (used size : Nat) :
    (evalProducer (.allocation input used size)).toV1With producerV1 =
      (AbiEntry.alloc input used size).mapError (fun _ => THalt.panic) := by
  unfold AbiEntry.alloc
  split
  · apply congrArg (Result.toV1With producerV1)
      (evalProducer_success _ _ (by simp only [Producer.run, AbiEntry.alloc, if_pos ‹_›]))
  · rw [evalProducer_origin _ .allocation (by
      simp only [Origin, Producer.run, AbiEntry.alloc, if_neg ‹_›])]
    rfl

/-- An origin's runtime site is the same site its proof certifies. -/
theorem Raised.ofOrigin_site {α : Type} (p : Producer α) (site : Site)
    (h : Origin p site) : (Raised.ofOrigin p site h).site = site := by
  cases p <;> rfl

end Solidity.Semantics.Panic
