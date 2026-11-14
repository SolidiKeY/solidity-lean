import Solidity.Semantics.Panic.Run.Checked

namespace Solidity.Semantics.Panic

variable {C : Contract} {Γ : Ctx}

def arhs (σ : State C Γ) {R : RefTy} : ARhs C Γ R → EvalResult (Storage C × SRef C (.ref R))
  | .path p => do pure (σ.storage, ← path σ p)
  | .push b _ => do
    let r ← path σ b
    if σ.storage.full r then .error .exhausted else
    let (st, n) ← ofOpt (σ.storage.pushPlace r)
    pure (st, r.index (.arr .dyn) n)

/-- The object a memory right-hand side names, and the state its allocation
leaves. -/
def mrhs (σ : State C Γ) {R : RefTy} : MRhs C Γ R → EvalResult (Grew C Γ σ.H (HRef · R))
  | .alias p => do
    let r ← mpath σ p
    pure ⟨σ, List.prefix_refl _, r⟩
  | .copy p hm => do
    let r ← path σ p
    let sv ← ofOpt (σ.storage.find r)
    let g := σ.copyStToMG sv hm
    pure ⟨g.st, g.ext, g.val⟩
  | .newArr n h =>
    let g := σ.copyStToMG (newArrT R (n.evalT σ) h) (RefTy.mapFree_of_newArrOk h)
    .ok ⟨g.st, g.ext, g.val⟩

/-- `a ⊕= v` at a storage reference: read, apply, check, write back. -/
def opStore (σ : State C Γ) (op : BinOp) {p : PrimTy} (hp : p.isNumeric = true) (r : SRef C (.prim p)) (v : p.Denote) :
    EvalResult (Out C σ.H Γ) := do
  let old ← ofOpt (σ.storage.find r)
  let new ← compound op p hp (SVal.view old) v
  let st ← ofOpt (σ.storage.save r (.prim new))
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

/-- `a ⊕= v` at a memory address. -/
def opMem (σ : State C Γ) (op : BinOp) {p : PrimTy} (hp : p.isNumeric = true) (a : MAddr σ.H (.prim p)) (v : p.Denote) :
    EvalResult (Out C σ.H Γ) := do
  let old ← memoryRead σ.heap a
  let new ← compound op p hp old v
  let hp ← ofOpt (σ.heap.writeAddr a new)
  pure ⟨σ.withHeap hp, List.prefix_refl _⟩

/-- A compound assignment's write of `v` into its target. -/
def opLocStore (σ : State C Γ) (op : BinOp) : {p : PrimTy} → p.isNumeric = true → OpLoc C Γ p → p.Denote →
    EvalResult (Out C σ.H Γ)
  | p, hp, .local i, v => do
    let new ← compound op p hp (TEnv.get i σ.env) v
    pure ⟨σ.setLocal i new, List.prefix_refl _⟩
  | _, hp, .root r h, v => opStore σ op hp (SRef.ofRoot r h) v
  | _, hp, .field b f h, v => do opStore σ op hp (← loc σ (Loc.field b f h)) v
  | _, hp, .index it b i, v => do opStore σ op hp (← loc σ (Loc.index it b (.simple i))) v
  | _, hp, .mfield b f h, v => do opMem σ op hp (← mloc σ (MLoc.field b f h)) v
  | _, hp, .mindex a b i, v => do opMem σ op hp (← mloc σ (MLoc.index a b (.simple i))) v

/-- `x++` at a storage reference: the state, and the value. -/
def bumpStore (σ : State C Γ) (op : IncDec) {p : PrimTy} (hp : p.isNumeric = true) (r : SRef C (.prim p)) :
    EvalResult (Out C σ.H Γ × p.Denote) := do
  let old ← ofOpt (σ.storage.find r)
  let new ← bump op p hp (SVal.view old)
  let st ← ofOpt (σ.storage.save r (.prim new))
  pure (⟨σ.withStorage st, List.prefix_refl _⟩, if op.isPre then new else SVal.view old)

/-- `x++` at a memory address. -/
def bumpMem (σ : State C Γ) (op : IncDec) {p : PrimTy} (hp : p.isNumeric = true) (a : MAddr σ.H (.prim p)) :
    EvalResult (Out C σ.H Γ × p.Denote) := do
  let old ← memoryRead σ.heap a
  let new ← bump op p hp old
  let hp ← ofOpt (σ.heap.writeAddr a new)
  pure (⟨σ.withHeap hp, List.prefix_refl _⟩, if op.isPre then new else old)

/-- `l++`: the state it leaves, and its value. -/
def opLocBump (σ : State C Γ) (op : IncDec) : {p : PrimTy} → p.isNumeric = true → OpLoc C Γ p →
    EvalResult (Out C σ.H Γ × p.Denote)
  | p, hp, .local i => do
    let old : p.Denote := TEnv.get i σ.env
    let new ← bump op p hp old
    pure (⟨σ.setLocal i new, List.prefix_refl _⟩, if op.isPre then new else old)
  | _, hp, .root r h => bumpStore σ op hp (SRef.ofRoot r h)
  | _, hp, .field b f h => do bumpStore σ op hp (← loc σ (Loc.field b f h))
  | _, hp, .index it b i => do bumpStore σ op hp (← loc σ (Loc.index it b (.simple i)))
  | _, hp, .mfield b f h => do bumpMem σ op hp (← mloc σ (MLoc.field b f h))
  | _, hp, .mindex a b i => do bumpMem σ op hp (← mloc σ (MLoc.index a b (.simple i)))

/-- Validate an indexed destination with its actual heap before writing it. -/
def memoryWrite {H : HTy} (hp : Heap H) {T : Ty} (a : MAddr H T)
    (v : MVal H T) : EvalResult (Heap H) := do
  let _ ← memoryRead hp a
  ofOpt (hp.writeAddr a v)

namespace Run

def assign {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) : Step C Γ Γ := fun σ => do
  let sv ← source σ r
  let ref ← loc σ l
  let st ← ofOpt (σ.storage.write ref sv)
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

def rebind {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R) : Step C Γ Γ := fun σ => do
  let (st, ref) ← arhs σ r
  pure ⟨(σ.withStorage st).setLocal i (some ref), List.prefix_refl _⟩

def assignLocal {p : PrimTy} (i : Idx Γ (.val p)) (r : Val C Γ p) : Step C Γ Γ := fun σ => do
  pure ⟨σ.setLocal i (← value σ r), List.prefix_refl _⟩

def declLocal (p : PrimTy) (init : Option (Val C Γ p)) : Step C Γ (.val p :: Γ) := fun σ => do
  let v ← match init with
    | none => pure (PrimTy.dflt p)
    | some e => value σ e
  pure ⟨σ.push (t := .val p) v, List.prefix_refl _⟩

def declStorage (R : RefTy) (init : Option (ARhs C Γ R)) : Step C Γ (.alias R :: Γ) := fun σ =>
  match init with
  | none => pure ⟨σ.push (t := .alias R) none, List.prefix_refl _⟩
  | some r => do
    let (st, ref) ← arhs σ r
    pure ⟨(σ.withStorage st).push (t := .alias R) (some ref), List.prefix_refl _⟩

def opAssign {p : PrimTy} (op : BinOp) (hp : p.isNumeric = true) (l : OpLoc C Γ p) (r : Val C Γ p) : Step C Γ Γ :=
  fun σ => do opLocStore σ op hp l (← value σ r)

def incDec {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) : Step C Γ Γ := fun σ => do
  pure (← opLocBump σ op hp l).1

def assignIncDec {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    Step C Γ Γ := fun σ => do
  let (o, v) ← opLocBump σ op hp l
  pure ⟨o.st.setLocal i v, o.ext⟩

def push {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E)) : Step C Γ Γ := fun σ => do
  let ref ← path σ b
  let x ← match v with
    | none => pure none
    | some r => do pure (some (← source σ r).strip)
  if σ.storage.full ref then .error .exhausted else
  let st ← ofOpt (σ.storage.push ref fun slot => some (x.getD slot))
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

/-- `y = values.push();`: the array grown as `values.push();` grows it, `y`
the default the cleared slot holds. -/
def assignLocalPush {p : PrimTy} (i : Idx Γ (.val p)) (b : SPath C Γ (.array (.prim p))) :
    Step C Γ Γ := fun σ => do
  let o ← push b none σ
  pure ⟨o.st.setLocal i (PrimTy.dflt p), o.ext⟩

/-- `values.push() += e`: RHS first, receiver once, then reset/append and
checked arithmetic. Capacity exhaustion precedes arithmetic failure. -/
def pushOpAssign {p : PrimTy} (op : BinOp) (hp : p.isNumeric = true) (b : SPath C Γ (.array (.prim p)))
    (rhs : Val C Γ p) : Step C Γ Γ := fun σ => do
  let value ← value σ rhs
  let ref ← path σ b
  if σ.storage.full ref then .error .exhausted else
  let (st, index) ← ofOpt (σ.storage.pushPlace ref)
  opStore (σ.withStorage st) op hp (ref.index (.arr .dyn) index) value

/-- `++values.push()` and `values.push()++` as statements: append/reset,
then bump the new slot; the prefix/postfix value is discarded. -/
def pushIncDec {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (b : SPath C Γ (.array (.prim p))) :
    Step C Γ Γ := fun σ => do
  let ref ← path σ b
  if σ.storage.full ref then .error .exhausted else
  let (st, index) ← ofOpt (σ.storage.pushPlace ref)
  pure (← bumpStore (σ.withStorage st) op hp (ref.index (.arr .dyn) index)).1

def pop {E : Ty} (b : SPath C Γ (.array E)) : Step C Γ Γ := fun σ => do
  let ref ← path σ b
  let st ← evalProducer (.pop σ.storage E.isMapping ref)
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

def transfer (r a : Val C Γ .uint) : Step C Γ Γ := fun σ => do
  let addr ← value σ r
  let amt ← value σ a
  if σ.canPay addr amt then pure ⟨σ.pay addr amt.1, List.prefix_refl _⟩
  else throw .revert

def send (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) : Step C Γ Γ := fun σ => do
  let addr ← value σ r
  let amt ← value σ a
  pure (sendT σ pv addr amt)

def declMem (R : RefTy) (init : Option (MRhs C Γ R)) (hm : (Ty.ref R).mapFree = true) :
    Step C Γ (.mem R :: Γ) := fun σ =>
  match init with
  | none =>
    let g := σ.allocDefaultG R hm
    pure ⟨g.st.push (t := .mem R) (some g.val), g.ext⟩
  | some r => do
    let g ← mrhs σ r
    pure ⟨g.st.push (t := .mem R) (some g.val), g.ext⟩

def rebindMem {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) : Step C Γ Γ := fun σ => do
  let g ← mrhs σ r
  pure ⟨g.st.setLocal i (some g.val), g.ext⟩

def assignFromMem {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) : Step C Γ Γ :=
  fun σ => do
    let m ← mpath σ p
    let ref ← loc σ l
    let st ← ofOpt (σ.storage.write ref (MVal.copyMToSt σ.heap m))
    pure ⟨σ.withStorage st, List.prefix_refl _⟩

def assignMem {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) : Step C Γ Γ := fun σ => do
  let mv ← msource σ r
  let a ← mloc σ l
  let hp ← memoryWrite σ.heap a mv
  pure ⟨σ.withHeap hp, List.prefix_refl _⟩

def delete {T : Ty} (l : Loc C Γ T) : Step C Γ Γ := fun σ => do
  let ref ← loc σ l
  let st ← ofOpt (σ.storage.delete ref)
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

/-- `delete` at a memory address: a word to its default, a
reference to a fresh default object. -/
def clear (σ : State C Γ) : {T : Ty} → MAddr σ.H T → T.mapFree = true → EvalResult (Out C σ.H Γ)
  | .prim p, a, _ => do
    let hp ← memoryWrite σ.heap a (PrimTy.dflt p)
    pure ⟨σ.withHeap hp, List.prefix_refl _⟩
  | .ref R, a, hm => do
    let g := σ.allocDefaultG R hm
    let hp ← memoryWrite g.st.heap (a.wk g.ext) g.val
    pure ⟨g.st.withHeap hp, g.ext⟩

def deleteMem {T : Ty} (p : MPath C Γ T) : Step C Γ Γ := fun σ =>
  match p with
  | .var i hm =>
    let g := σ.allocDefaultG _ hm
    pure ⟨g.st.setLocal i (some g.val), g.ext⟩
  | .loc l => do clear σ (← mloc σ l) l.mapFree

def assignNew {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint) (h : R.newArrOk = true) :
    Step C Γ Γ := fun σ =>
  let g := σ.copyStToMG (newArrT R (n.evalT σ) h) (RefTy.mapFree_of_newArrOk h)
  match l with
  | .store l => do
    let ref ← loc g.st l
    let st ← ofOpt (g.st.storage.write ref (MVal.copyMToSt g.st.heap g.val))
    pure ⟨g.st.withStorage st, g.ext⟩
  | .mem l => do
    let a ← mloc g.st l
    let hp ← memoryWrite g.st.heap a g.val
    pure ⟨g.st.withHeap hp, g.ext⟩

end Run
end Solidity.Semantics.Panic
