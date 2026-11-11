import Solidity.Semantics.PanicV2

/-!
# Expression, path and selected statement evaluation through the exact V2 interface

This structural evaluator uses the same typed state and the same operand
order/short circuit as V1. Each path/value constructor has an unconditional
projection theorem. Site classifiers are refined by family; unclassified
failed options remain unknown rather than receiving guessed panic codes.
Arithmetic options now retain 0x11/0x12 at their actual failure branches;
Storage/memory read bounds tests retain 0x32 after receiver resolution;
Ordinary compound-assignment, increment/decrement and pop steps are refined
below, including push arithmetic; plain writes and whole-program dispatch
remain pending. Capacity exhaustion retains its V1 resource meaning.
-/

namespace Solidity.PanicV2.Eval

variable {C : Contract} {Γ : Ctx}

/-- Failure provenance for the arithmetic operators. A negative exponent
is a V1-only failure with no solc panic classification here; wrapping and
bitwise operators likewise receive no guessed cause. Division by zero takes
precedence over the signed division overflow case. -/
def binaryFailure (op : BinOp) (p : PrimTy) (y : p.Denote) : Option OperationFailure :=
  match op with
  | .add | .sub | .mul => some .arithmetic
  | .pow => if PrimTy.key y < 0 then none else some .arithmetic
  | .div => some (if PrimTy.key y = 0 then .zeroDivisor else .arithmetic)
  | .mod => if PrimTy.key y = 0 then some .zeroDivisor else none
  | _ => none

/-- Classify only the actual failed option, after both operands were read. -/
def binary (op : BinOp) {p : PrimTy} (h : op.accepts p = true) (x y : p.Denote) :
    Result (op.ret p).Denote :=
  match binaryFailure op p y with
  | some failure => checked failure (op.evalT h x y)
  | none => ofOpt (op.evalT h x y)

/-- The arithmetic observation preserves the entire V1 operator result. -/
theorem binary_erase (op : BinOp) {p : PrimTy} (h : op.accepts p = true) (x y : p.Denote) :
    erase (binary op h x y) = TRes.ofOpt (op.evalT h x y) := by
  unfold binary
  split <;> simp only [erase_checked, erase_ofOpt]

/-- Only signed negation can fail arithmetically among the unary operators;
explicit word conversions remain the unchanged V1 options. -/
def unary (op : UnOp) {p : PrimTy} (h : op.accepts p = true) (x : p.Denote) :
    Result (op.ret p).Denote :=
  if op = .neg then checked .arithmetic (op.evalT h x) else ofOpt (op.evalT h x)

theorem unary_erase (op : UnOp) {p : PrimTy} (h : op.accepts p = true) (x : p.Denote) :
    erase (unary op h x) = TRes.ofOpt (op.evalT h x) := by
  unfold unary
  split <;> simp only [erase_checked, erase_ofOpt]

/-- The modular builtins report 0x12 only for their zero-modulus branch. -/
def modular (op : ModOp) (x y k : PrimTy.uint.Denote) : Result PrimTy.uint.Denote :=
  if k.val = 0 then checked .zeroDivisor (op.evalT x y k) else ofOpt (op.evalT x y k)

theorem modular_erase (op : ModOp) (x y k : PrimTy.uint.Denote) :
    erase (modular op x y k) = TRes.ofOpt (op.evalT x y k) := by
  unfold modular
  split <;> simp only [erase_checked, erase_ofOpt]

/-- Gap control for 0x11/0x12 on already evaluated operands: the
classified operator emits its cause only when its own option fails. -/
theorem binary_failed (op : BinOp) {p : PrimTy} (h : op.accepts p = true) (x y : p.Denote)
    {failure : OperationFailure} (site : binaryFailure op p y = some failure)
    (failed : op.evalT h x y = none) : binary op h x y = .error (.operation failure) := by
  simp only [binary, site, failed, checked]

/-- Gap control: checked addition/subtraction/multiplication failures carry
0x11, while the V1 projection remains a bare revert. -/
theorem arithmetic_failed (op : BinOp) {p : PrimTy} (h : op.accepts p = true) (x y : p.Denote)
    (family : op = .add ∨ op = .sub ∨ op = .mul) (failed : op.evalT h x y = none) :
    binary op h x y = .error (.operation .arithmetic) ∧
      (Halt.operation .arithmetic).panicCode? = some 0x11 := by
  constructor
  · apply binary_failed op h x y _ failed
    rcases family with rfl | rfl | rfl <;> rfl
  · rfl

/-- Gap control: a zero divisor reports 0x12 for both signed and unsigned
`/` and `%`, before any signed division range check. -/
theorem division_zero (op : BinOp) {p : PrimTy} (h : op.accepts p = true) (x y : p.Denote)
    (family : op = .div ∨ op = .mod) (zero : PrimTy.key y = 0) :
    binary op h x y = .error (.operation .zeroDivisor) ∧
      (Halt.operation .zeroDivisor).panicCode? = some 0x12 := by
  constructor
  · rcases family with rfl | rfl <;> cases p <;>
      simp_all [binary, binaryFailure, BinOp.evalT, BinOp.evalNum, BinOp.arithInt,
        PrimTy.key, checked] <;> cases h
  · rfl

/-- A nonzero division failure is arithmetic overflow (the signed
minimum divided by -1); a zero divisor instead takes the 0x12 branch above. -/
theorem division_nonzero_failed {p : PrimTy} (h : BinOp.div.accepts p = true) (x y : p.Denote)
    (nonzero : PrimTy.key y ≠ 0) (failed : BinOp.div.evalT h x y = none) :
    binary .div h x y = .error (.operation .arithmetic) := by
  apply binary_failed .div h x y _ failed
  simp only [binaryFailure, nonzero, ↓reduceIte]

/-- A nonnegative exponent's failed checked power carries 0x11. The
V1-only negative-exponent branch is deliberately left unclassified. -/
theorem power_failed {p : PrimTy} (h : BinOp.pow.accepts p = true) (x y : p.Denote)
    (nonnegative : ¬ PrimTy.key y < 0) (failed : BinOp.pow.evalT h x y = none) :
    binary .pow h x y = .error (.operation .arithmetic) := by
  apply binary_failed .pow h x y _ failed
  simp only [binaryFailure, nonnegative, ↓reduceIte]

/-- Gap control: signed negation overflow carries 0x11 without changing
any successful negation or any explicit conversion. -/
theorem negation_failed {p : PrimTy} (h : UnOp.neg.accepts p = true) (x : p.Denote)
    (failed : UnOp.neg.evalT h x = none) :
    unary .neg h x = .error (.operation .arithmetic) := by
  simp only [unary, ↓reduceIte, failed, checked]

/-- Gap control: both modular builtins report 0x12 for a zero modulus,
even though their wide addition/multiplication itself never overflows. -/
theorem modular_zero (op : ModOp) (x y k : PrimTy.uint.Denote) (zero : k.val = 0) :
    modular op x y k = .error (.operation .zeroDivisor) := by
  simp only [modular, zero, ↓reduceIte, ModOp.evalT, checked]

/-- Resolve the storage receiver before classifying the index test.
A missing/dangling receiver is not evidence of an out-of-bounds index. -/
def storageIndex {R : RefTy} {k : PrimTy} {V : Ty} (st : Storage C)
    (r : SRef C (.ref R)) (it : IndexTy R k V) (i : k.Denote) : Result Unit := do
  let receiver ← ofOpt (st.find r)
  checked .bounds (Storage.inBounds it i receiver)

/-- The receiver/index split preserves V1 for every storage, including
states whose receiver reference no longer resolves. -/
theorem storageIndex_erase {R : RefTy} {k : PrimTy} {V : Ty} (st : Storage C)
    (r : SRef C (.ref R)) (it : IndexTy R k V) (i : k.Denote) :
    erase (storageIndex st r it i) = TRes.ofOpt (st.checkIndex r it i) := by
  cases found : st.find r with
  | none => simp only [storageIndex, found, ofOpt, erase, Halt.erase, Storage.checkIndex,
      TRes.ofOpt]; rfl
  | some receiver =>
    simp only [storageIndex, found, ofOpt, Storage.checkIndex]
    exact erase_checked _ _

/-- Gap control for 0x32: classify an actual failed bounds test after a
successful receiver lookup; this does not classify arbitrary storage failures. -/
theorem storageIndex_bounds {R : RefTy} {k : PrimTy} {V : Ty} (st : Storage C)
    (r : SRef C (.ref R)) (it : IndexTy R k V) (i : k.Denote) (receiver : SVal (.ref R))
    (found : st.find r = some receiver) (failed : Storage.inBounds it i receiver = none) :
    storageIndex st r it i = .error (.operation .bounds) := by
  unfold storageIndex
  rw [found]
  change checked .bounds (Storage.inBounds it i receiver) = _
  rw [failed]
  rfl

/-- Gap control: a failed receiver lookup stays unclassified rather than
manufacturing code0x32 from the combined V1 `checkIndex` option. -/
theorem storageIndex_missing {R : RefTy} {k : PrimTy} {V : Ty} (st : Storage C)
    (r : SRef C (.ref R)) (it : IndexTy R k V) (i : k.Denote) (missing : st.find r = none) :
    storageIndex st r it i = .error (.legacy .revert) := by
  unfold storageIndex
  rw [missing]
  rfl

/-- Typed memory field access always succeeds; only an array index's
failed read carries the bounds cause. -/
def memoryRead {H : HTy} (hp : Heap H) {T : Ty} : MAddr H T → Result (MVal H T)
  | .field r h => .ok (hp.field r h)
  | .index r a i => checked .bounds (hp.index r a i)

theorem memoryRead_erase {H : HTy} (hp : Heap H) {T : Ty} (addr : MAddr H T) :
    erase (memoryRead hp addr) = TRes.ofOpt (hp.readAddr addr) := by
  cases addr with
  | field => rfl
  | index => exact erase_checked _ _

/-- Gap control for memory0x32: an actual failed array read retains its
cause at the index site, without changing the resolved memory address. -/
theorem memoryRead_bounds {H : HTy} (hp : Heap H) {R : RefTy} {E : Ty}
    (r : HRef H R) (a : ArrTy R E) (i : PrimTy.uint.Denote) (failed : hp.index r a i = none) :
    memoryRead hp (.index r a i) = .error (.operation .bounds) := by
  simp only [memoryRead, failed, checked]

/-- Bounds diagnostics use solc's index code0x32 and erase to V1 revert. -/
theorem bounds_code : (Halt.operation .bounds).panicCode? = some 0x32 ∧
    (Halt.operation .bounds).erase = .revert := by constructor <;> rfl

mutual

def path (σ : State C Γ) : {T : Ty} → SPath C Γ T → Result (SRef C T)
  | _, .alias i => ofOpt (TEnv.get i σ.env)
  | _, .loc l => loc σ l

def loc (σ : State C Γ) : {T : Ty} → Loc C Γ T → Result (SRef C T)
  | _, .root r h => .ok (SRef.ofRoot r h)
  | _, .field b _ h => do
    let r ← path σ b
    pure (r.field h)
  | _, .index it b i => do
    let r ← path σ b
    let k ← value σ i
    let _ ← storageIndex σ.storage r it k
    pure (r.index it k)

def mpath (σ : State C Γ) : {T : Ty} → MPath C Γ T → Result (MVal σ.H T)
  | _, .var i _ => ofOpt (TEnv.get i σ.env)
  | _, .loc l => do memoryRead σ.heap (← mloc σ l)

def mloc (σ : State C Γ) : {T : Ty} → MLoc C Γ T → Result (MAddr σ.H T)
  | _, .field b _ h => do
    let r ← mpath σ b
    pure (.field r h)
  | _, .index a b i => do
    let r ← mpath σ b
    let k ← value σ i
    pure (.index r a k)

def value (σ : State C Γ) : {p : PrimTy} → Val C Γ p → Result p.Denote
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

/-- Classify only the empty-array branch of `pop`. A missing receiver
and a failed write-back of a nonempty array retain their unknown V1 cause. -/
def storagePop {E : Ty} (st : Storage C) (keep : Bool)
    (r : SRef C (.ref (.array E))) : Result (Storage C) :=
  match st.find r with
  | none => ofOpt (st.pop keep r)
  | some receiver =>
    match (SVal.view receiver : ArrView E).elems.toList.reverse with
    | [] => checked .emptyPop (st.pop keep r)
    | _ :: _ => ofOpt (st.pop keep r)

/-- Pop diagnostics preserve every V1 storage outcome, including invalid
receiver or write-back failure; no state invariant is an added premise. -/
theorem storagePop_erase {E : Ty} (st : Storage C) (keep : Bool)
    (r : SRef C (.ref (.array E))) : erase (storagePop st keep r) = TRes.ofOpt (st.pop keep r) := by
  unfold storagePop
  split
  · exact erase_ofOpt _
  · split
    · exact erase_checked _ _
    · exact erase_ofOpt _

/-- Gap control for0x31: an actual empty-array pop reports its own cause,
not a code guessed from every failed `Storage.pop` option. -/
theorem storagePop_empty {E : Ty} (st : Storage C) (keep : Bool)
    (r : SRef C (.ref (.array E))) (receiver : SVal (.ref (.array E)))
    (found : st.find r = some receiver)
    (empty : (SVal.view receiver : ArrView E).elems.toList.reverse = []) :
    storagePop st keep r = .error (.operation .emptyPop) := by
  have failed : st.pop keep r = none := by
    simp only [Storage.pop, found]
    change (match (SVal.view receiver : ArrView E).elems.toList.reverse with
      | [] => none
      | _ :: _ => _) = none
    rw [empty]
  simp only [storagePop, found, empty, failed, checked]

/-- Missing pop receivers stay unknown rather than acquiring0x31. -/
theorem storagePop_missing {E : Ty} (st : Storage C) (keep : Bool)
    (r : SRef C (.ref (.array E))) (missing : st.find r = none) :
    storagePop st keep r = .error (.legacy .revert) := by
  simp only [storagePop, missing]
  have failed : st.pop keep r = none := by rw [Storage.pop, missing]; rfl
  rw [failed]
  rfl

/-- A typed V2 pop step: receiver once, then the actual storage operation. -/
def pop {E : Ty} (b : SPath C Γ (.array E)) (σ : State C Γ) : Result (Out C σ.H Γ) := do
  let receiver ← path σ b
  let st ← storagePop σ.storage E.isMapping receiver
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

/-- Exact whole-state projection of the V2 pop step to the frozen V1 step. -/
theorem pop_erase {E : Ty} (b : SPath C Γ (.array E)) (σ : State C Γ) :
    erase (pop b σ) = TRun.pop b σ :=
  erase_bind_congr (path_erase σ b) fun _ =>
    erase_bind_congr (storagePop_erase _ _ _) fun _ => rfl

/-- Gap control at the typed statement site: after resolving the receiver,
popping its actual empty array emits0x31 rather than losing the cause. -/
theorem pop_empty {E : Ty} (b : SPath C Γ (.array E)) (σ : State C Γ)
    (r : SRef C (.ref (.array E))) (receiver : SVal (.ref (.array E)))
    (resolved : path σ b = .ok r) (found : σ.storage.find r = some receiver)
    (empty : (SVal.view receiver : ArrView E).elems.toList.reverse = []) :
    pop b σ = .error (.operation .emptyPop) := by
  unfold pop
  rw [resolved]
  change (storagePop σ.storage E.isMapping r >>= _) = _
  rw [storagePop_empty σ.storage E.isMapping r receiver found empty]
  rfl

/-- Empty-pop diagnostics use solc0x31 and preserve the V1 revert halt. -/
theorem emptyPop_code : (Halt.operation .emptyPop).panicCode? = some 0x31 ∧
    (Halt.operation .emptyPop).erase = .revert := by constructor <;> rfl

/-- Compound arithmetic uses the same operand values and range check as
V1. Only numeric operator failures may receive an arithmetic cause. -/
def compound (op : BinOp) (p : PrimTy) (x y : p.Denote) : Result p.Denote :=
  if p.isNumeric then
    match binaryFailure op p y with
    | some failure => checked failure (compoundT op p (PrimTy.key x) (PrimTy.key y))
    | none => ofOpt (compoundT op p (PrimTy.key x) (PrimTy.key y))
  else ofOpt (compoundT op p (PrimTy.key x) (PrimTy.key y))

theorem compound_erase (op : BinOp) (p : PrimTy) (x y : p.Denote) :
    erase (compound op p x y) = TRes.ofOpt (compoundT op p (PrimTy.key x) (PrimTy.key y)) := by
  unfold compound
  split
  · split <;> first | exact erase_checked _ _ | exact erase_ofOpt _
  · exact erase_ofOpt _

/-- Gap control for compound0x11/0x12: only the actual failed numeric
operator option receives the independently selected arithmetic cause. -/
theorem compound_failed (op : BinOp) (p : PrimTy) (x y : p.Denote)
    (numeric : p.isNumeric = true) {failure : OperationFailure}
    (site : binaryFailure op p y = some failure)
    (failed : compoundT op p (PrimTy.key x) (PrimTy.key y) = none) :
    compound op p x y = .error (.operation failure) := by
  simp only [compound, numeric, ↓reduceIte, site, failed, checked]

/-- Compound assignment at a resolved storage target. Lookup and write-back
failures remain distinct from the classified arithmetic operation. -/
def opStore (σ : State C Γ) (op : BinOp) {p : PrimTy} (r : SRef C (.prim p)) (v : p.Denote) :
    Result (Out C σ.H Γ) := do
  let old ← ofOpt (σ.storage.find r)
  let new ← compound op p (SVal.view old) v
  let st ← ofOpt (σ.storage.save r (.prim new))
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

theorem opStore_erase (σ : State C Γ) (op : BinOp) {p : PrimTy}
    (r : SRef C (.prim p)) (v : p.Denote) : erase (opStore σ op r v) = opStoreT σ op r v :=
  erase_bind_congr (erase_ofOpt _) fun old =>
    erase_bind_congr (compound_erase op p (SVal.view old) v) fun _ =>
      erase_bind_congr (erase_ofOpt _) fun _ => rfl

/-- Compound assignment at a resolved memory target; the old-value read
may carry0x32 before the arithmetic option is evaluated. -/
def opMem (σ : State C Γ) (op : BinOp) {p : PrimTy} (addr : MAddr σ.H (.prim p)) (v : p.Denote) :
    Result (Out C σ.H Γ) := do
  let old ← memoryRead σ.heap addr
  let new ← compound op p old v
  let hp ← ofOpt (σ.heap.writeAddr addr new)
  pure ⟨σ.withHeap hp, List.prefix_refl _⟩

theorem opMem_erase (σ : State C Γ) (op : BinOp) {p : PrimTy}
    (addr : MAddr σ.H (.prim p)) (v : p.Denote) : erase (opMem σ op addr v) = opMemT σ op addr v :=
  erase_bind_congr (memoryRead_erase _ _) fun old =>
    erase_bind_congr (compound_erase op p old v) fun _ =>
      erase_bind_congr (erase_ofOpt _) fun _ => rfl

/-- All V1 compound target forms, with the same reference/address resolution. -/
def opLocStore (σ : State C Γ) (op : BinOp) : {p : PrimTy} → OpLoc C Γ p → p.Denote →
    Result (Out C σ.H Γ)
  | p, .local i, v => do
    let new ← compound op p (TEnv.get i σ.env) v
    pure ⟨σ.setLocal i new, List.prefix_refl _⟩
  | _, .root r h, v => opStore σ op (SRef.ofRoot r h) v
  | _, .field b f h, v => do opStore σ op (← loc σ (Loc.field b f h)) v
  | _, .index it b i, v => do opStore σ op (← loc σ (Loc.index it b (.simple i))) v
  | _, .mfield b f h, v => do opMem σ op (← mloc σ (MLoc.field b f h)) v
  | _, .mindex a b i, v => do opMem σ op (← mloc σ (MLoc.index a b (.simple i))) v

theorem opLocStore_erase (σ : State C Γ) (op : BinOp) : {p : PrimTy} → (l : OpLoc C Γ p) →
    (v : p.Denote) → erase (opLocStore σ op l v) = l.storeT σ op v
  | p, .local i, v => erase_bind_congr (compound_erase op p (TEnv.get i σ.env) v) fun _ => rfl
  | _, .root _ _, v => opStore_erase σ op _ v
  | _, .field b f h, v => erase_bind_congr (loc_erase σ (Loc.field b f h)) fun _ =>
      opStore_erase σ op _ v
  | _, .index it b i, v => erase_bind_congr (loc_erase σ (Loc.index it b (.simple i))) fun _ =>
      opStore_erase σ op _ v
  | _, .mfield b f h, v => erase_bind_congr (mloc_erase σ (MLoc.field b f h)) fun _ =>
      opMem_erase σ op _ v
  | _, .mindex a b i, v => erase_bind_congr (mloc_erase σ (MLoc.index a b (.simple i))) fun _ =>
      opMem_erase σ op _ v

/-- Compound assignment evaluates its RHS before resolving the target,
exactly as V1 does, and forwards the first intrinsic cause. -/
def opAssign {p : PrimTy} (op : BinOp) (l : OpLoc C Γ p) (rhs : Val C Γ p)
    (σ : State C Γ) : Result (Out C σ.H Γ) := do
  let v ← value σ rhs
  opLocStore σ op l v

theorem opAssign_erase {p : PrimTy} (op : BinOp) (l : OpLoc C Γ p) (rhs : Val C Γ p)
    (σ : State C Γ) : erase (opAssign op l rhs σ) = TRun.opAssign op l rhs σ :=
  erase_bind_congr (value_erase σ rhs) fun v => opLocStore_erase σ op l v

/-- Gap control: an earlier RHS failure wins over target/bounds/arithmetic
failure; the target is not evaluated to choose a different code. -/
theorem opAssign_rhs_failure {p : PrimTy} (op : BinOp) (l : OpLoc C Γ p) (rhs : Val C Γ p)
    (σ : State C Γ) (halt : Halt) (failed : value σ rhs = .error halt) :
    opAssign op l rhs σ = .error halt := by
  unfold opAssign
  rw [failed]
  rfl

/-- Gap control at a local compound-assignment step: after the RHS
returns, the actual failed arithmetic option carries its selected0x11/0x12 cause. -/
theorem opAssign_local_failure {p : PrimTy} (op : BinOp) (i : Idx Γ (.val p))
    (rhs : Val C Γ p) (σ : State C Γ) (v : p.Denote)
    (right : value σ rhs = .ok v) (numeric : p.isNumeric = true)
    {failure : OperationFailure} (site : binaryFailure op p v = some failure)
    (failed : compoundT op p (PrimTy.key (TEnv.get i σ.env)) (PrimTy.key v) = none) :
    opAssign op (.local i) rhs σ = .error (.operation failure) := by
  unfold opAssign
  rw [right]
  change (compound op p (TEnv.get i σ.env) v >>= _) = _
  rw [compound_failed op p (TEnv.get i σ.env) v numeric site failed]
  rfl

/-- Increment/decrement range checks classify only actual numeric
failures; a nonnumeric helper invocation stays unclassified. -/
def bump (op : IncDec) (p : PrimTy) (old : p.Denote) : Result p.Denote :=
  if p.isNumeric then checked .arithmetic (Solidity.bumpT op p (PrimTy.key old))
  else ofOpt (Solidity.bumpT op p (PrimTy.key old))

theorem bump_erase (op : IncDec) (p : PrimTy) (old : p.Denote) :
    erase (bump op p old) = TRes.ofOpt (Solidity.bumpT op p (PrimTy.key old)) := by
  unfold bump
  split
  · exact erase_checked _ _
  · exact erase_ofOpt _

/-- Gap control: actual numeric increment/decrement range failure carries
0x11, with no distinction between discarded prefix/postfix values. -/
theorem bump_failed (op : IncDec) (p : PrimTy) (old : p.Denote)
    (numeric : p.isNumeric = true) (failed : Solidity.bumpT op p (PrimTy.key old) = none) :
    bump op p old = .error (.operation .arithmetic) := by
  simp only [bump, numeric, ↓reduceIte, failed, checked]

/-- Storage increment/decrement retains both the updated state and the
prefix/postfix result; lookup/write failure does not acquire0x11. -/
def bumpStore (σ : State C Γ) (op : IncDec) {p : PrimTy} (r : SRef C (.prim p)) :
    Result (Out C σ.H Γ × p.Denote) := do
  let old ← ofOpt (σ.storage.find r)
  let new ← bump op p (SVal.view old)
  let st ← ofOpt (σ.storage.save r (.prim new))
  pure (⟨σ.withStorage st, List.prefix_refl _⟩, if op.isPre then new else SVal.view old)

theorem bumpStore_erase (σ : State C Γ) (op : IncDec) {p : PrimTy} (r : SRef C (.prim p)) :
    erase (bumpStore σ op r) = bumpStoreT σ op r :=
  erase_bind_congr (erase_ofOpt _) fun old =>
    erase_bind_congr (bump_erase op p (SVal.view old)) fun _ =>
      erase_bind_congr (erase_ofOpt _) fun _ => rfl

/-- A memory bounds failure occurs before the increment arithmetic. -/
def bumpMem (σ : State C Γ) (op : IncDec) {p : PrimTy} (addr : MAddr σ.H (.prim p)) :
    Result (Out C σ.H Γ × p.Denote) := do
  let old ← memoryRead σ.heap addr
  let new ← bump op p old
  let hp ← ofOpt (σ.heap.writeAddr addr new)
  pure (⟨σ.withHeap hp, List.prefix_refl _⟩, if op.isPre then new else old)

theorem bumpMem_erase (σ : State C Γ) (op : IncDec) {p : PrimTy} (addr : MAddr σ.H (.prim p)) :
    erase (bumpMem σ op addr) = bumpMemT σ op addr :=
  erase_bind_congr (memoryRead_erase _ _) fun old =>
    erase_bind_congr (bump_erase op p old) fun _ =>
      erase_bind_congr (erase_ofOpt _) fun _ => rfl

/-- All increment/decrement targets preserve V1 receiver resolution and
prefix/postfix values, while retaining a classified intrinsic failure. -/
def opLocBump (σ : State C Γ) (op : IncDec) : {p : PrimTy} → OpLoc C Γ p →
    Result (Out C σ.H Γ × p.Denote)
  | p, .local i => do
    let old : p.Denote := TEnv.get i σ.env
    let new ← bump op p old
    pure (⟨σ.setLocal i new, List.prefix_refl _⟩, if op.isPre then new else old)
  | _, .root r h => bumpStore σ op (SRef.ofRoot r h)
  | _, .field b f h => do bumpStore σ op (← loc σ (Loc.field b f h))
  | _, .index it b i => do bumpStore σ op (← loc σ (Loc.index it b (.simple i)))
  | _, .mfield b f h => do bumpMem σ op (← mloc σ (MLoc.field b f h))
  | _, .mindex a b i => do bumpMem σ op (← mloc σ (MLoc.index a b (.simple i)))

theorem opLocBump_erase (σ : State C Γ) (op : IncDec) : {p : PrimTy} → (l : OpLoc C Γ p) →
    erase (opLocBump σ op l) = l.bumpT σ op
  | p, .local i => erase_bind_congr (bump_erase op p (TEnv.get i σ.env)) fun _ => rfl
  | _, .root _ _ => bumpStore_erase σ op _
  | _, .field b f h => erase_bind_congr (loc_erase σ (Loc.field b f h)) fun _ =>
      bumpStore_erase σ op _
  | _, .index it b i => erase_bind_congr (loc_erase σ (Loc.index it b (.simple i))) fun _ =>
      bumpStore_erase σ op _
  | _, .mfield b f h => erase_bind_congr (mloc_erase σ (MLoc.field b f h)) fun _ =>
      bumpMem_erase σ op _
  | _, .mindex a b i => erase_bind_congr (mloc_erase σ (MLoc.index a b (.simple i))) fun _ =>
      bumpMem_erase σ op _

/-- An increment/decrement statement discards only the expression result. -/
def incDec {p : PrimTy} (op : IncDec) (l : OpLoc C Γ p) (σ : State C Γ) :
    Result (Out C σ.H Γ) := do pure (← opLocBump σ op l).1

theorem incDec_erase {p : PrimTy} (op : IncDec) (l : OpLoc C Γ p) (σ : State C Γ) :
    erase (incDec op l σ) = TRun.incDec op l σ :=
  erase_bind_congr (opLocBump_erase σ op l) fun _ => rfl

/-- The prefix/postfix result is assigned after the target update, just
as in V1, including when the assigned variable is the target itself. -/
def assignIncDec {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec) (l : OpLoc C Γ p)
    (σ : State C Γ) : Result (Out C σ.H Γ) := do
  let (out, result) ← opLocBump σ op l
  pure ⟨out.st.setLocal i result, out.ext⟩

theorem assignIncDec_erase {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec) (l : OpLoc C Γ p)
    (σ : State C Γ) : erase (assignIncDec i op l σ) = TRun.assignIncDec i op l σ :=
  erase_bind_congr (opLocBump_erase σ op l) fun _ => rfl

/-- Gap control at the typed statement: an actual local numeric bump
failure emits0x11 before any assignment of the result can occur. -/
theorem incDec_local_failure {p : PrimTy} (op : IncDec) (i : Idx Γ (.val p)) (σ : State C Γ)
    (numeric : p.isNumeric = true)
    (failed : Solidity.bumpT op p (PrimTy.key (TEnv.get i σ.env)) = none) :
    incDec op (.local i) σ = .error (.operation .arithmetic) := by
  have target : opLocBump σ op (.local i) = .error (.operation .arithmetic) := by
    change (bump op p (TEnv.get i σ.env) >>= _) = _
    rw [bump_failed op p (TEnv.get i σ.env) numeric failed]
    rfl
  unfold incDec
  rw [target]
  rfl

/-- `values.push() op= rhs` retains V1 RHS-first order, checks capacity
before appending/resetting, then applies the classified arithmetic step. -/
def pushOpAssign {p : PrimTy} (op : BinOp) (b : SPath C Γ (.array (.prim p)))
    (rhs : Val C Γ p) (σ : State C Γ) : Result (Out C σ.H Γ) := do
  let v ← value σ rhs
  let receiver ← path σ b
  if σ.storage.full receiver then .error (.legacy .exhausted) else
  let (st, index) ← ofOpt (σ.storage.pushPlace receiver)
  opStore (σ.withStorage st) op (receiver.index (.arr .dyn) index) v

/-- Exact push-compound projection preserves the intermediate reset/append
and every subsequent state update or failure; no capacity premise is added. -/
theorem pushOpAssign_erase {p : PrimTy} (op : BinOp) (b : SPath C Γ (.array (.prim p)))
    (rhs : Val C Γ p) (σ : State C Γ) :
    erase (pushOpAssign op b rhs σ) = TRun.pushOpAssign op b rhs σ := by
  refine erase_bind_congr (value_erase σ rhs) fun v => ?_
  refine erase_bind_congr (path_erase σ b) fun receiver => ?_
  cases capacity : σ.storage.full receiver with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact erase_bind_congr (erase_ofOpt _) fun slot => opStore_erase _ op _ v
  | true => simp only [↓reduceIte]; rfl

/-- Prefix/postfix increment/decrement of a pushed slot as a statement
discards its value and follows V1 capacity, reset/append, read, bump/write order. -/
def pushIncDec {p : PrimTy} (op : IncDec) (b : SPath C Γ (.array (.prim p)))
    (σ : State C Γ) : Result (Out C σ.H Γ) := do
  let receiver ← path σ b
  if σ.storage.full receiver then .error (.legacy .exhausted) else
  let (st, index) ← ofOpt (σ.storage.pushPlace receiver)
  pure (← bumpStore (σ.withStorage st) op (receiver.index (.arr .dyn) index)).1

theorem pushIncDec_erase {p : PrimTy} (op : IncDec) (b : SPath C Γ (.array (.prim p)))
    (σ : State C Γ) : erase (pushIncDec op b σ) = TRun.pushIncDec op b σ := by
  refine erase_bind_congr (path_erase σ b) fun receiver => ?_
  cases capacity : σ.storage.full receiver with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact erase_bind_congr (erase_ofOpt _) fun slot =>
      erase_bind_congr (bumpStore_erase _ op _) fun _ => rfl
  | true => simp only [↓reduceIte]; rfl

/-- Gap control: capacity exhaustion after RHS/receiver success precedes
push-compound arithmetic, retaining V1 exhausted rather than inventing0x41. -/
theorem pushOpAssign_full {p : PrimTy} (op : BinOp) (b : SPath C Γ (.array (.prim p)))
    (rhs : Val C Γ p) (σ : State C Γ) (v : p.Denote)
    (receiver : SRef C (.ref (.array (.prim p)))) (right : value σ rhs = .ok v)
    (resolved : path σ b = .ok receiver) (full : σ.storage.full receiver = true) :
    pushOpAssign op b rhs σ = .error (.legacy .exhausted) := by
  unfold pushOpAssign
  rw [right]
  change (path σ b >>= _) = _
  rw [resolved]
  change (if σ.storage.full receiver then
    (Except.error (Halt.legacy THalt.exhausted) : Result (Out C σ.H Γ)) else _) = _
  rw [full]
  rfl

/-- Gap control: pushed-slot bump arithmetic cannot override an earlier
capacity exhaustion. Its unknown resource cause is preserved. -/
theorem pushIncDec_full {p : PrimTy} (op : IncDec) (b : SPath C Γ (.array (.prim p)))
    (σ : State C Γ) (receiver : SRef C (.ref (.array (.prim p))))
    (resolved : path σ b = .ok receiver) (full : σ.storage.full receiver = true) :
    pushIncDec op b σ = .error (.legacy .exhausted) := by
  unfold pushIncDec
  rw [resolved]
  change (if σ.storage.full receiver then
    (Except.error (Halt.legacy THalt.exhausted) : Result (Out C σ.H Γ)) else _) = _
  rw [full]
  rfl

/-- Allocation-gap control: the intrinsic V1 resource-exhaustion halt has
no certified solc allocation0x41 observation. -/
theorem exhaustion_unclassified : (Halt.legacy .exhausted).panicCode? = none := rfl

/-- info: 'Solidity.PanicV2.Eval.path_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms path_erase
/-- info: 'Solidity.PanicV2.Eval.loc_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loc_erase
/-- info: 'Solidity.PanicV2.Eval.mpath_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mpath_erase
/-- info: 'Solidity.PanicV2.Eval.mloc_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mloc_erase
/-- info: 'Solidity.PanicV2.Eval.value_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms value_erase
/-- info: 'Solidity.PanicV2.Eval.value_of_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms value_of_ok

/-- info: 'Solidity.PanicV2.Eval.binary_erase' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms binary_erase
/-- info: 'Solidity.PanicV2.Eval.unary_erase' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms unary_erase
/-- info: 'Solidity.PanicV2.Eval.modular_erase' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms modular_erase
/-- info: 'Solidity.PanicV2.Eval.binary_failed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms binary_failed
/-- info: 'Solidity.PanicV2.Eval.arithmetic_failed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms arithmetic_failed
/-- info: 'Solidity.PanicV2.Eval.division_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms division_zero
/-- info: 'Solidity.PanicV2.Eval.division_nonzero_failed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms division_nonzero_failed
/-- info: 'Solidity.PanicV2.Eval.power_failed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms power_failed
/-- info: 'Solidity.PanicV2.Eval.negation_failed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms negation_failed
/-- info: 'Solidity.PanicV2.Eval.modular_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms modular_zero

/-- info: 'Solidity.PanicV2.Eval.storageIndex_erase' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms storageIndex_erase
/-- info: 'Solidity.PanicV2.Eval.storageIndex_bounds' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms storageIndex_bounds
/-- info: 'Solidity.PanicV2.Eval.storageIndex_missing' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms storageIndex_missing
/-- info: 'Solidity.PanicV2.Eval.memoryRead_erase' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms memoryRead_erase
/-- info: 'Solidity.PanicV2.Eval.memoryRead_bounds' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms memoryRead_bounds
/-- info: 'Solidity.PanicV2.Eval.bounds_code' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms bounds_code

/-- info: 'Solidity.PanicV2.Eval.storagePop_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms storagePop_erase
/-- info: 'Solidity.PanicV2.Eval.storagePop_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms storagePop_empty
/-- info: 'Solidity.PanicV2.Eval.storagePop_missing' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms storagePop_missing
/-- info: 'Solidity.PanicV2.Eval.pop_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pop_erase
/-- info: 'Solidity.PanicV2.Eval.pop_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pop_empty
/-- info: 'Solidity.PanicV2.Eval.emptyPop_code' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms emptyPop_code

/-- info: 'Solidity.PanicV2.Eval.compound_erase' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms compound_erase
/-- info: 'Solidity.PanicV2.Eval.compound_failed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms compound_failed
/-- info: 'Solidity.PanicV2.Eval.opStore_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms opStore_erase
/-- info: 'Solidity.PanicV2.Eval.opMem_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms opMem_erase
/-- info: 'Solidity.PanicV2.Eval.opLocStore_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms opLocStore_erase
/-- info: 'Solidity.PanicV2.Eval.opAssign_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms opAssign_erase
/-- info: 'Solidity.PanicV2.Eval.opAssign_rhs_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms opAssign_rhs_failure
/-- info: 'Solidity.PanicV2.Eval.opAssign_local_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms opAssign_local_failure

/-- info: 'Solidity.PanicV2.Eval.bump_erase' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms bump_erase
/-- info: 'Solidity.PanicV2.Eval.bump_failed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms bump_failed
/-- info: 'Solidity.PanicV2.Eval.bumpStore_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bumpStore_erase
/-- info: 'Solidity.PanicV2.Eval.bumpMem_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bumpMem_erase
/-- info: 'Solidity.PanicV2.Eval.opLocBump_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms opLocBump_erase
/-- info: 'Solidity.PanicV2.Eval.incDec_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms incDec_erase
/-- info: 'Solidity.PanicV2.Eval.assignIncDec_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assignIncDec_erase
/-- info: 'Solidity.PanicV2.Eval.incDec_local_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms incDec_local_failure

/-- info: 'Solidity.PanicV2.Eval.pushOpAssign_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pushOpAssign_erase
/-- info: 'Solidity.PanicV2.Eval.pushIncDec_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pushIncDec_erase
/-- info: 'Solidity.PanicV2.Eval.pushOpAssign_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pushOpAssign_full
/-- info: 'Solidity.PanicV2.Eval.pushIncDec_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pushIncDec_full
/-- info: 'Solidity.PanicV2.Eval.exhaustion_unclassified' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms exhaustion_unclassified

end Solidity.PanicV2.Eval
