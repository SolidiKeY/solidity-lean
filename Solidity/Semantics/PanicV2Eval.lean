import Solidity.Semantics.PanicV2

/-!
# Expression and path evaluation through the exact V2 result interface

This structural evaluator uses the same typed state and the same operand
order/short circuit as V1. Each path/value constructor has an unconditional
projection theorem. Site classifiers are refined by family; unclassified
failed options remain unknown rather than receiving guessed panic codes.
Arithmetic options now retain 0x11/0x12 at their actual failure branches;
statement-level compound assignments and increments are not yet migrated.
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
    let _ ← ofOpt (σ.storage.checkIndex r it k)
    pure (r.index it k)

def mpath (σ : State C Γ) : {T : Ty} → MPath C Γ T → Result (MVal σ.H T)
  | _, .var i _ => ofOpt (TEnv.get i σ.env)
  | _, .loc l => do ofOpt (σ.heap.readAddr (← mloc σ l))

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
  | _, .readMem l => do ofOpt (σ.heap.readAddr (← mloc σ l))
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
        erase_bind_congr (erase_ofOpt _) fun _ => rfl

theorem mpath_erase (σ : State C Γ) : {T : Ty} → (b : MPath C Γ T) →
    erase (mpath σ b) = b.mvalT σ
  | _, .var i _ => by
      simp only [mpath, MPath.mvalT, erase_ofOpt, TRes.ofOpt]
      cases TEnv.get i σ.env <;> rfl
  | _, .loc l => erase_bind_congr (mloc_erase σ l) fun _ => erase_ofOpt _

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
  | _, .readMem l => erase_bind_congr (mloc_erase σ l) fun _ => erase_ofOpt _
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

end Solidity.PanicV2.Eval
