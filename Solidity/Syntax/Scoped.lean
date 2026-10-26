import Solidity.Syntax
import Solidity.Scope

/-!
# The typed syntax, scoped

The typed syntax, with the locals in scope as an index
(`docs/intrinsic.md`, M2): every value is indexed by its type, every part is read in a context `Γ : Ctx`
(`Scope.lean`), a local is a position `Idx Γ t` that carries its type, and a
statement `Stmt C Γ Γ'` says which context it leaves.  So a local read
before it is declared, or at another type than declared, cannot be written:
the typing proofs need no locals check (`Typing/Soundness.lean`).

Scopes are explicit, as in solc: the branches of an `if` and of a `try`, a
loop's body and a block `{ … }` start from the enclosing context and their
locals end with them (the statement leaves `Γ`).  A call's body is closed
over a frame of its own, its return variables on its parameters
(`rs ++ ps`): the arguments are evaluated in the caller's context, and the
body sees nothing else.  What the call leaves in the caller's context is its
`CallRet`: nothing, a value assigned to a caller's local, or the return
variables themselves (a tuple's targets read them, and a memory return's
binding).

Names are labels on binders (`declLocal p x`, `Args.snoc`, `Binders`), not
part of the index (Gate G0, condition 3).  The printers keep them beside the
context, a `List Var` aligned with it, and write the Solidity the block was
read from.  `Stmt.wk` weakens a statement into a context with more
locals (`Thin`).  `Stmt.wk`/`Prog.wk` and `Idx.wk` use `match` and are also
evaluated by the kernel, once per `ifElseUnfold`, call or invariant rule
fired: the documented exceptions to condition 1 (`Calculus/Step.lean`).

The elaborator (`Syntax/Elab.lean`) emits these families, and the printers
(`Calculus/PrintStmt.lean`) read them.
-/

namespace Solidity

/-! ## Expressions -/

/-- A simple value (`se`): a literal of its type's range, a stack local, or
a value of the environment. -/
inductive Simple (C : Contract) (Γ : Ctx) : PrimTy → Type where
  | lit {p : PrimTy} (n : Int) (h : p.inRange n = true) : Simple C Γ p
  | bool (b : Bool) : Simple C Γ .bool
  | local {p : PrimTy} (i : Idx Γ (.val p)) : Simple C Γ p
  | env {p : PrimTy} (k : EnvKey) (hp : p = .uint) : Simple C Γ p

mutual

/-- A storage path of type `T`: an alias (`lsv`), or a location. -/
inductive SPath (C : Contract) (Γ : Ctx) : Ty → Type where
  | alias {R : RefTy} (i : Idx Γ (.alias R)) : SPath C Γ (.ref R)
  | loc {T : Ty} (l : Loc C Γ T) : SPath C Γ T

/-- A storage location: a state variable, a member, an entry. -/
inductive Loc (C : Contract) (Γ : Ctx) : Ty → Type where
  | root {T : Ty} (r : Name) (h : C.rootType r = some T) : Loc C Γ T
  | field {s : Name} {T : Ty} (b : SPath C Γ (.struct s)) (f : Name)
      (h : C.fieldType s f = some T) : Loc C Γ T
  | index {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) (b : SPath C Γ (.ref R))
      (i : Val C Γ k) : Loc C Γ V

/-- A memory path: a memory local (of a type that holds no mapping), or a
memory location. -/
inductive MPath (C : Contract) (Γ : Ctx) : Ty → Type where
  | var {R : RefTy} (i : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true) : MPath C Γ (.ref R)
  | loc {T : Ty} (l : MLoc C Γ T) : MPath C Γ T

/-- A member or an element of a memory object. -/
inductive MLoc (C : Contract) (Γ : Ctx) : Ty → Type where
  | field {s : Name} {T : Ty} (b : MPath C Γ (.struct s)) (f : Name)
      (h : C.fieldType s f = some T) : MLoc C Γ T
  | index {R : RefTy} {E : Ty} (a : ArrTy R E) (b : MPath C Γ (.ref R)) (i : Val C Γ .uint) :
      MLoc C Γ E

/-- A value of primitive type `p`. -/
inductive Val (C : Contract) (Γ : Ctx) : PrimTy → Type where
  | simple {p : PrimTy} (s : Simple C Γ p) : Val C Γ p
  | read {p : PrimTy} (l : Loc C Γ (.prim p)) : Val C Γ p
  | binop {p q : PrimTy} (op : BinOp) (h : op.accepts p = true) (hq : op.ret p = q)
      (a b : Val C Γ p) : Val C Γ q
  | unop {p q : PrimTy} (op : UnOp) (h : op.accepts p = true) (hq : op.ret p = q)
      (a : Val C Γ p) : Val C Γ q
  | ternary {p : PrimTy} (c : Val C Γ .bool) (a b : Val C Γ p) : Val C Γ p
  | readMem {p : PrimTy} (l : MLoc C Γ (.prim p)) : Val C Γ p
  | len {p : PrimTy} {E : Ty} (b : SPath C Γ (.array E)) (hp : p = .uint) : Val C Γ p
  | mlen {p : PrimTy} {E : Ty} (b : MPath C Γ (.array E)) (hp : p = .uint) : Val C Γ p
  | modular (op : ModOp) (a b k : Val C Γ .uint) : Val C Γ .uint
  /-- `keccak256(b)`, `sha256(b)`, … of a memory `bytes` (`Heap.hash`): the
  hash `k` computes of its bytes. -/
  | hash {p : PrimTy} {R : RefTy} (k : HashKind) (b : MPath C Γ (.ref R)) (hp : p = .uint) :
      Val C Γ p

end

/-- The source of a storage write: a value, a storage path copied, or a
memory object copied into storage. -/
inductive Src (C : Contract) (Γ : Ctx) : Ty → Type where
  | val {p : PrimTy} (v : Val C Γ p) : Src C Γ (.prim p)
  | copy {R : RefTy} (p : SPath C Γ (.ref R)) (h : (Ty.ref R).mapFree = true) : Src C Γ (.ref R)
  | fixedCopy {E : Ty} {n : Nat} {R : RefTy} (p : SPath C Γ (.ref (.fixed E n)))
      (shape : FixedCopy E n R) (h : E.mapFree = true) : Src C Γ (.ref R)
  | copyMem {R : RefTy} (p : MPath C Γ (.ref R)) : Src C Γ (.ref R)
  /-- A fixed memory snapshot copied to a compatible storage outer shape.
  The memory path already carries mapping-freedom. -/
  | fixedCopyMem {E : Ty} {n : Nat} {R : RefTy}
      (p : MPath C Γ (.ref (.fixed E n))) (shape : FixedCopy E n R) : Src C Γ (.ref R)

/-- What a storage alias is bound to: a path, or the slot `b.push()` appends. -/
inductive ARhs (C : Contract) (Γ : Ctx) (R : RefTy) where
  | path (p : SPath C Γ (.ref R))
  | push (b : SPath C Γ (.array (.ref R))) (hd : (Ty.ref R).defaultOkS = true)

/-- What a memory local is bound to: an object by identity, a deep copy of a
storage object, or a fresh array. -/
inductive MRhs (C : Contract) (Γ : Ctx) (R : RefTy) where
  | alias (p : MPath C Γ (.ref R))
  | copy (p : SPath C Γ (.ref R)) (hm : (Ty.ref R).mapFree = true)
  | newArr (n : Simple C Γ .uint) (h : R.newArrOk = true)

mutual
theorem MPath.mapFree {C : Contract} {Γ : Ctx} : {T : Ty} → MPath C Γ T → T.mapFree = true
  | _, .var _ hm => hm
  | _, .loc l => l.mapFree
theorem MLoc.mapFree {C : Contract} {Γ : Ctx} : {T : Ty} → MLoc C Γ T → T.mapFree = true
  | _, .field b _ h => Ty.mapFree_field b.mapFree h
  | _, .index .dyn b _ => b.mapFree
  | _, .index .fixed b _ => b.mapFree
end

theorem MRhs.mapFree {C : Contract} {Γ : Ctx} {R : RefTy} :
    MRhs C Γ R → (Ty.ref R).mapFree = true
  | .alias p => p.mapFree
  | .copy _ hm => hm
  | .newArr _ h => by
    cases R <;> simp only [RefTy.newArrOk, Bool.and_eq_true, Bool.false_eq_true] at h
    exact h.1

/-- Where a fresh array lands when it is not bound to a memory local. -/
inductive NewLhs (C : Contract) (Γ : Ctx) : RefTy → Type where
  | store {R : RefTy} (l : Loc C Γ (.ref R)) : NewLhs C Γ R
  | mem {R : RefTy} (l : MLoc C Γ (.ref R)) : NewLhs C Γ R

/-- What a memory location is written: a value, or a memory reference. -/
inductive MSrc (C : Contract) (Γ : Ctx) : Ty → Type where
  | val {p : PrimTy} (v : Val C Γ p) : MSrc C Γ (.prim p)
  | ref {R : RefTy} (p : MPath C Γ (.ref R)) : MSrc C Γ (.ref R)

/-- The target of `l ⊕= e` and `l++`. -/
inductive OpLoc (C : Contract) (Γ : Ctx) : PrimTy → Type where
  | local {p : PrimTy} (i : Idx Γ (.val p)) : OpLoc C Γ p
  | root {p : PrimTy} (r : Name) (h : C.rootType r = some (.prim p)) : OpLoc C Γ p
  | field {s : Name} {p : PrimTy} (b : SPath C Γ (.struct s)) (f : Name)
      (h : C.fieldType s f = some (.prim p)) : OpLoc C Γ p
  | index {R : RefTy} {k p : PrimTy} (it : IndexTy R k (.prim p)) (b : SPath C Γ (.ref R))
      (i : Simple C Γ k) : OpLoc C Γ p
  | mfield {s : Name} {p : PrimTy} (b : MPath C Γ (.struct s)) (f : Name)
      (h : C.fieldType s f = some (.prim p)) : OpLoc C Γ p
  | mindex {R : RefTy} {p : PrimTy} (a : ArrTy R (.prim p)) (b : MPath C Γ (.ref R))
      (i : Simple C Γ .uint) : OpLoc C Γ p

/-! ### Which parts are simple -/

def Val.isSimple {C : Contract} {Γ : Ctx} {p : PrimTy} : Val C Γ p → Bool
  | .simple _ => true
  | _ => false

/-- Whether this expression needs a Lean-only assignment rule at its root:
native modular arithmetic, `keccak256`. -/
def Val.isLeanOnly {C : Contract} {Γ : Ctx} {p : PrimTy} : Val C Γ p → Bool
  | .modular .. | .hash .. => true
  | _ => false

def SPath.isSimple {C : Contract} {Γ : Ctx} {T : Ty} : SPath C Γ T → Bool
  | .alias _ => true
  | .loc (.root ..) => true
  | .loc _ => false

def MPath.isSimple {C : Contract} {Γ : Ctx} {T : Ty} : MPath C Γ T → Bool
  | .var .. => true
  | .loc _ => false

def OpLoc.recvSimple {C : Contract} {Γ : Ctx} {p : PrimTy} : OpLoc C Γ p → Bool
  | .field b _ _ | .index _ b _ => b.isSimple
  | .mfield b _ _ | .mindex _ b _ => b.isSimple
  | _ => true

def Val.toSimple? {C : Contract} {Γ : Ctx} {p : PrimTy} : Val C Γ p → Option (Simple C Γ p)
  | .simple s => some s
  | _ => none

/-! ## Calls -/

/-- A call's arguments, each the value `e` its parameter `x : p` is bound
to, in the order they are bound: the last is innermost in the frame `ps`.
Every argument is evaluated in the caller's context `Γ`. -/
inductive Args (C : Contract) (Γ : Ctx) : Ctx → Type where
  | nil : Args C Γ []
  | snoc {ps : Ctx} (as : Args C Γ ps) (p : PrimTy) (x : Var) (e : Val C Γ p) :
      Args C Γ (.val p :: ps)
  /-- A storage parameter shares the selected storage identity. -/
  | snocStorage {ps : Ctx} (as : Args C Γ ps) (R : RefTy) (x : Var)
      (e : SPath C Γ (.ref R)) : Args C Γ (.alias R :: ps)
  /-- A memory parameter shares an existing object; caller preparation does copies. -/
  | snocMemory {ps : Ctx} (as : Args C Γ ps) (R : RefTy) (x : Var)
      (e : MPath C Γ (.ref R)) : Args C Γ (.mem R :: ps)

/-- What a call does with its return variables `rs`, which its frame
declares at their defaults on its parameters, and the context `Γ'` it
leaves the caller in:

* `none`: no return variable (a function of several returns called as a
  statement declares them in its body);
* `val p r res`: one, `r`, its value assigned to the caller's `res` if the
  call is assigned (`y = f(a);`);
* `rets bs`: several (or one with a target), left in the caller's context,
  where the tuple's targets read them (`(lo, hi) = f(a);` is the call and
  `lo = r0; hi = r1;`), KeY's `functionBodyExpand`;
* `mem R r`: a memory return, a fresh default object (as solc allocates one
  on entry), left in the caller's context for the statement after the call
  to bind (`Person memory m = f();` is the call and `Person memory m = r;`);
* `storage R r`: an unset storage alias on entry, exported by identity for
  the following storage declaration or rebinding. -/
inductive CallRet (Γ : Ctx) : Ctx → Ctx → Type where
  | none : CallRet Γ [] Γ
  | val (p : PrimTy) (r : Var) (res : Option (Idx Γ (.val p))) : CallRet Γ [.val p] Γ
  | rets {rs : Ctx} (bs : Binders rs) : CallRet Γ rs (rs ++ Γ)
  | mem (R : RefTy) (r : Var) (hd : (Ty.ref R).defaultOkS = true)
      (hm : (Ty.ref R).mapFree = true) : CallRet Γ [.mem R] (.mem R :: Γ)
  /-- A storage return is an alias, initially unset and exported by identity. -/
  | storage (R : RefTy) (r : Var) : CallRet Γ [.alias R] (.alias R :: Γ)

/-- An argument of an external call, at its type. -/
abbrev ExtArg (C : Contract) (Γ : Ctx) := (p : PrimTy) × Simple C Γ p

/-- `a.f(e₁, …, eₙ)`: an external call, its receiver and arguments simple. -/
structure ExtCall (C : Contract) (Γ : Ctx) where
  addr : Simple C Γ .uint
  fn : Name
  args : List (ExtArg C Γ)

/-- A quantified clause of a loop's invariant, `/// @custom:key invariant
\forall T x; a -> c` (solkey's specification language above a loop): its
bound local the innermost of its body's context, read by the invariant
rules as `∀` (`invFml`, `Calculus/Blocks.lean`). -/
inductive LoopQ (C : Contract) : Ctx → Type where
  | val {Γ : Ctx} (a : Val C Γ .bool) : LoopQ C Γ
  | imp {Γ : Ctx} (a c : Val C Γ .bool) : LoopQ C Γ
  | all {Γ : Ctx} (x : Var) (p : PrimTy) (body : LoopQ C (.val p :: Γ)) : LoopQ C Γ

/-- How a loop is proved: a written unwind bound, an invariant/variant,
or automatic unwinding within the proof search's existing budget.  An
invariant's `brk` says the loop was lowered with a `break` flag
(`Val.breakExit`, solkey's `\getLoopBreak`), and `qs` are its quantified
clauses, conjoined after `I`. -/
inductive LoopAnn (C : Contract) (Γ : Ctx) where
  | unwind (k : Nat)
  | inv (I : Val C Γ .bool) (dec : Option (Val C Γ .uint)) (brk : Bool) (qs : List (LoopQ C Γ))
  | auto

/-- The two ways the same `whileUnwind` taclet takes another iteration. -/
inductive LoopUnwind where
  | bounded (remaining : Nat)
  | automatic

def LoopUnwind.before {C : Contract} {Γ : Ctx} : LoopUnwind → LoopAnn C Γ
  | .bounded n => .unwind (n + 1)
  | .automatic => .auto

def LoopUnwind.after {C : Contract} {Γ : Ctx} : LoopUnwind → LoopAnn C Γ
  | .bounded n => .unwind n
  | .automatic => .auto

/-! ## Revert data -/

/-- What a catch binds, or how a memory operand is returned as revert data. -/
inductive CatchKind where
  | reason
  | raw
  deriving Repr, DecidableEq, Inhabited

/-- A memory byte string is an array of words holding individual bytes. -/
abbrev bytesR : RefTy := .array (.prim .uint)

/-- A part of the data `Stmt.revertData` reverts with
(`docs/semantic-gaps.md`, "Revert data"): literal bytes (an `Error(string)`
encoding of a literal reason), a custom error's selector (`customSelector`,
uninterpreted per signature), or a value as its ABI word. -/
inductive RevPart (C : Contract) (Γ : Ctx) where
  | bytes (bs : List UInt8)
  | sel (sig : String)
  | word {p : PrimTy} (v : Val C Γ p)
  /-- Copy the local's bytes from the heap at the revert: raw, or ABI Error(string). -/
  | mem (kind : CatchKind) (src : Idx Γ (.mem bytesR))

/-! ## Statements -/

/-- The array operation after a storage-returning receiver call. Its source
is read in the caller after the getter, and the returned alias is temporary. -/
inductive ReceiverOp (C : Contract) (Γ : Ctx) (E : Ty) where
  | push (v : Option (Src C Γ E)) (hd : (v.isSome || E.defaultOkS) = true)
  | pop

mutual

/-- A statement of contract `C`, read in `Γ`, leaving `Γ'`: a declaration
pushes its local, a call may leave its return variables, every other
statement leaves `Γ`. -/
inductive Stmt (C : Contract) : Ctx → Ctx → Type where
  | assign {Γ : Ctx} {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) : Stmt C Γ Γ
  | rebind {Γ : Ctx} {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R) : Stmt C Γ Γ
  | assignLocal {Γ : Ctx} {p : PrimTy} (i : Idx Γ (.val p)) (r : Val C Γ p) : Stmt C Γ Γ
  | declLocal {Γ : Ctx} (p : PrimTy) (x : Var) (init : Option (Val C Γ p)) :
      Stmt C Γ (.val p :: Γ)
  /-- `Person storage lsv = sp;`, and `Person storage lsv;`, an unset alias
  through which a read reverts. -/
  | declStorage {Γ : Ctx} (R : RefTy) (x : Var) (init : Option (ARhs C Γ R)) :
      Stmt C Γ (.alias R :: Γ)
  | opAssign {Γ : Ctx} {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
      (hp : p.isNumeric = true) (l : OpLoc C Γ p) (r : Val C Γ p) : Stmt C Γ Γ
  | incDec {Γ : Ctx} {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
      Stmt C Γ Γ
  | assignIncDec {Γ : Ctx} {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec)
      (hp : p.isNumeric = true) (l : OpLoc C Γ p) (hs : l.recvSimple = true) : Stmt C Γ Γ
  /-- `y = values.push();` with `y` a value local: the slot appended, `y` its
  default. A complex receiver is captured by the calculus before the push. -/
  | assignLocalPush {Γ : Ctx} {p : PrimTy} (i : Idx Γ (.val p))
      (b : SPath C Γ (.array (.prim p))) : Stmt C Γ Γ
  | push {Γ : Ctx} {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E))
      (hd : (v.isSome || E.defaultOkS) = true) : Stmt C Γ Γ
  | pop {Γ : Ctx} {E : Ty} (b : SPath C Γ (.array E)) : Stmt C Γ Γ
  | transfer {Γ : Ctx} (r a : Val C Γ .uint) : Stmt C Γ Γ
  /-- `pv = r.send(a);`, or with `full` the value call
  `(pv, ) = r.call{value: a}("");`, which forwards all the gas: its callee
  may call back under either `transferSemantics` (`Stmt.forksIn`). -/
  | send {Γ : Ctx} (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) (full : Bool) : Stmt C Γ Γ
  | declMem {Γ : Ctx} (R : RefTy) (x : Var) (init : Option (MRhs C Γ R))
      (hd : (init.isSome || (Ty.ref R).defaultOkS) = true) (hm : (Ty.ref R).mapFree = true) :
      Stmt C Γ (.mem R :: Γ)
  | rebindMem {Γ : Ctx} {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) : Stmt C Γ Γ
  | assignFromMem {Γ : Ctx} {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
      Stmt C Γ Γ
  | assignMem {Γ : Ctx} {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) : Stmt C Γ Γ
  | delete {Γ : Ctx} {T : Ty} (l : Loc C Γ T) : Stmt C Γ Γ
  | deleteMem {Γ : Ctx} {T : Ty} (p : MPath C Γ T) (hd : T.defaultOkS = true) : Stmt C Γ Γ
  | assignNew {Γ : Ctx} {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint)
      (h : R.newArrOk = true) : Stmt C Γ Γ
  /-- `if (c) { … } else { … }`: each branch a scope. -/
  | ite {Γ Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (thn : Prog C Γ Γ₁) (els : Prog C Γ Γ₂) : Stmt C Γ Γ
  | require {Γ : Ctx} (c : Val C Γ .bool) : Stmt C Γ Γ
  | assert {Γ : Ctx} (c : Val C Γ .bool) : Stmt C Γ Γ
  | revert {Γ : Ctx} : Stmt C Γ Γ
  /-- `assume(false);`: a run the readings assume away.  It halts as
  exhaustion does, which both modalities accept (`ignoringOverflow { … }`,
  `docs/options.md` O5); no Solidity source writes it. -/
  | assumeFalse {Γ : Ctx} : Stmt C Γ Γ
  /-- An internal call of `f`: the arguments bound to the parameters `ps`,
  the return variables `rs` declared on them, the body run in that frame. -/
  | call {Γ Γ' ps rs Γf : Ctx} (f : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Γ')
      (body : Prog C (rs ++ ps) Γf) : Stmt C Γ Γ'
  /-- `try a.f(e) returns (…) { ok } catch Error(string memory) { err }
  catch Panic(uint c) { panic } catch { other }`: `ok` sees the returned
  values `rets`, `panic` the code.  With `self`, the callee `f` is a function
  of this contract declared before the caller: `sbody` is its body in a
  frame of its own (the parameters bound to `sargs`, the return variables
  `ρ`), `msg.sender` read as `address(this)` and `msg.value` as `0`, which
  runs when the receiver is the contract itself (`TRun.tryCall`,
  `docs/options.md` O8). -/
  | tryCall {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} (call : ExtCall C Γ) (rets : Binders ρ)
      (ok : Prog C (ρ ++ Γ) Γ₁) (err : Prog C Γ Γ₂) (code : CodeBinder κ)
      (panic : Prog C (κ ++ Γ) Γ₃) (other : Prog C Γ Γ₄) (sargs : Args C Γ ps)
      (sbody : Prog C (ρ ++ ps) Γf) (self : Bool) : Stmt C Γ Γ
  /-- `while (c) { … }`: the body a scope, popped every iteration. -/
  | loop {Γ Γ₁ : Ctx} (a : LoopAnn C Γ) (c : Val C Γ .bool) (body : Prog C Γ Γ₁) : Stmt C Γ Γ
  /-- `{ … }`: a block, its locals ending with it. -/
  | block {Γ Γ₁ : Ctx} (body : Prog C Γ Γ₁) : Stmt C Γ Γ
  /-- `values.push() += e`: evaluate the RHS, append/reset one primitive
  slot, then perform the checked compound assignment at that slot. -/
  | pushOpAssign {Γ : Ctx} {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
      (hp : p.isNumeric = true) (b : SPath C Γ (.array (.prim p))) (r : Val C Γ p) : Stmt C Γ Γ
  /-- `++values.push()` / `values.push()++` (and decrement), as statements.
  The value is discarded; the appended slot is changed once. -/
  | pushIncDec {Γ : Ctx} {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
      (b : SPath C Γ (.array (.prim p))) : Stmt C Γ Γ
  /-- `f(args).push(e)`, `f(args).push()` or `f(args).pop()`: the receiver call
  remains one statement until the native storage-alias capture fires. -/
  | callReceiver {Γ ps Γf : Ctx} {E : Ty} (f : Name) (args : Args C Γ ps) (r : Var)
      (body : Prog C ([.alias (.array E)] ++ ps) Γf) (op : ReceiverOp C Γ E) : Stmt C Γ Γ
  /-- `f(args).push(e)` when `e` has effects. Its scoped prefix and source
  remain inside the receiver statement, to run after the getter. -/
  | callReceiverPush {Γ ps Γf Γv : Ctx} {E : Ty} (f : Name) (args : Args C Γ ps) (r : Var)
      (body : Prog C ([.alias (.array E)] ++ ps) Γf)
      (code : Prog C Γ Γv) (value : Src C Γv E) : Stmt C Γ Γ
  /-- A call of a recursive function `f` (Lean only, `docs/kernel-port.md`,
  "Recursion"): as `call`, its body run in a frame of its own, the body a
  block (`rs ++ ps` on both sides) held behind a thunk, so that a body which
  calls `f` again holds that call's body, one frame deeper, and no printer,
  quoter or analysis unfolds it.  `d` is how many frames the unrolling has
  left: the elaborator writes `recUnroll Prog.recBase step recDepth`, whose
  bottom frame halts with `exhausted` (`assume(false);`), the EVM's stack
  of 1024 words holding at most 1024 nested frames.  The run is the call's
  (`TRun.call`, `Stmt.run_callRec`); `d` is read by the quoters only. -/
  | callRec {Γ Γ' ps rs : Ctx} (f : Name) (d : Nat) (args : Args C Γ ps) (ret : CallRet Γ rs Γ')
      (body : Unit → Prog C (rs ++ ps) (rs ++ ps)) : Stmt C Γ Γ'
  /-- `revert(d)`: a revert with the data `d` (Lean only, `docs/semantic-gaps.md`,
  "Revert data"): `require(c, "m")`, `revert("m")` and `revert E(a)` in the
  callee a self-call `try` runs, where a `catch` may read it. -/
  | revertData {Γ : Ctx} (d : List (RevPart C Γ)) : Stmt C Γ Γ
  /-- A `catch` clause that names the data (Lean only): `x` bound to what the
  call `call` reverts with (`kind`: the decoded `Error` reason, or the raw
  data), read from the state the `try` started in — for a self-call the
  callee's run again (`sargs`, `sbody` as `Stmt.tryCall`'s), otherwise the
  transaction's entry — then `body`, its locals popped. -/
  | catchData {Γ ρ ps Γf Γ₁ : Ctx} (call : ExtCall C Γ) (rets : Binders ρ) (sargs : Args C Γ ps)
      (sbody : Prog C (ρ ++ ps) Γf) (self : Bool) (kind : CatchKind) (x : Var)
      (body : Prog C (.mem bytesR :: Γ) Γ₁) : Stmt C Γ Γ

/-- A sequence of statements, each read where the one before leaves. -/
inductive Prog (C : Contract) : Ctx → Ctx → Type where
  | nil {Γ : Ctx} : Prog C Γ Γ
  | cons {Γ Γ₁ Γ₂ : Ctx} (s : Stmt C Γ Γ₁) (P : Prog C Γ₁ Γ₂) : Prog C Γ Γ₂

end

/-! ## Recursion -/

/-- The bottom frame of a recursive call's unrolling: it halts as resource
exhaustion does (`assume(false);`), which both modalities accept. -/
def Prog.recBase {Γ : Ctx} : Prog C Γ Γ := .cons .assumeFalse .nil

/-- **The unrolling of a recursive function**: `n` frames, each `step k`
of the frame below it (`k` frames left there), behind a thunk, on `base`.
The elaborator writes a recursive call's body as
`recUnroll Prog.recBase step recDepth`. -/
def recUnroll {α : Type} (base : α) (step : Nat → (Unit → α) → α) : Nat → α
  | 0 => base
  | n + 1 => step n (fun _ => recUnroll base step n)

/-- The frames a recursive call is unrolled to: the EVM's stack holds 1024
words and every internal call's frame at least its return address, so no
run nests deeper (a deeper one halts on the stack's overflow, as the
bottom frame halts, `exhausted`). -/
def recDepth : Nat := 1024

/-- **Induction over an unrolling**: what holds of the base and of each
step from the frame below holds of every unrolling. -/
theorem recUnroll_induct {α : Type} {base : α} {step : Nat → (Unit → α) → α} (P : α → Prop)
    (h0 : P base) (hs : ∀ n (t : Unit → α), P (t ()) → P (step n t)) :
    ∀ n, P (recUnroll base step n)
  | 0 => h0
  | n + 1 => hs n _ (recUnroll_induct P h0 hs n)

/-! ## Printing

The printers write `Syntax.lean`'s Solidity: `ns` are the names of the
locals of the context, innermost first. -/

section Print

variable {C : Contract} [FreshNames]

def Simple.toStr {Γ : Ctx} {p : PrimTy} (ns : List Var) : Simple C Γ p → String
  | .lit n _ => toString n
  | .bool b => toString b
  | .local i => toString (i.name ns)
  | .env k _ => k.toStr

mutual

def SPath.toStr {Γ : Ctx} {T : Ty} (ns : List Var) : SPath C Γ T → String
  | .alias i => toString (i.name ns)
  | .loc l => l.toStr ns

def Loc.toStr {Γ : Ctx} {T : Ty} (ns : List Var) : Loc C Γ T → String
  | .root r _ => r
  | .field b f _ => s!"{b.toStr ns}.{f}"
  | .index _ b i => s!"{b.toStr ns}[{i.toStr ns true}]"

def MPath.toStr {Γ : Ctx} {T : Ty} (ns : List Var) : MPath C Γ T → String
  | .var i _ => toString (i.name ns)
  | .loc l => l.toStr ns

def MLoc.toStr {Γ : Ctx} {T : Ty} (ns : List Var) : MLoc C Γ T → String
  | .field b f _ => s!"{b.toStr ns}.{f}"
  | .index _ b i => s!"{b.toStr ns}[{i.toStr ns true}]"

/-- `top` is whether the value stands alone, so needs no parentheses. -/
def Val.toStr {Γ : Ctx} {p : PrimTy} (ns : List Var) : Val C Γ p → (top : Bool := false) → String
  | .simple s, _ => s.toStr ns
  | .read l, _ => l.toStr ns
  | .binop op _ _ a b, top =>
    let s := s!"{a.toStr ns} {BinOp.sym op} {b.toStr ns}"
    if top then s else s!"({s})"
  | .unop op _ _ a, _ => op.show (a.toStr ns (op matches .toInt | .toUint))
  | .ternary c a b, top =>
    let s := s!"{c.toStr ns} ? {a.toStr ns} : {b.toStr ns}"
    if top then s else s!"({s})"
  | .readMem l, _ => l.toStr ns
  | .len b _, _ => s!"{b.toStr ns}.length"
  | .mlen b _, _ => s!"{b.toStr ns}.length"
  | .modular op a b k, _ => s!"{op.toStr}({a.toStr ns true}, {b.toStr ns true}, {k.toStr ns true})"
  | .hash k b _, _ => s!"{k.toStr}({b.toStr ns})"

end

def Src.toStr {Γ : Ctx} {T : Ty} (ns : List Var) : Src C Γ T → String
  | .val v => v.toStr ns true
  | .copy p _ => p.toStr ns
  | .fixedCopy p _ _ => p.toStr ns
  | .copyMem p => p.toStr ns
  | .fixedCopyMem p _ => p.toStr ns

def ARhs.toStr {Γ : Ctx} {R : RefTy} (ns : List Var) : ARhs C Γ R → String
  | .path p => p.toStr ns
  | .push b _ => s!"{b.toStr ns}.push()"

def OpLoc.toStr {Γ : Ctx} {p : PrimTy} (ns : List Var) : OpLoc C Γ p → String
  | .local i => toString (i.name ns)
  | .root r _ => r
  | .field b f _ => s!"{b.toStr ns}.{f}"
  | .index _ b i => s!"{b.toStr ns}[{i.toStr ns}]"
  | .mfield b f _ => s!"{b.toStr ns}.{f}"
  | .mindex _ b i => s!"{b.toStr ns}[{i.toStr ns}]"

def MRhs.toStr {Γ : Ctx} {R : RefTy} (ns : List Var) : MRhs C Γ R → String
  | .alias p => p.toStr ns
  | .copy p _ => p.toStr ns
  | .newArr n _ => s!"new {Ty.toStr (.ref R)}({n.toStr ns})"

def NewLhs.toStr {Γ : Ctx} {R : RefTy} (ns : List Var) : NewLhs C Γ R → String
  | .store l => l.toStr ns
  | .mem l => l.toStr ns

def MSrc.toStr {Γ : Ctx} {T : Ty} (ns : List Var) : MSrc C Γ T → String
  | .val v => v.toStr ns true
  | .ref p => p.toStr ns

/-- A quantified clause as written, `\forall uint q; a -> c`. -/
def LoopQ.toStr : {Γ : Ctx} → List Var → LoopQ C Γ → String
  | _, ns, .val a => a.toStr ns true
  | _, ns, .imp a c => s!"{a.toStr ns true} -> {c.toStr ns true}"
  | _, ns, .all x p b => s!"\\forall {p.toStr} {x}; {LoopQ.toStr (x :: ns) b}"

def LoopAnn.toStr {Γ : Ctx} (ns : List Var) : LoopAnn C Γ → String
  | .auto => ""
  | .unwind k => s!"/// @custom:key unwind {k} "
  | .inv I dec _ qs =>
    s!"/// @custom:key invariant {I.toStr ns true} " ++
      String.join (qs.map fun q => s!"/// @custom:key invariant {q.toStr ns} ") ++
      ((dec.map fun d => s!"/// @custom:key decreases {d.toStr ns true} ").getD "")

/-- The arguments as written, in order. -/
def Args.toStrs {Γ : Ctx} (ns : List Var) : {ps : Ctx} → Args C Γ ps → List String
  | _, .nil => []
  | _, .snoc as _ _ e => as.toStrs ns ++ [e.toStr ns true]
  | _, .snocStorage as _ _ e => as.toStrs ns ++ [e.toStr ns]
  | _, .snocMemory as _ _ e => as.toStrs ns ++ [e.toStr ns]

/-- The parameters' names, innermost first: the frame's names below the
return variables. -/
def Args.names {Γ : Ctx} : {ps : Ctx} → Args C Γ ps → List Var
  | _, .nil => []
  | _, .snoc as _ x _ => x :: as.names
  | _, .snocStorage as _ x _ | _, .snocMemory as _ x _ => x :: as.names

/-- The return variables' names, innermost first. -/
def CallRet.names {Γ : Ctx} : {rs Γ' : Ctx} → CallRet Γ rs Γ' → List Var
  | _, _, .none => []
  | _, _, .val _ r _ => [r]
  | _, _, .rets bs => bs.names
  | _, _, .mem _ r _ _ => [r]
  | _, _, .storage _ r => [r]

/-- The names of the context a call leaves its caller in. -/
def CallRet.outNames {Γ : Ctx} (ns : List Var) : {rs Γ' : Ctx} → CallRet Γ rs Γ' → List Var
  | _, _, .none => ns
  | _, _, .val .. => ns
  | _, _, .rets bs => bs.names ++ ns
  | _, _, .mem _ r _ _ => r :: ns
  | _, _, .storage _ r => r :: ns

/-- The names of the context a statement leaves. -/
def Stmt.outNames {Γ Γ' : Ctx} (ns : List Var) : Stmt C Γ Γ' → List Var
  | .declLocal _ x _ => x :: ns
  | .declStorage _ x _ => x :: ns
  | .declMem _ x .. => x :: ns
  | .call _ _ ret _ => ret.outNames ns
  | .callRec _ _ _ ret _ => ret.outNames ns
  | _ => ns

/-- The names of the context a block leaves. -/
def Prog.outNames {Γ : Ctx} (ns : List Var) : {Γ' : Ctx} → Prog C Γ Γ' → List Var
  | _, .nil => ns
  | _, .cons s P => P.outNames (s.outNames ns)

/-- `f(e₁, …, eₙ);` -/
def callStr {Γ : Ctx} {ps : Ctx} (ns : List Var) (f : Name) (args : Args C Γ ps) : String :=
  s!"{f}({", ".intercalate (args.toStrs ns)});"

/-- A call returning a memory reference: its return variable and the call. -/
def Stmt.memRet? {Γ Γ' : Ctx} (ns : List Var) : Stmt C Γ Γ' → Option (Var × String)
  | .call f args (.mem _ r _ _) _ => some (r, callStr ns f args)
  | _ => none

/-- A statement binding a memory local to a local (`Person memory m = r;`,
`m = r;`): the local read, and how the statement writes with the call in
its place. -/
def Stmt.bindsMem? {Γ Γ' : Ctx} (ns : List Var) : Stmt C Γ Γ' → Option (Var × (String → String))
  | .declMem R x (some (.alias (.var i _))) _ _ =>
    some (i.name ns, fun c => s!"{Ty.toStr (.ref R)} memory {x} = {c}")
  | .rebindMem x (.alias (.var i _)) =>
    some (i.name ns, fun c => s!"{x.name ns} = {c}")
  | _ => none

/-- A memory call and the statement after it that binds its return
variable, written as the statement they are elaborated from. -/
def Stmt.memCallStr? {Γ Γ₁ Γ₂ : Ctx} (ns : List Var) (s : Stmt C Γ Γ₁) (P : Prog C Γ₁ Γ₂) :
    Option String :=
  match s.memRet? ns, P with
  | some (r, c), .cons t _ =>
    match t.bindsMem? (s.outNames ns) with
    | some (r', w) => if r' = r then some (w c) else none
    | none => none
  | _, _ => none

/-- A storage-returning call: its exported alias and the call. -/
def Stmt.storageRet? {Γ Γ' : Ctx} (ns : List Var) : Stmt C Γ Γ' → Option (Var × String)
  | .call f args (.storage _ r) _ => some (r, callStr ns f args)
  | _ => none

/-- A storage declaration or rebinding that consumes the exported alias. -/
def Stmt.bindsStorage? {Γ Γ' : Ctx} (ns : List Var) :
    Stmt C Γ Γ' → Option (Var × (String → String))
  | .declStorage R x (some (.path (.alias i))) =>
    some (i.name ns, fun c => s!"{Ty.toStr (.ref R)} storage {x} = {c}")
  | .rebind x (.path (.alias i)) =>
    some (i.name ns, fun c => s!"{x.name ns} = {c}")
  | _ => none

/-- A storage call and its following binding as their original source statement. -/
def Stmt.storageCallStr? {Γ Γ₁ Γ₂ : Ctx} (ns : List Var) (s : Stmt C Γ Γ₁)
    (P : Prog C Γ₁ Γ₂) : Option String :=
  match s.storageRet? ns, P with
  | some (r, c), .cons t _ =>
    match t.bindsStorage? (s.outNames ns) with
    | some (r', w) => if r' = r then some (w c) else none
    | none => none
  | _, _ => none

/-- The target a statement after a call of several returns assigns one of
them to (`lo = r0;`): the return's position among `rs`, and the target. -/
def Stmt.retTarget? {Γ Γ' : Ctx} (rs : List Var) (ns : List Var) :
    Stmt C Γ Γ' → Option (Nat × String)
  | .assignLocal x (.simple (.local r)) => (rs.findIdx? (· == r.name ns)).map (·, toString (x.name ns))
  | .assign l (.val (.simple (.local r))) => (rs.findIdx? (· == r.name ns)).map (·, l.toStr ns)
  | .assignMem l (.val (.simple (.local r))) => (rs.findIdx? (· == r.name ns)).map (·, l.toStr ns)
  | _ => none

/-- The statements after a call of several returns that assign them, in
their order, from the `start`-th return on. -/
def Prog.retTargets {Γ Γ' : Ctx} (rs : List Var) (start : Nat) (ns : List Var) :
    Prog C Γ Γ' → List (Nat × String)
  | .nil => []
  | .cons s P =>
    match s.retTarget? rs ns with
    | some (i, t) => if start ≤ i then (i, t) :: Prog.retTargets rs (i + 1) (s.outNames ns) P else []
    | none => []

/-- A call of several returns: their names in order, and the call. -/
def Stmt.tupleRets? {Γ Γ' : Ctx} (ns : List Var) : Stmt C Γ Γ' → Option (List Var × String)
  | .call f args (.rets bs) _ => some (bs.toList.map (·.2), callStr ns f args)
  | .callRec f _ args (.rets bs) _ => some (bs.toList.map (·.2), callStr ns f args)
  | _ => none

/-- A call of several returns and the statements after it that assign them,
written as the tuple assignment they are elaborated from, with the number
of statements after the call it covers. -/
def Stmt.tupleCallStr? {Γ Γ₁ Γ₂ : Ctx} (ns : List Var) (s : Stmt C Γ Γ₁) (P : Prog C Γ₁ Γ₂) :
    Option (String × Nat) :=
  match s.tupleRets? ns with
  | none => none
  | some (rs, cs) =>
    let ts := Prog.retTargets rs 0 (s.outNames ns) P
    if ts.isEmpty then
      if rs.length < 2 then none
      else some (s!"({String.mk (List.replicate (rs.length - 1) ',')}) = {cs}", 0)
    else if rs.length == 1 then some (s!"{((ts.head?).map (·.2)).getD ""} = {cs}", ts.length)
    else
      let slots := (List.range rs.length).map fun i => ((ts.find? (·.1 == i)).map (·.2)).getD ""
      some (s!"({", ".intercalate slots}) = {cs}", ts.length)

/-- Whether a printed primitive reads the local at position `n`. -/
def Simple.readsLocal {Γ : Ctx} {p : PrimTy} (n : Nat) : Simple C Γ p → Bool
  | .local i => i.toNat == n
  | .lit .. | .bool _ | .env .. => false

mutual

def SPath.readsLocal {Γ : Ctx} (n : Nat) : {T : Ty} → SPath C Γ T → Bool
  | _, .alias i => i.toNat == n
  | _, .loc l => l.readsLocal n

def Loc.readsLocal {Γ : Ctx} (n : Nat) : {T : Ty} → Loc C Γ T → Bool
  | _, .root .. => false
  | _, .field b _ _ => b.readsLocal n
  | _, .index _ b i => b.readsLocal n || i.readsLocal n

def MPath.readsLocal {Γ : Ctx} (n : Nat) : {T : Ty} → MPath C Γ T → Bool
  | _, .var i _ => i.toNat == n
  | _, .loc l => l.readsLocal n

def MLoc.readsLocal {Γ : Ctx} (n : Nat) : {T : Ty} → MLoc C Γ T → Bool
  | _, .field b _ _ => b.readsLocal n
  | _, .index _ b i => b.readsLocal n || i.readsLocal n

def Val.readsLocal {Γ : Ctx} (n : Nat) : {p : PrimTy} → Val C Γ p → Bool
  | _, .simple s => s.readsLocal n
  | _, .read l => l.readsLocal n
  | _, .binop _ _ _ a b => a.readsLocal n || b.readsLocal n
  | _, .unop _ _ _ a => a.readsLocal n
  | _, .ternary c a b => c.readsLocal n || a.readsLocal n || b.readsLocal n
  | _, .readMem l => l.readsLocal n
  | _, .len b _ => b.readsLocal n
  | _, .mlen b _ => b.readsLocal n
  | _, .modular _ a b k => a.readsLocal n || b.readsLocal n || k.readsLocal n
  | _, .hash _ b _ => b.readsLocal n

end

/-- The dependencies of a printed increment lvalue include every path index. -/
def OpLoc.readsLocal {Γ : Ctx} {p : PrimTy} (n : Nat) : OpLoc C Γ p → Bool
  | .local i => i.toNat == n
  | .root .. => false
  | .field b _ _ => b.readsLocal n
  | .index _ b i => b.readsLocal n || i.readsLocal n
  | .mfield b _ _ => b.readsLocal n
  | .mindex _ b i => b.readsLocal n || i.readsLocal n

/-- A source call may be reconstructed only when its arguments exclude the private local. -/
def Args.readsLocal {Γ : Ctx} (n : Nat) : {ps : Ctx} → Args C Γ ps → Bool
  | _, .nil => false
  | _, .snoc args _ _ value => args.readsLocal n || value.readsLocal n
  | _, .snocStorage args _ _ value => args.readsLocal n || value.readsLocal n
  | _, .snocMemory args _ _ value => args.readsLocal n || value.readsLocal n

/-- Reconstruct a sole increment or primitive call captured as a receiver operand.
Arbitrary statement prefixes have no single Solidity-expression spelling. -/
def Prog.receiverExpr? {Γ Γv : Ctx} {E : Ty} (ns : List Var)
    (code : Prog C Γ Γv) (value : Src C Γv E) : Option String :=
  match code, value with
  | .nil, _ => none
  | .cons (.declLocal _ x none)
      (.cons (.assignIncDec i op _ l _) .nil), .val (.simple (.local j)) =>
    if i.toNat == 0 && j.toNat == 0 && !l.readsLocal 0 then
      some (IncDec.show op (l.toStr (x :: ns))) else none
  | .cons (.declLocal _ x none)
      (.cons (.call f args (.val _ _ (some i)) _) .nil), .val (.simple (.local j)) =>
    if i.toNat == 0 && j.toNat == 0 && !args.readsLocal 0 then
      some s!"{f}({", ".intercalate (args.toStrs (x :: ns))})"
    else none
  | _, _ => none

/-- Bytes as a hex literal. -/
def hexStr (bs : List UInt8) : String :=
  let hex (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'
  "hex\"" ++ String.mk (bs.flatMap fun b => [hex (b.toNat / 16), hex (b.toNat % 16)]) ++ "\""

/-- A part of revert data. -/
def RevPart.toStr {Γ : Ctx} (ns : List Var) : RevPart C Γ → String
  | .bytes bs => hexStr bs
  | .sel sig => s!"selector(\"{sig}\")"
  | .word v => s!"abi.encode({v.toStr ns true})"
  | .mem .raw src => s!"bytes({src.name ns})"
  | .mem .reason src => s!"Error({src.name ns})"

mutual

def Stmt.toStr {Γ Γ' : Ctx} (ns : List Var) : Stmt C Γ Γ' → String
  | .assign l r => s!"{l.toStr ns} = {r.toStr ns};"
  | .rebind x r => s!"{x.name ns} = {r.toStr ns};"
  | .assignLocal x r => s!"{x.name ns} = {r.toStr ns true};"
  | .declLocal p x init =>
    match init with
    | none => s!"{Ty.toStr (.prim p)} {x};"
    | some e => s!"{Ty.toStr (.prim p)} {x} = {e.toStr ns true};"
  | .declStorage R x init =>
    match init with
    | none => s!"{Ty.toStr (.ref R)} storage {x};"
    | some e => s!"{Ty.toStr (.ref R)} storage {x} = {e.toStr ns};"
  | .declMem R x init _ _ =>
    match init with
    | none => s!"{Ty.toStr (.ref R)} memory {x};"
    | some r => s!"{Ty.toStr (.ref R)} memory {x} = {r.toStr ns};"
  | .rebindMem x r => s!"{x.name ns} = {r.toStr ns};"
  | .assignMem l r => s!"{l.toStr ns} = {r.toStr ns};"
  | .assignFromMem l p => s!"{l.toStr ns} = {p.toStr ns};"
  | .opAssign op _ _ l r => s!"{l.toStr ns} {BinOp.sym op}= {r.toStr ns true};"
  | .incDec op _ l => s!"{IncDec.show op (l.toStr ns)};"
  | .pushOpAssign op _ _ b r => s!"{b.toStr ns}.push() {BinOp.sym op}= {r.toStr ns true};"
  | .pushIncDec op _ b => s!"{IncDec.show op (b.toStr ns ++ ".push()")};"
  | .push b v _ =>
    match v with
    | none => s!"{b.toStr ns}.push();"
    | some r => s!"{b.toStr ns}.push({r.toStr ns});"
  | .pop b => s!"{b.toStr ns}.pop();"
  | .transfer r a => s!"{r.toStr ns}.transfer({a.toStr ns true});"
  | .send pv r a false => s!"{pv.name ns} = {r.toStr ns}.send({a.toStr ns true});"
  | .send pv r a true => s!"({pv.name ns}, ) = {r.toStr ns}.call\{value: {a.toStr ns true}}(\"\");"
  | .assignIncDec x op _ l _ => s!"{x.name ns} = {IncDec.show op (l.toStr ns)};"
  | .assignLocalPush x b => s!"{x.name ns} = {b.toStr ns}.push();"
  | .delete l => s!"delete {l.toStr ns};"
  | .deleteMem p _ => s!"delete {p.toStr ns};"
  | .assignNew (R := R) l n _ => s!"{l.toStr ns} = new {Ty.toStr (.ref R)}({n.toStr ns});"
  | .ite c thn els =>
    s!"if ({c.toStr ns true}) {braced (Prog.toStrs 0 ns thn)} else {braced (Prog.toStrs 0 ns els)}"
  | .require c => s!"require({c.toStr ns true});"
  | .assert c => s!"assert({c.toStr ns true});"
  | .revert => "revert();"
  | .assumeFalse => "assume(false);"
  | .revertData d => s!"revert({", ".intercalate (d.map (·.toStr ns))});"
  | .catchData c _ _ _ _ kind x body =>
    let src := match kind with
      | .reason => s!"string memory {x} = reason({c.fn})"
      | .raw => s!"bytes memory {x} = data({c.fn})"
    braced (s!"{src};" :: Prog.toStrs 0 (x :: ns) body)
  | .call f args ret _ =>
    let call := callStr ns f args
    match ret with
    | .val _ _ (some y) => s!"{y.name ns} = {call}"
    | _ => call
  | .callRec f _ args ret _ =>
    let call := callStr ns f args
    match ret with
    | .val _ _ (some y) => s!"{y.name ns} = {call}"
    | _ => call
  | .callReceiver f args _ _ op =>
    let receiver := s!"{f}({", ".intercalate (args.toStrs ns)})"
    match op with
    | .push none _ => s!"{receiver}.push();"
    | .push (some v) _ => s!"{receiver}.push({v.toStr ns});"
    | .pop => s!"{receiver}.pop();"
  | .callReceiverPush f args _ _ code value =>
    let receiver := s!"{f}({", ".intercalate (args.toStrs ns)})"
    match code.receiverExpr? ns value with
    | some operand => s!"{receiver}.push({operand});"
    | none => s!"{receiver}.push(eval {braced (Prog.toStrs 0 ns code)} {value.toStr (code.outNames ns)});"
  | .tryCall c rets ok err code pnc other _ _ _ =>
    let args := ", ".intercalate (c.args.map fun a => a.2.toStr ns)
    let rs := rets.toList
    let retsS := if rs.isEmpty then "" else
      s!" returns ({", ".intercalate (rs.map fun (p, x) => s!"{Ty.toStr (.prim p)} {x}")})"
    let codeS := match code.names with
      | [x] => s!"uint {x}"
      | _ => "uint"
    s!"try address({c.addr.toStr ns}).{c.fn}({args}){retsS} \
      {braced (Prog.toStrs 0 (rets.names ++ ns) ok)} \
      catch Error(string memory) {braced (Prog.toStrs 0 ns err)} \
      catch Panic({codeS}) {braced (Prog.toStrs 0 (code.names ++ ns) pnc)} \
      catch {braced (Prog.toStrs 0 ns other)}"
  | .loop a c body =>
    s!"{a.toStr ns}while ({c.toStr ns true}) {braced (Prog.toStrs 0 ns body)}"
  | .block body => braced (Prog.toStrs 0 ns body)

/-- The statements of a block, one string each; a memory call and the
statement binding its result are one, and so are a call of several returns
and the statements assigning them, the statements after the first skipped
(`skip` of them). -/
def Prog.toStrs {Γ Γ' : Ctx} (skip : Nat) (ns : List Var) : Prog C Γ Γ' → List String
  | .nil => []
  | .cons s P =>
    match skip with
    | k + 1 => Prog.toStrs k (s.outNames ns) P
    | 0 =>
      match Stmt.tupleCallStr? ns s P with
      | some (c, k) => c :: Prog.toStrs k (s.outNames ns) P
      | none =>
        match Stmt.memCallStr? ns s P with
        | some c => c :: Prog.toStrs 1 (s.outNames ns) P
        | none =>
          match Stmt.storageCallStr? ns s P with
          | some c => c :: Prog.toStrs 1 (s.outNames ns) P
          | none => s.toStr ns :: Prog.toStrs 0 (s.outNames ns) P

end

/-- A block, as the Solidity it came from. -/
def Prog.toStr {Γ Γ' : Ctx} (ns : List Var) (P : Prog C Γ Γ') : String :=
  " ".intercalate (Prog.toStrs 0 ns P)

/-- One statement per line, for display. -/
def Prog.show {Γ Γ' : Ctx} (ns : List Var) (P : Prog C Γ Γ') : String :=
  "\n".intercalate (Prog.toStrs 0 ns P)

end Print

/-! ## Weakening

A part read in `Γ` is read in any `Δ` that `Γ` thins into: every position
moves (`Idx.wk`).  A statement also returns the context it leaves in `Δ`,
with the thinning of its own output into it, to weaken what follows. -/

section Weaken

variable {C : Contract}

def Simple.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {p : PrimTy} : Simple C Γ p → Simple C Δ p
  | .lit n hr => .lit n hr
  | .bool b => .bool b
  | .local i => .local (i.wk h)
  | .env k hp => .env k hp

mutual

def SPath.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} : SPath C Γ T → SPath C Δ T
  | .alias i => .alias (i.wk h)
  | .loc l => .loc (l.wk h)

def Loc.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} : Loc C Γ T → Loc C Δ T
  | .root r hr => .root r hr
  | .field b f hf => .field (b.wk h) f hf
  | .index it b i => .index it (b.wk h) (i.wk h)

def MPath.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} : MPath C Γ T → MPath C Δ T
  | .var i hm => .var (i.wk h) hm
  | .loc l => .loc (l.wk h)

def MLoc.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} : MLoc C Γ T → MLoc C Δ T
  | .field b f hf => .field (b.wk h) f hf
  | .index a b i => .index a (b.wk h) (i.wk h)

def Val.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {p : PrimTy} : Val C Γ p → Val C Δ p
  | .simple s => .simple (s.wk h)
  | .read l => .read (l.wk h)
  | .binop op ha hq a b => .binop op ha hq (a.wk h) (b.wk h)
  | .unop op ha hq a => .unop op ha hq (a.wk h)
  | .ternary c a b => .ternary (c.wk h) (a.wk h) (b.wk h)
  | .readMem l => .readMem (l.wk h)
  | .len b hp => .len (b.wk h) hp
  | .mlen b hp => .mlen (b.wk h) hp
  | .modular op a b k => .modular op (a.wk h) (b.wk h) (k.wk h)
  | .hash k b hp => .hash k (b.wk h) hp

end

def Src.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} : Src C Γ T → Src C Δ T
  | .val v => .val (v.wk h)
  | .copy p hm => .copy (p.wk h) hm
  | .fixedCopy p shape hm => .fixedCopy (p.wk h) shape hm
  | .copyMem p => .copyMem (p.wk h)
  | .fixedCopyMem p shape => .fixedCopyMem (p.wk h) shape

def ARhs.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {R : RefTy} : ARhs C Γ R → ARhs C Δ R
  | .path p => .path (p.wk h)
  | .push b hd => .push (b.wk h) hd

def MRhs.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {R : RefTy} : MRhs C Γ R → MRhs C Δ R
  | .alias p => .alias (p.wk h)
  | .copy p hm => .copy (p.wk h) hm
  | .newArr n hn => .newArr (n.wk h) hn

def NewLhs.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {R : RefTy} : NewLhs C Γ R → NewLhs C Δ R
  | .store l => .store (l.wk h)
  | .mem l => .mem (l.wk h)

def MSrc.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} : MSrc C Γ T → MSrc C Δ T
  | .val v => .val (v.wk h)
  | .ref p => .ref (p.wk h)

def OpLoc.wk {Γ Δ : Ctx} (h : Thin Γ Δ) {p : PrimTy} : OpLoc C Γ p → OpLoc C Δ p
  | .local i => .local (i.wk h)
  | .root r hr => .root r hr
  | .field b f hf => .field (b.wk h) f hf
  | .index it b i => .index it (b.wk h) (i.wk h)
  | .mfield b f hf => .mfield (b.wk h) f hf
  | .mindex a b i => .mindex a (b.wk h) (i.wk h)

theorem SPath.isSimple_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} (b : SPath C Γ T) :
    (b.wk h).isSimple = b.isSimple := by
  rcases b with _ | (_ | _ | _) <;> rfl

theorem MPath.isSimple_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {T : Ty} (b : MPath C Γ T) :
    (b.wk h).isSimple = b.isSimple := by
  cases b <;> rfl

theorem OpLoc.recvSimple_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {p : PrimTy} (l : OpLoc C Γ p) :
    (l.wk h).recvSimple = l.recvSimple := by
  cases l <;> first | rfl | exact SPath.isSimple_wk h _ | exact MPath.isSimple_wk h _

def ExtCall.wk {Γ Δ : Ctx} (h : Thin Γ Δ) (c : ExtCall C Γ) : ExtCall C Δ :=
  ⟨c.addr.wk h, c.fn, c.args.map fun a => ⟨a.1, a.2.wk h⟩⟩

def LoopQ.wk : {Γ Δ : Ctx} → Thin Γ Δ → LoopQ C Γ → LoopQ C Δ
  | _, _, h, .val a => .val (a.wk h)
  | _, _, h, .imp a c => .imp (a.wk h) (c.wk h)
  | _, _, h, .all x p b => .all x p (LoopQ.wk h.keep b)

def LoopAnn.wk {Γ Δ : Ctx} (h : Thin Γ Δ) : LoopAnn C Γ → LoopAnn C Δ
  | .unwind k => .unwind k
  | .inv I dec brk qs => .inv (I.wk h) (dec.map (·.wk h)) brk (qs.map (·.wk h))
  | .auto => .auto

def Args.wk {Γ Δ : Ctx} (h : Thin Γ Δ) : {ps : Ctx} → Args C Γ ps → Args C Δ ps
  | _, .nil => .nil
  | _, .snoc as p x e => .snoc (as.wk h) p x (e.wk h)
  | _, .snocStorage as R x e => .snocStorage (as.wk h) R x (e.wk h)
  | _, .snocMemory as R x e => .snocMemory (as.wk h) R x (e.wk h)

def ReceiverOp.wk {Γ Δ : Ctx} {E : Ty} (h : Thin Γ Δ) : ReceiverOp C Γ E → ReceiverOp C Δ E
  | .push v hd => .push (v.map (·.wk h)) (by rw [Option.isSome_map]; exact hd)
  | .pop => .pop

/-- A call's result weakened: the context it leaves in `Δ`, and how its own
output thins into it. -/
def CallRet.wk {Γ Δ : Ctx} (h : Thin Γ Δ) : {rs Γ' : Ctx} → CallRet Γ rs Γ' →
    (Δ' : Ctx) × Thin Γ' Δ' × CallRet Δ rs Δ'
  | _, _, .none => ⟨Δ, h, .none⟩
  | _, _, .val p r res => ⟨Δ, h, .val p r (res.map (·.wk h))⟩
  | rs, _, .rets bs => ⟨rs ++ Δ, Thin.keepAll rs h, .rets bs⟩
  | _, _, .mem R r hd hm => ⟨.mem R :: Δ, .keep h, .mem R r hd hm⟩
  | _, _, .storage R r => ⟨.alias R :: Δ, .keep h, .storage R r⟩

def RevPart.wk {Γ Δ : Ctx} (h : Thin Γ Δ) : RevPart C Γ → RevPart C Δ
  | .bytes bs => .bytes bs
  | .sel sig => .sel sig
  | .word v => .word (v.wk h)
  | .mem kind src => .mem kind (src.wk h)

mutual

/-- Weakening a statement: the output context is computed, with the
thinning that relates it to the old one.  A call's body is closed over its
frame, so it is not touched. -/
def Stmt.wk {Γ Δ : Ctx} (h : Thin Γ Δ) : {Γ' : Ctx} → Stmt C Γ Γ' →
    (Δ' : Ctx) × Thin Γ' Δ' × Stmt C Δ Δ'
  | _, .assign l r => ⟨Δ, h, .assign (l.wk h) (r.wk h)⟩
  | _, .rebind i r => ⟨Δ, h, .rebind (i.wk h) (r.wk h)⟩
  | _, .assignLocal i r => ⟨Δ, h, .assignLocal (i.wk h) (r.wk h)⟩
  | _, .declLocal p x init => ⟨_, .keep h, .declLocal p x (init.map (·.wk h))⟩
  | _, .declStorage R x init => ⟨_, .keep h, .declStorage R x (init.map (·.wk h))⟩
  | _, .opAssign op hop hp l r => ⟨Δ, h, .opAssign op hop hp (l.wk h) (r.wk h)⟩
  | _, .incDec op hp l => ⟨Δ, h, .incDec op hp (l.wk h)⟩
  | _, .pushOpAssign op hop hp b r => ⟨Δ, h, .pushOpAssign op hop hp (b.wk h) (r.wk h)⟩
  | _, .pushIncDec op hp b => ⟨Δ, h, .pushIncDec op hp (b.wk h)⟩
  | _, .assignIncDec i op hp l hs =>
    ⟨Δ, h, .assignIncDec (i.wk h) op hp (l.wk h) ((OpLoc.recvSimple_wk h l).trans hs)⟩
  | _, .assignLocalPush i b =>
    ⟨Δ, h, .assignLocalPush (i.wk h) (b.wk h)⟩
  | _, .push b v hd =>
    ⟨Δ, h, .push (b.wk h) (v.map (·.wk h)) (by rw [Option.isSome_map]; exact hd)⟩
  | _, .pop b => ⟨Δ, h, .pop (b.wk h)⟩
  | _, .transfer r a => ⟨Δ, h, .transfer (r.wk h) (a.wk h)⟩
  | _, .send pv r a g => ⟨Δ, h, .send (pv.wk h) (r.wk h) (a.wk h) g⟩
  | _, .declMem R x init hd hm =>
    ⟨_, .keep h, .declMem R x (init.map (·.wk h)) (by rw [Option.isSome_map]; exact hd) hm⟩
  | _, .rebindMem i r => ⟨Δ, h, .rebindMem (i.wk h) (r.wk h)⟩
  | _, .assignFromMem l p => ⟨Δ, h, .assignFromMem (l.wk h) (p.wk h)⟩
  | _, .assignMem l r => ⟨Δ, h, .assignMem (l.wk h) (r.wk h)⟩
  | _, .delete l => ⟨Δ, h, .delete (l.wk h)⟩
  | _, .deleteMem p hd => ⟨Δ, h, .deleteMem (p.wk h) hd⟩
  | _, .assignNew l n hn => ⟨Δ, h, .assignNew (l.wk h) (n.wk h) hn⟩
  | _, .ite c thn els => ⟨Δ, h, .ite (c.wk h) (thn.wk h).2.2 (els.wk h).2.2⟩
  | _, .require c => ⟨Δ, h, .require (c.wk h)⟩
  | _, .assert c => ⟨Δ, h, .assert (c.wk h)⟩
  | _, .revert => ⟨Δ, h, .revert⟩
  | _, .assumeFalse => ⟨Δ, h, .assumeFalse⟩
  | _, .revertData d => ⟨Δ, h, .revertData (d.map (·.wk h))⟩
  | _, .catchData c rets sargs sbody self kind x body =>
    ⟨Δ, h, .catchData (c.wk h) rets (sargs.wk h) sbody self kind x (body.wk (.keep h)).2.2⟩
  | _, .call f args ret body =>
    let ⟨Δ', h', ret'⟩ := ret.wk h
    ⟨Δ', h', .call f (args.wk h) ret' body⟩
  | _, @Stmt.tryCall _ _ ρ κ _ _ _ _ _ _ c rets ok err code pnc other sargs sbody self =>
    ⟨Δ, h, .tryCall (c.wk h) rets (ok.wk (Thin.keepAll ρ h)).2.2 (err.wk h).2.2 code
      (pnc.wk (Thin.keepAll κ h)).2.2 (other.wk h).2.2 (sargs.wk h) sbody self⟩
  | _, .loop a c body => ⟨Δ, h, .loop (a.wk h) (c.wk h) (body.wk h).2.2⟩
  | _, .block body => ⟨Δ, h, .block (body.wk h).2.2⟩
  | _, .callRec f d args ret body =>
    let ⟨Δ', h', ret'⟩ := ret.wk h
    ⟨Δ', h', .callRec f d (args.wk h) ret' body⟩
  | _, .callReceiver f args r body op => ⟨Δ, h, .callReceiver f (args.wk h) r body (op.wk h)⟩
  | _, .callReceiverPush f args r body code value =>
    ⟨Δ, h, .callReceiverPush f (args.wk h) r body (code.wk h).2.2
      (value.wk (code.wk h).2.1)⟩

def Prog.wk {Γ Δ : Ctx} (h : Thin Γ Δ) : {Γ' : Ctx} → Prog C Γ Γ' →
    (Δ' : Ctx) × Thin Γ' Δ' × Prog C Δ Δ'
  | _, .nil => ⟨Δ, h, .nil⟩
  | _, .cons s P =>
    let ⟨_, h₁, s'⟩ := s.wk h
    let ⟨Δ₂, h₂, P'⟩ := P.wk h₁
    ⟨Δ₂, h₂, .cons s' P'⟩

end

end Weaken

/-! ## What a statement pushes

A statement leaves its context with locals pushed (`Ext`): a declaration
one, a call its exported return variables, a scope none.  The interpreter
drops a scope's locals by it (`Prog.ext` of a branch, Gate G0, condition 5),
so these are `casesOn` and structural recursion (condition 1). -/

section Pushes

variable {C : Contract}

/-- What a call pushes on its caller's context. -/
def CallRet.ext {Γ : Ctx} {rs Γ' : Ctx} (r : CallRet Γ rs Γ') : Ext Γ Γ' :=
  CallRet.casesOn (motive := fun _ Γ' _ => Ext Γ Γ') r .refl (fun _ _ _ => .refl)
    (fun {rs} _ => Ext.append Γ rs) (fun _ _ _ _ => .push .refl)
    (fun _ _ => .push .refl)

def Stmt.ext {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Ext Γ Γ' :=
  Stmt.casesOn (motive_1 := fun Γ Γ' _ => Ext Γ Γ') s
    (fun _ _ => .refl) (fun _ _ => .refl) (fun _ _ => .refl)
    (fun _ _ _ => .push .refl) (fun _ _ _ => .push .refl)
    (fun _ _ _ _ _ => .refl) (fun _ _ _ => .refl) (fun _ _ _ _ _ => .refl) (fun _ _ => .refl)
    (fun _ _ _ => .refl) (fun _ => .refl) (fun _ _ => .refl) (fun _ _ _ _ => .refl)
    (fun _ _ _ _ _ => .push .refl) (fun _ _ => .refl) (fun _ _ => .refl) (fun _ _ => .refl)
    (fun _ => .refl) (fun _ _ => .refl) (fun _ _ _ => .refl)
    (fun _ _ _ => .refl) (fun _ => .refl) (fun _ => .refl) .refl .refl
    (fun _ _ ret _ => ret.ext)
    (fun _ _ _ _ _ _ _ _ _ _ => .refl) (fun _ _ _ => .refl) (fun _ => .refl)
    (fun _ _ _ _ _ => .refl) (fun _ _ _ => .refl)
    (fun _ _ _ _ _ => .refl)
    (fun _ _ _ _ _ _ => .refl)
    (fun _ _ _ ret _ => ret.ext)
    (fun _ => .refl) (fun _ _ _ _ _ _ _ _ => .refl)

def Prog.ext : {Γ Γ' : Ctx} → Prog C Γ Γ' → Ext Γ Γ'
  | _, _, P => Prog.casesOn (motive_2 := fun Γ Γ' _ => Ext Γ Γ') P .refl
      (fun s P => (Stmt.ext s).trans (Prog.ext P))
  termination_by structural _ _ P => P

end Pushes

/-! ## A byte string's literal

The statements a literal `bytes memory x = hex"…";` elaborates to: a fresh
array of its length, then each byte written (`docs/semantic-gaps.md`,
"Bytes and strings").  `Stmt.catchData` allocates the data it binds as
these do, and its rule writes them in front of the clause. -/

section LitBytes

variable {C : Contract}

theorem PrimTy.inRange_uint_of_lt {n : Nat} (h : n < 2 ^ 256) : PrimTy.uint.inRange (n : Int) = true := by
  simp only [PrimTy.inRange, decide_eq_true_eq]
  exact ⟨Int.natCast_nonneg n, Int.ofNat_lt.mpr h⟩

/-- `x[i]`, at the local `x` on top. -/
def litLoc {Γ : Ctx} (i : Nat) (hi : i < 2 ^ 256) : MLoc C (.mem bytesR :: Γ) (.prim .uint) :=
  .index .dyn (.var .here rfl) (.simple (.lit (i : Int) (PrimTy.inRange_uint_of_lt hi)))

/-- A byte, as the `uint` a `bytes1[]` element holds. -/
def litSrc {Γ : Ctx} (b : UInt8) : MSrc C Γ (.prim .uint) :=
  .val (.simple (.lit (b.toNat : Int) (PrimTy.inRange_uint_of_lt (Nat.lt_trans b.toNat_lt (by decide)))))

/-- `x[i] = b;`, `b` a byte, at the local `x` on top. -/
def litWrite {Γ : Ctx} (i : Nat) (hi : i < 2 ^ 256) (b : UInt8) :
    Stmt C (.mem bytesR :: Γ) (.mem bytesR :: Γ) :=
  .assignMem (litLoc i hi) (litSrc b)

/-- The writes of a literal's bytes, from position `i` on, then `k`. -/
def litWrites {Γ Γ₁ : Ctx} : List UInt8 → Nat → Prog C (.mem bytesR :: Γ) Γ₁ →
    Prog C (.mem bytesR :: Γ) Γ₁
  | [], _, k => k
  | b :: bs, i, k => if hi : i < 2 ^ 256 then .cons (litWrite i hi b) (litWrites bs (i + 1) k) else k

/-- `bytes memory x = new bytes(n);`, the writes of a literal's bytes (`n`
its length, below `2^256`), then `k`. -/
def litBytes {Γ Γ₁ : Ctx} (x : Var) (bs : List UInt8) (k : Prog C (.mem bytesR :: Γ) Γ₁) :
    Prog C Γ Γ₁ :=
  if hn : bs.length < 2 ^ 256 then
    .cons (.declMem bytesR x (some (.newArr (.lit (bs.length : Int) (PrimTy.inRange_uint_of_lt hn)) rfl))
      rfl rfl) (litWrites bs 0 k)
  else .cons (.declMem bytesR x none rfl rfl) k

end LitBytes

/-! ## An example

Every scope at once over `StandardExample`, printed as `Syntax/Splice.lean`'s
`tour` prints the same statements (`Prog.show`, `Stmt.memCallStr?`,
`Stmt.tupleCallStr?`). -/

section Example

private abbrev SE := StandardExample
private abbrev P : RefTy := .struct "Person"

private def alice {Γ : Ctx} : SPath SE Γ (.struct "Person") := .loc (.root "alice" rfl)
private def lit {Γ : Ctx} (n : Int) (h : PrimTy.uint.inRange n = true := by rfl) : Val SE Γ .uint :=
  .simple (.lit n h)
private def loc {Γ : Ctx} {p : PrimTy} (i : Idx Γ (.val p)) : Val SE Γ p := .simple (.local i)

/-- `x`, `p`, `r` (a memory return), `m`, and the tuple's `r0`, `r1`. -/
private def example₁ : Prog SE [] [.val .uint, .val .uint, .mem P, .mem P, .alias P, .val .uint] :=
  .cons (.declLocal .uint (.user "x")
    (some (.binop .add rfl rfl (.read (.field alice "age" rfl)) (lit 1)))) <|
  .cons (.declStorage P (.user "p") (some (.path alice))) <|
  .cons (.assign (.field (.alias .here) "age" rfl) (.val (loc (.there .here)))) <|
  .cons (.ite (.binop .gt rfl rfl (loc (.there .here)) (lit 3))
    (.cons (.declLocal .uint (.user "y") (some (loc (.there .here)))) <|
      .cons (.assign (.field alice "age" rfl) (.val (loc .here))) .nil)
    (.cons .revert .nil)) <|
  .cons (.block (.cons (.declLocal .uint (.user "z") (some (lit 2))) <|
    .cons (.assign (.index .map (.loc (.root "balances" rfl)) (loc .here))
      (.val (loc (.there (.there .here))))) .nil)) <|
  .cons (.call "f" ((Args.nil.snoc .uint (.user "a") (loc (.there .here))).snoc .uint (.user "b")
      (lit 1)) (.val .uint (.user "r") (some (.there .here))) .nil) <|
  .cons (.call "g" .nil (.mem P (.user "r") rfl rfl) .nil) <|
  .cons (.declMem P (.user "m") (some (.alias (.var .here rfl))) rfl rfl) <|
  .cons (.call "h" .nil (.rets ((Binders.nil.snoc .uint (.user "r0")).snoc .uint (.user "r1")))
    .nil) <|
  .cons (.assignLocal (.there (.there (.there (.there (.there .here))))) (loc .here)) <|
  .cons (.tryCall ⟨.local (.there (.there (.there (.there (.there .here))))), "ping",
      [⟨.uint, .local .here⟩]⟩ (Binders.nil.snoc .uint (.user "v"))
    (.cons (.assignLocal (.there (.there (.there (.there (.there (.there .here)))))) (loc .here))
      .nil)
    .nil (.some (.user "c")) .nil (.cons .revert .nil) .nil .nil false) .nil

/--
info: uint x = alice.age + 1;
Person storage p = alice;
p.age = x;
if (x > 3) { uint y = x; alice.age = y; } else { revert(); }
{ uint z = 2; balances[z] = x; }
x = f(x, 1);
Person memory m = g();
(, x) = h();
try address(x).ping(r1) returns (uint v) { x = v; } catch Error(string memory) { } catch Panic(uint c) { } catch { revert(); }
-/
#guard_msgs in #eval IO.println (Prog.show [] example₁)

/-- `x = x + 1; uint y = x;`, reading the local `x` it is given. -/
private def example₂ : Prog SE [.val .uint] [.val .uint, .val .uint] :=
  .cons (.assignLocal .here (.binop .add rfl rfl (loc .here) (lit 1))) <|
  .cons (.declLocal .uint (.user "y") (some (loc .here))) .nil

-- Weakened under a local `w` declared after `x`, it still reads `x`.
#guard Prog.toStr [.user "w", .user "x"] (example₂.wk (.drop (t := .val .bool) .refl)).2.2 =
  "x = x + 1; uint y = x;"

-- A block weakened under one more local reads the same locals.
#guard Prog.toStr [.user "w"] (example₁.wk (.drop (t := .val .bool) .refl)).2.2 =
  Prog.toStr [] example₁

/-- `example₁` pushes its six locals, the memory return's among them. -/
example : example₁.ext.depth = 6 := by decide

end Example

end Solidity
