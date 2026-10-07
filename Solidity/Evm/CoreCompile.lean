import Solidity.Evm.Compile
import Solidity.Syntax.Resolve

/-!
# The compiler over the scoped syntax

`Evm/Compile.lean`'s compiler, on `Syntax/Core.lean`'s statements
(`docs/intrinsic.md`, M5).  The code is the same instruction for
instruction; what changes is where a local lives and what the fragment
check still has to say.

**A local lives at its level.**  A local of `Γ` at position `i` (innermost
`0`) lives in memory cell `b + (Γ.length - 1 - i)`: its *level*, counted from
the outermost local, so a cell does not move when locals are pushed above
it.  `b` is the frame's base: `0` for the program, the caller's next free
level for a call's body, which is closed over its own frame `rs ++ ps`
(parameters from `b`, then the return variables).  The machine's memory is
still addressed by `Var` until the untyped syntax retires (M4); a level `l`
is the cell `cell l` (printed `%l`), so `Machine.mem ∘ cell` is the
level-addressed view.  A scope's locals are not cleared at its end: the next
local declared at that level overwrites the cell (a declaration always
writes its cell).

**The fragment is what `inFrag` accepts.**  Typing is the syntax's now: a
local is read at its declared type and in scope by construction, so
`inFrag` keeps only the facts about the target that `wtStmt` kept beside
the types (the same list as `Evm/Compile.lean`'s module docstring): which
aliases may be read (`Frag Γ`: a plain alias, a *fragile* one bound through
an array index and forgotten at the next `pop` or `delete`, or an unset or
forgotten one), the operators, static copies, `push` shapes, no memory, no
`send`/`try`/loop, no call of several returns.  A branch's or a block's
locals end with it: what it did to the enclosing aliases is kept
(`Frag.restrict`), the two branches' met.  A call's body starts from a frame
of its own, where every parameter and return variable may be read; a `pop`
or `delete` anywhere in it forgets the caller's fragile aliases
(`Stmt.shrinks`).

**Against the untyped compiler** (`compile_erase`): compiling `s` and
compiling `s.erase ns` give the same code up to the memory cells
(`Instr.forgetCell`), for every `s` whose calls have separated arguments
(`Stmt.sepArgs`).  The cells differ by design (a name there, a level here).
A call whose arguments are not separated is erased with its arguments bound
at the head of its body, after the return variable is zeroed, so the two
codes store the same words in another order; the elaborator's calls are
separated (`Solidity.Stmt.call` requires it), and `Evm/CoreExamples.lean`
checks the agreement on resolved programs (`sameCode`).
-/

namespace Solidity.Evm
namespace Core

open Solidity.Core (Ctx Idx)

/-- The scoped syntax's local types (`Evm.LTy` is the untyped compiler's). -/
abbrev CLTy := Solidity.Core.LTy

variable {C : Contract}

/-! ## Levels -/

/-- The memory cell of level `l`. -/
def cell (l : Nat) : Var := .fresh "%" l

theorem cell_inj {l l' : Nat} (h : cell l = cell l') : l = l' := by
  simp only [cell, Var.fresh.injEq, true_and] at h
  exact h

/-- The level of the local at position `i` of `Γ`, in a frame based at `b`. -/
def lvl (b : Nat) {Γ : Ctx} {t : CLTy} (i : Idx Γ t) : Nat := b + (Γ.length - 1 - i.toNat)

/-- The cell of the local at position `i`. -/
abbrev cellOf (b : Nat) {Γ : Ctx} {t : CLTy} (i : Idx Γ t) : Var := cell (lvl b i)

/-- An instruction with its memory cell forgotten: what the two compilers
agree on (`compile_erase`). -/
def _root_.Solidity.Evm.Instr.forgetCell : Instr → Instr
  | .mload _ => .mload (.user "")
  | .mstore _ => .mstore (.user "")
  | i => i

/-- The memory read by level. -/
def _root_.Solidity.Evm.Machine.memAt (m : Machine) (l : Nat) : Word := m.mem (cell l)

/-! ## The fragment -/

/-- What the fragment knows of a local: it may be read (a value, a plain
alias), it is an alias bound through an array index (read, not rebound
from, and forgotten at a `pop` or `delete`), or it may not be read (an
unset or forgotten alias). -/
inductive Fl where
  | ok
  | fragile
  | dead
  deriving DecidableEq, Repr

/-- What the fragment knows of each local of `Γ`, innermost first. -/
structure Frag (Γ : Ctx) where
  fl : List Fl
  deriving DecidableEq, Repr

namespace Frag

/-- Every local readable: a call's frame, the empty program's. -/
def init (Γ : Ctx) : Frag Γ := ⟨Γ.map fun _ => .ok⟩

def get {Γ : Ctx} {t : CLTy} (F : Frag Γ) (i : Idx Γ t) : Fl := F.fl.getD i.toNat .dead

/-- A local pushed. -/
def push {Γ : Ctx} (t : CLTy) (F : Frag Γ) (f : Fl) : Frag (t :: Γ) := ⟨f :: F.fl⟩

def set {Γ : Ctx} {t : CLTy} (F : Frag Γ) (i : Idx Γ t) (f : Fl) : Frag Γ := ⟨F.fl.set i.toNat f⟩

/-- After a `pop` or a `delete`: the fragile aliases forgotten. -/
def dropFragile {Γ : Ctx} (F : Frag Γ) : Frag Γ :=
  ⟨F.fl.map fun f => if f = .fragile then .dead else f⟩

/-- After an `if`: what both branches agree on. -/
def meet {Γ : Ctx} (F G : Frag Γ) : Frag Γ :=
  ⟨List.zipWith (fun f g => if f = g then f else .dead) F.fl G.fl⟩

/-- At a scope's end: its own locals popped, the enclosing ones kept. -/
def restrict (Γ : Ctx) {Δ : Ctx} (F : Frag Δ) : Frag Γ := ⟨F.fl.drop (Δ.length - Γ.length)⟩

end Frag

/-- An environment value the fragment reads: not `address(this).balance`. -/
def simpleIn {Γ : Ctx} : {p : PrimTy} → Solidity.Core.Simple C Γ p → Bool
  | _, .env k _ => k != .selfBalance
  | _, _ => true

mutual
/-- `free`: the path indexes no array (what an alias may be bound to). -/
def spathIn {Γ : Ctx} (F : Frag Γ) (free : Bool) : {T : Ty} → Solidity.Core.SPath C Γ T → Bool
  | _, .alias i => F.get i == .ok || (!free && F.get i == .fragile)
  | _, .loc l => locIn F free l
def locIn {Γ : Ctx} (F : Frag Γ) (free : Bool) : {T : Ty} → Solidity.Core.Loc C Γ T → Bool
  | _, .root .. => true
  | _, .field b _ _ => spathIn F free b
  | _, @Solidity.Core.Loc.index _ _ _ k _ .map b i => k == .uint && spathIn F free b && valIn F i
  | _, .index (.arr _) b i => !free && spathIn F free b && valIn F i
def valIn {Γ : Ctx} (F : Frag Γ) : {p : PrimTy} → Solidity.Core.Val C Γ p → Bool
  | _, .simple s => simpleIn s
  | _, .read l => locIn F false l
  | _, @Solidity.Core.Val.binop _ _ p _ op _ _ a b => binInFrag op p && valIn F a && valIn F b
  | _, @Solidity.Core.Val.unop _ _ p _ op _ _ a => unInFrag op p && valIn F a
  | _, .ternary c a b => valIn F c && valIn F a && valIn F b
  | _, .len b _ => spathIn F false b
  | _, .readMem _ | _, .mlen .. => false
end

/-- The storage location an `op=` target names, if it is one. -/
def opLocToLoc {Γ : Ctx} : {p : PrimTy} → Solidity.Core.OpLoc C Γ p →
    Option (Solidity.Core.Loc C Γ (.prim p))
  | _, .root r h => some (.root r h)
  | _, .field b f h => some (.field b f h)
  | _, .index it b i => some (.index it b (.simple i))
  | _, .local _ | _, .mfield .. | _, .mindex .. => none

def opLocIn {Γ : Ctx} (F : Frag Γ) {p : PrimTy} (l : Solidity.Core.OpLoc C Γ p) : Bool :=
  match l with
  | .local _ => true
  | l => match opLocToLoc l with
    | some loc => locIn F false loc
    | none => false

/-- Every argument of a call in the fragment. -/
def argsIn {Γ : Ctx} (F : Frag Γ) : {ps : Ctx} → Solidity.Core.Args C Γ ps → Bool
  | _, .nil => true
  | _, .snoc as _ _ e => argsIn F as && valIn F e

/-- What a call leaves the caller knowing: nothing new for no return or one
return value; a call of several returns, or of a memory return, is out. -/
def CallRetIn {Γ : Ctx} (F : Frag Γ) : {rs Γ' : Ctx} → Solidity.Core.CallRet Γ rs Γ' →
    Option (Frag Γ')
  | _, _, .none => some F
  | _, _, .val .. => some F
  | _, _, .rets _ => none
  | _, _, .mem .. => none

/-- An alias bound to `q`: plain if `q` indexes no array, fragile if it does. -/
def bindFl {Γ : Ctx} (F : Frag Γ) {R : RefTy} (q : Solidity.Core.SPath C Γ (.ref R)) :
    Option Fl :=
  if spathIn F true q then some .ok else if spathIn F false q then some .fragile else none

/-- A `push` of the fragment: `push()` of a primitive, `push(e)`, `push(sp)`
of a static element. -/
def pushIn {Γ : Ctx} (F : Frag Γ) : {E : Ty} → Option (Solidity.Core.Src C Γ E) →
    Solidity.Core.SPath C Γ (.array E) → Bool
  | E, none, b => E.isPrimitive && spathIn F false b
  | _, some (.val e), b => spathIn F false b && valIn F e
  | _, some (@Solidity.Core.Src.copy _ _ R q _), b =>
    static (.ref R) && spathIn F false b && spathIn F false q

mutual
/-- Whether a statement may shrink an array (a `pop` or a `delete`, in a
branch, a block or a called body): the caller's fragile aliases are
forgotten after it. -/
def Stmt.shrinks {Γ Γ' : Ctx} : Solidity.Core.Stmt C Γ Γ' → Bool
  | .pop _ | .delete _ => true
  | .ite _ t e => Prog.shrinks t || Prog.shrinks e
  | .block body => Prog.shrinks body
  | .call _ _ _ body => Prog.shrinks body
  | .assign .. | .rebind .. | .assignLocal .. | .declLocal .. | .declStorage .. | .opAssign ..
  | .incDec .. | .assignIncDec .. | .push .. | .transfer .. | .send .. | .declMem ..
  | .rebindMem .. | .assignFromMem .. | .assignMem .. | .deleteMem .. | .assignNew ..
  | .require _ | .assert _ | .revert | .tryCall .. | .loop .. => false
def Prog.shrinks {Γ Γ' : Ctx} : Solidity.Core.Prog C Γ Γ' → Bool
  | .nil => false
  | .cons s P => Stmt.shrinks s || Prog.shrinks P
end

/-- `F` after a statement that does or does not shrink an array. -/
def Frag.after {Γ : Ctx} (F : Frag Γ) (shrinks : Bool) : Frag Γ :=
  if shrinks then F.dropFragile else F

/-- `F` if the check passes. -/
def Frag.guard {Γ : Ctx} (F : Frag Γ) (ok : Bool) : Option (Frag Γ) := if ok then some F else none

/-- `l = r;` of the fragment: a value, or a copy of a static value. -/
def assignIn {Γ : Ctx} (F : Frag Γ) : {T : Ty} → Solidity.Core.Src C Γ T →
    Solidity.Core.Loc C Γ T → Bool
  | _, .val v, l => locIn F false l && valIn F v
  | _, @Solidity.Core.Src.copy _ _ R q _, l =>
    static (.ref R) && spathIn F false q && locIn F false l

/-- A storage alias declared: unset (not readable), or bound to a path of
the fragment. -/
def declStorageIn {Γ : Ctx} (F : Frag Γ) (R : RefTy) :
    Option (Solidity.Core.ARhs C Γ R) → Option (Frag (.alias R :: Γ))
  | none => some (F.push (.alias R) .dead)
  | some (.path q) => (bindFl F q).map (F.push (.alias R))
  | some (.push ..) => none

mutual
/-- A statement of the fragment, and what is known after it. -/
def inFrag {Γ Γ' : Ctx} (F : Frag Γ) : Solidity.Core.Stmt C Γ Γ' → Option (Frag Γ')
  | .assign l r => F.guard (assignIn F r l)
  | .rebind i r => match r with
    | .path q => (bindFl F q).map (F.set i)
    | .push .. => none
  | .assignLocal _ r => F.guard (valIn F r)
  | .declLocal p _ init => (F.push (.val p) .ok).guard (init.all (valIn F))
  | .declStorage R _ init => declStorageIn F R init
  | @Solidity.Core.Stmt.opAssign _ _ p _ _ _ l r => F.guard (p != .bool && opLocIn F l && valIn F r)
  | @Solidity.Core.Stmt.incDec _ _ p _ _ l => F.guard (p != .bool && opLocIn F l)
  | @Solidity.Core.Stmt.assignIncDec _ _ p _ _ _ l _ => F.guard (p != .bool && opLocIn F l)
  | .push b v _ => F.guard (pushIn F v b)
  | .pop b => F.dropFragile.guard (spathIn F false b)
  | .transfer r a => F.guard (valIn F r && valIn F a)
  | .delete l => F.dropFragile.guard (locIn F false l)
  | .ite c t e =>
    if valIn F c then
      match inFragP F t, inFragP F e with
      | some F₁, some F₂ => some ((F₁.restrict Γ).meet (F₂.restrict Γ))
      | _, _ => none
    else none
  | .block body => (inFragP F body).map (Frag.restrict Γ)
  | .require c | .assert c => F.guard (valIn F c)
  | .revert => some F
  | @Solidity.Core.Stmt.call _ _ _ ps rs _ _ args ret body =>
    if argsIn F args then
      match inFragP (Frag.init (rs ++ ps)) body with
      | some _ => CallRetIn (F.after (Prog.shrinks body)) ret
      | none => none
    else none
  | .send .. | .declMem .. | .rebindMem .. | .assignFromMem .. | .assignMem .. | .deleteMem ..
  | .assignNew .. | .tryCall .. | .loop .. => none
/-- A block of the fragment. -/
def inFragP {Γ Γ' : Ctx} (F : Frag Γ) : Solidity.Core.Prog C Γ Γ' → Option (Frag Γ')
  | .nil => some F
  | .cons s P => match inFrag F s with
    | some F' => inFragP F' P
    | none => none
end

/-! ## The compiler -/

def compileSimple (b : Nat) {Γ : Ctx} : {p : PrimTy} → Solidity.Core.Simple C Γ p → List Instr
  | _, .lit n _ => [.push (.val (toWord n))]
  | _, .bool v => [.push (.val (bword v))]
  | _, .local i => [.mload (cellOf b i)]
  | _, .env k _ => [envInstr k]

mutual
/-- Push the slot a storage path names. -/
def compileSPath (b : Nat) {Γ : Ctx} : {T : Ty} → Solidity.Core.SPath C Γ T → List Instr
  | _, .alias i => [.mload (cellOf b i)]
  | _, .loc l => compileLoc b l
/-- Push the slot of a location. -/
def compileLoc (b : Nat) {Γ : Ctx} : {T : Ty} → Solidity.Core.Loc C Γ T → List Instr
  | _, .root r _ => [.push (.slot (rootSlot C r))]
  | _, @Solidity.Core.Loc.field _ _ s _ q f _ => compileSPath b q ++ [.push (.val (offset s f)), .add]
  | _, .index .map q i => compileSPath b q ++ compileVal b i ++ [.keccakMap]
  | _, @Solidity.Core.Loc.index _ _ _ _ E (.arr .dyn) q i =>
    compileSPath b q ++ compileVal b i ++ boundsCheck ++ elemSlot (size E)
  | _, @Solidity.Core.Loc.index _ _ _ _ E (@IndexTy.arr _ _ (@ArrTy.fixed _ n)) q i =>
    compileSPath b q ++ compileVal b i ++ fixedCheck n ++ fixedSlot (size E)
/-- Push the value of an expression. -/
def compileVal (b : Nat) {Γ : Ctx} : {p : PrimTy} → Solidity.Core.Val C Γ p → List Instr
  | _, .simple s => compileSimple b s
  | _, .read l => compileLoc b l ++ [.sload]
  | _, @Solidity.Core.Val.binop _ _ p _ op _ _ x y =>
    match op with
    | .and => compileVal b x ++ [.dup 1, .iszero, .jumpi ((compileVal b y).length + 1), .pop] ++
        compileVal b y
    | .or => compileVal b x ++ [.dup 1, .jumpi ((compileVal b y).length + 1), .pop] ++
        compileVal b y
    | op => compileVal b x ++ compileVal b y ++ binTail p op
  | _, .unop op _ _ x =>
    compileVal b x ++ match op with
      | .not => [.iszero]
      | .neg => negCode
      | .bnot => [.not]
  | _, .ternary c x y =>
    compileVal b c ++ [.iszero, .jumpi ((compileVal b x).length + 1)] ++ compileVal b x ++
      [.jump (compileVal b y).length] ++ compileVal b y
  | _, .len q _ => compileSPath b q ++ [.sload]
  | _, .readMem _ | _, .mlen .. => []
end

/-- `b.push(…)`, as `Evm.pushCode`. -/
def pushCode (b : Nat) {Γ : Ctx} : {E : Ty} → Option (Solidity.Core.Src C Γ E) →
    Solidity.Core.SPath C Γ (.array E) → List Instr
  | _, none, q => compileSPath b q ++ [.push (.val 0), .dup 2] ++ pushSlotCode 1 ++ [.sstore, .pop]
  | _, some (.val e), q =>
    compileSPath b q ++ compileVal b e ++ [.dup 2] ++ pushSlotCode 1 ++ [.sstore, .pop]
  | _, some (@Solidity.Core.Src.copy _ _ R p _), q =>
    compileSPath b q ++ compileSPath b p ++ loadLeaves (leaves (.ref R)) ++
      [.pop, .dup ((leaves (.ref R)).length + 1)] ++ pushSlotCode (size (.ref R)) ++
      storeLeaves (leaves (.ref R)).reverse ++ [.pop, .pop]

/-- A call's parameters bound, each argument evaluated in the caller's
context and stored at its level in the frame, which starts at `b + Γ.length`. -/
def argsCode (b : Nat) {Γ : Ctx} : {ps : Ctx} → Solidity.Core.Args C Γ ps → List Instr
  | _, .nil => []
  | _, @Solidity.Core.Args.snoc _ _ ps as _ _ e =>
    argsCode b as ++ compileVal b e ++ [.mstore (cell (b + Γ.length + ps.length))]

/-- The return variable declared: `0` in its cell, above the parameters.  A
call of several returns has no code (it is outside the fragment). -/
def retEnterCode (b : Nat) {Γ : Ctx} (ps : Ctx) : {rs Γ' : Ctx} →
    Solidity.Core.CallRet Γ rs Γ' → List Instr
  | _, _, .val .. => [.push (.val 0), .mstore (cell (b + Γ.length + ps.length))]
  | _, _, _ => []

/-- The returned value copied where the call lands. -/
def retLeaveCode (b : Nat) {Γ : Ctx} (ps : Ctx) : {rs Γ' : Ctx} →
    Solidity.Core.CallRet Γ rs Γ' → List Instr
  | _, _, .val _ _ (some y) => [.mload (cell (b + Γ.length + ps.length)), .mstore (cellOf b y)]
  | _, _, _ => []

/-- `l = r;`: a value written, or a static value's words copied. -/
def assignCode (b : Nat) {Γ : Ctx} : {T : Ty} → Solidity.Core.Src C Γ T →
    Solidity.Core.Loc C Γ T → List Instr
  | _, .val v, l => compileVal b v ++ compileLoc b l ++ [.sstore]
  | _, @Solidity.Core.Src.copy _ _ R q _, l =>
    compileSPath b q ++ loadLeaves (leaves (.ref R)) ++ [.pop] ++ compileLoc b l ++
      storeLeaves (leaves (.ref R)).reverse ++ [.pop]

/-- The code of an update of `l` (`op=`, `++`): `onLocal` a local's cell,
`onLoc` a storage location; nothing for a memory target. -/
def opLocCode (b : Nat) {Γ : Ctx} {p : PrimTy} (l : Solidity.Core.OpLoc C Γ p)
    (onLocal : Var → List Instr) (onLoc : Solidity.Core.Loc C Γ (.prim p) → List Instr) :
    List Instr :=
  match l with
  | .local i => onLocal (cellOf b i)
  | .root r h => onLoc (.root r h)
  | .field q f h => onLoc (.field q f h)
  | .index it q i => onLoc (.index it q (.simple i))
  | .mfield .. | .mindex .. => []

mutual
/-- The code of a statement in a frame based at `b`; `[]` outside the
fragment (which `inFrag` rejects). -/
def compileStmt (b : Nat) {Γ Γ' : Ctx} : Solidity.Core.Stmt C Γ Γ' → List Instr
  | .assign l r => assignCode b r l
  | .rebind i r => match r with
    | .path q => compileSPath b q ++ [.mstore (cellOf b i)]
    | .push .. => []
  | .assignLocal i r => compileVal b r ++ [.mstore (cellOf b i)]
  | .declLocal _ _ init => match init with
    | none => [.push (.val 0), .mstore (cell (b + Γ.length))]
    | some e => compileVal b e ++ [.mstore (cell (b + Γ.length))]
  | .declStorage _ _ init => match init with
    | some (.path q) => compileSPath b q ++ [.mstore (cell (b + Γ.length))]
    | none | some (.push ..) => []
  | @Solidity.Core.Stmt.opAssign _ _ p op _ _ l r =>
    opLocCode b l (fun x => [.mload x] ++ compileVal b r ++ binTail p op ++ [.mstore x])
      fun loc => compileLoc b loc ++ [.dup 1, .sload] ++ compileVal b r ++ binTail p op ++
        [.swap 1, .sstore]
  | @Solidity.Core.Stmt.incDec _ _ p op _ l =>
    opLocCode b l (fun x => [.mload x, .push (.val 1)] ++ binTail p op.binOp ++ [.mstore x])
      fun loc => compileLoc b loc ++ [.dup 1, .sload, .push (.val 1)] ++ binTail p op.binOp ++
        [.swap 1, .sstore]
  | @Solidity.Core.Stmt.assignIncDec _ _ p i op _ l _ =>
    opLocCode b l (fun y => [.mload y] ++ bumpCode p op ++ [.mstore y, .mstore (cellOf b i)])
      fun loc => compileLoc b loc ++ [.dup 1, .sload] ++ bumpCode p op ++
        [.dup 3, .sstore, .swap 1, .pop, .mstore (cellOf b i)]
  | .push q v _ => pushCode b v q
  | .pop q => compileSPath b q ++ popCode
  | .transfer r a => compileVal b r ++ compileVal b a ++ [.call] ++ assertTop
  | @Solidity.Core.Stmt.delete _ _ T l => compileLoc b l ++ zeroCode (leaves T) ++ [.pop]
  | .ite c t e =>
    compileVal b c ++ [.iszero, .jumpi ((compileProg b t).length + 1)] ++ compileProg b t ++
      [.jump (compileProg b e).length] ++ compileProg b e
  | .require c | .assert c => compileVal b c ++ assertTop
  | .revert => [.revert]
  -- the body in its own frame, above the caller's locals
  | @Solidity.Core.Stmt.call _ _ _ ps _ _ _ args ret body =>
    argsCode b args ++ retEnterCode b ps ret ++ compileProg (b + Γ.length) body ++
      retLeaveCode b ps ret
  | .block body => compileProg b body
  | .send .. | .declMem .. | .rebindMem .. | .assignFromMem .. | .assignMem .. | .deleteMem ..
  | .assignNew .. | .tryCall .. | .loop .. => []
/-- The code of a block: its statements' codes in order. -/
def compileProg (b : Nat) {Γ Γ' : Ctx} : Solidity.Core.Prog C Γ Γ' → List Instr
  | .nil => []
  | .cons s P => compileStmt b s ++ compileProg b P
end

mutual
/-- How many `push` statements a statement has (`Evm.pushes`): each runs at
most once, since the fragment has no loop. -/
def Stmt.pushes {Γ Γ' : Ctx} : Solidity.Core.Stmt C Γ Γ' → Nat
  | .push .. => 1
  | .ite _ t e => Prog.pushes t + Prog.pushes e
  | .block body => Prog.pushes body
  | .call _ _ _ body => Prog.pushes body
  | .assign .. | .rebind .. | .assignLocal .. | .declLocal .. | .declStorage .. | .opAssign ..
  | .incDec .. | .assignIncDec .. | .pop _ | .transfer .. | .send .. | .declMem ..
  | .rebindMem .. | .assignFromMem .. | .assignMem .. | .delete _ | .deleteMem .. | .assignNew ..
  | .require _ | .assert _ | .revert | .tryCall .. | .loop .. => 0
def Prog.pushes {Γ Γ' : Ctx} : Solidity.Core.Prog C Γ Γ' → Nat
  | .nil => 0
  | .cons s P => Stmt.pushes s + Prog.pushes P
end

mutual
/-- Whether a statement pays (`Evm.pays`): a `transfer` or a `send`, or one
in a branch, a block or a called body. -/
def Stmt.pays {Γ Γ' : Ctx} : Solidity.Core.Stmt C Γ Γ' → Bool
  | .transfer .. | .send .. => true
  | .ite _ t e => Prog.pays t || Prog.pays e
  | .block body => Prog.pays body
  | .call _ _ _ body => Prog.pays body
  | .assign .. | .rebind .. | .assignLocal .. | .declLocal .. | .declStorage .. | .opAssign ..
  | .incDec .. | .assignIncDec .. | .push .. | .pop _ | .declMem ..
  | .rebindMem .. | .assignFromMem .. | .assignMem .. | .delete _ | .deleteMem .. | .assignNew ..
  | .require _ | .assert _ | .revert | .tryCall .. | .loop .. => false
def Prog.pays {Γ Γ' : Ctx} : Solidity.Core.Prog C Γ Γ' → Bool
  | .nil => false
  | .cons s P => Stmt.pays s || Prog.pays P
end

/-! ## Against the untyped compiler -/

section Erase

open Solidity.Core (Stmt.erase Prog.erase Stmt.outNames)

mutual
/-- Every call's arguments are separated (`Arg.separatedFrom`) once
erased: the calls `erase` keeps as calls, whose arguments it does not move
into the body. -/
def Stmt.sepArgs {Γ Γ' : Ctx} (ns : List Var) : Solidity.Core.Stmt C Γ Γ' → Bool
  | .call _ args ret body =>
    Arg.separatedFrom [] (args.erase ns) && Prog.sepArgs (ret.names ++ args.names) body
  | .ite _ t e => Prog.sepArgs ns t && Prog.sepArgs ns e
  | .block body => Prog.sepArgs ns body
  | .assign .. | .rebind .. | .assignLocal .. | .declLocal .. | .declStorage .. | .opAssign ..
  | .incDec .. | .assignIncDec .. | .push .. | .pop _ | .transfer .. | .send .. | .declMem ..
  | .rebindMem .. | .assignFromMem .. | .assignMem .. | .delete _ | .deleteMem .. | .assignNew ..
  | .require _ | .assert _ | .revert | .tryCall .. | .loop .. => true
def Prog.sepArgs {Γ Γ' : Ctx} (ns : List Var) : Solidity.Core.Prog C Γ Γ' → Bool
  | .nil => true
  | .cons s P => Stmt.sepArgs ns s && Prog.sepArgs (s.outNames ns) P
end

local notation "⌊" l "⌋" => List.map Instr.forgetCell l

theorem length_of_forget {l₁ l₂ : List Instr} (h : ⌊l₁⌋ = ⌊l₂⌋) : l₁.length = l₂.length := by
  simpa only [List.length_map] using congrArg List.length h

theorem _root_.Solidity.Evm.compileProg_append (P Q : Solidity.Prog C) :
    Evm.compileProg (P ++ Q) = Evm.compileProg P ++ Evm.compileProg Q := by
  induction P with
  | nil => rfl
  | cons s P ih => simp only [List.cons_append, Evm.compileProg, ih, List.append_assoc]

theorem compileSimple_erase (b : Nat) (ns : List Var) {Γ : Ctx} {p : PrimTy}
    (s : Solidity.Core.Simple C Γ p) :
    ⌊compileSimple b s⌋ = ⌊Evm.compileSimple (s.erase ns)⌋ := by
  cases s <;> rfl

mutual
theorem compileSPath_erase (b : Nat) (ns : List Var) {Γ : Ctx} : {T : Ty} →
    (q : Solidity.Core.SPath C Γ T) → ⌊compileSPath b q⌋ = ⌊Evm.compileSPath (q.erase ns)⌋
  | _, .alias _ => rfl
  | _, .loc l => by
    simp only [compileSPath, Evm.compileSPath, Solidity.Core.SPath.erase]
    exact compileLoc_erase b ns l
theorem compileLoc_erase (b : Nat) (ns : List Var) {Γ : Ctx} : {T : Ty} →
    (l : Solidity.Core.Loc C Γ T) → ⌊compileLoc b l⌋ = ⌊Evm.compileLoc (l.erase ns)⌋
  | _, .root _ _ => rfl
  | _, .field q _ _ => by
    simp only [compileLoc, Evm.compileLoc, Solidity.Core.Loc.erase, List.map_append,
      compileSPath_erase b ns q]
  | _, .index .map q i => by
    simp only [compileLoc, Evm.compileLoc, Solidity.Core.Loc.erase, List.map_append,
      compileSPath_erase b ns q, compileVal_erase b ns i]
  | _, .index (.arr .dyn) q i => by
    simp only [compileLoc, Evm.compileLoc, Solidity.Core.Loc.erase, List.map_append,
      compileSPath_erase b ns q, compileVal_erase b ns i]
  | _, .index (.arr .fixed) q i => by
    simp only [compileLoc, Evm.compileLoc, Solidity.Core.Loc.erase, List.map_append,
      compileSPath_erase b ns q, compileVal_erase b ns i]
theorem compileVal_erase (b : Nat) (ns : List Var) {Γ : Ctx} : {p : PrimTy} →
    (v : Solidity.Core.Val C Γ p) → ⌊compileVal b v⌋ = ⌊Evm.compileVal (v.erase ns)⌋
  | _, .simple s => by
    simp only [compileVal, Evm.compileVal, Solidity.Core.Val.erase]
    exact compileSimple_erase b ns s
  | _, .read l => by
    simp only [compileVal, Evm.compileVal, Solidity.Core.Val.erase, List.map_append,
      compileLoc_erase b ns l]
  | _, .binop op _ _ x y => by
    have hx := compileVal_erase b ns x
    have hy := compileVal_erase b ns y
    have ly := length_of_forget hy
    cases op <;> simp only [compileVal, Evm.compileVal, Solidity.Core.Val.erase, List.map_append,
      hx, hy, ly]
  | _, .unop op _ _ x => by
    have hx := compileVal_erase b ns x
    cases op <;> simp only [compileVal, Evm.compileVal, Solidity.Core.Val.erase, List.map_append, hx]
  | _, .ternary c x y => by
    have hc := compileVal_erase b ns c
    have hx := compileVal_erase b ns x
    have hy := compileVal_erase b ns y
    simp only [compileVal, Evm.compileVal, Solidity.Core.Val.erase, List.map_append, hc, hx, hy,
      length_of_forget hx, length_of_forget hy]
  | _, .len q _ => by
    simp only [compileVal, Evm.compileVal, Solidity.Core.Val.erase, List.map_append,
      compileSPath_erase b ns q]
  | _, .readMem _ => rfl
  | _, .mlen .. => rfl
end

theorem _root_.Solidity.Evm.argsCode_append (l₁ l₂ : List (Arg C)) :
    Evm.argsCode (l₁ ++ l₂) = Evm.argsCode l₁ ++ Evm.argsCode l₂ := by
  induction l₁ with
  | nil => rfl
  | cons a l ih => simp only [List.cons_append, Evm.argsCode, ih, List.append_assoc]

theorem argsCode_erase (b : Nat) (ns : List Var) {Γ : Ctx} : {ps : Ctx} →
    (args : Solidity.Core.Args C Γ ps) → ⌊argsCode b args⌋ = ⌊Evm.argsCode (args.erase ns)⌋
  | _, .nil => rfl
  | _, .snoc as _ _ e => by
    simp only [argsCode, Solidity.Core.Args.erase, Evm.argsCode_append, Evm.argsCode,
      List.append_nil, List.map_append, argsCode_erase b ns as, compileVal_erase b ns e,
      List.append_assoc]
    rfl

theorem retEnterCode_erase (b : Nat) (ns : List Var) {Γ : Ctx} (ps : Ctx) {rs Γ' : Ctx}
    (ret : Solidity.Core.CallRet Γ rs Γ') :
    ⌊retEnterCode b ps ret⌋ = ⌊Evm.retEnterCode (ret.erase ns)⌋ := by
  cases ret <;> rfl

theorem retLeaveCode_erase (b : Nat) (ns : List Var) {Γ : Ctx} (ps : Ctx) {rs Γ' : Ctx}
    (ret : Solidity.Core.CallRet Γ rs Γ') :
    ⌊retLeaveCode b ps ret⌋ = ⌊Evm.retLeaveCode (ret.erase ns)⌋ := by
  cases ret with
  | val _ _ res => cases res <;> rfl
  | _ => rfl

/-- A memory return's declaration, which `erase` puts at the body's head, has
no code. -/
theorem compileProg_pre {Γ : Ctx} {rs Γ' : Ctx} (ret : Solidity.Core.CallRet Γ rs Γ') :
    Evm.compileProg (ret.pre (C := C)) = [] := by
  cases ret <;> rfl

theorem pushCode_erase (b : Nat) (ns : List Var) {Γ : Ctx} {E : Ty}
    (v : Option (Solidity.Core.Src C Γ E)) (q : Solidity.Core.SPath C Γ (.array E)) :
    ⌊pushCode b v q⌋ = ⌊Evm.pushCode (v.map (Solidity.Core.Src.erase ns)) (q.erase ns)⌋ := by
  rcases v with _ | (v | q')
  · simp only [pushCode, Evm.pushCode, Option.map, List.map_append, compileSPath_erase b ns q]
  · simp only [pushCode, Evm.pushCode, Option.map, Solidity.Core.Src.erase, List.map_append,
      compileSPath_erase b ns q, compileVal_erase b ns v]
  · simp only [pushCode, Evm.pushCode, Option.map, Solidity.Core.Src.erase, List.map_append,
      compileSPath_erase b ns q, compileSPath_erase b ns q']

mutual
/-- **The two compilers agree**: a statement and its erasure compile to the
same code up to the memory cells, when its calls' arguments are separated. -/
theorem compileStmt_erase (b : Nat) (ns : List Var) {Γ Γ' : Ctx} :
    (s : Solidity.Core.Stmt C Γ Γ') → Stmt.sepArgs ns s = true →
    ⌊compileStmt b s⌋ = ⌊Evm.compileProg (s.erase ns)⌋
  | .assign l (.val v), _ => by
    simp only [compileStmt, assignCode, Stmt.erase, Solidity.Core.Src.erase, Evm.compileProg, Evm.compileStmt,
      List.append_nil, List.map_append, compileVal_erase b ns v, compileLoc_erase b ns l]
  | .assign l (.copy q _), _ => by
    simp only [compileStmt, assignCode, Stmt.erase, Solidity.Core.Src.erase, Evm.compileProg, Evm.compileStmt,
      List.append_nil, List.map_append, compileSPath_erase b ns q, compileLoc_erase b ns l]
  | .rebind _ (.path q), _ => by
    simp only [compileStmt, Stmt.erase, Solidity.Core.ARhs.erase, Evm.compileProg,
      Evm.compileStmt, List.append_nil, List.map_append, compileSPath_erase b ns q]
    rfl
  | .rebind _ (.push ..), _ => rfl
  | .assignLocal _ r, _ => by
    simp only [compileStmt, Stmt.erase, Evm.compileProg, Evm.compileStmt, List.append_nil,
      List.map_append, compileVal_erase b ns r]
    rfl
  | .declLocal _ _ none, _ => rfl
  | .declLocal _ _ (some e), _ => by
    simp only [compileStmt, Stmt.erase, Option.map, Evm.compileProg, Evm.compileStmt,
      List.append_nil, List.map_append, compileVal_erase b ns e]
    rfl
  | .declStorage _ _ none, _ => rfl
  | .declStorage _ _ (some (.path q)), _ => by
    simp only [compileStmt, Stmt.erase, Option.map, Solidity.Core.ARhs.erase, Evm.compileProg,
      Evm.compileStmt, List.append_nil, List.map_append, compileSPath_erase b ns q]
    rfl
  | .declStorage _ _ (some (.push ..)), _ => rfl
  | .opAssign _ _ _ l r, _ => by
    cases l <;> simp only [compileStmt, opLocCode, Stmt.erase, Solidity.Core.OpLoc.erase,
      Evm.compileProg, Evm.compileStmt, Evm.opLocToLoc, List.append_nil, List.map_append,
      compileLoc_erase b ns, Solidity.Core.Loc.erase, Solidity.Core.Val.erase, compileVal_erase b ns r] <;> rfl
  | .incDec _ _ l, _ => by
    cases l <;> simp only [compileStmt, opLocCode, Stmt.erase, Solidity.Core.OpLoc.erase,
      Evm.compileProg, Evm.compileStmt, Evm.opLocToLoc, List.append_nil, List.map_append,
      compileLoc_erase b ns, Solidity.Core.Loc.erase, Solidity.Core.Val.erase] <;> rfl
  | .assignIncDec _ _ _ l _, _ => by
    cases l <;> simp only [compileStmt, opLocCode, Stmt.erase, Solidity.Core.OpLoc.erase,
      Evm.compileProg, Evm.compileStmt, Evm.opLocToLoc, List.append_nil, List.map_append,
      compileLoc_erase b ns, Solidity.Core.Loc.erase, Solidity.Core.Val.erase] <;> rfl
  | .push q v _, _ => by
    simp only [compileStmt, Stmt.erase, Evm.compileProg, Evm.compileStmt, List.append_nil]
    exact pushCode_erase b ns v q
  | .pop q, _ => by
    simp only [compileStmt, Stmt.erase, Evm.compileProg, Evm.compileStmt, List.append_nil,
      List.map_append, compileSPath_erase b ns q]
  | .transfer r a, _ => by
    simp only [compileStmt, Stmt.erase, Evm.compileProg, Evm.compileStmt, List.append_nil,
      List.map_append, compileVal_erase b ns r, compileVal_erase b ns a]
  | .send .., _ => rfl
  | .declMem .., _ => rfl
  | .rebindMem .., _ => rfl
  | .assignFromMem .., _ => rfl
  | .assignMem .., _ => rfl
  | .delete l, _ => by
    simp only [compileStmt, Stmt.erase, Evm.compileProg, Evm.compileStmt, List.append_nil,
      List.map_append, compileLoc_erase b ns l]
  | .deleteMem .., _ => rfl
  | .assignNew .., _ => rfl
  | .ite c t e, h => by
    simp only [Stmt.sepArgs, Bool.and_eq_true] at h
    have ht := compileProg_erase b ns t h.1
    have he := compileProg_erase b ns e h.2
    simp only [compileStmt, Stmt.erase, Evm.compileProg, Evm.compileStmt, List.append_nil,
      List.map_append, compileVal_erase b ns c, ht, he, length_of_forget ht, length_of_forget he]
  | .require c, _ => by
    simp only [compileStmt, Stmt.erase, Evm.compileProg, Evm.compileStmt, List.append_nil,
      List.map_append, compileVal_erase b ns c]
  | .assert c, _ => by
    simp only [compileStmt, Stmt.erase, Evm.compileProg, Evm.compileStmt, List.append_nil,
      List.map_append, compileVal_erase b ns c]
  | .revert, _ => rfl
  | @Solidity.Core.Stmt.call _ Γ _ ps _ _ f args ret body, h => by
    simp only [Stmt.sepArgs, Bool.and_eq_true] at h
    rw [Solidity.Core.Stmt.erase_call ns f args ret body h.1]
    simp only [compileStmt, Evm.compileProg, Evm.compileStmt, List.append_nil, List.map_append,
      Evm.compileProg_append, compileProg_pre, List.nil_append, argsCode_erase b ns args,
      retEnterCode_erase b ns ps ret, retLeaveCode_erase b ns ps ret,
      compileProg_erase (b + Γ.length) _ body h.2]
  | .tryCall .., _ => rfl
  | .loop .., _ => rfl
  | .block body, h => by
    simp only [Stmt.sepArgs] at h
    simp only [compileStmt, Stmt.erase]
    exact compileProg_erase b ns body h
theorem compileProg_erase (b : Nat) (ns : List Var) {Γ Γ' : Ctx} :
    (P : Solidity.Core.Prog C Γ Γ') → Prog.sepArgs ns P = true →
    ⌊compileProg b P⌋ = ⌊Evm.compileProg (P.erase ns)⌋
  | .nil, _ => rfl
  | .cons s P, h => by
    simp only [Prog.sepArgs, Bool.and_eq_true] at h
    simp only [compileProg, Prog.erase, Evm.compileProg_append, List.map_append,
      compileStmt_erase b ns s h.1, compileProg_erase b (s.outNames ns) P h.2]
end

theorem _root_.Solidity.Evm.pushesP_append (P Q : Solidity.Prog C) :
    Evm.pushesP (P ++ Q) = Evm.pushesP P + Evm.pushesP Q := by
  induction P with
  | nil => simp only [List.nil_append, Evm.pushesP, Nat.zero_add]
  | cons s P ih => simp only [List.cons_append, Evm.pushesP, ih, Nat.add_assoc]

theorem _root_.Solidity.Evm.paysP_append (P Q : Solidity.Prog C) :
    Evm.paysP (P ++ Q) = (Evm.paysP P || Evm.paysP Q) := by
  induction P with
  | nil => simp only [List.nil_append, Evm.paysP, Bool.false_or]
  | cons s P ih => simp only [List.cons_append, Evm.paysP, ih, Bool.or_assoc]

/-- A call's erased body starts with what has no `push` and no payment: the
memory return's declaration, the unseparated arguments' declarations. -/
theorem pushesP_pre {Γ : Ctx} {rs Γ' : Ctx} (ret : Solidity.Core.CallRet Γ rs Γ') :
    Evm.pushesP (ret.pre (C := C)) = 0 ∧ Evm.paysP (ret.pre (C := C)) = false := by
  cases ret <;> exact ⟨rfl, rfl⟩

theorem pushesP_decls (as : List (Arg C)) :
    Evm.pushesP (as.map Arg.decl) = 0 ∧ Evm.paysP (as.map Arg.decl) = false := by
  induction as with
  | nil => exact ⟨rfl, rfl⟩
  | cons a as ih =>
    simp only [List.map_cons, Evm.pushesP, Evm.paysP, ih.1, ih.2]
    exact ⟨rfl, rfl⟩

mutual
/-- The two counts agree with the untyped ones, for every statement. -/
theorem pushes_erase (ns : List Var) {Γ Γ' : Ctx} : (s : Solidity.Core.Stmt C Γ Γ') →
    Stmt.pushes s = Evm.pushesP (s.erase ns) ∧ Stmt.pays s = Evm.paysP (s.erase ns)
  | .ite _ t e => by
    obtain ⟨ht, ht'⟩ := pushesP_erase ns t
    obtain ⟨he, he'⟩ := pushesP_erase ns e
    simp only [Stmt.pushes, Stmt.pays, Stmt.erase, Evm.pushesP, Evm.pushes, Evm.paysP, Evm.pays,
      ht, he, ht', he', Nat.add_zero, Bool.or_false, and_self]
  | .block body => by
    simp only [Stmt.pushes, Stmt.pays, Stmt.erase]
    exact pushesP_erase ns body
  | .call f args ret body => by
    obtain ⟨hb, hb'⟩ := pushesP_erase (ret.names ++ args.names) body
    obtain ⟨hp, hp'⟩ := pushesP_pre (C := C) ret
    simp only [Stmt.pushes, Stmt.pays, Stmt.erase]
    split
    · simp only [Evm.pushesP, Evm.pushes, Evm.paysP, Evm.pays, Evm.pushesP_append,
        Evm.paysP_append, hp, hp', hb, hb', Nat.zero_add, Nat.add_zero, Bool.false_or,
        Bool.or_false, and_self]
    · obtain ⟨hd, hd'⟩ := pushesP_decls (args.erase ns)
      simp only [Evm.pushesP, Evm.pushes, Evm.paysP, Evm.pays, Evm.pushesP_append,
        Evm.paysP_append, hp, hp', hb, hb', hd, hd', Nat.zero_add, Nat.add_zero, Bool.false_or,
        Bool.or_false, and_self]
  | .assign .. | .rebind .. | .assignLocal .. | .declLocal .. | .declStorage .. | .opAssign ..
  | .incDec .. | .assignIncDec .. | .push .. | .pop _ | .transfer .. | .send .. | .declMem ..
  | .rebindMem .. | .assignFromMem .. | .assignMem .. | .delete _ | .deleteMem .. | .assignNew ..
  | .require _ | .assert _ | .revert | .tryCall .. | .loop .. => ⟨rfl, rfl⟩
theorem pushesP_erase (ns : List Var) {Γ Γ' : Ctx} : (P : Solidity.Core.Prog C Γ Γ') →
    Prog.pushes P = Evm.pushesP (P.erase ns) ∧ Prog.pays P = Evm.paysP (P.erase ns)
  | .nil => ⟨rfl, rfl⟩
  | .cons s P => by
    obtain ⟨hs, hs'⟩ := pushes_erase ns s
    obtain ⟨hP, hP'⟩ := pushesP_erase (s.outNames ns) P
    simp only [Prog.pushes, Prog.pays, Prog.erase, Evm.pushesP_append, Evm.paysP_append, hs, hs',
      hP, hP', and_self]
end

end Erase

end Core
end Solidity.Evm
