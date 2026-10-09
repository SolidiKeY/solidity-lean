import Solidity.Evm.Layout
import Solidity.Syntax.Resolve
import Solidity.Semantics.StorageErase

/-!
# The compiler over the scoped syntax

The compiler, on `Syntax/Scoped.lean`'s statements (`docs/intrinsic.md`,
M5), from `Evm/Layout.lean`'s code sequences.

**A local lives at its level.**  A local of `Γ` at position `i` (innermost
`0`) lives in memory cell `b + (Γ.length - 1 - i)`: its *level*, counted from
the outermost local, so a cell does not move when locals are pushed above
it.  `b` is the frame's base: `0` for the program, the caller's next free
level for a call's body, which is closed over its own frame `rs ++ ps`
(parameters from `b`, then the return variables).  The machine's memory is
addressed by level: the cell of level `l` is `cell l = l` (printed `%l`).  A scope's locals are not cleared at its end: the next
local declared at that level overwrites the cell (every declaration but
an unset `T storage x;` writes its cell; that alias is `dead` in `Frag` and
not read until a rebind writes the cell).

**The fragment is what `inFrag` accepts.**  Typing is the syntax's: a
local is read at its declared type and in scope by construction, so
`inFrag` keeps only the facts about the target: which aliases may be read (`Frag Γ`: a plain alias, a *fragile* one bound through
an array index and forgotten at the next `pop` or `delete`, or an unset or
forgotten one), the operators, static copies, `push` shapes, no memory, no
`send`/`try`/loop, no call of several returns.  A branch's or a block's
locals end with it: what it did to the enclosing aliases is kept
(`Frag.restrict`), the two branches' met.  A call's body starts from a frame
of its own, where every parameter and return variable may be read; a `pop`
or `delete` anywhere in it forgets the caller's fragile aliases
(`Stmt.shrinks`).
-/

namespace Solidity.Evm

open Solidity (Ctx Idx)

variable {C : Contract}

/-! ## Levels -/

/-- The memory cell of level `l`: the machine's memory is addressed by
level, so the cell is the level itself. -/
abbrev cell (l : Nat) : Nat := l

theorem cell_inj {l l' : Nat} (h : cell l = cell l') : l = l' := h

/-- The level of the local at position `i` of `Γ`, in a frame based at `b`. -/
def lvl (b : Nat) {Γ : Ctx} {t : LTy} (i : Idx Γ t) : Nat := b + (Γ.length - 1 - i.toNat)

/-- The cell of the local at position `i`. -/
abbrev cellOf (b : Nat) {Γ : Ctx} {t : LTy} (i : Idx Γ t) : Nat := cell (lvl b i)

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

def get {Γ : Ctx} {t : LTy} (F : Frag Γ) (i : Idx Γ t) : Fl := F.fl.getD i.toNat .dead

/-- A local pushed. -/
def push {Γ : Ctx} (t : LTy) (F : Frag Γ) (f : Fl) : Frag (t :: Γ) := ⟨f :: F.fl⟩

def set {Γ : Ctx} {t : LTy} (F : Frag Γ) (i : Idx Γ t) (f : Fl) : Frag Γ := ⟨F.fl.set i.toNat f⟩

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
def simpleIn {Γ : Ctx} : {p : PrimTy} → Solidity.Simple C Γ p → Bool
  | _, .env k _ => k != .selfBalance
  | _, _ => true

mutual
/-- `free`: the path indexes no array (what an alias may be bound to). -/
def spathIn {Γ : Ctx} (F : Frag Γ) (free : Bool) : {T : Ty} → Solidity.SPath C Γ T → Bool
  | _, .alias i => F.get i == .ok || (!free && F.get i == .fragile)
  | _, .loc l => locIn F free l
def locIn {Γ : Ctx} (F : Frag Γ) (free : Bool) : {T : Ty} → Solidity.Loc C Γ T → Bool
  | _, .root .. => true
  | _, .field b _ _ => spathIn F free b
  | _, @Solidity.Loc.index _ _ _ k _ .map b i => k == .uint && spathIn F free b && valIn F i
  | _, .index (.arr _) b i => !free && spathIn F free b && valIn F i
def valIn {Γ : Ctx} (F : Frag Γ) : {p : PrimTy} → Solidity.Val C Γ p → Bool
  | _, .simple s => simpleIn s
  | _, .read l => locIn F false l
  | _, @Solidity.Val.binop _ _ p _ op _ _ a b => binInFrag op p && valIn F a && valIn F b
  | _, @Solidity.Val.unop _ _ p _ op _ _ a => unInFrag op p && valIn F a
  | _, .ternary c a b => valIn F c && valIn F a && valIn F b
  | _, .len b _ => spathIn F false b
  | _, .readMem _ | _, .mlen .. => false
end

/-- The storage location an `op=` target names, if it is one. -/
def opLocToLoc {Γ : Ctx} : {p : PrimTy} → Solidity.OpLoc C Γ p →
    Option (Solidity.Loc C Γ (.prim p))
  | _, .root r h => some (.root r h)
  | _, .field b f h => some (.field b f h)
  | _, .index it b i => some (.index it b (.simple i))
  | _, .local _ | _, .mfield .. | _, .mindex .. => none

def opLocIn {Γ : Ctx} (F : Frag Γ) {p : PrimTy} (l : Solidity.OpLoc C Γ p) : Bool :=
  match l with
  | .local _ => true
  | l => match opLocToLoc l with
    | some loc => locIn F false loc
    | none => false

/-- Every argument of a call in the fragment. -/
def argsIn {Γ : Ctx} (F : Frag Γ) : {ps : Ctx} → Solidity.Args C Γ ps → Bool
  | _, .nil => true
  | _, .snoc as _ _ e => argsIn F as && valIn F e

/-- What a call leaves the caller knowing: nothing new for no return or one
return value; a call of several returns, or of a memory return, is out. -/
def CallRetIn {Γ : Ctx} (F : Frag Γ) : {rs Γ' : Ctx} → Solidity.CallRet Γ rs Γ' →
    Option (Frag Γ')
  | _, _, .none => some F
  | _, _, .val .. => some F
  | _, _, .rets _ => none
  | _, _, .mem .. => none

/-- An alias bound to `q`: plain if `q` indexes no array, fragile if it does. -/
def bindFl {Γ : Ctx} (F : Frag Γ) {R : RefTy} (q : Solidity.SPath C Γ (.ref R)) :
    Option Fl :=
  if spathIn F true q then some .ok else if spathIn F false q then some .fragile else none

/-- A `push` of the fragment: `push()` of a primitive, `push(e)`, `push(sp)`
of a static element. -/
def pushIn {Γ : Ctx} (F : Frag Γ) : {E : Ty} → Option (Solidity.Src C Γ E) →
    Solidity.SPath C Γ (.array E) → Bool
  | E, none, b => E.isPrimitive && spathIn F false b
  | _, some (.val e), b => spathIn F false b && valIn F e
  | _, some (@Solidity.Src.copy _ _ R q _), b =>
    static (.ref R) && spathIn F false b && spathIn F false q

mutual
/-- Whether a statement may shrink an array (a `pop` or a `delete`, in a
branch, a block or a called body): the caller's fragile aliases are
forgotten after it. -/
def Stmt.shrinks {Γ Γ' : Ctx} : Solidity.Stmt C Γ Γ' → Bool
  | .pop _ | .delete _ => true
  | .ite _ t e => Prog.shrinks t || Prog.shrinks e
  | .block body => Prog.shrinks body
  | .call _ _ _ body => Prog.shrinks body
  | .assign .. | .rebind .. | .assignLocal .. | .declLocal .. | .declStorage .. | .opAssign ..
  | .incDec .. | .assignIncDec .. | .push .. | .transfer .. | .send .. | .declMem ..
  | .rebindMem .. | .assignFromMem .. | .assignMem .. | .deleteMem .. | .assignNew ..
  | .require _ | .assert _ | .revert | .tryCall .. | .loop .. => false
def Prog.shrinks {Γ Γ' : Ctx} : Solidity.Prog C Γ Γ' → Bool
  | .nil => false
  | .cons s P => Stmt.shrinks s || Prog.shrinks P
end

/-- `F` after a statement that does or does not shrink an array. -/
def Frag.after {Γ : Ctx} (F : Frag Γ) (shrinks : Bool) : Frag Γ :=
  if shrinks then F.dropFragile else F

/-- `F` if the check passes. -/
def Frag.guard {Γ : Ctx} (F : Frag Γ) (ok : Bool) : Option (Frag Γ) := if ok then some F else none

/-- `l = r;` of the fragment: a value, or a copy of a static value (the
typed run's positional copy is the name-wise one the representation reads:
no struct repeats a member name, `structDef_nodup`, which
`Storage.writeStorage_erase` reads). -/
def assignIn {Γ : Ctx} (F : Frag Γ) : {T : Ty} → Solidity.Src C Γ T →
    Solidity.Loc C Γ T → Bool
  | _, .val v, l => locIn F false l && valIn F v
  | _, @Solidity.Src.copy _ _ R q _, l =>
    static (.ref R) && spathIn F false q && locIn F false l

/-- A storage alias declared: unset (not readable), or bound to a path of
the fragment. -/
def declStorageIn {Γ : Ctx} (F : Frag Γ) (R : RefTy) :
    Option (Solidity.ARhs C Γ R) → Option (Frag (.alias R :: Γ))
  | none => some (F.push (.alias R) .dead)
  | some (.path q) => (bindFl F q).map (F.push (.alias R))
  | some (.push ..) => none

mutual
/-- A statement of the fragment, and what is known after it. -/
def inFrag {Γ Γ' : Ctx} (F : Frag Γ) : Solidity.Stmt C Γ Γ' → Option (Frag Γ')
  | .assign l r => F.guard (assignIn F r l)
  | .rebind i r => match r with
    | .path q => (bindFl F q).map (F.set i)
    | .push .. => none
  | .assignLocal _ r => F.guard (valIn F r)
  | .declLocal p _ init => (F.push (.val p) .ok).guard (init.all (valIn F))
  | .declStorage R _ init => declStorageIn F R init
  | .opAssign _ _ _ l r => F.guard (opLocIn F l && valIn F r)
  | .incDec _ _ l => F.guard (opLocIn F l)
  | .assignIncDec _ _ _ l _ => F.guard (opLocIn F l)
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
  | @Solidity.Stmt.call _ _ _ ps rs _ _ args ret body =>
    if argsIn F args then
      match inFragP (Frag.init (rs ++ ps)) body with
      | some _ => CallRetIn (F.after (Prog.shrinks body)) ret
      | none => none
    else none
  | .send .. | .declMem .. | .rebindMem .. | .assignFromMem .. | .assignMem .. | .deleteMem ..
  | .assignNew .. | .tryCall .. | .loop .. => none
/-- A block of the fragment. -/
def inFragP {Γ Γ' : Ctx} (F : Frag Γ) : Solidity.Prog C Γ Γ' → Option (Frag Γ')
  | .nil => some F
  | .cons s P => match inFrag F s with
    | some F' => inFragP F' P
    | none => none
end

/-! ## The compiler -/

def compileSimple (b : Nat) {Γ : Ctx} : {p : PrimTy} → Solidity.Simple C Γ p → List Instr
  | _, .lit n _ => [.push (.val (toWord n))]
  | _, .bool v => [.push (.val (bword v))]
  | _, .local i => [.mload (cellOf b i)]
  | _, .env k _ => [envInstr k]

mutual
/-- Push the slot a storage path names. -/
def compileSPath (b : Nat) {Γ : Ctx} : {T : Ty} → Solidity.SPath C Γ T → List Instr
  | _, .alias i => [.mload (cellOf b i)]
  | _, .loc l => compileLoc b l
/-- Push the slot of a location. -/
def compileLoc (b : Nat) {Γ : Ctx} : {T : Ty} → Solidity.Loc C Γ T → List Instr
  | _, .root r _ => [.push (.slot (rootSlot C r))]
  | _, @Solidity.Loc.field _ _ s _ q f _ => compileSPath b q ++ [.push (.val (offset s f)), .add]
  | _, .index .map q i => compileSPath b q ++ compileVal b i ++ [.keccakMap]
  | _, @Solidity.Loc.index _ _ _ _ E (.arr .dyn) q i =>
    compileSPath b q ++ compileVal b i ++ boundsCheck ++ elemSlot (size E)
  | _, @Solidity.Loc.index _ _ _ _ E (@IndexTy.arr _ _ (@ArrTy.fixed _ n)) q i =>
    compileSPath b q ++ compileVal b i ++ fixedCheck n ++ fixedSlot (size E)
/-- Push the value of an expression. -/
def compileVal (b : Nat) {Γ : Ctx} : {p : PrimTy} → Solidity.Val C Γ p → List Instr
  | _, .simple s => compileSimple b s
  | _, .read l => compileLoc b l ++ [.sload]
  | _, @Solidity.Val.binop _ _ p _ op _ _ x y =>
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

/-- `b.push(…)`: the array's slot, the value (a word, or a static value's
words), the length checked and grown, the value stored at the new element. -/
def pushCode (b : Nat) {Γ : Ctx} : {E : Ty} → Option (Solidity.Src C Γ E) →
    Solidity.SPath C Γ (.array E) → List Instr
  | _, none, q => compileSPath b q ++ [.push (.val 0), .dup 2] ++ pushSlotCode 1 ++ [.sstore, .pop]
  | _, some (.val e), q =>
    compileSPath b q ++ compileVal b e ++ [.dup 2] ++ pushSlotCode 1 ++ [.sstore, .pop]
  | _, some (@Solidity.Src.copy _ _ R p _), q =>
    compileSPath b q ++ compileSPath b p ++ loadLeaves (leaves (.ref R)) ++
      [.pop, .dup ((leaves (.ref R)).length + 1)] ++ pushSlotCode (size (.ref R)) ++
      storeLeaves (leaves (.ref R)).reverse ++ [.pop, .pop]

/-- A call's parameters bound, each argument evaluated in the caller's
context and stored at its level in the frame, which starts at `b + Γ.length`. -/
def argsCode (b : Nat) {Γ : Ctx} : {ps : Ctx} → Solidity.Args C Γ ps → List Instr
  | _, .nil => []
  | _, @Solidity.Args.snoc _ _ ps as _ _ e =>
    argsCode b as ++ compileVal b e ++ [.mstore (cell (b + Γ.length + ps.length))]

/-- The return variable declared: `0` in its cell, above the parameters.  A
call of several returns has no code (it is outside the fragment). -/
def retEnterCode (b : Nat) {Γ : Ctx} (ps : Ctx) : {rs Γ' : Ctx} →
    Solidity.CallRet Γ rs Γ' → List Instr
  | _, _, .val .. => [.push (.val 0), .mstore (cell (b + Γ.length + ps.length))]
  | _, _, _ => []

/-- The returned value copied where the call lands. -/
def retLeaveCode (b : Nat) {Γ : Ctx} (ps : Ctx) : {rs Γ' : Ctx} →
    Solidity.CallRet Γ rs Γ' → List Instr
  | _, _, .val _ _ (some y) => [.mload (cell (b + Γ.length + ps.length)), .mstore (cellOf b y)]
  | _, _, _ => []

/-- `l = r;`: a value written, or a static value's words copied. -/
def assignCode (b : Nat) {Γ : Ctx} : {T : Ty} → Solidity.Src C Γ T →
    Solidity.Loc C Γ T → List Instr
  | _, .val v, l => compileVal b v ++ compileLoc b l ++ [.sstore]
  | _, @Solidity.Src.copy _ _ R q _, l =>
    compileSPath b q ++ loadLeaves (leaves (.ref R)) ++ [.pop] ++ compileLoc b l ++
      storeLeaves (leaves (.ref R)).reverse ++ [.pop]

/-- The code of an update of `l` (`op=`, `++`): `onLocal` a local's cell,
`onLoc` a storage location; nothing for a memory target. -/
def opLocCode (b : Nat) {Γ : Ctx} {p : PrimTy} (l : Solidity.OpLoc C Γ p)
    (onLocal : Nat → List Instr) (onLoc : Solidity.Loc C Γ (.prim p) → List Instr) :
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
def compileStmt (b : Nat) {Γ Γ' : Ctx} : Solidity.Stmt C Γ Γ' → List Instr
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
  | @Solidity.Stmt.opAssign _ _ p op _ _ l r =>
    opLocCode b l (fun x => [.mload x] ++ compileVal b r ++ binTail p op ++ [.mstore x])
      fun loc => compileLoc b loc ++ [.dup 1, .sload] ++ compileVal b r ++ binTail p op ++
        [.swap 1, .sstore]
  | @Solidity.Stmt.incDec _ _ p op _ l =>
    opLocCode b l (fun x => [.mload x, .push (.val 1)] ++ binTail p op.binOp ++ [.mstore x])
      fun loc => compileLoc b loc ++ [.dup 1, .sload, .push (.val 1)] ++ binTail p op.binOp ++
        [.swap 1, .sstore]
  | @Solidity.Stmt.assignIncDec _ _ p i op _ l _ =>
    opLocCode b l (fun y => [.mload y] ++ bumpCode p op ++ [.mstore y, .mstore (cellOf b i)])
      fun loc => compileLoc b loc ++ [.dup 1, .sload] ++ bumpCode p op ++
        [.dup 3, .sstore, .swap 1, .pop, .mstore (cellOf b i)]
  | .push q v _ => pushCode b v q
  | .pop q => compileSPath b q ++ popCode
  | .transfer r a => compileVal b r ++ compileVal b a ++ [.call] ++ assertTop
  | @Solidity.Stmt.delete _ _ T l => compileLoc b l ++ zeroCode (leaves T) ++ [.pop]
  | .ite c t e =>
    compileVal b c ++ [.iszero, .jumpi ((compileProg b t).length + 1)] ++ compileProg b t ++
      [.jump (compileProg b e).length] ++ compileProg b e
  | .require c | .assert c => compileVal b c ++ assertTop
  | .revert => [.revert]
  -- the body in its own frame, above the caller's locals
  | @Solidity.Stmt.call _ _ _ ps _ _ _ args ret body =>
    argsCode b args ++ retEnterCode b ps ret ++ compileProg (b + Γ.length) body ++
      retLeaveCode b ps ret
  | .block body => compileProg b body
  | .send .. | .declMem .. | .rebindMem .. | .assignFromMem .. | .assignMem .. | .deleteMem ..
  | .assignNew .. | .tryCall .. | .loop .. => []
/-- The code of a block: its statements' codes in order. -/
def compileProg (b : Nat) {Γ Γ' : Ctx} : Solidity.Prog C Γ Γ' → List Instr
  | .nil => []
  | .cons s P => compileStmt b s ++ compileProg b P
end

mutual
/-- How many `push` statements a statement has: each runs at
most once, since the fragment has no loop. -/
def Stmt.pushes {Γ Γ' : Ctx} : Solidity.Stmt C Γ Γ' → Nat
  | .push .. => 1
  | .ite _ t e => Prog.pushes t + Prog.pushes e
  | .block body => Prog.pushes body
  | .call _ _ _ body => Prog.pushes body
  | .assign .. | .rebind .. | .assignLocal .. | .declLocal .. | .declStorage .. | .opAssign ..
  | .incDec .. | .assignIncDec .. | .pop _ | .transfer .. | .send .. | .declMem ..
  | .rebindMem .. | .assignFromMem .. | .assignMem .. | .delete _ | .deleteMem .. | .assignNew ..
  | .require _ | .assert _ | .revert | .tryCall .. | .loop .. => 0
def Prog.pushes {Γ Γ' : Ctx} : Solidity.Prog C Γ Γ' → Nat
  | .nil => 0
  | .cons s P => Stmt.pushes s + Prog.pushes P
end

mutual
/-- Whether a statement pays: a `transfer` or a `send`, or one
in a branch, a block or a called body. -/
def Stmt.pays {Γ Γ' : Ctx} : Solidity.Stmt C Γ Γ' → Bool
  | .transfer .. | .send .. => true
  | .ite _ t e => Prog.pays t || Prog.pays e
  | .block body => Prog.pays body
  | .call _ _ _ body => Prog.pays body
  | .assign .. | .rebind .. | .assignLocal .. | .declLocal .. | .declStorage .. | .opAssign ..
  | .incDec .. | .assignIncDec .. | .push .. | .pop _ | .declMem ..
  | .rebindMem .. | .assignFromMem .. | .assignMem .. | .delete _ | .deleteMem .. | .assignNew ..
  | .require _ | .assert _ | .revert | .tryCall .. | .loop .. => false
def Prog.pays {Γ Γ' : Ctx} : Solidity.Prog C Γ Γ' → Bool
  | .nil => false
  | .cons s P => Stmt.pays s || Prog.pays P
end

end Solidity.Evm
