import Solidity.Syntax.Scoped

/-!
# `checked { … }`: an overflow is an assertion failure

KeY Java's `intRules:arithmeticSemanticsCheckingOF` for Solidity
(`docs/options.md`, O2): inside `checked { … }` a checked operation that
leaves its type's range fails the proof under either modality, where the
run reverts (`Panic(0x11)`, read as `revert` by both readings) outside it.
The block is a program transformation, not a reading: every statement is
preceded by an `assert` of the range of each checked operation it
evaluates (`Stmt.guard`, `Prog.checkOF`), and a failing `assert` is a panic,
which neither modality accepts (`Modality.afterRunTR`).  So the run, the
rules and the readings are unchanged; the theorem shows the asserts.

What is guarded, at `uint` and at `int` (256 bits; a narrow type is the
elaborator's `require` after the write, an `assert` inside the block,
`narrowCheck`):

* `a + b`, `a - b`, `a * b`; at `int` also `a / b` (`MIN / -1`) and `-a`;
* `x += e` and the other compound assignments, `x++`, `x−−` (on the
  target's current value), and a push's (on the default `0`);
* in evaluation order: the right operand of `&&`/`||` only where it is
  evaluated, the branches of `c ? a : b` under `c`, a loop's condition again
  at the end of every iteration.

Not guarded: `**` (no closed bound; it reverts as outside the block), the
wrapping operators of `unchecked`, division by zero (`Panic(0x12)`, a revert
as outside), the source of a push on a getter's array (read after the
getter's body).  The guards' own operators cannot overflow: at `uint` they
are the wrapping ones (`a <= a +% b`), at `int` `MAX - b` under `b ≥ 0` and
`MIN / a` under `a > 0`; they read the operands again, so a guard halts
where reading them halts.  A right-hand side is guarded before its target,
and a binary operator's left operand that may halt is read first
(`Checked.touch`), in the run's order; what is left of that order is
`docs/options.md`'s, O2.

`ignoringOverflow { … }` (KeY Java's `ignoringOF`, O5) is the same
transformation with `if (g) {} else { assume(false); }` for `assert(g)`
(`OFMode.guardStmt`): an overflowing run is assumed away, under either
modality, rather than going on with an unbounded value the typed state
cannot hold.
-/

namespace Solidity

variable {C : Contract}

namespace Checked

variable {Γ : Ctx}

/-- The largest `uint`. -/
def maxU : Int := ((2 ^ 256 - 1 : Nat) : Int)
/-- The largest and the smallest `int`. -/
def maxI : Int := ((2 ^ 255 - 1 : Nat) : Int)
def minI : Int := -((2 ^ 255 : Nat) : Int)

def litU (n : Int) (h : PrimTy.uint.inRange n = true) : Val C Γ .uint := .simple (.lit n h)
def litI (n : Int) (h : PrimTy.int.inRange n = true) : Val C Γ .int := .simple (.lit n h)

def tt : Val C Γ .bool := .simple (.bool true)
def andB (a b : Val C Γ .bool) : Val C Γ .bool := .binop .and rfl rfl a b
def orB (a b : Val C Γ .bool) : Val C Γ .bool := .binop .or rfl rfl a b
def notB (a : Val C Γ .bool) : Val C Γ .bool := .unop .not rfl rfl a

/-- `a ⊙ b` at a number type: a comparison, or an operation the guards use. -/
def cmpU (op : BinOp) (h : op.accepts .uint = true) (hq : op.ret .uint = .bool)
    (a b : Val C Γ .uint) : Val C Γ .bool := .binop op h hq a b
def cmpI (op : BinOp) (h : op.accepts .int = true) (hq : op.ret .int = .bool)
    (a b : Val C Γ .int) : Val C Γ .bool := .binop op h hq a b
def arU (op : BinOp) (h : op.accepts .uint = true) (hq : op.ret .uint = .uint)
    (a b : Val C Γ .uint) : Val C Γ .uint := .binop op h hq a b
def arI (op : BinOp) (h : op.accepts .int = true) (hq : op.ret .int = .int)
    (a b : Val C Γ .int) : Val C Γ .int := .binop op h hq a b

/-- Both guards, either missing. -/
def andO : Option (Val C Γ .bool) → Option (Val C Γ .bool) → Option (Val C Γ .bool)
  | none, g | g, none => g
  | some a, some b => some (andB a b)

/-- `c ? g : h`, a missing guard `true`. -/
def iteO (c : Val C Γ .bool) : Option (Val C Γ .bool) → Option (Val C Γ .bool) →
    Option (Val C Γ .bool)
  | none, none => none
  | g, h => some (.ternary c (g.getD tt) (h.getD tt))

/-- `a ⊙ b` stays in range at `uint`, by the wrapping operators of
`unchecked`: the sum wraps below `a` exactly when it overflows, the product
divided back is `b` exactly when it does not. -/
def rangeU (op : BinOp) (a b : Val C Γ .uint) : Option (Val C Γ .bool) :=
  let zero : Val C Γ .uint := litU 0 (by decide)
  match op with
  -- `a <= a +% b`
  | .add => some (cmpU .le rfl rfl a (arU .addW rfl rfl a b))
  -- `b <= a`
  | .sub => some (cmpU .le rfl rfl b a)
  -- `a == 0 || (a *% b) / a == b`
  | .mul => some (orB (cmpU .eqB rfl rfl a zero)
      (cmpU .eqB rfl rfl (arU .div rfl rfl (arU .mulW rfl rfl a b) a) b))
  | _ => none

/-- `a ⊙ b` stays in range at `int`. -/
def rangeI (op : BinOp) (a b : Val C Γ .int) : Option (Val C Γ .bool) :=
  let max : Val C Γ .int := litI maxI (by decide)
  let min : Val C Γ .int := litI minI (by decide)
  let zero : Val C Γ .int := litI 0 (by decide)
  let one : Val C Γ .int := litI (-1) (by decide)
  let nonneg (x : Val C Γ .int) : Val C Γ .bool := cmpI .ge rfl rfl x zero
  let pos (x : Val C Γ .int) : Val C Γ .bool := cmpI .gt rfl rfl x zero
  match op with
  -- `b >= 0 ? a <= MAX - b : a >= MIN - b`
  | .add => some (.ternary (nonneg b) (cmpI .le rfl rfl a (arI .sub rfl rfl max b))
      (cmpI .ge rfl rfl a (arI .sub rfl rfl min b)))
  -- `b >= 0 ? a >= MIN + b : a <= MAX + b`
  | .sub => some (.ternary (nonneg b) (cmpI .ge rfl rfl a (arI .add rfl rfl min b))
      (cmpI .le rfl rfl a (arI .add rfl rfl max b)))
  -- `a == 0 || b == 0 || (a > 0 ? (b > 0 ? a <= MAX / b : b >= MIN / a)
  --   : (b > 0 ? a >= MIN / b : a != MIN && b != MIN && 0 - a <= MAX / (0 - b)))`
  | .mul =>
    let neg (x : Val C Γ .int) : Val C Γ .int := arI .sub rfl rfl zero x
    some (orB (cmpI .eqB rfl rfl a zero) (orB (cmpI .eqB rfl rfl b zero)
      (.ternary (pos a)
        (.ternary (pos b) (cmpI .le rfl rfl a (arI .div rfl rfl max b))
          (cmpI .ge rfl rfl b (arI .div rfl rfl min a)))
        (.ternary (pos b) (cmpI .ge rfl rfl a (arI .div rfl rfl min b))
          (andB (cmpI .neB rfl rfl a min) (andB (cmpI .neB rfl rfl b min)
            (cmpI .le rfl rfl (neg a) (arI .div rfl rfl max (neg b)))))))))
  -- `!(a == MIN && b == -1)`
  | .div => some (notB (andB (cmpI .eqB rfl rfl a min) (cmpI .eqB rfl rfl b one)))
  | _ => none

/-- `a ⊙ b` stays in range at `p`. -/
def range : (op : BinOp) → (p : PrimTy) → Val C Γ p → Val C Γ p → Option (Val C Γ .bool)
  | op, .uint, a, b => rangeU op a b
  | op, .int, a, b => rangeI op a b
  | _, .bool, _, _ => none

/-- `-a` stays in range: `a != MIN` at `int`. -/
def negRange : (p : PrimTy) → Val C Γ p → Option (Val C Γ .bool)
  | .int, a => some (cmpI .neB rfl rfl a (litI minI (by decide)))
  | _, _ => none

/-- `x++` (`x−−`) stays in range on the value `v`. -/
def bumpRange (op : IncDec) : (p : PrimTy) → Val C Γ p → Option (Val C Γ .bool)
  | .uint, v =>
    if op.isIncrement then rangeU .add v (litU 1 (by decide)) else rangeU .sub v (litU 1 (by decide))
  | .int, v =>
    if op.isIncrement then rangeI .add v (litI 1 (by decide)) else rangeI .sub v (litI 1 (by decide))
  | .bool, _ => none

/-- `a == a`: evaluates `a`, and so halts where reading it halts, before the
guards of what is evaluated after it. -/
def touch : (p : PrimTy) → Val C Γ p → Val C Γ .bool
  | .uint, a => cmpU .eqB rfl rfl a a
  | .int, a => cmpI .eqB rfl rfl a a
  | .bool, a => .binop .eqB rfl rfl a a

/-- The default `0` a push appends. -/
def zero : (p : PrimTy) → Val C Γ p
  | .uint => litU 0 (by decide)
  | .int => litI 0 (by decide)
  | .bool => .simple (.bool false)

end Checked

open Checked

/-! ## The guards -/

/-- Whether reading at a storage location may halt (an index out of bounds,
an unset alias). -/
def Loc.mayHalt {Γ : Ctx} : {T : Ty} → Loc C Γ T → Bool
  | _, .root .. => false
  | _, .field .. | _, .index .. => true

/-- Whether evaluating a value may halt, its checked operations in range: a
read (an index out of bounds, an unset alias), `**`, `/`, `%`, a shift,
`addmod`/`mulmod` (by zero).  Over-approximated: it only adds a `touch`. -/
def Val.mayHalt {Γ : Ctx} : {p : PrimTy} → Val C Γ p → Bool
  | _, .simple _ => false
  | _, .read l => l.mayHalt
  | _, .binop op _ _ a b =>
    a.mayHalt || b.mayHalt || [BinOp.pow, .div, .mod, .shl, .shr].contains op
  | _, .unop _ _ _ a => a.mayHalt
  | _, .ternary c a b => c.mayHalt || a.mayHalt || b.mayHalt
  | _, .readMem _ | _, .len .. | _, .mlen .. | _, .modular .. => true

mutual

/-- What a value's checked operations need to stay in range, in the order
they are evaluated; `none` where nothing is checked.  Where the right
operand has a guard and the left may halt, the left is read first
(`touch`): the run halts there before it evaluates the right. -/
def Val.guard {Γ : Ctx} : {p : PrimTy} → Val C Γ p → Option (Val C Γ .bool)
  | _, .simple _ => none
  | _, .read l => l.guard
  -- the right operand of `&&` and `||` only where it is evaluated
  | _, .binop (p := .bool) .and _ _ a b => andO a.guard (b.guard.map fun g => orB (notB a) g)
  | _, .binop (p := .bool) .or _ _ a b => andO a.guard (b.guard.map fun g => orB a g)
  | _, .binop op _ _ a b =>
    let gb := b.guard
    let ga := if gb.isSome && a.mayHalt then andO a.guard (some (touch _ a)) else a.guard
    andO ga (andO gb (if op.isArith then range op _ a b else none))
  | _, .unop op _ _ a => andO a.guard (if op = .neg then negRange _ a else none)
  | _, .ternary c a b => andO c.guard (iteO c a.guard b.guard)
  | _, .readMem l => l.guard
  | _, .len b _ => b.guard
  | _, .mlen b _ => b.guard
  | _, .modular _ a b k => andO a.guard (andO b.guard k.guard)

def SPath.guard {Γ : Ctx} : {T : Ty} → SPath C Γ T → Option (Val C Γ .bool)
  | _, .alias _ => none
  | _, .loc l => l.guard

def Loc.guard {Γ : Ctx} : {T : Ty} → Loc C Γ T → Option (Val C Γ .bool)
  | _, .root .. => none
  | _, .field b _ _ => b.guard
  | _, .index _ b i => andO b.guard i.guard

def MPath.guard {Γ : Ctx} : {T : Ty} → MPath C Γ T → Option (Val C Γ .bool)
  | _, .var .. => none
  | _, .loc l => l.guard

def MLoc.guard {Γ : Ctx} : {T : Ty} → MLoc C Γ T → Option (Val C Γ .bool)
  | _, .field b _ _ => b.guard
  | _, .index _ b i => andO b.guard i.guard

end

def Src.guard {Γ : Ctx} {T : Ty} : Src C Γ T → Option (Val C Γ .bool)
  | .val v => v.guard
  | .copy p _ | .fixedCopy p _ _ => p.guard
  | .copyMem p => p.guard

def ARhs.guard {Γ : Ctx} {R : RefTy} : ARhs C Γ R → Option (Val C Γ .bool)
  | .path p => p.guard
  | .push b _ => b.guard

def MRhs.guard {Γ : Ctx} {R : RefTy} : MRhs C Γ R → Option (Val C Γ .bool)
  | .alias p => p.guard
  | .copy p _ => p.guard
  | .newArr .. => none

def MSrc.guard {Γ : Ctx} {T : Ty} : MSrc C Γ T → Option (Val C Γ .bool)
  | .val v => v.guard
  | .ref p => p.guard

def NewLhs.guard {Γ : Ctx} {R : RefTy} : NewLhs C Γ R → Option (Val C Γ .bool)
  | .store l => l.guard
  | .mem l => l.guard

def Args.guard {Γ : Ctx} : {ps : Ctx} → Args C Γ ps → Option (Val C Γ .bool)
  | _, .nil => none
  | _, .snoc as _ _ e => andO as.guard e.guard
  | _, .snocStorage as _ _ e => andO as.guard e.guard
  | _, .snocMemory as _ _ e => andO as.guard e.guard

/-- The current value at a compound target. -/
def OpLoc.val {Γ : Ctx} {p : PrimTy} : OpLoc C Γ p → Val C Γ p
  | .local i => .simple (.local i)
  | .root r h => .read (.root r h)
  | .field b f h => .read (.field b f h)
  | .index it b i => .read (.index it b (.simple i))
  | .mfield b f h => .readMem (.field b f h)
  | .mindex a b i => .readMem (.index a b (.simple i))

def OpLoc.guard {Γ : Ctx} {p : PrimTy} : OpLoc C Γ p → Option (Val C Γ .bool)
  | .local _ | .root .. => none
  | .field b _ _ | .index _ b _ => b.guard
  | .mfield b _ _ | .mindex _ b _ => b.guard

/-- What a statement's own checked operations need to stay in range, before
it runs (its values are read before its effects); a loop's condition, a
call's arguments; not what the programs it holds evaluate. -/
def Stmt.guard {Γ Γ' : Ctx} : Stmt C Γ Γ' → Option (Val C Γ .bool)
  -- the right-hand side is evaluated before the target (`TRun.assign`)
  | .assign l r => andO r.guard l.guard
  | .rebind _ r => r.guard
  | .assignLocal _ r => r.guard
  | .declLocal _ _ init => init.bind Val.guard
  | .declStorage _ _ init => init.bind ARhs.guard
  | .opAssign op _ _ l r => andO r.guard (andO l.guard (range op _ l.val r))
  | .incDec op _ l => andO l.guard (bumpRange op _ l.val)
  | .assignIncDec _ op _ l _ => andO l.guard (bumpRange op _ l.val)
  | .assignLocalPush _ b => b.guard
  | .push b v _ => andO b.guard (v.bind Src.guard)
  | .pop b => b.guard
  | .transfer r a => andO r.guard a.guard
  | .send _ r a _ => andO r.guard a.guard
  | .declMem _ _ init _ _ => init.bind MRhs.guard
  | .rebindMem _ r => r.guard
  | .assignFromMem l p => andO p.guard l.guard
  | .assignMem l r => andO r.guard l.guard
  | .delete l => l.guard
  | .deleteMem p _ => p.guard
  | .assignNew l _ _ => l.guard
  | .ite c _ _ => c.guard
  | .require c | .assert c => c.guard
  | .revert | .assumeFalse => none
  | .call _ args _ _ => args.guard
  | .tryCall .. => none
  | .loop _ c _ => c.guard
  | .block _ => none
  | .pushOpAssign op _ _ b r => andO r.guard (andO b.guard (range op _ (zero _) r))
  | .pushIncDec (p := p) op _ b => andO b.guard (bumpRange op p (zero p))
  -- the push's source is read after the getter's body, which may change
  -- what it reads: not guarded, it reverts on an overflow as outside
  | .callReceiver _ args _ _ _ => args.guard
  | .callReceiverPush _ args _ _ _ _ => args.guard

/-! ## The transformation -/

/-- `P`, then `s`. -/
def Prog.snocS {Γ Γ₁ : Ctx} : Prog C Γ Γ₁ → Stmt C Γ₁ Γ₁ → Prog C Γ Γ₁
  | .nil, s => .cons s .nil
  | .cons t P, s => .cons t (P.snocS s)

/-- The statement a guard is owed by: `assert(g);` when checking, `if (g) {}
else { assume(false); }` when ignoring. -/
def OFMode.guardStmt {Γ : Ctx} : OFMode → Val C Γ .bool → Stmt C Γ Γ
  | .checking, g => .assert g
  | .ignoring, g => .ite g .nil (.cons .assumeFalse .nil)

/-- `P`, then the guard's statement where a guard is due. -/
def Prog.snocGuard {Γ Γ₁ : Ctx} (o : OFMode) (P : Prog C Γ Γ₁) :
    Option (Val C Γ₁ .bool) → Prog C Γ Γ₁
  | none => P
  | some g => P.snocS (o.guardStmt g)

mutual

/-- A statement with the programs it holds guarded: a loop's condition
guarded again at the end of its body, the source of a deferred push at the
end of its prefix. -/
def Stmt.withOF {Γ Γ' : Ctx} (o : OFMode) : Stmt C Γ Γ' → Stmt C Γ Γ'
  | .ite c thn els => .ite c (thn.withOF o) (els.withOF o)
  | .call f args ret body => .call f args ret (body.withOF o)
  | .tryCall call rets ok err code pnc other =>
    .tryCall call rets (ok.withOF o) (err.withOF o) code (pnc.withOF o) (other.withOF o)
  | .loop a c body =>
    .loop a c ((body.withOF o).snocGuard o ((c.wk (Thin.ofExt body.ext)).guard))
  | .block body => .block (body.withOF o)
  | .callReceiver f args r body op => .callReceiver f args r (body.withOF o) op
  | .callReceiverPush f args r body code value =>
    .callReceiverPush f args r (body.withOF o) ((code.withOF o).snocGuard o value.guard) value
  | s => s

/-- **A program, guarded**: each statement preceded by its guard's
statement (`Stmt.guard`, `OFMode.guardStmt`). -/
def Prog.withOF {Γ Γ' : Ctx} (o : OFMode) : Prog C Γ Γ' → Prog C Γ Γ'
  | .nil => .nil
  | .cons s P =>
    match s.guard with
    | none => .cons (s.withOF o) (P.withOF o)
    | some g => .cons (o.guardStmt g) (.cons (s.withOF o) (P.withOF o))

end

/-- `checked { … }`'s program. -/
abbrev Prog.checkOF {Γ Γ' : Ctx} (P : Prog C Γ Γ') : Prog C Γ Γ' := P.withOF .checking

/-- `ignoringOverflow { … }`'s program. -/
abbrev Prog.ignoreOF {Γ Γ' : Ctx} (P : Prog C Γ Γ') : Prog C Γ Γ' := P.withOF .ignoring

end Solidity
