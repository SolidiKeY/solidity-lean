import Solidity.Calculus.Fml

/-!
# The nodes of a term and of a statement

The sizes `Calculus/TermSize.lean` bounds what a rule emits by (`Tm.size`,
`Stmt.size`), below the rules: a call's summary is used only where its term
is no larger than that bound allows (`CallRet.summary?`,
`Calculus/CallSummary.lean`).  A size counts the nodes of a term or of a
statement, never a type, a name, a literal's digits or a proof.
-/

namespace Solidity

variable {C : Contract}

/-- The nodes of a term. -/
def Tm.size {Γ : Ctx} : {s : Srt} → Tm C Γ s → Nat
  | _, .pvV _ => 1
  | _, .pvP _ => 1
  | _, .pvS _ => 1
  | _, .pvI _ => 1
  | _, .netOf _ a => 1 + a.size
  | _, .app0 _ => 1
  | _, .app1 _ x => 1 + x.size
  | _, .app2 _ x y => 1 + x.size + y.size
  | _, .app3 _ x y z => 1 + x.size + y.size + z.size
  | _, .pvZ _ => 1

/-! ## Sizes of statements -/

section Syntax

variable {Γ : Ctx}

/-- A simple value is one node. -/
def Simple.size {p : PrimTy} (_ : Simple C Γ p) : Nat := 1

mutual

def SPath.size : {T : Ty} → SPath C Γ T → Nat
  | _, .alias _ => 1
  | _, .loc l => 1 + l.size

def Loc.size : {T : Ty} → Loc C Γ T → Nat
  | _, .root _ _ => 1
  | _, .field b _ _ => 1 + b.size
  | _, .index _ b i => 1 + b.size + i.size

def MPath.size : {T : Ty} → MPath C Γ T → Nat
  | _, .var _ _ => 1
  | _, .loc l => 1 + l.size

def MLoc.size : {T : Ty} → MLoc C Γ T → Nat
  | _, .field b _ _ => 1 + b.size
  | _, .index _ b i => 1 + b.size + i.size

def Val.size : {p : PrimTy} → Val C Γ p → Nat
  | _, .simple s => 1 + s.size
  | _, .read l => 1 + l.size
  | _, .binop _ _ _ a b => 1 + a.size + b.size
  | _, .unop _ _ _ a => 1 + a.size
  | _, .ternary c a b => 1 + c.size + a.size + b.size
  | _, .readMem l => 1 + l.size
  | _, .len b _ => 1 + b.size
  | _, .mlen b _ => 1 + b.size
  | _, .modular _ a b k => 1 + a.size + b.size + k.size
  | _, .hash _ b _ => 1 + b.size

end

def Src.size {T : Ty} : Src C Γ T → Nat
  | .val v => 1 + v.size
  | .copy p _ => 1 + p.size
  | .fixedCopy p _ _ => 1 + p.size
  | .copyMem p | .fixedCopyMem p _ => 1 + p.size

def MSrc.size {T : Ty} : MSrc C Γ T → Nat
  | .val v => 1 + v.size
  | .ref p => 1 + p.size

def ARhs.size {R : RefTy} : ARhs C Γ R → Nat
  | .path p => 1 + p.size
  | .push b _ => 1 + b.size

def MRhs.size {R : RefTy} : MRhs C Γ R → Nat
  | .alias p => 1 + p.size
  | .copy p _ => 1 + p.size
  | .newArr n _ => 1 + n.size

def NewLhs.size {R : RefTy} : NewLhs C Γ R → Nat
  | .store l => 1 + l.size
  | .mem l => 1 + l.size

/-- A compound target, as the location it denotes (`OpLoc.set`). -/
def OpLoc.size {p : PrimTy} : OpLoc C Γ p → Nat
  | .local _ => 1
  | .root _ _ => 1
  | .field b _ _ => 1 + b.size
  | .index _ b _ => 3 + b.size
  | .mfield b _ _ => 1 + b.size
  | .mindex _ b _ => 3 + b.size

def Args.size : {ps : Ctx} → Args C Γ ps → Nat
  | _, .nil => 0
  | _, .snoc as _ _ e => as.size + 1 + e.size
  | _, .snocStorage as _ _ e => as.size + 1 + e.size
  | _, .snocMemory as _ _ e => as.size + 1 + e.size

def ExtCall.size (e : ExtCall C Γ) : Nat := 1 + e.addr.size + e.args.length

def ReceiverOp.size {E : Ty} : ReceiverOp C Γ E → Nat
  | .push none _ => 1
  | .push (some v) _ => 1 + v.size
  | .pop => 1

end Syntax

def LoopQ.size : {Γ : Ctx} → LoopQ C Γ → Nat
  | _, .val a => 1 + a.size
  | _, .imp a c => 1 + a.size + c.size
  | _, .all _ _ b => 1 + b.size

def LoopAnn.size {Γ : Ctx} : LoopAnn C Γ → Nat
  | .unwind _ => 1
  | .auto => 1
  | .inv I dec _ qs => 1 + I.size + (match dec with | some d => d.size | none => 0) +
      (qs.map LoopQ.size).sum

mutual

/-- The nodes of a statement: its own, its expressions', its blocks'. -/
def Stmt.size : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Nat
  | _, _, .assign l r => 1 + l.size + r.size
  | _, _, .rebind _ r => 1 + r.size
  | _, _, .assignLocal _ r => 1 + r.size
  | _, _, .declLocal _ _ init => 1 + (match init with | some e => e.size | none => 0)
  | _, _, .declStorage _ _ init => 1 + (match init with | some r => r.size | none => 0)
  | _, _, .opAssign _ _ _ l r => 1 + l.size + r.size
  | _, _, .incDec _ _ l => 1 + l.size
  | _, _, .assignIncDec _ _ _ l _ => 1 + l.size
  | _, _, .assignLocalPush _ b => 1 + b.size
  | _, _, .push b v _ => 1 + b.size + (match v with | some e => e.size | none => 0)
  | _, _, .pop b => 1 + b.size
  | _, _, .transfer r a => 1 + r.size + a.size
  | _, _, .send _ r a _ => 1 + r.size + a.size
  | _, _, .declMem _ _ init _ _ => 1 + (match init with | some r => r.size | none => 0)
  | _, _, .rebindMem _ r => 1 + r.size
  | _, _, .assignFromMem l p => 1 + l.size + p.size
  | _, _, .assignMem l r => 1 + l.size + r.size
  | _, _, .delete l => 1 + l.size
  | _, _, .deleteMem p _ => 1 + p.size
  | _, _, .assignNew l n _ => 1 + l.size + n.size
  | _, _, .ite c thn els => 1 + c.size + thn.size + els.size
  | _, _, .require c => 1 + c.size
  | _, _, .assert c => 1 + c.size
  | _, _, .revert => 1
  | _, _, .assumeFalse => 1
  | _, _, .call _ args _ body => 1 + args.size + body.size
  | _, _, .tryCall call _ ok err _ pnc other sargs sbody _ =>
    1 + call.size + ok.size + err.size + pnc.size + other.size + sargs.size + sbody.size
  | _, _, .loop a c body => 1 + a.size + c.size + body.size
  | _, _, .block body => 1 + body.size
  | _, _, .revertData _ => 1
  | _, _, .catchData call _ sargs sbody _ _ _ body =>
    1 + call.size + sargs.size + sbody.size + body.size
  | _, _, .pushOpAssign _ _ _ b r => 1 + b.size + r.size
  | _, _, .pushIncDec _ _ b => 1 + b.size
  | _, _, .callReceiver _ args _ body op => 1 + args.size + body.size + op.size
  | _, _, .callReceiverPush _ args _ body code value =>
    1 + args.size + body.size + code.size + value.size
  -- the body is read when the call is unfolded
  | _, _, .callRec _ _ args _ _ => 1 + args.size

def Prog.size : {Γ Γ' : Ctx} → Prog C Γ Γ' → Nat
  | _, _, .nil => 0
  | _, _, .cons s P => s.size + P.size

end

end Solidity
