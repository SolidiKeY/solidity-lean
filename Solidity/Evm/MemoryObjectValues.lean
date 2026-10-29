import Solidity.Evm.MemoryObjectPaths
import Solidity.Evm.MemoryObjectExpr

/-! Typed value certificates over both array layouts. -/
namespace Solidity.Evm.Memory.Objects
open Semantics
variable {C : Contract}

inductive ValFrag (b : Nat) {Γ : Ctx} (F : Frag Γ) : {p : PrimTy} → Val C Γ p → List Instr → Prop where
  | core {p : PrimTy} (e : Val C Γ p) (he : valIn F e = true) :
      ValFrag b F e (Evm.compileVal b e)
  | read {A : RefTy} {p : PrimTy} (a : ArrTy A (.prim p))
      (src : MPath C Γ (.ref A)) (pointer : List Instr) (hp : PtrFrag b F src pointer)
      (i : Val C Γ .uint) (hi : valIn F i = true) :
      ValFrag b F (.readMem (.index a src i)) (pointer ++ Evm.compileVal b i ++ readCode a)
  | field {s f : Name} {p : PrimTy} (src : MPath C Γ (.ref (.struct s)))
      (hf : C.fieldType s f = some (.prim p)) (pointer : List Instr) (hp : PtrFrag b F src pointer) :
      ValFrag b F (.readMem (.field src f hf)) (pointer ++ readFieldCode (fieldOffset (structDef s) f))
  | length {E : Ty} (src : MPath C Γ (.ref (.array E)))
      (pointer : List Instr) (hp : PtrFrag b F src pointer) :
      ValFrag b F (.mlen src rfl) (pointer ++ [.mloadAt])
  | binary {p : PrimTy} (op : BinOp) (hop : binInFrag op p = true) (hacc : op.accepts p = true)
      (x y : Val C Γ p) (left right : List Instr)
      (hx : ValFrag b F x left) (hy : ValFrag b F y right) :
      ValFrag b F (.binop op hacc rfl x y) (binaryCode p op left right)
  | unary {p : PrimTy} (op : UnOp) (hop : unInFrag op p = true) (hacc : op.accepts p = true)
      (x : Val C Γ p) (code : List Instr) (hx : ValFrag b F x code) :
      ValFrag b F (.unop op hacc rfl x) (unaryCode op code)
  | conditional {p : PrimTy} (c : Val C Γ .bool) (x y : Val C Γ p) (cond left right : List Instr)
      (hc : ValFrag b F c cond) (hx : ValFrag b F x left) (hy : ValFrag b F y right) :
      ValFrag b F (.ternary c x y) (conditionalCode cond left right)

structure CompiledVal (b : Nat) {Γ : Ctx} (F : Frag Γ) {p : PrimTy} (e : Val C Γ p) where
  code : List Instr
  cert : ValFrag b F e code

def compileVal (b : Nat) {Γ : Ctx} (F : Frag Γ) :
    {p : PrimTy} → (e : Val C Γ p) → Option (CompiledVal b F e)
  | _, .readMem (.index a src i) => do
    let pointer ← compilePtr b F src
    if hi : valIn F i = true then pure ⟨_, .read a src pointer.code pointer.cert i hi⟩ else none
  | _, .readMem (.field src _ hf) => do
    let pointer ← compilePtr b F src
    pure ⟨_, .field src hf pointer.code pointer.cert⟩
  | _, @Solidity.Val.mlen _ _ _ _ src rfl => do
    let pointer ← compilePtr b F src
    pure ⟨_, .length src pointer.code pointer.cert⟩
  | _, @Solidity.Val.binop _ _ p _ op hacc rfl x y =>
    if hop : binInFrag op p = true then do
      let left ← compileVal b F x
      let right ← compileVal b F y
      pure ⟨_, .binary op hop hacc x y left.code right.code left.cert right.cert⟩
    else none
  | _, @Solidity.Val.unop _ _ p _ op hacc rfl x =>
    if hop : unInFrag op p = true then do
      let operand ← compileVal b F x
      pure ⟨_, .unary op hop hacc x operand.code operand.cert⟩
    else none
  | _, .ternary c x y => do
    let cond ← compileVal b F c
    let left ← compileVal b F x
    let right ← compileVal b F y
    pure ⟨_, .conditional c x y cond.code left.code right.code cond.cert left.cert right.cert⟩
  | _, e => if he : valIn F e = true then some ⟨_, .core e he⟩ else none

theorem ValFrag.correct {b L frame : Nat} {Γ : Ctx} {F : Frag Γ} {p : PrimTy}
    {e : Val C Γ p} {code : List Instr} (he : ValFrag b F e code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} (h : StateRepr L b frame F σ base m) :
    ValOutT p (e.evalT σ) (run code m) m := by
  induction he generalizing m with
  | core e he => exact val_sim e h.core he
  | read a src pointer hp i hi => exact hp.readPrimitive h a i hi
  | field src hf pointer hp => exact hp.readField h hf
  | length src pointer hp => exact hp.length h
  | binary op hop hacc x y left right hx hy ihx ihy =>
    exact binaryValue_correct op hop hacc x y left right (fun h' => ihx h') (fun h' => ihy h') h
  | unary op hop hacc x code hx ihx =>
    exact unaryValue_correct op hop hacc x code (fun h' => ihx h') h
  | conditional c x y cond left right hc hx hy ihc ihx ihy =>
    exact conditionalValue_correct c x y cond left right (fun h' => ihc h')
      (fun h' => ihx h') (fun h' => ihy h') h

end Solidity.Evm.Memory.Objects
