import Solidity.Evm.MemoryLocals
import Solidity.Evm.MemoryStructSource
import Solidity.Evm.MemoryStructDefault
import Solidity.Evm.MemoryStructCopySource
import Solidity.Evm.MemoryPaths
import Solidity.Evm.MemoryRefWrite
import Solidity.Evm.MemoryRefDelete
import Solidity.Evm.MemoryExpr
import Solidity.Evm.MemoryStatements
import Solidity.Evm.MemoryDelete
import Solidity.Evm.MemoryCompound
import Solidity.Evm.MemoryCapture
import Solidity.Evm.MemoryScope

/-!
# A checked compiler path for primitive arrays and structs

The compiler consumes the existing scoped Solidity syntax. Its result carries
a fragment certificate; the certificate is proof data, erased at runtime.
This path composes core and memory values with the existing checked operators,
short-circuiting and conditional expressions. Local/array/storage assignments,
declarations, deletion, numeric compound updates, standalone and captured
increments/decrements, pointer aliasing, require and
revert preserve the memory relation. Primitive struct fields read and write
through typed local pointers; all memory aliases use the same copy operation.
Struct declarations with only primitive members allocate their default object;
the ordinary source elaborator builds positional/named literals from them.
Primitive allocation grows the address map and carries an explicit reached
capacity premise. Blocks and branches retain heap growth across scope exit;
the reserved frame covers temporary locals in either branch.
-/
namespace Solidity.Evm.Memory

variable {C : Contract}

mutual
private def nestedFramesStmt {Γ Δ : Ctx} : Stmt C Γ Δ → Nat
  | .block body => frameNeedProg body
  | .ite _ thn els => max (frameNeedProg thn) (frameNeedProg els)
  | .assign .. | .rebind .. | .assignLocal .. | .declLocal ..
  | .declStorage .. | .opAssign .. | .incDec .. | .assignIncDec ..
  | .assignLocalPush .. | .push .. | .pop .. | .transfer ..
  | .send .. | .declMem .. | .rebindMem .. | .assignFromMem ..
  | .assignMem .. | .delete .. | .deleteMem .. | .assignNew ..
  | .require .. | .assert .. | .revert | .assumeFalse
  | .call .. | .tryCall .. | .loop .. | .pushOpAssign ..
  | .pushIncDec .. | .callReceiver .. | .callReceiverPush .. | .callRec ..
  | .revertData .. | .catchData .. => 0

/-- Reserve every intermediate local context, not only the final one. -/
def frameNeedProg {Γ Δ : Ctx} : Prog C Γ Δ → Nat
  | .nil => Γ.length
  | .cons (Γ₁ := Δ) s P =>
    max (max Γ.length (max Δ.length (nestedFramesStmt s))) (frameNeedProg P)
end

/-- Maximum context length used by a statement, including scoped bodies. -/
def frameNeedStmt {Γ Δ : Ctx} (s : Stmt C Γ Δ) : Nat :=
  max Γ.length (max Δ.length (nestedFramesStmt s))

theorem frameNeedStmt_end {Γ Δ : Ctx} (s : Stmt C Γ Δ) : Δ.length ≤ frameNeedStmt s := by
  unfold frameNeedStmt
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- Value leaves supported by the memory compiler. -/
inductive ValFrag (b : Nat) {Γ : Ctx} (F : Frag Γ) : {p : PrimTy} → Val C Γ p → List Instr → Prop where
  | core {p : PrimTy} (e : Val C Γ p) (he : valIn F e = true) :
      ValFrag b F e (Evm.compileVal b e)
  | read {p : PrimTy} (src : Idx Γ (.mem (.array (.prim p)))) (hm)
      (i : Val C Γ .uint) (index : List Instr) (hi : ValFrag b F i index) :
      ValFrag b F (.readMem (.index .dyn (.var src hm) i)) (readLocalValueCode b src index)
  | length {p : PrimTy} (src : Idx Γ (.mem (.array (.prim p)))) (hm) :
      ValFrag b F (.mlen (.var src hm) rfl) (lengthLocalCode b src)
  | field {s f : Name} {p : PrimTy} (src : Idx Γ (.mem (.struct s))) (hm)
      (hf : C.fieldType s f = some (.prim p)) :
      ValFrag b F (.readMem (.field (.var src hm) f hf)) (readLocalFieldCode b src f)
  | pathRead {p : PrimTy} (src : MPath C Γ (.ref (.array (.prim p)))) (pointer : List Instr)
      (hp : PtrFrag b src pointer) (i : Val C Γ .uint) (index : List Instr)
      (hi : ValFrag b F i index) :
      ValFrag b F (.readMem (.index .dyn src i)) (pointer ++ index ++ readArrayStackCode)
  | pathLength {p : PrimTy} (src : MPath C Γ (.ref (.array (.prim p)))) (pointer : List Instr)
      (hp : PtrFrag b src pointer) :
      ValFrag b F (.mlen src rfl) (pointer ++ [.mloadAt])
  | pathField {s f : Name} {p : PrimTy} (src : MPath C Γ (.ref (.struct s)))
      (hf : C.fieldType s f = some (.prim p)) (pointer : List Instr) (hp : PtrFrag b src pointer) :
      ValFrag b F (.readMem (.field src f hf))
        (pointer ++ readFieldCode (fieldOffset (Semantics.structDef s) f))
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
  | _, .readMem (.index .dyn (.var src hm) i) =>
    do
      let index ← compileVal b F i
      pure ⟨_, .read src hm i index.code index.cert⟩
  | _, @Solidity.Val.mlen _ _ _ (.prim _) (.var src hm) rfl => some ⟨_, .length src hm⟩
  | _, .readMem (.field (.var src hm) _ hf) => some ⟨_, .field src hm hf⟩
  | _, .readMem (.index .dyn src i) => do
    let pointer ← compilePtr b src
    let index ← compileVal b F i
    pure ⟨_, .pathRead src pointer.code pointer.cert i index.code index.cert⟩
  | _, @Solidity.Val.mlen _ _ _ (.prim _) src rfl => do
    let pointer ← compilePtr b src
    pure ⟨_, .pathLength src pointer.code pointer.cert⟩
  | _, .readMem (.field src _ hf) => do
    let pointer ← compilePtr b src
    pure ⟨_, .pathField src hf pointer.code pointer.cert⟩
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

/-- No value compiler result is trusted: its clause proves the typed result. -/
theorem ValFrag.correct {b L frame : Nat} {Γ : Ctx} {F : Frag Γ} {p : PrimTy}
    {e : Val C Γ p} {code : List Instr} (he : ValFrag b F e code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} (h : StateRepr L b frame F σ base m) :
    ValOutT p (e.evalT σ) (run code m) m := by
  induction he generalizing m with
  | core e he => exact val_sim e h.core he
  | read src hm i index hi ih => exact readLocalValue_correct h src i index (fun h' => ih h')
  | length src hm => exact lengthLocal_correct h src
  | field src hm hf => exact readLocalField_correct h src hm hf
  | pathRead src pointer hp i index hi ih => exact hp.readArray h i index (fun h' => ih h')
  | pathLength src pointer hp => exact hp.length h
  | pathField src hf pointer hp => exact hp.readPrimitive h hf
  | binary op hop hacc x y left right hx hy ihx ihy =>
    exact binaryValue_correct op hop hacc x y left right (fun h' => ihx h') (fun h' => ihy h') h
  | unary op hop hacc x code hx ihx =>
    exact unaryValue_correct op hop hacc x code (fun h' => ihx h') h
  | conditional c x y cond left right hc hx hy ihc ihx ihy =>
    exact conditionalValue_correct c x y cond left right (fun h' => ihc h')
      (fun h' => ihx h') (fun h' => ihy h') h

mutual
/-- Supported scoped statements and their emitted instructions. -/
inductive StmtFrag (b : Nat) : {Γ Δ : Ctx} → Frag Γ → Frag Δ → Stmt C Γ Δ → List Instr → Prop where
  | assign {Γ : Ctx} (F : Frag Γ) {p : PrimTy} (dst : Idx Γ (.val p))
      (e : Val C Γ p) (code : List Instr) (he : ValFrag b F e code) :
      StmtFrag b F F (.assignLocal dst e) (code ++ [.mstore (cellOf b dst)])
  | declare {Γ : Ctx} (F : Frag Γ) {p : PrimTy} (x : Var)
      (e : Val C Γ p) (code : List Instr) (he : ValFrag b F e code) :
      StmtFrag b F (F.push (.val p) .ok) (.declLocal p x (some e))
        (code ++ [.mstore (cell (b + Γ.length))])
  | declareDefault {Γ : Ctx} (F : Frag Γ) (p : PrimTy) (x : Var) :
      StmtFrag b F (F.push (.val p) .ok) (.declLocal p x none)
        [.push w[0], .mstore (cell (b + Γ.length))]
  | rebind {Γ : Ctx} (F : Frag Γ) {R : RefTy}
      (dst src : Idx Γ (.mem R)) (hm) :
      StmtFrag b F F (.rebindMem dst (.alias (.var src hm))) (aliasLocalCode b dst src)
  | declareAlias {Γ : Ctx} (F : Frag Γ) {R : RefTy} (x : Var)
      (src : Idx Γ (.mem R)) (hm) :
      StmtFrag b F (F.push (.mem R) .ok)
        (.declMem R x (some (.alias (.var src hm))) rfl hm)
        (declareAliasCode b src)
  | rebindPath {Γ : Ctx} (F : Frag Γ) {R : RefTy} (dst : Idx Γ (.mem R))
      (src : MPath C Γ (.ref R)) (code : List Instr) (hp : PtrFrag b src code) :
      StmtFrag b F F (.rebindMem dst (.alias src)) (code ++ [.mstore (cellOf b dst)])
  | declarePathAlias {Γ : Ctx} (F : Frag Γ) {R : RefTy} (x : Var)
      (src : MPath C Γ (.ref R)) (hm) (code : List Instr) (hp : PtrFrag b src code) :
      StmtFrag b F (F.push (.mem R) .ok) (.declMem R x (some (.alias src)) rfl hm)
        (code ++ [.mstore (cell (b + Γ.length))])
  | allocate {Γ : Ctx} (F : Frag Γ) (p : PrimTy) (x : Var)
      (n : Simple C Γ .uint) (hb : 0 < b) (hn : simpleIn n = true) :
      StmtFrag b F (F.push (.mem (.array (.prim p))) .ok)
        (.declMem (.array (.prim p)) x (some (.newArr n rfl)) rfl rfl)
        (declareNewCode b n)
  | defaultArray {Γ : Ctx} (F : Frag Γ) (p : PrimTy) (x : Var) (code : List Instr)
      (hs : StmtFrag b F (F.push (.mem (.array (.prim p))) .ok)
        (.declMem (.array (.prim p)) x (some (.newArr (.lit 0 rfl) rfl)) rfl rfl) code) :
      StmtFrag b F (F.push (.mem (.array (.prim p))) .ok)
        (.declMem (.array (.prim p)) x none rfl rfl) code
  | allocateStruct {Γ : Ctx} (F : Frag Γ) (s : Name) (x : Var)
      (hd : (Ty.ref (.struct s)).defaultOkS = true) (hm : (Ty.ref (.struct s)).mapFree = true)
      (hb : 0 < b) (hp : primitiveMembers (Semantics.structDef s) = true) :
      StmtFrag b F (F.push (.mem (.struct s)) .ok)
        (.declMem (.struct s) x none hd hm) (declareStructCode (Γ := Γ) b s)
  | copyStruct {Γ : Ctx} (F : Frag Γ) (s : Name) (x : Var) (root : Name)
      (hr : C.rootType root = some (.ref (.struct s)))
      (hm : (Ty.ref (.struct s)).mapFree = true)
      (hb : 0 < b) (hp : primitiveMembers (Semantics.structDef s) = true)
      (loads : List Instr) (plan : CopyLoads b F root hr (Semantics.structDef s) loads) :
      StmtFrag b F (F.push (.mem (.struct s)) .ok)
        (.declMem (.struct s) x (some (.copy (.loc (.root root hr)) hm)) rfl hm)
        (declareCopyStructCode (Γ := Γ) b s loads)
  | rebindCopyStruct {Γ : Ctx} (F : Frag Γ) (s : Name)
      (dst : Idx Γ (.mem (.struct s))) (root : Name)
      (hr : C.rootType root = some (.ref (.struct s))) (hm : (Ty.ref (.struct s)).mapFree = true)
      (hb : 0 < b) (hp : primitiveMembers (Semantics.structDef s) = true)
      (loads : List Instr) (plan : CopyLoads b F root hr (Semantics.structDef s) loads) :
      StmtFrag b F F (.rebindMem dst (.copy (.loc (.root root hr)) hm))
        (rebindCopyStructCode b dst loads)
  | reallocate {Γ : Ctx} (F : Frag Γ) (p : PrimTy)
      (dst : Idx Γ (.mem (.array (.prim p)))) (n : Simple C Γ .uint)
      (hb : 0 < b) (hn : simpleIn n = true) :
      StmtFrag b F F (.rebindMem dst (.newArr n rfl)) (rebindNewCode b dst n)
  | write {Γ : Ctx} (F : Frag Γ) {p : PrimTy}
      (dst : Idx Γ (.mem (.array (.prim p)))) (hm) (i : Val C Γ .uint) (v : Val C Γ p)
      (index value : List Instr) (hi : ValFrag b F i index) (hv : ValFrag b F v value) :
      StmtFrag b F F (.assignMem (.index .dyn (.var dst hm) i) (.val v))
        (writeLocalValueCode b dst index value)
  | writeField {Γ : Ctx} (F : Frag Γ) {s f : Name} {p : PrimTy}
      (dst : Idx Γ (.mem (.struct s))) (hm) (hf : C.fieldType s f = some (.prim p))
      (v : Val C Γ p) (value : List Instr) (hv : ValFrag b F v value) :
      StmtFrag b F F (.assignMem (.field (.var dst hm) f hf) (.val v))
        (writeLocalFieldCode b dst f value)
  | writePathArray {Γ : Ctx} (F : Frag Γ) {p : PrimTy}
      (src : MPath C Γ (.ref (.array (.prim p)))) (pointer : List Instr) (hp : PtrFrag b src pointer)
      (i : Val C Γ .uint) (v : Val C Γ p) (index value : List Instr)
      (hi : ValFrag b F i index) (hv : ValFrag b F v value) :
      StmtFrag b F F (.assignMem (.index .dyn src i) (.val v))
        (value ++ pointer ++ index ++ writeArrayStackCode)
  | writePathField {Γ : Ctx} (F : Frag Γ) {s f : Name} {p : PrimTy}
      (src : MPath C Γ (.ref (.struct s))) (pointer : List Instr) (hp : PtrFrag b src pointer)
      (hf : C.fieldType s f = some (.prim p)) (v : Val C Γ p) (value : List Instr)
      (hv : ValFrag b F v value) :
      StmtFrag b F F (.assignMem (.field src f hf) (.val v))
        (value ++ pointer ++ writeFieldCode (fieldOffset (Semantics.structDef s) f))
  | writeReference {Γ : Ctx} (F : Frag Γ) {s f : Name} {R : RefTy}
      (dst : MPath C Γ (.ref (.struct s))) (src : MPath C Γ (.ref R))
      (hf : C.fieldType s f = some (.ref R)) (pointer value : List Instr)
      (hd : PtrFrag b dst pointer) (hs : PtrFrag b src value) :
      StmtFrag b F F (.assignMem (.field dst f hf) (.ref src))
        (value ++ pointer ++ writeFieldCode (fieldOffset (Semantics.structDef s) f))
  | deleteElement {Γ : Ctx} (F : Frag Γ) {p : PrimTy}
      (dst : Idx Γ (.mem (.array (.prim p)))) (hm) (i : Val C Γ .uint)
      (index : List Instr) (hi : ValFrag b F i index) :
      StmtFrag b F F (.deleteMem (.loc (.index .dyn (.var dst hm) i)) rfl)
        (deleteLocalCode b dst index)
  | deletePathElement {Γ : Ctx} (F : Frag Γ) {p : PrimTy}
      (src : MPath C Γ (.ref (.array (.prim p)))) (i : Val C Γ .uint) (code : List Instr)
      (hs : StmtFrag b F F (.assignMem (.index .dyn src i) (.val (deleteDefaultValue p))) code) :
      StmtFrag b F F (.deleteMem (.loc (.index .dyn src i)) rfl) code
  | deleteArray {Γ : Ctx} (F : Frag Γ) {p : PrimTy}
      (dst : Idx Γ (.mem (.array (.prim p)))) (code : List Instr)
      (hs : StmtFrag b F F (.rebindMem dst (.newArr (.lit 0 rfl) rfl)) code) :
      StmtFrag b F F (.deleteMem (.var dst rfl) rfl) code
  | deleteStruct {Γ : Ctx} (F : Frag Γ) {s : Name}
      (dst : Idx Γ (.mem (.struct s))) (hd : (Ty.ref (.struct s)).defaultOkS = true)
      (hm : (Ty.ref (.struct s)).mapFree = true) (hb : 0 < b)
      (hp : primitiveMembers (Semantics.structDef s) = true) :
      StmtFrag b F F (.deleteMem (.var dst hm) hd) (deleteStructCode b dst)
  | deleteArrayField {Γ : Ctx} (F : Frag Γ) {s f : Name} {p : PrimTy}
      (src : MPath C Γ (.ref (.struct s))) (hf : C.fieldType s f = some (.ref (.array (.prim p))))
      (pointer : List Instr) (hs : PtrFrag b src pointer) (hb : 0 < b) :
      StmtFrag b F F (.deleteMem (.loc (.field src f hf)) rfl)
        (clearReferenceCode pointer ([.push w[0]] ++ allocateArrayCode)
          (fieldOffset (Semantics.structDef s) f))
  | deleteStructField {Γ : Ctx} (F : Frag Γ) {s t f : Name}
      (src : MPath C Γ (.ref (.struct s))) (hf : C.fieldType s f = some (.ref (.struct t)))
      (hd : (Ty.ref (.struct t)).defaultOkS = true) (hm : (Ty.ref (.struct t)).mapFree = true)
      (pointer : List Instr) (hs : PtrFrag b src pointer) (hb : 0 < b)
      (hp : primitiveMembers (Semantics.structDef t) = true) :
      StmtFrag b F F (.deleteMem (.loc (.field src f hf)) hd)
        (clearReferenceCode pointer (allocateStructCode (structAllocationSize t))
          (fieldOffset (Semantics.structDef s) f))
  | deleteField {Γ : Ctx} (F : Frag Γ) {s f : Name} {p : PrimTy}
      (src : MPath C Γ (.struct s)) (hf : C.fieldType s f = some (.prim p)) (code : List Instr)
      (hs : StmtFrag b F F (.assignMem (.field src f hf) (.val (deleteDefaultValue p))) code) :
      StmtFrag b F F (.deleteMem (.loc (.field src f hf)) rfl) code
  | compoundMemory {Γ : Ctx} (F : Frag Γ) {p : PrimTy} {R : RefTy}
      (op : BinOp) (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
      (a : ArrTy R (.prim p)) (src : MPath C Γ (.ref R)) (i : Simple C Γ .uint)
      (r : Val C Γ p) (code : List Instr)
      (hs : StmtFrag b F F (.assignMem (.index a src (.simple i))
        (.val (compoundValue op hop hp (.readMem (.index a src (.simple i))) r))) code) :
      StmtFrag b F F (.opAssign op hop hp (.mindex a src i) r) code
  | compoundLocal {Γ : Ctx} (F : Frag Γ) {p : PrimTy}
      (op : BinOp) (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
      (dst : Idx Γ (.val p)) (r : Val C Γ p) (code : List Instr)
      (hs : StmtFrag b F F (.assignLocal dst
        (compoundValue op hop hp (.simple (.local dst)) r)) code) :
      StmtFrag b F F (.opAssign op hop hp (.local dst) r) code
  | compoundField {Γ : Ctx} (F : Frag Γ) {p : PrimTy} {s : Name}
      (op : BinOp) (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
      (src : MPath C Γ (.struct s)) (f : Name) (hf : C.fieldType s f = some (.prim p))
      (r : Val C Γ p) (code : List Instr)
      (hs : StmtFrag b F F (.assignMem (.field src f hf)
        (.val (compoundValue op hop hp (.readMem (.field src f hf)) r))) code) :
      StmtFrag b F F (.opAssign op hop hp (.mfield src f hf) r) code
  | incrementMemory {Γ : Ctx} (F : Frag Γ) {p : PrimTy} {R : RefTy}
      (op : IncDec) (hp : p.isNumeric = true) (a : ArrTy R (.prim p))
      (src : MPath C Γ (.ref R)) (i : Simple C Γ .uint) (code : List Instr)
      (hs : StmtFrag b F F (.opAssign op.binOp (increment_compound op) hp
        (.mindex a src i) (incrementOne hp)) code) :
      StmtFrag b F F (.incDec op hp (.mindex a src i)) code
  | incrementLocal {Γ : Ctx} (F : Frag Γ) {p : PrimTy}
      (op : IncDec) (hp : p.isNumeric = true) (dst : Idx Γ (.val p)) (code : List Instr)
      (hs : StmtFrag b F F (.opAssign op.binOp (increment_compound op) hp
        (.local dst) (incrementOne hp)) code) :
      StmtFrag b F F (.incDec op hp (.local dst)) code
  | incrementField {Γ : Ctx} (F : Frag Γ) {p : PrimTy} {s : Name}
      (op : IncDec) (hp : p.isNumeric = true) (src : MPath C Γ (.struct s))
      (f : Name) (hf : C.fieldType s f = some (.prim p)) (code : List Instr)
      (hs : StmtFrag b F F (.opAssign op.binOp (increment_compound op) hp
        (.mfield src f hf) (incrementOne hp)) code) :
      StmtFrag b F F (.incDec op hp (.mfield src f hf)) code
  | captureMemory {Γ : Ctx} (F : Frag Γ) {p : PrimTy} {R : RefTy}
      (dst : Idx Γ (.val p)) (op : IncDec) (hp : p.isNumeric = true)
      (a : ArrTy R (.prim p)) (src : MPath C Γ (.ref R)) (i : Simple C Γ .uint)
      (hrecv : (OpLoc.mindex a src i).recvSimple = true) (value step : List Instr)
      (hv : ValFrag b F (bumpResultValue op hp (.readMem (.index a src (.simple i)))) value)
      (hs : StmtFrag b F F (.incDec op hp (.mindex a src i)) step) :
      StmtFrag b F F (.assignIncDec dst op hp (.mindex a src i) hrecv)
        (value ++ step ++ [.mstore (cellOf b dst)])
  | captureLocal {Γ : Ctx} (F : Frag Γ) {p : PrimTy}
      (dst : Idx Γ (.val p)) (op : IncDec) (hp : p.isNumeric = true)
      (src : Idx Γ (.val p)) (hrecv : (OpLoc.local (C := C) src).recvSimple = true)
      (value step : List Instr)
      (hv : ValFrag (C := C) b F (bumpResultValue op hp (.simple (.local src))) value)
      (hs : StmtFrag b F F (.incDec op hp (.local src)) step) :
      StmtFrag b F F (.assignIncDec dst op hp (.local src) hrecv)
        (value ++ step ++ [.mstore (cellOf b dst)])
  | captureField {Γ : Ctx} (F : Frag Γ) {p : PrimTy} {s : Name}
      (dst : Idx Γ (.val p)) (op : IncDec) (hp : p.isNumeric = true)
      (src : MPath C Γ (.struct s)) (f : Name) (hf : C.fieldType s f = some (.prim p))
      (hrecv : (OpLoc.mfield src f hf).recvSimple = true) (value step : List Instr)
      (hv : ValFrag b F (bumpResultValue op hp (.readMem (.field src f hf))) value)
      (hs : StmtFrag b F F (.incDec op hp (.mfield src f hf)) step) :
      StmtFrag b F F (.assignIncDec dst op hp (.mfield src f hf) hrecv)
        (value ++ step ++ [.mstore (cellOf b dst)])
  | storageWrite {Γ : Ctx} (F : Frag Γ) {p : PrimTy} (l : Loc C Γ (.prim p))
      (v : Val C Γ p) (code : List Instr) (hl : locIn F false l = true) (hv : ValFrag b F v code) :
      StmtFrag b F F (.assign l (.val v)) (storageAssignCode b l code)
  | require {Γ : Ctx} (F : Frag Γ) (c : Val C Γ .bool) (code : List Instr) (hc : ValFrag b F c code) :
      StmtFrag b F F (.require c) (code ++ assertTop)
  | revert {Γ : Ctx} (F : Frag Γ) : StmtFrag b F F .revert [.revert]
  | block {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ} (body : Prog C Γ Δ)
      (code : List Instr) (hp : ProgFrag b F G body code) :
      StmtFrag b F (G.restrict Γ) (.block body) code
  | ite {Γ Δ Ξ : Ctx} {F : Frag Γ} {G : Frag Δ} {K : Frag Ξ}
      (c : Val C Γ .bool) (thn : Prog C Γ Δ) (els : Prog C Γ Ξ)
      (cond left right : List Instr) (hc : ValFrag b F c cond)
      (ht : ProgFrag b F G thn left) (he : ProgFrag b F K els right) :
      StmtFrag b F ((G.restrict Γ).meet (K.restrict Γ)) (.ite c thn els)
        (conditionalCode cond left right)

inductive ProgFrag (b : Nat) : {Γ Δ : Ctx} → Frag Γ → Frag Δ → Prog C Γ Δ → List Instr → Prop where
  | nil {Γ : Ctx} (F : Frag Γ) : ProgFrag b F F .nil []
  | cons {Γ Δ Ξ : Ctx} {F : Frag Γ} {G : Frag Δ} {K : Frag Ξ}
      {s : Stmt C Γ Δ} {P : Prog C Δ Ξ} {head tail : List Instr}
      (hs : StmtFrag b F G s head) (hp : ProgFrag b G K P tail) :
      ProgFrag b F K (.cons s P) (head ++ tail)

end

structure CompiledStmt (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (s : Stmt C Γ Δ) where
  frag : Frag Δ
  code : List Instr
  cert : StmtFrag b F frag s code

structure CompiledProg (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) where
  frag : Frag Δ
  code : List Instr
  cert : ProgFrag b F frag P code

/-- The standalone bump certificate is shared by captured and discarded results. -/
def compileBump (b : Nat) {Γ : Ctx} (F : Frag Γ) {p : PrimTy}
    (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    Option {code : List Instr // StmtFrag b F F (.incDec op hp l) code} :=
  match l with
  | .mindex .dyn (.var dst hm) i => do
    let one := incrementOne hp
    let valueExpr := compoundValue op.binOp (increment_compound op) hp
      (.readMem (.index .dyn (.var dst hm) (.simple i))) one
    let index ← compileVal b F (.simple i)
    let value ← compileVal b F valueExpr
    pure ⟨_, .incrementMemory F op hp .dyn (.var dst hm) i _
      (.compoundMemory F op.binOp (increment_compound op) hp .dyn (.var dst hm) i one _
        (.write F dst hm (.simple i) valueExpr index.code value.code index.cert value.cert))⟩
  | .mfield (.var dst hm) f hf => do
    let one := incrementOne hp
    let valueExpr := compoundValue op.binOp (increment_compound op) hp
      (.readMem (.field (.var dst hm) f hf)) one
    let value ← compileVal b F valueExpr
    pure ⟨_, .incrementField F op hp (.var dst hm) f hf _
      (.compoundField F op.binOp (increment_compound op) hp (.var dst hm) f hf one _
        (.writeField F dst hm hf valueExpr value.code value.cert))⟩
  | .mindex .dyn src i => do
    let pointer ← compilePtr b src
    let one := incrementOne hp
    let valueExpr := compoundValue op.binOp (increment_compound op) hp
      (.readMem (.index .dyn src (.simple i))) one
    let index ← compileVal b F (.simple i)
    let value ← compileVal b F valueExpr
    pure ⟨_, .incrementMemory F op hp .dyn src i _
      (.compoundMemory F op.binOp (increment_compound op) hp .dyn src i one _
        (.writePathArray F src pointer.code pointer.cert (.simple i) valueExpr
          index.code value.code index.cert value.cert))⟩
  | .mfield src f hf => do
    let pointer ← compilePtr b src
    let one := incrementOne hp
    let valueExpr := compoundValue op.binOp (increment_compound op) hp (.readMem (.field src f hf)) one
    let value ← compileVal b F valueExpr
    pure ⟨_, .incrementField F op hp src f hf _
      (.compoundField F op.binOp (increment_compound op) hp src f hf one _
        (.writePathField F src pointer.code pointer.cert hf valueExpr value.code value.cert))⟩
  | .local dst => do
    let one := incrementOne hp
    let valueExpr := compoundValue op.binOp (increment_compound op) hp (.simple (.local dst)) one
    let value ← compileVal b F valueExpr
    pure ⟨_, .incrementLocal F op hp dst _
      (.compoundLocal F op.binOp (increment_compound op) hp dst one _
        (.assign F dst valueExpr value.code value.cert))⟩
  | _ => none

mutual
/-- Refuse every shape for which the memory simulation has no clause. -/
def compileStmt (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) :
    (s : Stmt C Γ Δ) → Option (CompiledStmt b F s)
  | .assignLocal dst e => do
    let value ← compileVal b F e
    pure ⟨F, _, .assign F dst e value.code value.cert⟩
  | .declLocal p x (some e) => do
    let value ← compileVal b F e
    pure ⟨F.push (.val p) .ok, _, .declare F x e value.code value.cert⟩
  | .declLocal p x none => some ⟨F.push (.val p) .ok, _, .declareDefault F p x⟩
  | .rebindMem dst (.alias (.var src hm)) =>
    some ⟨F, _, .rebind F dst src hm⟩
  | @Solidity.Stmt.rebindMem _ _ (.array (.prim p)) dst (.newArr n _) =>
    if hb : 0 < b then
      if hn : simpleIn n = true then some ⟨F, _, .reallocate F p dst n hb hn⟩
      else none
    else none
  | .declMem R x (some (.alias (.var src hm))) _ _ =>
    some ⟨F.push (.mem R) .ok, _, .declareAlias F x src hm⟩
  | .rebindMem dst (.alias src) => do
    let pointer ← compilePtr b src
    pure ⟨F, _, .rebindPath F dst src pointer.code pointer.cert⟩
  | .declMem R x (some (.alias src)) _ hm => do
    let pointer ← compilePtr b src
    pure ⟨F.push (.mem R) .ok, _, .declarePathAlias F x src hm pointer.code pointer.cert⟩
  | .declMem (.struct s) x none hd hm =>
    if hb : 0 < b then
      if hp : primitiveMembers (Semantics.structDef s) = true then
        some ⟨F.push (.mem (.struct s)) .ok, _, .allocateStruct F s x hd hm hb hp⟩
      else none
    else none
  | .declMem (.struct s) x (some (.copy (.loc (.root root hr)) _)) _ hm =>
    if hb : 0 < b then
      if hp : primitiveMembers (Semantics.structDef s) = true then do
        let loads ← compileCopyLoads b F root hr (Semantics.structDef s)
        pure ⟨F.push (.mem (.struct s)) .ok, _, .copyStruct F s x root hr hm hb hp loads.code loads.cert⟩
      else none
    else none
  | @Solidity.Stmt.rebindMem _ _ (.struct s) dst (.copy (.loc (.root root hr)) hm) =>
    if hb : 0 < b then
      if hp : primitiveMembers (Semantics.structDef s) = true then do
        let loads ← compileCopyLoads b F root hr (Semantics.structDef s)
        pure ⟨F, _, .rebindCopyStruct F s dst root hr hm hb hp loads.code loads.cert⟩
      else none
    else none
  | .declMem (.array (.prim p)) x (some (.newArr n _)) _ _ =>
    if hb : 0 < b then
      if hn : simpleIn n = true then
        some ⟨F.push (.mem (.array (.prim p))) .ok, _, .allocate F p x n hb hn⟩
      else none
    else none
  | .declMem (.array (.prim p)) x none _ _ =>
    if hb : 0 < b then
      some ⟨F.push (.mem (.array (.prim p))) .ok, _,
        .defaultArray F p x _ (.allocate F p x (.lit 0 rfl) hb rfl)⟩
    else none
  | .assignMem (.index .dyn (.var dst hm) i) (.val v) => do
    let index ← compileVal b F i
    let value ← compileVal b F v
    pure ⟨F, _, .write F dst hm i v index.code value.code index.cert value.cert⟩
  | .assignMem (.field (.var dst hm) _ hf) (.val v) => do
    let value ← compileVal b F v
    pure ⟨F, _, .writeField F dst hm hf v value.code value.cert⟩
  | .assignMem (.index .dyn src i) (.val v) => do
    let pointer ← compilePtr b src
    let index ← compileVal b F i
    let value ← compileVal b F v
    pure ⟨F, _, .writePathArray F src pointer.code pointer.cert i v index.code value.code index.cert value.cert⟩
  | .assignMem (.field src _ hf) (.val v) => do
    let pointer ← compilePtr b src
    let value ← compileVal b F v
    pure ⟨F, _, .writePathField F src pointer.code pointer.cert hf v value.code value.cert⟩
  | .assignMem (.field dst _ hf) (.ref src) => do
    let pointer ← compilePtr b dst
    let value ← compilePtr b src
    pure ⟨F, _, .writeReference F dst src hf pointer.code value.code pointer.cert value.cert⟩
  | @Solidity.Stmt.deleteMem _ _ (.prim _) (.loc (.index .dyn (.var dst hm) i)) _ => do
    let index ← compileVal b F i
    pure ⟨F, _, .deleteElement F dst hm i index.code index.cert⟩
  | @Solidity.Stmt.deleteMem _ _ (.ref (.array (.prim p))) (.var dst _) _ =>
    if hb : 0 < b then
      some ⟨F, _, .deleteArray F dst _ (.reallocate F p dst (.lit 0 rfl) hb rfl)⟩
    else none
  | @Solidity.Stmt.deleteMem _ _ (.ref (.struct s)) (.var dst hm) hd =>
    if hb : 0 < b then
      if hp : primitiveMembers (Semantics.structDef s) = true then
        some ⟨F, _, .deleteStruct F dst hd hm hb hp⟩
      else none
    else none
  | @Solidity.Stmt.deleteMem _ _ (.ref (.array (.prim _))) (.loc (.field src _ hf)) _ =>
    if hb : 0 < b then do
      let pointer ← compilePtr b src
      pure ⟨F, _, .deleteArrayField F src hf pointer.code pointer.cert hb⟩
    else none
  | @Solidity.Stmt.deleteMem _ _ (.ref (.struct t)) (.loc (.field src f hf)) hd =>
    if hb : 0 < b then
      if hp : primitiveMembers (Semantics.structDef t) = true then do
        let pointer ← compilePtr b src
        pure ⟨F, _, .deleteStructField F src hf hd (MLoc.field src f hf).mapFree
          pointer.code pointer.cert hb hp⟩
      else none
    else none
  | @Solidity.Stmt.deleteMem _ _ (.prim p) (.loc (.field (.var dst hm) _ hf)) _ => do
    let value ← compileVal b F (deleteDefaultValue p)
    pure ⟨F, _, .deleteField F (.var dst hm) hf _
      (.writeField F dst hm hf (deleteDefaultValue p) value.code value.cert)⟩
  | @Solidity.Stmt.deleteMem _ _ (.prim p) (.loc (.index .dyn src i)) _ => do
    let pointer ← compilePtr b src
    let index ← compileVal b F i
    let value ← compileVal b F (deleteDefaultValue p)
    pure ⟨F, _, .deletePathElement F src i _
      (.writePathArray F src pointer.code pointer.cert i (deleteDefaultValue p)
        index.code value.code index.cert value.cert)⟩
  | @Solidity.Stmt.deleteMem _ _ (.prim p) (.loc (.field src _ hf)) _ => do
    let pointer ← compilePtr b src
    let value ← compileVal b F (deleteDefaultValue p)
    pure ⟨F, _, .deleteField F src hf _
      (.writePathField F src pointer.code pointer.cert hf (deleteDefaultValue p) value.code value.cert)⟩
  | .opAssign op hop hp (.mindex .dyn (.var dst hm) i) r => do
    let valueExpr := compoundValue op hop hp (.readMem (.index .dyn (.var dst hm) (.simple i))) r
    let index ← compileVal b F (.simple i)
    let value ← compileVal b F valueExpr
    pure ⟨F, _, .compoundMemory F op hop hp .dyn (.var dst hm) i r _
      (.write F dst hm (.simple i) valueExpr index.code value.code index.cert value.cert)⟩
  | .opAssign op hop hp (.local dst) r => do
    let valueExpr := compoundValue op hop hp (.simple (.local dst)) r
    let value ← compileVal b F valueExpr
    pure ⟨F, _, .compoundLocal F op hop hp dst r _ (.assign F dst valueExpr value.code value.cert)⟩
  | .opAssign op hop hp (.mfield (.var dst hm) f hf) r => do
    let valueExpr := compoundValue op hop hp (.readMem (.field (.var dst hm) f hf)) r
    let value ← compileVal b F valueExpr
    pure ⟨F, _, .compoundField F op hop hp (.var dst hm) f hf r _
      (.writeField F dst hm hf valueExpr value.code value.cert)⟩
  | .opAssign op hop hp (.mindex .dyn src i) r => do
    let pointer ← compilePtr b src
    let valueExpr := compoundValue op hop hp (.readMem (.index .dyn src (.simple i))) r
    let index ← compileVal b F (.simple i)
    let value ← compileVal b F valueExpr
    pure ⟨F, _, .compoundMemory F op hop hp .dyn src i r _
      (.writePathArray F src pointer.code pointer.cert (.simple i) valueExpr
        index.code value.code index.cert value.cert)⟩
  | .opAssign op hop hp (.mfield src f hf) r => do
    let pointer ← compilePtr b src
    let valueExpr := compoundValue op hop hp (.readMem (.field src f hf)) r
    let value ← compileVal b F valueExpr
    pure ⟨F, _, .compoundField F op hop hp src f hf r _
      (.writePathField F src pointer.code pointer.cert hf valueExpr value.code value.cert)⟩
  | .incDec op hp l => do
    let bump ← compileBump b F op hp l
    pure ⟨F, bump.val, bump.property⟩
  | .assignIncDec dst op hp (.mindex .dyn (.var src hm) i) hrecv => do
    let value ← compileVal b F (bumpResultValue op hp
      (.readMem (.index .dyn (.var src hm) (.simple i))))
    let bump ← compileBump b F op hp (.mindex .dyn (.var src hm) i)
    pure ⟨F, _, .captureMemory F dst op hp .dyn (.var src hm) i hrecv
      value.code bump.val value.cert bump.property⟩
  | .assignIncDec dst op hp (.local src) hrecv => do
    let value ← compileVal b F (bumpResultValue op hp (.simple (.local src)))
    let bump ← compileBump b F op hp (.local src)
    pure ⟨F, _, .captureLocal F dst op hp src hrecv value.code bump.val value.cert bump.property⟩
  | .assignIncDec dst op hp (.mfield (.var src hm) f hf) hrecv => do
    let value ← compileVal b F (bumpResultValue op hp (.readMem (.field (.var src hm) f hf)))
    let bump ← compileBump b F op hp (.mfield (.var src hm) f hf)
    pure ⟨F, _, .captureField F dst op hp (.var src hm) f hf hrecv
      value.code bump.val value.cert bump.property⟩
  | .assign l (.val v) =>
    if hl : locIn F false l = true then do
      let value ← compileVal b F v
      pure ⟨F, _, .storageWrite F l v value.code hl value.cert⟩
    else none
  | .require c => do
    let cond ← compileVal b F c
    pure ⟨F, _, .require F c cond.code cond.cert⟩
  | .revert => some ⟨F, _, .revert F⟩
  | .block body => do
    let result ← compileProg b F body
    pure ⟨result.frag.restrict Γ, result.code, .block body result.code result.cert⟩
  | .ite c thn els => do
    let cond ← compileVal b F c
    let left ← compileProg b F thn
    let right ← compileProg b F els
    pure ⟨(left.frag.restrict Γ).meet (right.frag.restrict Γ), _,
      .ite c thn els cond.code left.code right.code cond.cert left.cert right.cert⟩
  | _ => none

def compileProg (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) :
    (P : Prog C Γ Δ) → Option (CompiledProg b F P)
  | .nil => some ⟨F, [], .nil F⟩
  | .cons s P => do
    let head ← compileStmt b F s
    let tail ← compileProg b head.frag P
    pure ⟨tail.frag, head.code ++ tail.code, .cons head.cert tail.cert⟩

end

private def rhsAllocationExpr {Γ : Ctx} {R : RefTy} (rhs : MRhs C Γ R) :
    Option (Simple C Γ .uint) :=
  match rhs with
  | .newArr n _ => match R with
    | .array (.prim _) => some n
    | _ => none
  | _ => none

/-- Extract primitive allocation lengths, including the fresh empty object of local deletion. -/
def allocationExpr {Γ Δ : Ctx} (s : Stmt C Γ Δ) : Option (Simple C Γ .uint) :=
  match s with
  | .declMem _ _ (some rhs) _ _ => rhsAllocationExpr rhs
  | .rebindMem _ rhs => rhsAllocationExpr rhs
  | @Solidity.Stmt.deleteMem _ _ (.ref (.array (.prim _))) (.var _ _) _ => some (.lit 0 rfl)
  | _ => none

mutual
/-- Recognize allocation inside a supported scoped statement. -/
def hasAllocationStmt {Γ Δ : Ctx} (s : Stmt C Γ Δ) : Bool :=
  match s with
  | .block body => hasAllocation body
  | .ite _ thn els => hasAllocation thn || hasAllocation els
  | .declMem R _ init _ _ => match init with
    | none => match R with | .struct _ | .array (.prim _) => true | _ => false
    | some (.copy (.loc (.root ..)) _) => match R with | .struct _ => true | _ => false
    | some rhs => (rhsAllocationExpr rhs).isSome
  | .rebindMem (R := R) _ rhs => match rhs with
    | .copy (.loc (.root ..)) _ => match R with | .struct _ => true | _ => false
    | rhs => (rhsAllocationExpr rhs).isSome
  | @Solidity.Stmt.deleteMem _ _ (.ref (.struct _)) (.var _ _) _ => true
  | @Solidity.Stmt.deleteMem _ _ (.ref (.array (.prim _))) (.loc (.field ..)) _ => true
  | @Solidity.Stmt.deleteMem _ _ (.ref (.struct _)) (.loc (.field ..)) _ => true
  | .assign .. | .rebind .. | .assignLocal .. | .declLocal ..
  | .declStorage .. | .opAssign .. | .incDec .. | .assignIncDec ..
  | .assignLocalPush .. | .push .. | .pop .. | .transfer ..
  | .send .. | .assignFromMem ..
  | .assignMem .. | .delete .. | .deleteMem .. | .assignNew ..
  | .require .. | .assert .. | .revert
  | .assumeFalse | .call .. | .tryCall .. | .loop ..
  | .pushOpAssign .. | .pushIncDec .. | .callReceiver .. | .callReceiverPush ..
  | .callRec .. | .revertData .. | .catchData .. => (allocationExpr s).isSome

def hasAllocation {Γ Δ : Ctx} : Prog C Γ Δ → Bool
  | .nil => false
  | .cons s P => hasAllocationStmt s || hasAllocation P
end

mutual
/-- The number of cells reserved by a reached statement, including scoped bodies. -/
private def rawAllocationCostStmt {Γ Δ : Ctx} (s : Stmt C Γ Δ) (σ : State C Γ) : Nat :=
  match s with
  | .block body => allocationCostProg body σ
  | .ite c thn els => match c.evalT σ with
    | .ok v => if boolT v then allocationCostProg thn σ else allocationCostProg els σ
    | .error _ => 0
  | .declMem R _ init _ _ => match init with
    | none => match R with
      | .struct s => structAllocationSize s
      | .array (.prim _) => 1
      | _ => 0
    | some (.copy (.loc (.root ..)) _) => match R with | .struct s => structAllocationSize s | _ => 0
    | some rhs => match rhsAllocationExpr rhs with
        | some n => (n.evalT σ).word.val + 1
        | none => 0
  | .rebindMem (R := R) _ rhs => match rhs with
    | .copy (.loc (.root ..)) _ => match R with | .struct s => structAllocationSize s | _ => 0
    | rhs => match rhsAllocationExpr rhs with
        | some n => (n.evalT σ).word.val + 1
        | none => 0
  | @Solidity.Stmt.deleteMem _ _ (.ref (.struct s)) (.var _ _) _ => structAllocationSize s
  | @Solidity.Stmt.deleteMem _ _ (.ref (.array (.prim _))) (.loc (.field src ..)) _ =>
    match src.mvalT σ with | .ok _ => 1 | .error _ => 0
  | @Solidity.Stmt.deleteMem _ _ (.ref (.struct t)) (.loc (.field src ..)) _ =>
    match src.mvalT σ with | .ok _ => structAllocationSize t | .error _ => 0
  | .assign .. | .rebind .. | .assignLocal .. | .declLocal ..
  | .declStorage .. | .opAssign .. | .incDec .. | .assignIncDec ..
  | .assignLocalPush .. | .push .. | .pop .. | .transfer ..
  | .send .. | .assignFromMem ..
  | .assignMem .. | .delete .. | .deleteMem .. | .assignNew ..
  | .require .. | .assert .. | .revert
  | .assumeFalse | .call .. | .tryCall .. | .loop ..
  | .pushOpAssign .. | .pushIncDec .. | .callReceiver .. | .callReceiverPush ..
  | .callRec .. | .revertData .. | .catchData .. => match allocationExpr s with
    | some n => (n.evalT σ).word.val + 1
    | none => 0

/-- Only reached source allocations contribute to the capacity premise. -/
def allocationCostProg {Γ Δ : Ctx} (P : Prog C Γ Δ) (σ : State C Γ) : Nat :=
  match P with
  | .nil => 0
  | .cons s tail => (if hasAllocationStmt s then rawAllocationCostStmt s σ else 0) +
    if hasAllocation tail then
      match s.run σ with
      | .ok o => allocationCostProg tail o.st
      | .error _ => 0
    else 0

end

/-- Skip even the statement evaluator when the syntax contains no allocation. -/
def allocationCostStmt {Γ Δ : Ctx} (s : Stmt C Γ Δ) (σ : State C Γ) : Nat :=
  if hasAllocationStmt s then rawAllocationCostStmt s σ else 0

/-- A nonallocating suffix needs no interpreter evaluation for its cost. -/
theorem allocationCostProg_zero {Γ Δ : Ctx} (P : Prog C Γ Δ)
    (h : hasAllocation P = false) (σ : State C Γ) : allocationCostProg P σ = 0 := by
  cases P with
  | nil => rfl
  | cons s P =>
    have hh : hasAllocationStmt s = false ∧ hasAllocation P = false := Bool.or_eq_false_iff.mp h
    rw [allocationCostProg]
    simp only [hh.1, hh.2, Bool.false_eq_true, if_false, Nat.add_zero]

/-- The cost of a block is exactly the reached cost of its body. -/
theorem allocationCostStmt_block {Γ Δ : Ctx} (P : Prog C Γ Δ) (σ : State C Γ) :
    allocationCostStmt (.block P) σ = allocationCostProg P σ := by
  simp only [allocationCostStmt, hasAllocationStmt, rawAllocationCostStmt]
  cases hh : hasAllocation P with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    exact (allocationCostProg_zero P hh σ).symm
  | true => simp only [if_true]

/-- Only the selected branch contributes cells; a failed condition contributes none. -/
theorem allocationCostStmt_ite {Γ Δ Ξ : Ctx} (c : Val C Γ .bool)
    (thn : Prog C Γ Δ) (els : Prog C Γ Ξ) (σ : State C Γ) :
    allocationCostStmt (.ite c thn els) σ = match c.evalT σ with
      | .ok v => if boolT v then allocationCostProg thn σ else allocationCostProg els σ
      | .error _ => 0 := by
  simp only [allocationCostStmt, hasAllocationStmt, rawAllocationCostStmt]
  cases ht : hasAllocation thn <;> cases he : hasAllocation els
  · rw [allocationCostProg_zero thn ht, allocationCostProg_zero els he]
    cases c.evalT σ with
    | error _ => rfl
    | ok v => simp only [Bool.false_or, Bool.false_eq_true, ite_self]
  all_goals rfl

/-- The optimized cost still equals the cost of the reached source prefix. -/
theorem allocationCostProg_cons {Γ Δ Ξ : Ctx} (s : Stmt C Γ Δ) (P : Prog C Δ Ξ)
    (σ : State C Γ) :
    allocationCostProg (.cons s P) σ = allocationCostStmt s σ +
      match s.run σ with
      | .ok o => allocationCostProg P o.st
      | .error _ => 0 := by
  rw [allocationCostProg]
  change allocationCostStmt s σ + _ = _
  apply congrArg (allocationCostStmt s σ + ·)
  cases ht : hasAllocation P with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    cases he : s.run σ with
    | ok o => exact (allocationCostProg_zero P ht o.st).symm
    | error _ => rfl
  | true =>
    simp only [if_true]
    cases s.run σ <;> rfl

abbrev StmtFrag.cost {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {s : Stmt C Γ Δ} {code : List Instr} (_hs : StmtFrag b F G s code)
    (σ : State C Γ) : Nat := allocationCostStmt s σ

abbrev ProgFrag.cost {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {P : Prog C Γ Δ} {code : List Instr} (_hp : ProgFrag b F G P code)
    (σ : State C Γ) : Nat := allocationCostProg P σ

theorem StmtFrag.length_mono {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {s : Stmt C Γ Δ} {code : List Instr} (hs : StmtFrag b F G s code) :
    Γ.length ≤ Δ.length := by
  cases hs <;> first | exact Nat.le_refl _ | exact Nat.le_succ _

theorem ProgFrag.length_mono {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {P : Prog C Γ Δ} {code : List Instr} (_hp : ProgFrag b F G P code) :
    Γ.length ≤ Δ.length := by
  have he : Δ.length = Γ.length + P.ext.depth := P.ext.length_eq
  omega

theorem StmtFrag.pushes_zero {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {s : Stmt C Γ Δ} {code : List Instr} (hs : StmtFrag b F G s code) :
    Evm.Stmt.pushes s = 0 := by
  induction hs using StmtFrag.rec
    (motive_2 := fun _ _ P _ _ => Evm.Prog.pushes P = 0)
  case block body code hp ih => exact ih
  case ite c thn els cond left right hc ht he iht ihe =>
    change Evm.Prog.pushes thn + Evm.Prog.pushes els = 0
    rw [iht, ihe]
  case cons hs hp ihs ihp =>
    change Evm.Stmt.pushes _ + Evm.Prog.pushes _ = 0
    rw [ihs, ihp]
  all_goals rfl

theorem ProgFrag.pushes_zero {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {P : Prog C Γ Δ} {code : List Instr} (hp : ProgFrag b F G P code) :
    Evm.Prog.pushes P = 0 := by
  induction hp using ProgFrag.rec
    (motive_1 := fun _ _ s _ _ => Evm.Stmt.pushes s = 0)
  case block body code hp ih => exact ih
  case ite c thn els cond left right hc ht he iht ihe =>
    change Evm.Prog.pushes thn + Evm.Prog.pushes els = 0
    rw [iht, ihe]
  case cons hs hp ihs ihp =>
    change Evm.Stmt.pushes _ + Evm.Prog.pushes _ = 0
    rw [ihs, ihp]
  all_goals rfl

private theorem run_cons_revert {Γ Δ Ξ : Ctx} {σ : State C Γ}
    {s : Stmt C Γ Δ} {P : Prog C Δ Ξ} (h : s.run σ = .error .revert) :
    (Prog.cons s P).run σ = .error .revert := by
  show TRun.seq s.runR P.runR σ = _
  simp only [TRun.seq, Solidity.Stmt.run] at h ⊢
  rw [h]

private def StmtSound (L b frame : Nat) {Γ Δ : Ctx} (F : Frag Γ) (G : Frag Δ)
    (s : Stmt C Γ Δ) (code : List Instr) : Prop :=
  ∀ {σ : State C Γ} {base : Nat → Fin W} {m : Machine}, StateRepr L b frame F σ base m →
    b + frameNeedStmt s ≤ frame → AllocationInput b frame (allocationCostStmt s σ) σ base m →
      GrowingResult L b frame (allocationCostStmt s σ) G σ base m (s.run σ) (run code m)

private def ProgSound (L b frame : Nat) {Γ Δ : Ctx} (F : Frag Γ) (G : Frag Δ)
    (P : Prog C Γ Δ) (code : List Instr) : Prop :=
  ∀ {σ : State C Γ} {base : Nat → Fin W} {m : Machine}, StateRepr L b frame F σ base m →
    b + frameNeedProg P ≤ frame → AllocationInput b frame (allocationCostProg P σ) σ base m →
      GrowingResult L b frame (allocationCostProg P σ) G σ base m (P.run σ) (run code m)

private theorem statementEndCap {Γ Δ : Ctx} {s : Stmt C Γ Δ} {b frame : Nat}
    (h : b + frameNeedStmt s ≤ frame) : b + Δ.length ≤ frame :=
  Nat.le_trans (Nat.add_le_add_left (frameNeedStmt_end s) b) h

private theorem nil_sound {L b frame : Nat} {Γ : Ctx} (F : Frag Γ) :
    ProgSound (C := C) L b frame F F .nil [] :=
  fun h _ _ => .inl ⟨⟨_, List.prefix_refl _⟩, _, _, rfl, rfl, h, rfl,
    BaseExtends.refl _, fun _ _ ha _ => ha⟩

private theorem cons_sound {L b frame : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ} {G : Frag Δ} {K : Frag Ξ}
    {s : Stmt C Γ Δ} {P : Prog C Δ Ξ} {head tail : List Instr}
    (hs : StmtFrag b F G s head) (hp : ProgFrag b G K P tail)
    (ihs : StmtSound L b frame F G s head) (ihp : ProgSound L b frame G K P tail) :
    ProgSound L b frame F K (.cons s P) (head ++ tail) := by
  intro σ base m h hcap ha
  have hcaps : b + frameNeedStmt s ≤ frame := by
    change b + max (frameNeedStmt s) (frameNeedProg P) ≤ frame at hcap
    omega
  have hcapp : b + frameNeedProg P ≤ frame := by
    change b + max (frameNeedStmt s) (frameNeedProg P) ≤ frame at hcap
    omega
  have hah : AllocationInput b frame (hs.cost σ) σ base m :=
    ha.of_le (by rw [allocationCostProg_cons]; exact Nat.le_add_right _ _)
  rcases ihs h hcaps hah with ⟨o, m₁, base₁, ho, hc, hm, hst, hex, hal⟩ | ⟨ho, hc⟩
  · rw [Solidity.Prog.run_cons_ok ho, run_append_ok hc]
    have hcost : allocationCostProg (.cons s P) σ = hs.cost σ + hp.cost o.st := by
      rw [allocationCostProg_cons, ho]
    have hat : AllocationInput b frame (hp.cost o.st) o.st base₁ m₁ := hal.nextInput (hcost ▸ ha)
    rcases ihp hm hcapp hat with ⟨o', m₂, base₂, ho', hc', hm', hst', hex', hal'⟩ | ⟨ho', hc'⟩
    · refine .inl ⟨⟨o'.st, o.ext.trans o'.ext⟩, m₂, base₂,
        by rw [ho']; rfl, hc', hm', hst'.trans hst, hex.trans o.ext hex', ?_⟩
      rw [hcost]
      exact hal.comp hal'
    · exact .inr ⟨by rw [ho']; rfl, hc'⟩
  · exact .inr ⟨run_cons_revert ho, run_append_revert hc⟩

private theorem block_sound {L b frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {body : Prog C Γ Δ} {code : List Instr} (ih : ProgSound L b frame F G body code) :
    StmtSound L b frame F (G.restrict Γ) (.block body) code := by
  intro σ base m h hcap ha
  have hb : b + frameNeedProg body ≤ frame := by
    simp only [frameNeedStmt, nestedFramesStmt] at hcap
    omega
  have ha' : AllocationInput b frame (allocationCostProg body σ) σ base m :=
    allocationCostStmt_block body σ ▸ ha
  rcases ih h hb ha' with ⟨o, m', base', ho, hc, hm, hk, he, hal⟩ | ⟨ho, hc⟩
  · refine .inl ⟨⟨o.st.drop body.ext, o.ext⟩, m', base', ?_, hc,
      hm.drop body.ext, hk, he, ?_⟩
    · change (body.run σ).map (fun o => (⟨o.st.drop body.ext, o.ext⟩ : Solidity.Out C σ.H Γ)) = _
      rw [ho]
      rfl
    · rw [allocationCostStmt_block]
      exact hal
  · refine .inr ⟨?_, hc⟩
    change (body.run σ).map (fun o => (⟨o.st.drop body.ext, o.ext⟩ : Solidity.Out C σ.H Γ)) = _
    rw [ho]
    rfl

private theorem ite_sound {L b frame : Nat} {Γ Δ Ξ : Ctx}
    {F : Frag Γ} {G : Frag Δ} {K : Frag Ξ}
    {c : Val C Γ .bool} {thn : Prog C Γ Δ} {els : Prog C Γ Ξ}
    {cond left right : List Instr} (hc : ValFrag b F c cond)
    (iht : ProgSound L b frame F G thn left) (ihe : ProgSound L b frame F K els right) :
    StmtSound L b frame F ((G.restrict Γ).meet (K.restrict Γ)) (.ite c thn els)
      (conditionalCode cond left right) := by
  intro σ base m h hcap ha
  have hbt : b + frameNeedStmt (.block thn) ≤ frame := by
    simp only [frameNeedStmt, nestedFramesStmt] at hcap ⊢
    omega
  have hbe : b + frameNeedStmt (.block els) ≤ frame := by
    simp only [frameNeedStmt, nestedFramesStmt] at hcap ⊢
    omega
  change GrowingResult _ _ _ _ _ _ _ _ (TRun.ite c thn.ext thn.runR els.ext els.runR σ) _
  simp only [TRun.ite, conditionalCode, List.append_assoc]
  rcases hc.correct h with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
  · obtain rfl := hrc.bool_inv
    rw [run_append_ok hrunc, hvc]
    simp only [bind, Except.bind, Solidity.boolT]
    cases vc
    · have hcost : allocationCostStmt (.ite c thn els) σ = allocationCostStmt (.block els) σ := by
        rw [allocationCostStmt_ite, allocationCostStmt_block, hvc]
        rfl
      rw [hcost] at ha ⊢
      rw [run_append_skip (m' := m) (k := left.length + 1) rfl,
        show left.length + 1 = left.length + 1 from rfl, exec_append, exec_skip]
      simp only [Out.ok_bind, Bool.false_eq_true, ↓reduceIte]
      rcases block_sound ihe h hbe ha with ⟨o, m', base', ho, ht, hm, hk, he, hal⟩ | ⟨ho, ht⟩
      · exact .inl ⟨o, m', base', ho, ht, hm.meetRight _, hk, he, hal⟩
      · exact .inr ⟨ho, ht⟩
    · have hcost : allocationCostStmt (.ite c thn els) σ = allocationCostStmt (.block thn) σ := by
        rw [allocationCostStmt_ite, allocationCostStmt_block, hvc]
        rfl
      rw [hcost] at ha ⊢
      rw [run_append_skip (m' := m) (k := 0) rfl]
      simp only [↓reduceIte]
      rcases block_sound iht h hbt ha with ⟨o, m', base', ho, ht, hm, hk, he, hal⟩ | ⟨ho, ht⟩
      · refine .inl ⟨o, m', base', ho, ?_, hm.meet _, hk, he, hal⟩
        change run _ m = _
        rw [run_append_ok ht]
        exact exec_length _ _
      · exact .inr ⟨ho, run_append_revert ht⟩
  · exact .inr ⟨by simp only [bind, Except.bind, hvc], run_append_revert hrunc⟩

private theorem stmt_sound {L b frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {s : Stmt C Γ Δ} {code : List Instr} (hs : StmtFrag b F G s code) :
    StmtSound L b frame F G s code := by
  induction hs using StmtFrag.rec
    (motive_2 := fun F G P code _ => ProgSound L b frame F G P code) with
  | assign F dst e code he =>
    intro σ base m h hcap ha
    exact (assignValue_correct h dst e code (he.correct h)).growing
  | declare F x e code he =>
    intro σ base m h hcap ha
    exact (declareValue_correct h e code (he.correct h) (statementEndCap hcap)).growing
  | declareDefault F p x =>
    intro σ base m h hcap ha
    exact (declareDefault_correct h p (statementEndCap hcap)).growing
  | rebind F dst src hm =>
    intro σ base m h hcap ha
    exact (aliasLocal_correct h dst src hm).growing
  | declareAlias F x src hm =>
    intro σ base m h hcap ha
    exact (declareAlias_correct h src hm (statementEndCap hcap)).growing
  | rebindPath F dst src code hp =>
    intro σ base m h hcap ha
    exact (hp.rebind h dst).growing
  | declarePathAlias F x src hm code hp =>
    intro σ base m h hcap ha
    exact (hp.declareAlias h hm (statementEndCap hcap)).growing
  | allocate F p x n hb hn =>
    intro σ base m h hcap ha
    rcases ha with hz | ⟨_, cursor, hal, hspace⟩
    · change (n.evalT σ).word.val + 1 = 0 at hz
      omega
    · have hs : n.evalT σ = indexValue (n.evalT σ).word :=
        Subtype.ext (word_val (n.evalT σ)).symm
      have hspace' : cursor.val + (n.evalT σ).word.val + 1 < W := by
        change cursor.val + ((n.evalT σ).word.val + 1) < W at hspace
        omega
      have hn' := newArray_correct h hal hb p n hn (n.evalT σ).word hs hspace' (statementEndCap hcap)
      refine .inl ⟨⟨σ.allocPush (defaultArray p (n.evalT σ).word), List.prefix_append _ _⟩,
        _, upd base σ.H.length cursor, hn'.1, hn'.2.1, hn'.2.2.1, hn'.2.2.2.2, ?_, ?_⟩
      · exact fun r => allocationBase_old base cursor r
      · intro c _ hc hcspace
        have he : c = cursor := Word.val.inj (hc.arrays.free.cell.symm.trans hal.arrays.free.cell)
        subst c
        simpa only [Nat.add_assoc] using hn'.2.2.2.1
  | defaultArray F p x code hs ih =>
    intro σ base m h hcap ha
    change GrowingResult L b frame 1 (F.push (.mem (.array (.prim p))) .ok) σ base m
      (TRun.declMem (.array (.prim p)) none rfl σ) (run code m)
    rw [defaultArray_eq_allocate]
    exact ih h hcap ha
  | allocateStruct F s x hd hm hb hp =>
    intro σ base m h hcap ha
    rcases ha with hz | ⟨_, cursor, hal, hspace⟩
    · change structAllocationSize s = 0 at hz
      have hs : 1 ≤ structAllocationSize s := Nat.le_max_left _ _
      omega
    · have hn := defaultStruct_correct h hal hb hp hm hspace (statementEndCap hcap)
      refine .inl ⟨⟨σ.allocPush (R := .struct s) (defaultFields (Semantics.structDef s) hp), List.prefix_append _ _⟩,
        _, upd base σ.H.length cursor, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.2, ?_, ?_⟩
      · exact fun r => allocationBase_old base cursor r
      · intro c _ hc hcspace
        have he : c = cursor := Word.val.inj (hc.arrays.free.cell.symm.trans hal.arrays.free.cell)
        subst c
        exact hn.2.2.2.1
  | copyStruct F s x root hr hm hb hp loads plan =>
    intro σ base m h hcap ha
    rcases ha with hz | ⟨_, cursor, hal, hspace⟩
    · change structAllocationSize s = 0 at hz
      have hs : 1 ≤ structAllocationSize s := Nat.le_max_left _ _
      omega
    · cases hv : σ.storage.get hr with
      | struct v =>
        obtain ⟨m', hs, ht, hrepr, halloc, hstack⟩ :=
          copiedStruct_correct h hal hb root hr plan v hv hp hm hspace (statementEndCap hcap)
        refine .inl ⟨⟨σ.allocPush (R := .struct s) (copiedFields (Semantics.structDef s) hp v), List.prefix_append _ _⟩,
          m', upd base σ.H.length cursor, hs, ht, hrepr, hstack, ?_, ?_⟩
        · exact fun r => allocationBase_old base cursor r
        · intro c _ hc hcspace
          have he : c = cursor := Word.val.inj (hc.arrays.free.cell.symm.trans hal.arrays.free.cell)
          subst c
          exact halloc
  | rebindCopyStruct F s dst root hr hm hb hp loads plan =>
    intro σ base m h hcap ha
    rcases ha with hz | ⟨_, cursor, hal, hspace⟩
    · change structAllocationSize s = 0 at hz
      have hs : 1 ≤ structAllocationSize s := Nat.le_max_left _ _
      omega
    · cases hv : σ.storage.get hr with
      | struct v =>
        obtain ⟨m', hs, ht, hrepr, halloc, hstack⟩ :=
          copiedStruct_rebind_correct h hal hb dst root hr plan v hv hp hm hspace
        refine .inl ⟨⟨_, List.prefix_append _ _⟩, m', upd base σ.H.length cursor,
          hs, ht, hrepr, hstack, ?_, ?_⟩
        · exact fun r => allocationBase_old base cursor r
        · intro c _ hc hcspace
          have he : c = cursor := Word.val.inj (hc.arrays.free.cell.symm.trans hal.arrays.free.cell)
          subst c
          exact halloc
  | write F dst hm i v index value hi hv =>
    intro σ base m h hcap ha
    exact (writeLocalValue_correct h dst i v index value (fun h' => hi.correct h') (hv.correct h)).growing
  | writeField F dst hm hf v value hv =>
    intro σ base m h hcap ha
    exact (writeLocalField_correct h dst hm hf v value (hv.correct h)).growing
  | writePathArray F src pointer hp i v index value hi hv =>
    intro σ base m h hcap ha
    exact (hp.writeArray h i v index value (fun h' => hi.correct h') (hv.correct h)).growing
  | writePathField F src pointer hp hf v value hv =>
    intro σ base m h hcap ha
    exact (hp.writePrimitive h hf v value (hv.correct h)).growing
  | writeReference F dst src hf pointer value hd hs =>
    intro σ base m h hcap ha
    exact (writeReference_correct h hd hs hf).growing
  | deleteElement F dst hm i index hi =>
    intro σ base m h hcap ha
    exact (deleteLocalValue_correct h dst i index (fun h' => hi.correct h')).growing
  | deletePathElement F src i code hs ih =>
    intro σ base m h hcap ha
    change GrowingResult L b frame 0 F σ base m
      (TRun.deleteMem (.loc (.index .dyn src i)) σ) (run code m)
    rw [deleteMem_primitive_eq_assign]
    exact ih h hcap ha
  | deleteArray F dst code hs ih =>
    exact ih
  | deleteStruct F dst hd hm hb hp =>
    intro σ base m h hcap ha
    rcases ha with hz | ⟨_, cursor, hal, hspace⟩
    · change structAllocationSize _ = 0 at hz
      unfold structAllocationSize at hz
      omega
    · have hn := deleteStruct_correct h hal hb dst hp hm hspace
      refine .inl ⟨⟨_, List.prefix_append _ _⟩,
        _, upd base σ.H.length cursor, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.2, ?_, ?_⟩
      · exact fun r => allocationBase_old base cursor r
      · intro c _ hc hcspace
        have he : c = cursor := Word.val.inj (hc.arrays.free.cell.symm.trans hal.arrays.free.cell)
        subst c
        exact hn.2.2.2.1
  | deleteArrayField F src hf pointer hs hb =>
    intro σ base m h hcap ha
    obtain ⟨r, hr, _⟩ := hs.correct h
    have hcost : allocationCostStmt (.deleteMem (.loc (.field src _ hf)) rfl) σ = 1 := by
      simp only [allocationCostStmt, hasAllocationStmt, rawAllocationCostStmt, hr, if_true]
    rw [hcost] at ha ⊢
    rcases ha with hz | ⟨_, cursor, hal, hspace⟩
    · omega
    · have hn := deleteArrayField_correct h hal hb hs r hr hf hspace
      refine .inl ⟨⟨_, List.prefix_append _ _⟩, _, upd base σ.H.length cursor,
        hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.2, ?_, ?_⟩
      · exact fun r => allocationBase_old base cursor r
      · intro c _ hc hcspace
        have he : c = cursor := Word.val.inj (hc.arrays.free.cell.symm.trans hal.arrays.free.cell)
        subst c
        exact hn.2.2.2.1
  | deleteStructField F src hf hd hm pointer hs hb hp =>
    rename_i parent child member
    intro σ base m h hcap ha
    obtain ⟨r, hr, _⟩ := hs.correct h
    have hcost : allocationCostStmt (.deleteMem (.loc (.field src _ hf)) hd) σ = structAllocationSize child := by
      simp only [allocationCostStmt, hasAllocationStmt, rawAllocationCostStmt, hr, if_true]
    rw [hcost] at ha ⊢
    rcases ha with hz | ⟨_, cursor, hal, hspace⟩
    · unfold structAllocationSize at hz
      omega
    · have hn := deleteStructField_correct h hal hb hs r hr hf hp hm hspace
      refine .inl ⟨⟨_, List.prefix_append _ _⟩, _, upd base σ.H.length cursor,
        hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.2, ?_, ?_⟩
      · exact fun r => allocationBase_old base cursor r
      · intro c _ hc hcspace
        have he : c = cursor := Word.val.inj (hc.arrays.free.cell.symm.trans hal.arrays.free.cell)
        subst c
        exact hn.2.2.2.1
  | deleteField F src hf code hs ih =>
    intro σ base m h hcap ha
    change GrowingResult L b frame 0 F σ base m (TRun.deleteMem (.loc (.field src _ hf)) σ) (run code m)
    rw [deleteMem_primitive_eq_assign]
    exact ih h hcap ha
  | compoundMemory F op hop hp a src i r code hs ih =>
    intro σ base m h hcap ha
    change GrowingResult L b frame 0 F σ base m
      (TRun.opAssign op (.mindex a src i) r σ) (run code m)
    rw [compoundAssign_eq_write σ op hop hp a src i r]
    exact ih h hcap ha
  | compoundLocal F op hop hp dst r code hs ih =>
    intro σ base m h hcap ha
    change GrowingResult L b frame 0 F σ base m
      (TRun.opAssign op (.local dst) r σ) (run code m)
    rw [compoundLocal_eq_assign σ op hop hp dst r]
    exact ih h hcap ha
  | compoundField F op hop hp src f hf r code hs ih =>
    intro σ base m h hcap ha
    change GrowingResult L b frame 0 F σ base m (TRun.opAssign op (.mfield src f hf) r σ) (run code m)
    rw [compoundField_eq_write σ op hop hp src hf r]
    exact ih h hcap ha
  | incrementMemory F op hp a src i code hs ih =>
    intro σ base m h hcap ha
    change GrowingResult L b frame 0 F σ base m
      (TRun.incDec op (.mindex a src i) σ) (run code m)
    rw [incrementMemory_eq_compound σ op hp a src i]
    exact ih h hcap ha
  | incrementLocal F op hp dst code hs ih =>
    intro σ base m h hcap ha
    change GrowingResult L b frame 0 F σ base m
      (TRun.incDec op (.local dst) σ) (run code m)
    rw [incrementLocal_eq_compound σ op hp dst]
    exact ih h hcap ha
  | incrementField F op hp src f hf code hs ih =>
    intro σ base m h hcap ha
    change GrowingResult L b frame 0 F σ base m (TRun.incDec op (.mfield src f hf) σ) (run code m)
    rw [incrementField_eq_compound σ op hp src hf]
    exact ih h hcap ha
  | captureMemory F dst op hp a src i hrecv value step hv hs ih =>
    intro σ base m h hcap ha
    change GrowingResult L b frame 0 F σ base m
      (TRun.assignIncDec dst op (.mindex a src i) σ) (run _ m)
    rw [captureMemory_eq σ dst op hp a src i]
    exact captureStep_correct h dst _ _ value step (hv.correct h)
      (fun h' => ih h' hcap (.inl rfl))
  | captureLocal F dst op hp src hrecv value step hv hs ih =>
    intro σ base m h hcap ha
    change GrowingResult L b frame 0 F σ base m
      (TRun.assignIncDec dst op (.local src) σ) (run _ m)
    rw [captureLocal_eq σ dst op hp src]
    exact captureStep_correct h dst _ _ value step (hv.correct h)
      (fun h' => ih h' hcap (.inl rfl))
  | captureField F dst op hp src f hf hrecv value step hv hs ih =>
    intro σ base m h hcap ha
    change GrowingResult L b frame 0 F σ base m
      (TRun.assignIncDec dst op (.mfield src f hf) σ) (run _ m)
    rw [captureField_eq σ dst op hp src hf]
    exact captureStep_correct h dst _ _ value step (hv.correct h)
      (fun h' => ih h' hcap (.inl rfl))
  | reallocate F p dst n hb hn =>
    intro σ base m h hcap ha
    rcases ha with hz | ⟨_, cursor, hal, hspace⟩
    · change (n.evalT σ).word.val + 1 = 0 at hz
      omega
    · have hs : n.evalT σ = indexValue (n.evalT σ).word :=
        Subtype.ext (word_val (n.evalT σ)).symm
      have hspace' : cursor.val + (n.evalT σ).word.val + 1 < W := by
        change cursor.val + ((n.evalT σ).word.val + 1) < W at hspace
        omega
      have hn' := rebindNew_correct h hal hb p dst n hn (n.evalT σ).word hs hspace'
      refine .inl ⟨⟨(σ.alloc (defaultArray p (n.evalT σ).word)).1.setLocal dst
        (some (σ.alloc (defaultArray p (n.evalT σ).word)).2), List.prefix_append _ _⟩,
        _, upd base σ.H.length cursor, hn'.1, hn'.2.1, hn'.2.2.1, hn'.2.2.2.2, ?_, ?_⟩
      · exact fun r => allocationBase_old base cursor r
      · intro c _ hc hcspace
        have he : c = cursor := Word.val.inj (hc.arrays.free.cell.symm.trans hal.arrays.free.cell)
        subst c
        simpa only [Nat.add_assoc] using hn'.2.2.2.1
  | storageWrite F l v code hl hv =>
    intro σ base m h hcap ha
    exact (storageAssign_correct h l v code hl (hv.correct h)).growing
  | require F c code hc =>
    intro σ base m h hcap ha
    exact (requireValue_correct h c code (hc.correct h)).growing
  | revert F =>
    intro σ base m h hcap ha
    exact .inr ⟨rfl, rfl⟩
  | block body code hp ih =>
    exact block_sound ih
  | ite c thn els cond left right hc ht he iht ihe => exact ite_sound hc iht ihe
  | nil F => exact nil_sound F
  | cons hs hp ihs ihp => exact cons_sound hs hp ihs ihp

/-- Each supported statement preserves scoped source execution and its peak local frame. -/
theorem StmtFrag.correct {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {s : Stmt C Γ Δ} {code : List Instr} (hs : StmtFrag b F G s code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} (h : StateRepr L b frame F σ base m)
    (hcap : b + frameNeedStmt s ≤ frame)
    (ha : AllocationInput b frame (hs.cost σ) σ base m) :
    GrowingResult L b frame (hs.cost σ) G σ base m (s.run σ) (run code m) :=
  stmt_sound hs h hcap ha

/-- Composition preserves heap growth and reserves locals inside scoped bodies. -/
theorem ProgFrag.correct {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {P : Prog C Γ Δ} {code : List Instr} (hp : ProgFrag b F G P code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine} (h : StateRepr L b frame F σ base m)
    (hcap : b + frameNeedProg P ≤ frame)
    (ha : AllocationInput b frame (hp.cost σ) σ base m) :
    GrowingResult L b frame (hp.cost σ) G σ base m (P.run σ) (run code m) := by
  have ih : ProgSound L b frame F G P code := by
    clear h hcap ha σ base m
    induction hp using ProgFrag.rec (motive_1 := fun _ _ _ _ _ => True)
    case nil F => exact nil_sound F
    case cons hs hp _ ihp => exact cons_sound hs hp (stmt_sound hs) ihp
    all_goals exact True.intro
  exact ih h hcap ha

/-- Every successful compilation carries a kernel-checked source simulation. -/
theorem compile_correct {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ}
    {P : Prog C Γ Δ} {result : CompiledProg b F P}
    (_hc : compileProg b F P = some result)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) (hcap : b + frameNeedProg P ≤ frame)
    (ha : AllocationInput b frame (result.cert.cost σ) σ base m) :
    GrowingResult L b frame (result.cert.cost σ) result.frag σ base m (P.run σ) (run result.code m) :=
  result.cert.correct h hcap ha

end Solidity.Evm.Memory
