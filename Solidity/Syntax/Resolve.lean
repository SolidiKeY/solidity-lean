import Solidity.Syntax.Core

/-!
# Names to positions, and back

The bridge between `Syntax.lean`'s statements, whose locals are names, and
the scoped ones of `Syntax/Core.lean`, whose locals are positions
(`docs/intrinsic.md`, M2).

`erase` forgets the scopes: a position becomes the name its binder gave it
(`Idx.name`, from the names `ns` kept beside the context, innermost first),
and a block `{ … }` becomes its statements.  `Syntax.lean`'s programs are
flat (the elaborator writes no block), so `erase` is the identity on them.

`resolve` goes the other way, from a context of named locals `NCtx`
(innermost first).  A name is the newest local of that name
(`NCtx.find`), which must have the type its use needs; the branches of an
`if` and of a `try`, a loop's body and a call's body are scopes, so what
they declare is not seen after them.  A call's body is read in its own frame:
the parameters (each argument read in the caller's context, and none reading
a parameter), then its return variables — the one assigned to the caller
(`CallRet.val`), the tuple's (`rets`), or a memory return, which the
elaborator declares at the head of the body (`Person memory mv2;`) and
`resolve` moves into the frame (`CallRet.mem`), leaving it to the statement
after the call.  `erase` puts it back.

Each `resolve` returns its result with the proof that it erases to its
input, so `resolve_erase` holds by construction.  The elaborator's entry
points run `Prog.resolveCheck` on every block they produce
(`Syntax/Splice.lean`): that is the locals check, and its error names the
innermost statement it rejects and the local.
-/

namespace Solidity.Core

variable {C : Contract}

/-! ## Erasure -/

section Erase

def Simple.erase {Γ : Ctx} {p : PrimTy} (ns : List Var) : Simple C Γ p → Solidity.Simple C p
  | .lit n h => .lit n h
  | .bool b => .bool b
  | .local i => .local (i.name ns)
  | .env k hp => .env k hp

mutual

def SPath.erase {Γ : Ctx} (ns : List Var) {T : Ty} : SPath C Γ T → Solidity.SPath C T
  | .alias i => .alias (i.name ns)
  | .loc l => .loc (l.erase ns)

def Loc.erase {Γ : Ctx} (ns : List Var) {T : Ty} : Loc C Γ T → Solidity.Loc C T
  | .root r h => .root r h
  | .field b f h => .field (b.erase ns) f h
  | .index it b i => .index it (b.erase ns) (i.erase ns)

def MPath.erase {Γ : Ctx} (ns : List Var) {T : Ty} : MPath C Γ T → Solidity.MPath C T
  | .var i hm => .var (i.name ns) hm
  | .loc l => .loc (l.erase ns)

def MLoc.erase {Γ : Ctx} (ns : List Var) {T : Ty} : MLoc C Γ T → Solidity.MLoc C T
  | .field b f h => .field (b.erase ns) f h
  | .index a b i => .index a (b.erase ns) (i.erase ns)

def Val.erase {Γ : Ctx} (ns : List Var) {p : PrimTy} : Val C Γ p → Solidity.Val C p
  | .simple s => .simple (s.erase ns)
  | .read l => .read (l.erase ns)
  | .binop op h hq a b => .binop op h hq (a.erase ns) (b.erase ns)
  | .unop op h hq a => .unop op h hq (a.erase ns)
  | .ternary c a b => .ternary (c.erase ns) (a.erase ns) (b.erase ns)
  | .readMem l => .readMem (l.erase ns)
  | .len b hp => .len (b.erase ns) hp
  | .mlen b hp => .mlen (b.erase ns) hp

end

def Src.erase {Γ : Ctx} (ns : List Var) {T : Ty} : Src C Γ T → Solidity.Src C T
  | .val v => .val (v.erase ns)
  | .copy p h => .copy (p.erase ns) h

def ARhs.erase {Γ : Ctx} (ns : List Var) {R : RefTy} : ARhs C Γ R → Solidity.ARhs C R
  | .path p => .path (p.erase ns)
  | .push b hd => .push (b.erase ns) hd

def MRhs.erase {Γ : Ctx} (ns : List Var) {R : RefTy} : MRhs C Γ R → Solidity.MRhs C R
  | .alias p => .alias (p.erase ns)
  | .copy p hm => .copy (p.erase ns) hm
  | .newArr n h => .newArr (n.erase ns) h

def NewLhs.erase {Γ : Ctx} (ns : List Var) {R : RefTy} : NewLhs C Γ R → Solidity.NewLhs C R
  | .store l => .store (l.erase ns)
  | .mem l => .mem (l.erase ns)

def MSrc.erase {Γ : Ctx} (ns : List Var) {T : Ty} : MSrc C Γ T → Solidity.MSrc C T
  | .val v => .val (v.erase ns)
  | .ref p => .ref (p.erase ns)

def OpLoc.erase {Γ : Ctx} (ns : List Var) {p : PrimTy} : OpLoc C Γ p → Solidity.OpLoc C p
  | .local i => .local (i.name ns)
  | .root r h => .root r h
  | .field b f h => .field (b.erase ns) f h
  | .index it b i => .index it (b.erase ns) (i.erase ns)
  | .mfield b f h => .mfield (b.erase ns) f h
  | .mindex a b i => .mindex a (b.erase ns) (i.erase ns)

theorem SPath.isSimple_erase {Γ : Ctx} (ns : List Var) {T : Ty} (b : SPath C Γ T) :
    (b.erase ns).isSimple = b.isSimple := by
  rcases b with _ | (_ | _ | _) <;> rfl

theorem MPath.isSimple_erase {Γ : Ctx} (ns : List Var) {T : Ty} (b : MPath C Γ T) :
    (b.erase ns).isSimple = b.isSimple := by
  cases b <;> rfl

theorem OpLoc.recvSimple_erase {Γ : Ctx} (ns : List Var) {p : PrimTy} (l : OpLoc C Γ p) :
    (l.erase ns).recvSimple = l.recvSimple := by
  cases l <;> first | rfl | exact SPath.isSimple_erase ns _ | exact MPath.isSimple_erase ns _

/-- An external call's argument, erased. -/
def ExtArg.erase {Γ : Ctx} (ns : List Var) (a : ExtArg C Γ) : Solidity.ExtArg C :=
  ⟨a.1, a.2.erase ns⟩

def ExtCall.erase {Γ : Ctx} (ns : List Var) (c : ExtCall C Γ) : Solidity.ExtCall C :=
  ⟨c.addr.erase ns, c.fn, c.args.map (ExtArg.erase ns)⟩

def LoopAnn.erase {Γ : Ctx} (ns : List Var) : LoopAnn C Γ → Solidity.LoopAnn C
  | .unwind k => .unwind k
  | .inv I dec => .inv (I.erase ns) (dec.map (Val.erase ns))

/-- The arguments in order, each with its parameter. -/
def Args.erase {Γ : Ctx} (ns : List Var) : {ps : Ctx} → Args C Γ ps → List (Arg C)
  | _, .nil => []
  | _, .snoc as p x e => as.erase ns ++ [⟨p, x, e.erase ns⟩]

/-- What the call returns, as `Syntax.lean` writes it: a memory return is
`CallRet.none`, its return variable declared by the body (`CallRet.pre`). -/
def CallRet.erase {Γ : Ctx} (ns : List Var) : {rs Γ' : Ctx} → CallRet Γ rs Γ' → Solidity.CallRet
  | _, _, .none => .none
  | _, _, .val p r res => .val p r (res.map (Idx.name ns))
  | _, _, .rets bs => .rets bs.toList
  | _, _, .mem .. => .none

/-- The statements a call's erased body starts with: a memory return's
declaration, a fresh default object. -/
def CallRet.pre {Γ : Ctx} : {rs Γ' : Ctx} → CallRet Γ rs Γ' → List (Solidity.Stmt C)
  | _, _, .mem R r hd hm => [.declMem R r Option.none hd hm]
  | _, _, _ => []

def CodeBinder.toOption {κ : Ctx} : CodeBinder κ → Option Var
  | .none => Option.none
  | .some x => Option.some x

mutual

/-- A statement as `Syntax.lean` writes it, from the names `ns` of its
context: a block is its statements.  A call whose arguments are not
separated (`Arg.separatedFrom`), which `resolve` never returns, binds them
at the head of its body instead. -/
def Stmt.erase {Γ Γ' : Ctx} (ns : List Var) : Stmt C Γ Γ' → List (Solidity.Stmt C)
  | .assign l r => [.assign (l.erase ns) (r.erase ns)]
  | .rebind i r => [.rebind (i.name ns) (r.erase ns)]
  | .assignLocal i r => [.assignLocal (i.name ns) (r.erase ns)]
  | .declLocal p x init => [.declLocal p x (init.map (Val.erase ns))]
  | .declStorage R x init => [.declStorage R x (init.map (ARhs.erase ns))]
  | .opAssign op hop hp l r => [.opAssign op hop hp (l.erase ns) (r.erase ns)]
  | .incDec op hp l => [.incDec op hp (l.erase ns)]
  | .assignIncDec i op hp l hs =>
    [.assignIncDec (i.name ns) op hp (l.erase ns) ((OpLoc.recvSimple_erase ns l).trans hs)]
  | .push b v hd =>
    [.push (b.erase ns) (v.map (Src.erase ns)) (by rw [Option.isSome_map]; exact hd)]
  | .pop b => [.pop (b.erase ns)]
  | .transfer r a => [.transfer (r.erase ns) (a.erase ns)]
  | .send pv r a => [.send (pv.name ns) (r.erase ns) (a.erase ns)]
  | .declMem R x init hd hm =>
    [.declMem R x (init.map (MRhs.erase ns)) (by rw [Option.isSome_map]; exact hd) hm]
  | .rebindMem i r => [.rebindMem (i.name ns) (r.erase ns)]
  | .assignFromMem l p => [.assignFromMem (l.erase ns) (p.erase ns)]
  | .assignMem l r => [.assignMem (l.erase ns) (r.erase ns)]
  | .delete l => [.delete (l.erase ns)]
  | .deleteMem p hd => [.deleteMem (p.erase ns) hd]
  | .assignNew l n h => [.assignNew (l.erase ns) (n.erase ns) h]
  | .ite c thn els => [.ite (c.erase ns) (thn.erase ns) (els.erase ns)]
  | .require c => [.require (c.erase ns)]
  | .assert c => [.assert (c.erase ns)]
  | .revert => [.revert]
  | .call f args ret body =>
    let as := args.erase ns
    let b := ret.pre ++ body.erase (ret.names ++ args.names)
    if h : Arg.separatedFrom [] as = true then [.call f as h (ret.erase ns) b]
    else [.call f [] rfl (ret.erase ns) (as.map Arg.decl ++ b)]
  | .tryCall c rets ok err code pnc other =>
    [.tryCall (c.erase ns) rets.toList (ok.erase (rets.names ++ ns)) (err.erase ns)
      code.toOption (pnc.erase (code.names ++ ns)) (other.erase ns)]
  | .loop a c body => [.loop (a.erase ns) (c.erase ns) (body.erase ns)]
  | .block body => body.erase ns

/-- A block as `Syntax.lean` writes it: each statement erased from the names
the one before it leaves. -/
def Prog.erase {Γ Γ' : Ctx} (ns : List Var) : Prog C Γ Γ' → List (Solidity.Stmt C)
  | .nil => []
  | .cons s P => s.erase ns ++ P.erase (s.outNames ns)

end

theorem Stmt.erase_call {Γ Γ' ps rs Γf : Ctx} (ns : List Var) (f : Name) (args : Args C Γ ps)
    (ret : CallRet Γ rs Γ') (body : Prog C (rs ++ ps) Γf)
    (h : Arg.separatedFrom [] (args.erase ns) = true) :
    (Stmt.call f args ret body).erase ns =
      [.call f (args.erase ns) h (ret.erase ns) (ret.pre ++ body.erase (ret.names ++ args.names))] := by
  simp only [Stmt.erase]
  exact dif_pos h

/-! ### Casts of a context index

`resolve` reads an appended context (`ρ ++ Γ`) as the named context it
builds, which is equal to it but not by definition. -/

/-- A block read in a context equal to its own. -/
def Prog.castIn {Γ₁ Γ₂ Δ : Ctx} (h : Γ₁ = Γ₂) (P : Prog C Γ₁ Δ) : Prog C Γ₂ Δ := h ▸ P

theorem Prog.erase_castIn {Γ₁ Γ₂ Δ : Ctx} (h : Γ₁ = Γ₂) (P : Prog C Γ₁ Δ) (ns : List Var) :
    (P.castIn h).erase ns = P.erase ns := by
  subst h; rfl

/-- A statement leaving a context equal to its own. -/
def Stmt.castOut {Γ Δ₁ Δ₂ : Ctx} (h : Δ₁ = Δ₂) (s : Stmt C Γ Δ₁) : Stmt C Γ Δ₂ := h ▸ s

theorem Stmt.erase_castOut {Γ Δ₁ Δ₂ : Ctx} (h : Δ₁ = Δ₂) (s : Stmt C Γ Δ₁) (ns : List Var) :
    (s.castOut h).erase ns = s.erase ns := by
  subst h; rfl

theorem Stmt.outNames_castOut [FreshNames] {Γ Δ₁ Δ₂ : Ctx} (h : Δ₁ = Δ₂) (s : Stmt C Γ Δ₁)
    (ns : List Var) : (s.castOut h).outNames ns = s.outNames ns := by
  subst h; rfl

mutual
/-- Every call's arguments are separated (`Arg.separatedFrom`) once
erased, in a loop's body and a `try`'s branches too: the calls `erase`
keeps as calls, whose arguments it does not move into the body.  What
`resolve` returns (`Prog.resolve_sepArgs`). -/
def Stmt.sepArgs {Γ Γ' : Ctx} (ns : List Var) : Stmt C Γ Γ' → Bool
  | .call _ args ret body =>
    Arg.separatedFrom [] (args.erase ns) && Prog.sepArgs (ret.names ++ args.names) body
  | .ite _ t e => Prog.sepArgs ns t && Prog.sepArgs ns e
  | .block body => Prog.sepArgs ns body
  | .tryCall _ rets ok err code pnc other =>
    Prog.sepArgs (rets.names ++ ns) ok && Prog.sepArgs ns err &&
      Prog.sepArgs (code.names ++ ns) pnc && Prog.sepArgs ns other
  | .loop _ _ body => Prog.sepArgs ns body
  | .assign .. | .rebind .. | .assignLocal .. | .declLocal .. | .declStorage .. | .opAssign ..
  | .incDec .. | .assignIncDec .. | .push .. | .pop _ | .transfer .. | .send .. | .declMem ..
  | .rebindMem .. | .assignFromMem .. | .assignMem .. | .delete _ | .deleteMem .. | .assignNew ..
  | .require _ | .assert _ | .revert => true
def Prog.sepArgs {Γ Γ' : Ctx} (ns : List Var) : Prog C Γ Γ' → Bool
  | .nil => true
  | .cons s P => Stmt.sepArgs ns s && Prog.sepArgs (s.outNames ns) P
end

theorem Prog.sepArgs_castIn {Γ₁ Γ₂ Δ : Ctx} (h : Γ₁ = Γ₂) (P : Prog C Γ₁ Δ) (ns : List Var) :
    (P.castIn h).sepArgs ns = P.sepArgs ns := by
  subst h; rfl

theorem Stmt.sepArgs_castOut {Γ Δ₁ Δ₂ : Ctx} (h : Δ₁ = Δ₂) (s : Stmt C Γ Δ₁) (ns : List Var) :
    (s.castOut h).sepArgs ns = s.sepArgs ns := by
  subst h; rfl

mutual

/-- No binder of the statement reuses a name in scope (`ns`) or of an
enclosing frame (`out`), and a call's arguments are separated: what makes
the untyped run, one map from names to bindings, follow the scoped one
(`Semantics/RunErase.lean`).  What `resolve` returns (`Prog.resolve_fresh`). -/
def Stmt.Fresh (out : List Var) : {Γ Γ' : Ctx} → List Var → Stmt C Γ Γ' → Prop
  | _, _, ns, .declLocal _ x _ => x ∉ ns ∧ x ∉ out
  | _, _, ns, .declStorage _ x _ => x ∉ ns ∧ x ∉ out
  | _, _, ns, .declMem _ x .. => x ∉ ns ∧ x ∉ out
  | _, _, ns, .ite _ thn els => Prog.Fresh out ns thn ∧ Prog.Fresh out ns els
  | _, _, ns, .call _ args ret body =>
    (ret.names ++ args.names).Nodup ∧ (∀ y ∈ ret.names ++ args.names, y ∉ ns ∧ y ∉ out) ∧
      Arg.separatedFrom [] (args.erase ns) = true ∧
      Prog.Fresh (ns ++ out) (ret.names ++ args.names) body
  | _, _, ns, .tryCall _ rets ok err code pnc other =>
    rets.names.Nodup ∧ (∀ y ∈ rets.names, y ∉ ns ∧ y ∉ out) ∧ Prog.Fresh out (rets.names ++ ns) ok ∧
      Prog.Fresh out ns err ∧ (∀ y ∈ code.names, y ∉ ns ∧ y ∉ out) ∧
      Prog.Fresh out (code.names ++ ns) pnc ∧ Prog.Fresh out ns other
  | _, _, ns, .loop _ _ body => Prog.Fresh out ns body
  | _, _, ns, .block body => Prog.Fresh out ns body
  | _, _, _, .assign .. | _, _, _, .rebind .. | _, _, _, .assignLocal .. | _, _, _, .opAssign ..
  | _, _, _, .incDec .. | _, _, _, .assignIncDec .. | _, _, _, .push .. | _, _, _, .pop ..
  | _, _, _, .transfer .. | _, _, _, .send .. | _, _, _, .rebindMem .. | _, _, _, .assignFromMem ..
  | _, _, _, .assignMem .. | _, _, _, .delete .. | _, _, _, .deleteMem .. | _, _, _, .assignNew ..
  | _, _, _, .require .. | _, _, _, .assert .. | _, _, _, .revert => True

def Prog.Fresh (out : List Var) : {Γ Γ' : Ctx} → List Var → Prog C Γ Γ' → Prop
  | _, _, _, .nil => True
  | _, _, ns, .cons s P => Stmt.Fresh out ns s ∧ Prog.Fresh out (s.outNames ns) P

end

theorem Prog.fresh_castIn {Γ₁ Γ₂ Δ : Ctx} (h : Γ₁ = Γ₂) (P : Prog C Γ₁ Δ) (out ns : List Var) :
    (P.castIn h).Fresh out ns ↔ P.Fresh out ns := by
  subst h; rfl

theorem Stmt.fresh_castOut {Γ Δ₁ Δ₂ : Ctx} (h : Δ₁ = Δ₂) (s : Stmt C Γ Δ₁) (out ns : List Var) :
    (s.castOut h).Fresh out ns ↔ s.Fresh out ns := by
  subst h; rfl

end Erase

/-! ## Named contexts -/

/-- Named locals, innermost first: a context with its names beside it. -/
abbrev NCtx := List (Var × LTy)

/-- The types. -/
abbrev NCtx.ctx (Γ : NCtx) : Ctx := Γ.map (·.2)

/-- The names. -/
abbrev NCtx.names (Γ : NCtx) : List Var := Γ.map (·.1)

theorem NCtx.ctx_append (A B : NCtx) : (A ++ B).ctx = A.ctx ++ B.ctx := List.map_append

theorem NCtx.names_append (A B : NCtx) : (A ++ B).names = A.names ++ B.names := List.map_append

/-- How a declaration writes the type: `uint`, `Person storage`, `Person memory`. -/
def LTy.toStr : LTy → String
  | .val p => p.toStr
  | .alias R => s!"{Ty.ref R} storage"
  | .mem R => s!"{Ty.ref R} memory"
  | .old => "storage"
  | .oldNet => "ledger"

/-- The newest local named `x`, which must be of type `t`. -/
def NCtx.find [FreshNames] (x : Var) (t : LTy) :
    (Γ : NCtx) → Except String {i : Idx Γ.ctx t // i.name Γ.names = x}
  | [] => .error s!"{x} is not declared"
  | (y, u) :: Γ =>
    if hy : y = x then
      if hu : u = t then by subst hu hy; exact .ok ⟨.here, rfl⟩
      else .error s!"{x} is declared as {u.toStr}, used as {t.toStr}"
    else
      match NCtx.find x t Γ with
      | .ok ⟨i, h⟩ => .ok ⟨.there i, h⟩
      | .error e => .error e

/-- The binders as a named context. -/
def Binders.nctx {ρ : Ctx} : Binders ρ → NCtx
  | .nil => []
  | .snoc bs p x => (x, .val p) :: bs.nctx

theorem Binders.nctx_ctx {ρ : Ctx} (bs : Binders ρ) : bs.nctx.ctx = ρ := by
  induction bs with
  | nil => rfl
  | snoc bs p x ih => exact congrArg (List.cons _) ih

theorem Binders.nctx_names {ρ : Ctx} (bs : Binders ρ) : bs.nctx.names = bs.names := by
  induction bs with
  | nil => rfl
  | snoc bs p x ih => exact congrArg (List.cons _) ih

/-- `bs` with the locals `l` bound after it, in order. -/
def Binders.snocAll {ρ : Ctx} (bs : Binders ρ) : List (PrimTy × Var) → (ρ' : Ctx) × Binders ρ'
  | [] => ⟨ρ, bs⟩
  | (p, x) :: l => (bs.snoc p x).snocAll l

theorem Binders.toList_snocAll {ρ : Ctx} (bs : Binders ρ) (l : List (PrimTy × Var)) :
    (bs.snocAll l).2.toList = bs.toList ++ l := by
  induction l generalizing ρ with
  | nil => exact (List.append_nil _).symm
  | cons a l ih =>
    obtain ⟨p, x⟩ := a
    rw [snocAll, ih]
    simp only [toList, List.append_assoc, List.cons_append, List.nil_append]

/-- The locals `l` bound in order. -/
def Binders.ofList (l : List (PrimTy × Var)) : (ρ : Ctx) × Binders ρ := Binders.nil.snocAll l

theorem Binders.toList_ofList (l : List (PrimTy × Var)) : (Binders.ofList l).2.toList = l :=
  (Binders.toList_snocAll .nil l).trans (List.nil_append l)

def CodeBinder.ofOption : Option Var → (κ : Ctx) × CodeBinder κ
  | Option.none => ⟨[], .none⟩
  | Option.some x => ⟨[.val .uint], .some x⟩

def CodeBinder.nctx {κ : Ctx} : CodeBinder κ → NCtx
  | .none => []
  | .some x => [(x, .val .uint)]

theorem CodeBinder.nctx_ctx {κ : Ctx} (c : CodeBinder κ) : c.nctx.ctx = κ := by
  cases c <;> rfl

theorem CodeBinder.nctx_names {κ : Ctx} (c : CodeBinder κ) : c.nctx.names = c.names := by
  cases c <;> rfl

theorem CodeBinder.toOption_ofOption (o : Option Var) : (CodeBinder.ofOption o).2.toOption = o := by
  cases o <;> rfl

/-! ## Resolution -/

section Resolve

variable [FreshNames]

/-- An optional part resolved. -/
def resolveOpt {α β : Type} (er : α → β) (f : (b : β) → Except String {a : α // er a = b}) :
    (o : Option β) → Except String {o' : Option α // o'.map er = o}
  | Option.none => pure ⟨Option.none, rfl⟩
  | Option.some b => do
    let ⟨a, h⟩ ← f b
    pure ⟨Option.some a, congrArg Option.some h⟩

/-- A list of parts resolved. -/
def resolveList {α β : Type} (er : α → β) (f : (b : β) → Except String {a : α // er a = b}) :
    (l : List β) → Except String {l' : List α // l'.map er = l}
  | [] => pure ⟨[], rfl⟩
  | b :: l => do
    let ⟨a, h⟩ ← f b
    let ⟨l', h'⟩ ← resolveList er f l
    pure ⟨a :: l', by rw [List.map_cons, h, h']⟩

def resolveSimple (Γ : NCtx) {p : PrimTy} :
    (u : Solidity.Simple C p) → Except String {s : Simple C Γ.ctx p // s.erase Γ.names = u}
  | .lit n h => pure ⟨.lit n h, rfl⟩
  | .bool b => pure ⟨.bool b, rfl⟩
  | .local x => do
    let ⟨i, h⟩ ← Γ.find x (.val p)
    pure ⟨.local i, by subst h; rfl⟩
  | .env k hp => pure ⟨.env k hp, rfl⟩

mutual

def resolveSPath (Γ : NCtx) {T : Ty} :
    (u : Solidity.SPath C T) → Except String {s : SPath C Γ.ctx T // s.erase Γ.names = u}
  | .alias (R := R) x => do
    let ⟨i, h⟩ ← Γ.find x (.alias R)
    pure ⟨.alias i, by subst h; rfl⟩
  | .loc l => do
    let ⟨l', h⟩ ← resolveLoc Γ l
    pure ⟨.loc l', by subst h; rfl⟩

def resolveLoc (Γ : NCtx) {T : Ty} :
    (u : Solidity.Loc C T) → Except String {s : Loc C Γ.ctx T // s.erase Γ.names = u}
  | .root r h => pure ⟨.root r h, rfl⟩
  | .field b f h => do
    let ⟨b', hb⟩ ← resolveSPath Γ b
    pure ⟨.field b' f h, by subst hb; rfl⟩
  | .index it b i => do
    let ⟨b', hb⟩ ← resolveSPath Γ b
    let ⟨i', hi⟩ ← resolveVal Γ i
    pure ⟨.index it b' i', by subst hb hi; rfl⟩

def resolveMPath (Γ : NCtx) {T : Ty} :
    (u : Solidity.MPath C T) → Except String {s : MPath C Γ.ctx T // s.erase Γ.names = u}
  | .var (R := R) x hm => do
    let ⟨i, h⟩ ← Γ.find x (.mem R)
    pure ⟨.var i hm, by subst h; rfl⟩
  | .loc l => do
    let ⟨l', h⟩ ← resolveMLoc Γ l
    pure ⟨.loc l', by subst h; rfl⟩

def resolveMLoc (Γ : NCtx) {T : Ty} :
    (u : Solidity.MLoc C T) → Except String {s : MLoc C Γ.ctx T // s.erase Γ.names = u}
  | .field b f h => do
    let ⟨b', hb⟩ ← resolveMPath Γ b
    pure ⟨.field b' f h, by subst hb; rfl⟩
  | .index a b i => do
    let ⟨b', hb⟩ ← resolveMPath Γ b
    let ⟨i', hi⟩ ← resolveVal Γ i
    pure ⟨.index a b' i', by subst hb hi; rfl⟩

def resolveVal (Γ : NCtx) {p : PrimTy} :
    (u : Solidity.Val C p) → Except String {s : Val C Γ.ctx p // s.erase Γ.names = u}
  | .simple s => do
    let ⟨s', h⟩ ← resolveSimple Γ s
    pure ⟨.simple s', by subst h; rfl⟩
  | .read l => do
    let ⟨l', h⟩ ← resolveLoc Γ l
    pure ⟨.read l', by subst h; rfl⟩
  | .binop op h hq a b => do
    let ⟨a', ha⟩ ← resolveVal Γ a
    let ⟨b', hb⟩ ← resolveVal Γ b
    pure ⟨.binop op h hq a' b', by subst ha hb; rfl⟩
  | .unop op h hq a => do
    let ⟨a', ha⟩ ← resolveVal Γ a
    pure ⟨.unop op h hq a', by subst ha; rfl⟩
  | .ternary c a b => do
    let ⟨c', hc⟩ ← resolveVal Γ c
    let ⟨a', ha⟩ ← resolveVal Γ a
    let ⟨b', hb⟩ ← resolveVal Γ b
    pure ⟨.ternary c' a' b', by subst hc ha hb; rfl⟩
  | .readMem l => do
    let ⟨l', h⟩ ← resolveMLoc Γ l
    pure ⟨.readMem l', by subst h; rfl⟩
  | .len b hp => do
    let ⟨b', h⟩ ← resolveSPath Γ b
    pure ⟨.len b' hp, by subst h; rfl⟩
  | .mlen b hp => do
    let ⟨b', h⟩ ← resolveMPath Γ b
    pure ⟨.mlen b' hp, by subst h; rfl⟩

end

def resolveSrc (Γ : NCtx) {T : Ty} :
    (u : Solidity.Src C T) → Except String {s : Src C Γ.ctx T // s.erase Γ.names = u}
  | .val v => do
    let ⟨v', h⟩ ← resolveVal Γ v
    pure ⟨.val v', by subst h; rfl⟩
  | .copy p hm => do
    let ⟨p', h⟩ ← resolveSPath Γ p
    pure ⟨.copy p' hm, by subst h; rfl⟩

def resolveARhs (Γ : NCtx) {R : RefTy} :
    (u : Solidity.ARhs C R) → Except String {s : ARhs C Γ.ctx R // s.erase Γ.names = u}
  | .path p => do
    let ⟨p', h⟩ ← resolveSPath Γ p
    pure ⟨.path p', by subst h; rfl⟩
  | .push b hd => do
    let ⟨b', h⟩ ← resolveSPath Γ b
    pure ⟨.push b' hd, by subst h; rfl⟩

def resolveMRhs (Γ : NCtx) {R : RefTy} :
    (u : Solidity.MRhs C R) → Except String {s : MRhs C Γ.ctx R // s.erase Γ.names = u}
  | .alias p => do
    let ⟨p', h⟩ ← resolveMPath Γ p
    pure ⟨.alias p', by subst h; rfl⟩
  | .copy p hm => do
    let ⟨p', h⟩ ← resolveSPath Γ p
    pure ⟨.copy p' hm, by subst h; rfl⟩
  | .newArr n hn => do
    let ⟨n', h⟩ ← resolveSimple Γ n
    pure ⟨.newArr n' hn, by subst h; rfl⟩

def resolveNewLhs (Γ : NCtx) {R : RefTy} :
    (u : Solidity.NewLhs C R) → Except String {s : NewLhs C Γ.ctx R // s.erase Γ.names = u}
  | .store l => do
    let ⟨l', h⟩ ← resolveLoc Γ l
    pure ⟨.store l', by subst h; rfl⟩
  | .mem l => do
    let ⟨l', h⟩ ← resolveMLoc Γ l
    pure ⟨.mem l', by subst h; rfl⟩

def resolveMSrc (Γ : NCtx) {T : Ty} :
    (u : Solidity.MSrc C T) → Except String {s : MSrc C Γ.ctx T // s.erase Γ.names = u}
  | .val v => do
    let ⟨v', h⟩ ← resolveVal Γ v
    pure ⟨.val v', by subst h; rfl⟩
  | .ref p => do
    let ⟨p', h⟩ ← resolveMPath Γ p
    pure ⟨.ref p', by subst h; rfl⟩

def resolveOpLoc (Γ : NCtx) {p : PrimTy} :
    (u : Solidity.OpLoc C p) → Except String {s : OpLoc C Γ.ctx p // s.erase Γ.names = u}
  | .local x => do
    let ⟨i, h⟩ ← Γ.find x (.val p)
    pure ⟨.local i, by subst h; rfl⟩
  | .root r h => pure ⟨.root r h, rfl⟩
  | .field b f h => do
    let ⟨b', hb⟩ ← resolveSPath Γ b
    pure ⟨.field b' f h, by subst hb; rfl⟩
  | .index it b i => do
    let ⟨b', hb⟩ ← resolveSPath Γ b
    let ⟨i', hi⟩ ← resolveSimple Γ i
    pure ⟨.index it b' i', by subst hb hi; rfl⟩
  | .mfield b f h => do
    let ⟨b', hb⟩ ← resolveMPath Γ b
    pure ⟨.mfield b' f h, by subst hb; rfl⟩
  | .mindex a b i => do
    let ⟨b', hb⟩ ← resolveMPath Γ b
    let ⟨i', hi⟩ ← resolveSimple Γ i
    pure ⟨.mindex a b' i', by subst hb hi; rfl⟩

def resolveExtCall (Γ : NCtx) (u : Solidity.ExtCall C) :
    Except String {c : ExtCall C Γ.ctx // c.erase Γ.names = u} := do
  let ⟨a, ha⟩ ← resolveSimple Γ u.addr
  let ⟨as, has⟩ ← resolveList (ExtArg.erase Γ.names)
    (fun (b : Solidity.ExtArg C) => do
      let ⟨s, h⟩ ← resolveSimple Γ b.2
      pure ⟨⟨b.1, s⟩, by simp only [ExtArg.erase, h]⟩) u.args
  pure ⟨⟨a, u.fn, as⟩, by simp only [ExtCall.erase, ha, has]⟩

def resolveLoopAnn (Γ : NCtx) :
    (u : Solidity.LoopAnn C) → Except String {a : LoopAnn C Γ.ctx // a.erase Γ.names = u}
  | .unwind k => pure ⟨.unwind k, rfl⟩
  | .inv I dec => do
    let ⟨I', hI⟩ ← resolveVal Γ I
    let ⟨dec', hd⟩ ← resolveOpt (Val.erase Γ.names) (resolveVal Γ) dec
    pure ⟨.inv I' dec', by subst hI hd; rfl⟩

/-- A call's arguments after the ones bound in `P` (`as`): each read in the
caller's context `Γ`, at its parameter's type, and none reading a parameter
(the elaborator's are fresh). -/
def resolveArgsFrom (Γ : NCtx) :
    (P : NCtx) → (as : Args C Γ.ctx P.ctx) → P.names = as.names → (l : List (Arg C)) →
    Except String {r : (P' : NCtx) × Args C Γ.ctx P'.ctx //
      r.2.erase Γ.names = as.erase Γ.names ++ l ∧ r.1.names = r.2.names}
  | P, as, hP, [] => pure ⟨⟨P, as⟩, (List.append_nil _).symm, hP⟩
  | P, as, hP, a :: l => do
    if let some y := a.e.vars.find? (P.names.contains ·) then
      throw s!"the argument {a.e.toStr true} reads the parameter {y}"
    let ⟨e, he⟩ ← resolveVal Γ a.e
    let ⟨r, hr, hn⟩ ← resolveArgsFrom Γ ((a.x, .val a.p) :: P) (as.snoc a.p a.x e)
      (congrArg (List.cons a.x) hP) l
    pure ⟨r, by rw [hr]; simp only [Args.erase, he, List.append_assoc, List.singleton_append],
      hn⟩

def resolveArgs (Γ : NCtx) (l : List (Arg C)) :
    Except String {r : (P : NCtx) × Args C Γ.ctx P.ctx //
      r.2.erase Γ.names = l ∧ r.1.names = r.2.names} := do
  let ⟨r, hr, hn⟩ ← resolveArgsFrom Γ [] .nil rfl l
  pure ⟨r, hr.trans (List.nil_append l), hn⟩

/-- An error of statement `u`'s own parts, naming it. -/
def rejects {α : Type} (u : Solidity.Stmt C) (x : Except String α) : Except String α :=
  x.mapError fun why => s!"the locals check (`resolve`) rejects `{u.toStr}`: {why}"

/-- What `resolveStmt` returns for `u` read in `Γ`: the statement, the
context it leaves, and that it erases to `u` and leaves the names it binds. -/
abbrev Resolved (strict : Bool) (out : List Var) (Γ : NCtx) (u : Solidity.Stmt C) :=
  {r : (Γ' : NCtx) × Stmt C Γ.ctx Γ'.ctx //
    r.2.erase Γ.names = [u] ∧ r.1.names = r.2.outNames Γ.names ∧ r.2.sepArgs Γ.names = true ∧
      (strict = true → r.2.Fresh out Γ.names)}

/-- A binder that reuses a name in scope or of an enclosing frame. -/
def redeclared (x : Var) : String :=
  s!"{x} is declared again in its scope (`Prog.Fresh`)"

/-- A frame's names: distinct, and none in scope (`ns`) or of an enclosing
frame (`out`). -/
abbrev FrameFresh (out ns names : List Var) : Prop :=
  names.Nodup ∧ ∀ y ∈ names, y ∉ ns ∧ y ∉ out

/-- Why a frame's names are not fresh. -/
def frameMsg (names : List Var) : String :=
  s!"a frame binding {names} reuses a name, or one in scope (`Prog.Fresh`)"

mutual

/-- `u` read in `Γ`, inside the frames whose names are `out`.  `strict`: refused
when a binder reuses a name in scope or of an enclosing frame, so that what
it returns is `Fresh`; a formula's program may shadow what the formula binds
(a `∀`, an update), and is read with `strict` off. -/
def resolveStmt (strict : Bool) (out : List Var) (Γ : NCtx) :
    (u : Solidity.Stmt C) → Except String (Resolved strict out Γ u)
  | .assign l r => rejects (.assign l r) do
    let ⟨l', hl⟩ ← resolveLoc Γ l
    let ⟨r', hr⟩ ← resolveSrc Γ r
    pure ⟨⟨Γ, .assign l' r'⟩, by subst hl hr; exact ⟨rfl, rfl, rfl, fun _ => trivial⟩⟩
  | .rebind (R := R) x r => rejects (.rebind x r) do
    let ⟨i, hi⟩ ← Γ.find x (.alias R)
    let ⟨r', hr⟩ ← resolveARhs Γ r
    pure ⟨⟨Γ, .rebind i r'⟩, by subst hi hr; exact ⟨rfl, rfl, rfl, fun _ => trivial⟩⟩
  | .assignLocal (p := p) x r => rejects (.assignLocal x r) do
    let ⟨i, hi⟩ ← Γ.find x (.val p)
    let ⟨r', hr⟩ ← resolveVal Γ r
    pure ⟨⟨Γ, .assignLocal i r'⟩, by subst hi hr; exact ⟨rfl, rfl, rfl, fun _ => trivial⟩⟩
  | .declLocal p x init => rejects (.declLocal p x init) do
    let ⟨init', h⟩ ← resolveOpt (Val.erase Γ.names) (resolveVal Γ) init
    if hx : strict = true → x ∉ Γ.names ∧ x ∉ out then
      pure ⟨⟨(x, .val p) :: Γ, .declLocal p x init'⟩, by subst h; exact ⟨rfl, rfl, rfl, hx⟩⟩
    else throw (redeclared x)
  | .declStorage R x init => rejects (.declStorage R x init) do
    let ⟨init', h⟩ ← resolveOpt (ARhs.erase Γ.names) (resolveARhs Γ) init
    if hx : strict = true → x ∉ Γ.names ∧ x ∉ out then
      pure ⟨⟨(x, .alias R) :: Γ, .declStorage R x init'⟩, by subst h; exact ⟨rfl, rfl, rfl, hx⟩⟩
    else throw (redeclared x)
  | .opAssign op hop hp l r => rejects (.opAssign op hop hp l r) do
    let ⟨l', hl⟩ ← resolveOpLoc Γ l
    let ⟨r', hr⟩ ← resolveVal Γ r
    pure ⟨⟨Γ, .opAssign op hop hp l' r'⟩, by subst hl hr; exact ⟨rfl, rfl, rfl, fun _ => trivial⟩⟩
  | .incDec op hp l => rejects (.incDec op hp l) do
    let ⟨l', hl⟩ ← resolveOpLoc Γ l
    pure ⟨⟨Γ, .incDec op hp l'⟩, by subst hl; exact ⟨rfl, rfl, rfl, fun _ => trivial⟩⟩
  | .assignIncDec (p := p) x op hp l hs => rejects (.assignIncDec x op hp l hs) do
    let ⟨i, hi⟩ ← Γ.find x (.val p)
    let ⟨l', hl⟩ ← resolveOpLoc Γ l
    have hs' : l'.recvSimple = true := by
      rw [← OpLoc.recvSimple_erase Γ.names l', hl]; exact hs
    pure ⟨⟨Γ, .assignIncDec i op hp l' hs'⟩, by subst hi hl; exact ⟨rfl, rfl, rfl, fun _ => trivial⟩⟩
  | .push b v hd => rejects (.push b v hd) do
    let ⟨b', hb⟩ ← resolveSPath Γ b
    let ⟨v', hv⟩ ← resolveOpt (Src.erase Γ.names) (resolveSrc Γ) v
    have hd' : (v'.isSome || _) = true := by rw [← Option.isSome_map (f := Src.erase Γ.names), hv]; exact hd
    pure ⟨⟨Γ, .push b' v' hd'⟩, by subst hb hv; exact ⟨rfl, rfl, rfl, fun _ => trivial⟩⟩
  | .pop b => rejects (.pop b) do
    let ⟨b', hb⟩ ← resolveSPath Γ b
    pure ⟨⟨Γ, .pop b'⟩, by subst hb; exact ⟨rfl, rfl, rfl, fun _ => trivial⟩⟩
  | .transfer r a => rejects (.transfer r a) do
    let ⟨r', hr⟩ ← resolveVal Γ r
    let ⟨a', ha⟩ ← resolveVal Γ a
    pure ⟨⟨Γ, .transfer r' a'⟩, by subst hr ha; exact ⟨rfl, rfl, rfl, fun _ => trivial⟩⟩
  | .send pv r a => rejects (.send pv r a) do
    let ⟨i, hi⟩ ← Γ.find pv (.val .bool)
    let ⟨r', hr⟩ ← resolveVal Γ r
    let ⟨a', ha⟩ ← resolveVal Γ a
    pure ⟨⟨Γ, .send i r' a'⟩, by subst hi hr ha; exact ⟨rfl, rfl, rfl, fun _ => trivial⟩⟩
  | .declMem R x init hd hm => rejects (.declMem R x init hd hm) do
    let ⟨init', h⟩ ← resolveOpt (MRhs.erase Γ.names) (resolveMRhs Γ) init
    have hd' : (init'.isSome || _) = true := by
      rw [← Option.isSome_map (f := MRhs.erase Γ.names), h]; exact hd
    if hx : strict = true → x ∉ Γ.names ∧ x ∉ out then
      pure ⟨⟨(x, .mem R) :: Γ, .declMem R x init' hd' hm⟩, by subst h; exact ⟨rfl, rfl, rfl, hx⟩⟩
    else throw (redeclared x)
  | .rebindMem (R := R) x r => rejects (.rebindMem x r) do
    let ⟨i, hi⟩ ← Γ.find x (.mem R)
    let ⟨r', hr⟩ ← resolveMRhs Γ r
    pure ⟨⟨Γ, .rebindMem i r'⟩, by subst hi hr; exact ⟨rfl, rfl, rfl, fun _ => trivial⟩⟩
  | .assignFromMem l p => rejects (.assignFromMem l p) do
    let ⟨l', hl⟩ ← resolveLoc Γ l
    let ⟨p', hp⟩ ← resolveMPath Γ p
    pure ⟨⟨Γ, .assignFromMem l' p'⟩, by subst hl hp; exact ⟨rfl, rfl, rfl, fun _ => trivial⟩⟩
  | .assignMem l r => rejects (.assignMem l r) do
    let ⟨l', hl⟩ ← resolveMLoc Γ l
    let ⟨r', hr⟩ ← resolveMSrc Γ r
    pure ⟨⟨Γ, .assignMem l' r'⟩, by subst hl hr; exact ⟨rfl, rfl, rfl, fun _ => trivial⟩⟩
  | .delete l => rejects (.delete l) do
    let ⟨l', hl⟩ ← resolveLoc Γ l
    pure ⟨⟨Γ, .delete l'⟩, by subst hl; exact ⟨rfl, rfl, rfl, fun _ => trivial⟩⟩
  | .deleteMem p hd => rejects (.deleteMem p hd) do
    let ⟨p', hp⟩ ← resolveMPath Γ p
    pure ⟨⟨Γ, .deleteMem p' hd⟩, by subst hp; exact ⟨rfl, rfl, rfl, fun _ => trivial⟩⟩
  | .assignNew l n h => rejects (.assignNew l n h) do
    let ⟨l', hl⟩ ← resolveNewLhs Γ l
    let ⟨n', hn⟩ ← resolveSimple Γ n
    pure ⟨⟨Γ, .assignNew l' n' h⟩, by subst hl hn; exact ⟨rfl, rfl, rfl, fun _ => trivial⟩⟩
  | .ite c thn els => do
    let ⟨c', hc⟩ ← rejects (.ite c thn els) (resolveVal Γ c)
    let ⟨⟨_, t⟩, ht, hts, htf⟩ ← resolveProg strict out Γ thn
    let ⟨⟨_, e⟩, he, hes, hef⟩ ← resolveProg strict out Γ els
    pure ⟨⟨Γ, .ite c' t e⟩, by
      subst hc ht he
      exact ⟨rfl, rfl, by simp only [Stmt.sepArgs, hts, hes, Bool.and_self], fun h => And.intro (htf h) (hef h)⟩⟩
  | .require c => rejects (.require c) do
    let ⟨c', hc⟩ ← resolveVal Γ c
    pure ⟨⟨Γ, .require c'⟩, by subst hc; exact ⟨rfl, rfl, rfl, fun _ => trivial⟩⟩
  | .assert c => rejects (.assert c) do
    let ⟨c', hc⟩ ← resolveVal Γ c
    pure ⟨⟨Γ, .assert c'⟩, by subst hc; exact ⟨rfl, rfl, rfl, fun _ => trivial⟩⟩
  | .revert => pure ⟨⟨Γ, .revert⟩, rfl, rfl, rfl, fun _ => trivial⟩
  | .call f args hsep ret body => do
    let ⟨⟨P, as⟩, has, hP⟩ ← rejects (.call f args hsep ret body) (resolveArgs Γ args)
    match ret with
    | .none =>
      match body with
      | .declMem R r Option.none hd hm :: rest =>
        -- a memory return: declared by the frame, left to the caller
        if hfr : strict = true → FrameFresh out Γ.names ([r] ++ as.names) then
          let ⟨⟨_, b⟩, hb, hbs, hbf⟩ ← resolveProg strict (Γ.names ++ out) ((r, .mem R) :: P) rest
          pure ⟨⟨(r, .mem R) :: Γ, .call f as (.mem R r hd hm) b⟩, by
            refine ⟨?_, rfl, ?_, ?_⟩
            rotate_left
            · subst has
              simp only [NCtx.names, List.map_cons, hP] at hbs
              simp only [Stmt.sepArgs, hsep, CallRet.names, List.cons_append, List.nil_append, hbs,
                Bool.and_self]
            · subst has
              simp only [NCtx.names, List.map_cons, hP] at hbf
              exact fun h => ⟨(hfr h).1, (hfr h).2, hsep, hbf h⟩
            subst has hb
            rw [Stmt.erase_call _ _ _ _ _ hsep]
            simp only [CallRet.erase, CallRet.pre, CallRet.names, List.cons_append, List.nil_append,
              NCtx.names, List.map_cons, ← hP]⟩
        else throw (frameMsg ([r] ++ as.names))
      | body =>
        if hfr : strict = true → FrameFresh out Γ.names as.names then
          let ⟨⟨_, b⟩, hb, hbs, hbf⟩ ← resolveProg strict (Γ.names ++ out) P body
          pure ⟨⟨Γ, .call f as .none b⟩, by
            refine ⟨?_, rfl, ?_, ?_⟩
            rotate_left
            · subst has
              rw [hP] at hbs
              simp only [Stmt.sepArgs, hsep, CallRet.names, List.nil_append, hbs, Bool.and_self]
            · subst has
              rw [hP] at hbf
              exact fun h => ⟨(hfr h).1, (hfr h).2, hsep, hbf h⟩
            subst has hb
            rw [Stmt.erase_call _ _ _ _ _ hsep]
            simp only [CallRet.erase, CallRet.pre, CallRet.names, List.nil_append, hP]⟩
        else throw (frameMsg as.names)
    | .val p r res =>
      let ⟨res', hres⟩ ← rejects (.call f args hsep (.val p r res) body)
        (resolveOpt (Idx.name Γ.names) (fun y => Γ.find y (.val p)) res)
      if hfr : strict = true → FrameFresh out Γ.names ([r] ++ as.names) then
        let ⟨⟨_, b⟩, hb, hbs, hbf⟩ ← resolveProg strict (Γ.names ++ out) ((r, .val p) :: P) body
        pure ⟨⟨Γ, .call f as (.val p r res') b⟩, by
          refine ⟨?_, rfl, ?_, ?_⟩
          rotate_left
          · subst has
            simp only [NCtx.names, List.map_cons, hP] at hbs
            simp only [Stmt.sepArgs, hsep, CallRet.names, List.cons_append, List.nil_append, hbs,
              Bool.and_self]
          · subst has
            simp only [NCtx.names, List.map_cons, hP] at hbf
            exact fun h => ⟨(hfr h).1, (hfr h).2, hsep, hbf h⟩
          subst has hb hres
          rw [Stmt.erase_call _ _ _ _ _ hsep]
          simp only [CallRet.erase, CallRet.pre, CallRet.names, List.cons_append, List.nil_append,
            NCtx.names, List.map_cons, ← hP]⟩
      else throw (frameMsg ([r] ++ as.names))
    | .rets rs =>
      let ⟨⟨ρ, bs⟩, hbs⟩ : {r : (ρ : Ctx) × Binders ρ // r.2.toList = rs} :=
        ⟨Binders.ofList rs, Binders.toList_ofList rs⟩
      if hfr : strict = true → FrameFresh out Γ.names (bs.names ++ as.names) then
        let ⟨⟨_, b⟩, hb, hbsep, hbf⟩ ← resolveProg strict (Γ.names ++ out) (bs.nctx ++ P) body
        let b' := b.castIn (by rw [NCtx.ctx_append, Binders.nctx_ctx])
        let s := (Stmt.call f as (.rets bs) b').castOut (by rw [NCtx.ctx_append, Binders.nctx_ctx])
        pure ⟨⟨bs.nctx ++ Γ, s⟩, by
          refine ⟨?_, ?_, ?_, ?_⟩
          · subst has hb hbs
            rw [Stmt.erase_castOut, Stmt.erase_call _ _ _ _ _ hsep, Prog.erase_castIn]
            simp only [CallRet.erase, CallRet.pre, CallRet.names, List.nil_append,
              NCtx.names_append, Binders.nctx_names, hP]
          · rw [Stmt.outNames_castOut, NCtx.names_append, Binders.nctx_names]; rfl
          · subst has
            rw [NCtx.names_append, Binders.nctx_names, hP] at hbsep
            simp only [s, b', Stmt.sepArgs_castOut, Stmt.sepArgs, hsep, CallRet.names,
              Prog.sepArgs_castIn, hbsep, Bool.and_self]
          · subst has
            rw [NCtx.names_append, Binders.nctx_names, hP] at hbf
            exact fun h => (Stmt.fresh_castOut _ _ _ _).2
              ⟨(hfr h).1, (hfr h).2, hsep, (Prog.fresh_castIn _ _ _ _).2 (hbf h)⟩⟩
      else throw (frameMsg (bs.names ++ as.names))
  | .tryCall c rets ok err code pnc other => do
    let ⟨c', hc⟩ ← rejects (.tryCall c rets ok err code pnc other) (resolveExtCall Γ c)
    let ⟨⟨ρ, bs⟩, hbs⟩ : {r : (ρ : Ctx) × Binders ρ // r.2.toList = rets} :=
      ⟨Binders.ofList rets, Binders.toList_ofList rets⟩
    let ⟨⟨κ, cb⟩, hcb⟩ : {r : (κ : Ctx) × CodeBinder κ // r.2.toOption = code} :=
      ⟨CodeBinder.ofOption code, CodeBinder.toOption_ofOption code⟩
    if hfr : strict = true → FrameFresh out Γ.names bs.names ∧ ∀ y ∈ cb.names, y ∉ Γ.names ∧ y ∉ out then
      let ⟨⟨_, ok'⟩, hok, hoks, hokf⟩ ← resolveProg strict out (bs.nctx ++ Γ) ok
      let ⟨⟨_, err'⟩, herr, herrs, herrf⟩ ← resolveProg strict out Γ err
      let ⟨⟨_, pnc'⟩, hpnc, hpncs, hpncf⟩ ← resolveProg strict out (cb.nctx ++ Γ) pnc
      let ⟨⟨_, other'⟩, hother, hothers, hotherf⟩ ← resolveProg strict out Γ other
      pure ⟨⟨Γ, .tryCall c' bs (ok'.castIn (by rw [NCtx.ctx_append, Binders.nctx_ctx])) err' cb
          (pnc'.castIn (by rw [NCtx.ctx_append, CodeBinder.nctx_ctx])) other'⟩, by
        refine ⟨?_, rfl, ?_, ?_⟩
        · subst hc herr hother hbs hcb
          simp only [Stmt.erase, Prog.erase_castIn, ← hok, ← hpnc, NCtx.names_append,
            Binders.nctx_names, CodeBinder.nctx_names]
        · rw [NCtx.names_append, Binders.nctx_names] at hoks
          rw [NCtx.names_append, CodeBinder.nctx_names] at hpncs
          simp only [Stmt.sepArgs, Prog.sepArgs_castIn, hoks, herrs, hpncs, hothers, Bool.and_self]
        · rw [NCtx.names_append, Binders.nctx_names] at hokf
          rw [NCtx.names_append, CodeBinder.nctx_names] at hpncf
          exact fun h => ⟨(hfr h).1.1, (hfr h).1.2, (Prog.fresh_castIn _ _ _ _).2 (hokf h), herrf h,
            (hfr h).2, (Prog.fresh_castIn _ _ _ _).2 (hpncf h), hotherf h⟩⟩
    else throw (frameMsg (bs.names ++ cb.names))
  | .loop a c body => do
    let ⟨a', ha⟩ ← rejects (.loop a c body) (resolveLoopAnn Γ a)
    let ⟨c', hc⟩ ← rejects (.loop a c body) (resolveVal Γ c)
    let ⟨⟨_, b⟩, hb, hbs, hbf⟩ ← resolveProg strict out Γ body
    pure ⟨⟨Γ, .loop a' c' b⟩, by
      subst ha hc hb; exact ⟨rfl, rfl, by simp only [Stmt.sepArgs, hbs], hbf⟩⟩

def resolveProg (strict : Bool) (out : List Var) (Γ : NCtx) : (us : List (Solidity.Stmt C)) →
    Except String {r : (Γ' : NCtx) × Prog C Γ.ctx Γ'.ctx //
      r.2.erase Γ.names = us ∧ r.2.sepArgs Γ.names = true ∧ (strict = true → r.2.Fresh out Γ.names)}
  | [] => pure ⟨⟨Γ, .nil⟩, rfl, rfl, fun _ => trivial⟩
  | u :: us => do
    let ⟨⟨Γ₁, s⟩, hs, hn, hss, hsf⟩ ← resolveStmt strict out Γ u
    let ⟨⟨Γ₂, P⟩, hP, hPs, hPf⟩ ← resolveProg strict out Γ₁ us
    pure ⟨⟨Γ₂, .cons s P⟩, by
      refine ⟨?_, ?_, ?_⟩
      · show s.erase Γ.names ++ P.erase (s.outNames Γ.names) = u :: us
        rw [hs, ← hn, hP]; rfl
      · show (s.sepArgs Γ.names && P.sepArgs (s.outNames Γ.names)) = true
        rw [hss, ← hn, hPs]; rfl
      · exact fun h => And.intro (hsf h) (hn ▸ hPf h)⟩

end

/-- **Resolution**: a statement's names read as positions in `Γ`, scopes
explicit, and the context it leaves. -/
def Stmt.resolve (Γ : NCtx) (u : Solidity.Stmt C) (strict : Bool := true) :
    Except String ((Γ' : NCtx) × Stmt C Γ.ctx Γ'.ctx) :=
  (resolveStmt strict [] Γ u).map (·.1)

/-- A block resolved. -/
def Prog.resolve (Γ : NCtx) (us : List (Solidity.Stmt C)) (strict : Bool := true) :
    Except String ((Γ' : NCtx) × Prog C Γ.ctx Γ'.ctx) :=
  (resolveProg strict [] Γ us).map (·.1)

/-- The locals check of the elaborator's entry points: the context a block
leaves, or why it is rejected. -/
def Prog.resolveCheck (Γ : NCtx) (us : List (Solidity.Stmt C)) : Except String NCtx :=
  (resolveProg true [] Γ us).map (·.1.1)

omit [FreshNames] in
private theorem ok_of_map {ε α : Type} {P : α → Prop} {x : Except ε {a : α // P a}} {a : α}
    (h : x.map (·.1) = .ok a) : P a := by
  cases x with
  | error e => cases h
  | ok r =>
    cases h
    exact r.2

/-- **`resolve` inverts `erase`**: a resolved statement erases to the one it
was resolved from. -/
theorem Stmt.resolve_erase {strict : Bool} {Γ Γ' : NCtx} {u : Solidity.Stmt C}
    {s : Stmt C Γ.ctx Γ'.ctx}
    (h : Stmt.resolve Γ u strict = .ok ⟨Γ', s⟩) : s.erase Γ.names = [u] :=
  (ok_of_map (P := fun r : (Γ' : NCtx) × Stmt C Γ.ctx Γ'.ctx =>
    r.2.erase Γ.names = [u] ∧ r.1.names = r.2.outNames Γ.names ∧ r.2.sepArgs Γ.names = true ∧
      (strict = true → r.2.Fresh [] Γ.names)) h).1

theorem Prog.resolve_erase {strict : Bool} {Γ Γ' : NCtx} {us : List (Solidity.Stmt C)}
    {P : Prog C Γ.ctx Γ'.ctx}
    (h : Prog.resolve Γ us strict = .ok ⟨Γ', P⟩) : P.erase Γ.names = us :=
  (ok_of_map (P := fun r : (Γ' : NCtx) × Prog C Γ.ctx Γ'.ctx =>
    r.2.erase Γ.names = us ∧ r.2.sepArgs Γ.names = true ∧
      (strict = true → r.2.Fresh [] Γ.names)) h).1

/-- **`resolve`'s output is `Fresh`**: no binder reuses a name in scope, so
`Prog.run_erase` applies to it. -/
theorem Stmt.resolve_fresh {Γ Γ' : NCtx} {u : Solidity.Stmt C} {s : Stmt C Γ.ctx Γ'.ctx}
    (h : Stmt.resolve Γ u = .ok ⟨Γ', s⟩) : s.Fresh [] Γ.names :=
  (ok_of_map (P := fun r : (Γ' : NCtx) × Stmt C Γ.ctx Γ'.ctx =>
    r.2.erase Γ.names = [u] ∧ r.1.names = r.2.outNames Γ.names ∧ r.2.sepArgs Γ.names = true ∧
      (true = true → r.2.Fresh [] Γ.names)) h).2.2.2 rfl

theorem Prog.resolve_fresh {Γ Γ' : NCtx} {us : List (Solidity.Stmt C)} {P : Prog C Γ.ctx Γ'.ctx}
    (h : Prog.resolve Γ us = .ok ⟨Γ', P⟩) : P.Fresh [] Γ.names :=
  (ok_of_map (P := fun r : (Γ' : NCtx) × Prog C Γ.ctx Γ'.ctx =>
    r.2.erase Γ.names = us ∧ r.2.sepArgs Γ.names = true ∧ (true = true → r.2.Fresh [] Γ.names)) h).2.2 rfl

/-- `resolveCheck` accepts exactly what `resolve` resolves, to the context
it returns (`Prog.resolveCheck_of_resolve` is the converse). -/
theorem Prog.resolve_of_resolveCheck {Γ Γ' : NCtx} {us : List (Solidity.Stmt C)}
    (h : Prog.resolveCheck Γ us = .ok Γ') : ∃ P : Prog C Γ.ctx Γ'.ctx, Prog.resolve Γ us = .ok ⟨Γ', P⟩ := by
  unfold Prog.resolveCheck at h
  unfold Prog.resolve
  cases hr : resolveProg true [] Γ us with
  | error e => rw [hr] at h; cases h
  | ok r =>
    rw [hr] at h
    cases h
    exact ⟨r.1.2, rfl⟩

theorem Prog.resolveCheck_of_resolve {Γ Γ' : NCtx} {us : List (Solidity.Stmt C)}
    {P : Prog C Γ.ctx Γ'.ctx}
    (h : Prog.resolve Γ us = .ok ⟨Γ', P⟩) : Prog.resolveCheck Γ us = .ok Γ' := by
  unfold Prog.resolve at h
  unfold Prog.resolveCheck
  cases hr : resolveProg true [] Γ us with
  | error e => rw [hr] at h; cases h
  | ok r =>
    rw [hr] at h
    have h' : r.1 = ⟨Γ', P⟩ := Except.ok.inj h
    show Except.ok r.1.1 = Except.ok Γ'
    rw [h']

/-- **`resolve` separates every call's arguments**: the calls it returns
erase to calls, not to their arguments bound in the body. -/
theorem Stmt.resolve_sepArgs {strict : Bool} {Γ Γ' : NCtx} {u : Solidity.Stmt C}
    {s : Stmt C Γ.ctx Γ'.ctx}
    (h : Stmt.resolve Γ u strict = .ok ⟨Γ', s⟩) : s.sepArgs Γ.names = true :=
  (ok_of_map (P := fun r : (Γ' : NCtx) × Stmt C Γ.ctx Γ'.ctx =>
    r.2.erase Γ.names = [u] ∧ r.1.names = r.2.outNames Γ.names ∧ r.2.sepArgs Γ.names = true ∧
      (strict = true → r.2.Fresh [] Γ.names)) h).2.2.1

theorem Prog.resolve_sepArgs {strict : Bool} {Γ Γ' : NCtx} {us : List (Solidity.Stmt C)}
    {P : Prog C Γ.ctx Γ'.ctx}
    (h : Prog.resolve Γ us strict = .ok ⟨Γ', P⟩) : P.sepArgs Γ.names = true :=
  (ok_of_map (P := fun r : (Γ' : NCtx) × Prog C Γ.ctx Γ'.ctx =>
    r.2.erase Γ.names = us ∧ r.2.sepArgs Γ.names = true ∧
      (strict = true → r.2.Fresh [] Γ.names)) h).2.1

end Resolve

/-- The elaborator's locals in scope as a named context: `old` is a
specification's storage snapshot.  A name is read as the file's
`FreshNames` spells it (`acc` may be `sp1`). -/
def _root_.Solidity.ECtx.toNCtx [FreshNames] (Γ : ECtx) : NCtx :=
  Γ.map fun (x, t) => (Var.ofName x, match t with
    | .val p _ => .val p
    | .alias R => .alias R
    | .mem R => .mem R
    | .store => .old)

end Solidity.Core
