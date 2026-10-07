import Solidity.Semantics.Core.TypedRun

/-!
# The typed run erases to the scoped run

`Prog.trun_erase` (`docs/intrinsic.md`, "M4 lane", wiring item 4): running
`P` on a typed state `σ` (`Semantics/Core/TypedRun.lean`) and erasing the
state it ends in agrees with running `P` on `σ.erase` with
`Semantics/Core.lean`'s interpreter.  The relation is `TRes.Agrees`: the
same state, the same `revert` or `panic`; a typed `diverge` is matched by any
untyped outcome, since the typed run also diverges on a length past `uint`'s
range (`lenT`), which the untyped run reads as an integer and goes on with.
So the untyped run is never stuck where the typed one ends.

Two programs fall outside, `Prog.bridgeOk` excluding them: an index of a
`mapping(bool => V)`, which the typed run hashes as `0`/`1` (decision 10)
where the untyped one is stuck, and a storage copy at a type with a struct
whose members share a name (`BadDup`), which the typed copy overlays by
position and the untyped one by name (`SVal.overlay_erase`, `TyNodup`).
Both are decided by `Prog.bridgeOk`, so a concrete program checks it by
`rfl`.

Each operation's agreement is one lemma, from the storage and heap ones of
`Semantics/Core/StorageErase.lean` and `Semantics/Core/HeapErase.lean`; the
statements are each `TRun.*` step against its `Run.*` namesake, given its
sub-programs' agreement (`StepAgrees`), and the run is the recursor over
them.
-/

namespace Solidity.Core

open Semantics (Value Seg Halt Res lookupBy setBy ExtKey ExtResult structDef)

variable {C : Contract}

/-! ## Agreement of results -/

/-- A typed result against an untyped one: the value erased, the same
`revert` or `panic`; a typed `diverge` against anything. -/
def TRes.Agrees {α β : Type} (f : α → β) : TRes α → Res β → Prop
  | .ok a, u => u = .ok (f a)
  | .error .revert, u => u = .error .revert
  | .error .panic, u => u = .error .panic
  | .error .diverge, _ => True

namespace TRes.Agrees

variable {α β γ δ : Type} {f : α → β} {g : γ → δ}

theorem pure (a : α) : TRes.Agrees f (.ok a) (.ok (f a)) := rfl

theorem bind {t : TRes α} {u : Res β} (h : TRes.Agrees f t u) {k : α → TRes γ}
    {k' : β → Res δ} (hk : ∀ a, TRes.Agrees g (k a) (k' (f a))) :
    TRes.Agrees g (t >>= k) (u >>= k') := by
  match t, h with
  | .ok a, h => subst h; exact hk a
  | .error .revert, h => subst h; rfl
  | .error .panic, h => subst h; rfl
  | .error .diverge, _ => trivial

theorem map {t : TRes α} {u : Res β} (h : TRes.Agrees f t u) {k : α → γ} {k' : β → δ}
    (hk : ∀ a, k' (f a) = g (k a)) : TRes.Agrees g (k <$> t) (k' <$> u) := by
  match t, h with
  | .ok a, h => subst h; exact congrArg Except.ok (hk a)
  | .error .revert, h => subst h; rfl
  | .error .panic, h => subst h; rfl
  | .error .diverge, _ => trivial

theorem ofOpt (x : Option α) : TRes.Agrees f (TRes.ofOpt x) (toRes f x) := by
  cases x <;> rfl

theorem of_eq {a : α} {u : Res β} (h : u = .ok (f a)) : TRes.Agrees f (.ok a) u := h

/-- A typed result against an untyped one followed by a step that only
converts the value. -/
theorem bind_pure {t : TRes α} {u : Res β} (h : TRes.Agrees f t u) {k' : β → Res δ}
    {g' : α → δ} (hk : ∀ a, k' (f a) = .ok (g' a)) : TRes.Agrees g' t (u >>= k') := by
  match t, h with
  | .ok a, h => subst h; exact hk a
  | .error .revert, h => subst h; rfl
  | .error .panic, h => subst h; rfl
  | .error .diverge, _ => trivial

theorem congr {f' : α → β} {t : TRes α} {u : Res β} (h : TRes.Agrees f t u)
    (hf : ∀ a, f a = f' a) : TRes.Agrees f' t u := by
  match t, h with
  | .ok a, h => subst h; exact congrArg Except.ok (hf a)
  | .error .revert, h => exact h
  | .error .panic, h => exact h
  | .error .diverge, _ => trivial

end TRes.Agrees

/-- A typed result that does not panic (an expression's: it reverts or
diverges only). -/
def TRes.NoPanic {α : Type} (t : TRes α) : Prop := t ≠ .error .panic

theorem ok_bind {ε α β : Type} (a : α) (k : α → Except ε β) :
    (Except.ok a : Except ε α) >>= k = k a := rfl

theorem TRes.NoPanic.bind {α γ : Type} {t : TRes α} (h : t.NoPanic) {k : α → TRes γ}
    (hk : ∀ a, (k a).NoPanic) : (t >>= k).NoPanic := by
  match t with
  | .ok a => exact hk a
  | .error e => exact fun h' => h (by cases h'; rfl)

theorem TRes.NoPanic.ofOpt {α : Type} (x : Option α) : (TRes.ofOpt x).NoPanic := by
  cases x <;> exact fun h => nomatch h

/-! ## Where the bridge holds -/

section BridgeOk

variable {Γ : Ctx}

mutual

/-- No `bool` mapping key on the path. -/
def SPath.bridgeOk : {T : Ty} → SPath C Γ T → Bool
  | _, .alias _ => true
  | _, .loc l => l.bridgeOk

def Loc.bridgeOk : {T : Ty} → Loc C Γ T → Bool
  | _, .root .. => true
  | _, .field b _ _ => b.bridgeOk
  | _, .index (k := k) _ b i => k != .bool && b.bridgeOk && i.bridgeOk

def MPath.bridgeOk : {T : Ty} → MPath C Γ T → Bool
  | _, .var .. => true
  | _, .loc l => l.bridgeOk

def MLoc.bridgeOk : {T : Ty} → MLoc C Γ T → Bool
  | _, .field b _ _ => b.bridgeOk
  | _, .index _ b i => b.bridgeOk && i.bridgeOk

def Val.bridgeOk : {p : PrimTy} → Val C Γ p → Bool
  | _, .simple _ => true
  | _, .read l => l.bridgeOk
  | _, .binop _ _ _ a b => a.bridgeOk && b.bridgeOk
  | _, .unop _ _ _ a => a.bridgeOk
  | _, .ternary c a b => c.bridgeOk && a.bridgeOk && b.bridgeOk
  | _, .readMem l => l.bridgeOk
  | _, .len b _ => b.bridgeOk
  | _, .mlen b _ => b.bridgeOk

end

/-- A storage copy at a type with distinct member names. -/
def Src.bridgeOk {T : Ty} : Src C Γ T → Bool
  | .val v => v.bridgeOk
  | .copy (R := R) p _ => (Ty.ref R).nodupS && p.bridgeOk

def ARhs.bridgeOk {R : RefTy} : ARhs C Γ R → Bool
  | .path p => p.bridgeOk
  | .push b _ => b.bridgeOk

def MRhs.bridgeOk {R : RefTy} : MRhs C Γ R → Bool
  | .alias p => p.bridgeOk
  | .copy p _ => p.bridgeOk
  | .newArr .. => true

def NewLhs.bridgeOk {R : RefTy} : NewLhs C Γ R → Bool
  | .store l => (Ty.ref R).nodupS && l.bridgeOk
  | .mem l => l.bridgeOk

def MSrc.bridgeOk {T : Ty} : MSrc C Γ T → Bool
  | .val v => v.bridgeOk
  | .ref p => p.bridgeOk

def OpLoc.bridgeOk {p : PrimTy} : OpLoc C Γ p → Bool
  | .local _ | .root .. => true
  | .field b _ _ => b.bridgeOk
  | .index (k := k) _ b _ => k != .bool && b.bridgeOk
  | .mfield b _ _ => b.bridgeOk
  | .mindex _ b _ => b.bridgeOk

def Args.bridgeOk : {ps : Ctx} → Args C Γ ps → Bool
  | _, .nil => true
  | _, .snoc as _ _ e => as.bridgeOk && e.bridgeOk

end BridgeOk

mutual

/-- The statement is one the untyped run agrees on: no `bool` mapping key,
no storage copy at a type with a repeated member name. -/
def Stmt.bridgeOk : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Bool
  | _, _, .assign l r => l.bridgeOk && r.bridgeOk
  | _, _, .rebind _ r => r.bridgeOk
  | _, _, .assignLocal _ r => r.bridgeOk
  | _, _, .declLocal _ _ init => init.all Val.bridgeOk
  | _, _, .declStorage _ _ init => init.all ARhs.bridgeOk
  | _, _, .opAssign _ _ _ l r => l.bridgeOk && r.bridgeOk
  | _, _, .incDec _ _ l => l.bridgeOk
  | _, _, .assignIncDec _ _ _ l _ => l.bridgeOk
  | _, _, .push b v _ => b.bridgeOk && v.all Src.bridgeOk
  | _, _, .pop b => b.bridgeOk
  | _, _, .transfer r a => r.bridgeOk && a.bridgeOk
  | _, _, .send _ r a => r.bridgeOk && a.bridgeOk
  | _, _, .declMem _ _ init _ _ => init.all MRhs.bridgeOk
  | _, _, .rebindMem _ r => r.bridgeOk
  | _, _, .assignFromMem (R := R) l p => (Ty.ref R).nodupS && l.bridgeOk && p.bridgeOk
  | _, _, .assignMem l r => l.bridgeOk && r.bridgeOk
  | _, _, .delete l => l.bridgeOk
  | _, _, .deleteMem p _ => p.bridgeOk
  | _, _, .assignNew l _ _ => l.bridgeOk
  | _, _, .ite c thn els => c.bridgeOk && Prog.bridgeOk thn && Prog.bridgeOk els
  | _, _, .require c => c.bridgeOk
  | _, _, .assert c => c.bridgeOk
  | _, _, .revert => true
  | _, _, .call _ args _ body => args.bridgeOk && Prog.bridgeOk body
  | _, _, .tryCall _ _ ok err _ pnc other =>
    Prog.bridgeOk ok && Prog.bridgeOk err && Prog.bridgeOk pnc && Prog.bridgeOk other
  | _, _, .loop _ c body => c.bridgeOk && Prog.bridgeOk body
  | _, _, .block body => Prog.bridgeOk body

def Prog.bridgeOk : {Γ Γ' : Ctx} → Prog C Γ Γ' → Bool
  | _, _, .nil => true
  | _, _, .cons s P => s.bridgeOk && Prog.bridgeOk P

end

/-! ## Expressions -/

section Eval

variable {Γ : Ctx}

theorem Simple.evalT_erase (σ : TState C Γ) {p : PrimTy} (s : Simple C Γ p) :
    s.eval σ.erase = .ok (PrimTy.erase (s.evalT σ)) := by
  cases s with
  | lit n h => cases p <;> first | rfl | simp only [PrimTy.inRange, Bool.false_eq_true] at h
  | bool b => rfl
  | «local» i =>
    show Except.ok (Env.get i (TEnv.erase Γ σ.env)) = _
    rw [TEnv.get_erase]
    rfl
  | env k hp => subst hp; cases k <;> rfl

theorem SVal.asValue_erase_prim {p : PrimTy} (v : SVal (.prim p)) :
    v.erase.asValue = .ok (PrimTy.erase (SVal.view v)) := by
  cases v with
  | prim x => rw [SVal.erase_prim]; cases p <;> rfl

theorem MVal.asValue_erase_prim {H : HTy} {p : PrimTy} (x : MVal H (.prim p)) :
    (MVal.erase (.prim p) x).asValue = .ok (PrimTy.erase (p := p) x) := by
  cases p <;> rfl

theorem SRef.erase_field {s f : Name} {T : Ty} (r : SRef C (.ref (.struct s)))
    (h : C.fieldType s f = some T) :
    (r.field h).erase = (r.root, r.path.erase ++ [.field f]) := by
  simp only [SRef.field, SRef.erase, SRef.append, Path.erase_append]
  rfl

theorem SRef.erase_index {R : RefTy} {k : PrimTy} {V : Ty} (r : SRef C (.ref R))
    (it : IndexTy R k V) (i : Int) : (r.index it i).erase = (r.root, r.path.erase ++ [.at i]) := by
  simp only [SRef.index, SRef.erase, SRef.append, Path.erase_append, Path.erase_index]

/-- `a && b`/`a || b` decided by `a`: the untyped operator does not read `b`. -/
theorem evalBinop_short {op : BinOp} {p : PrimTy} {x : p.Denote} {y : (op.ret p).Denote}
    (hs : op.shortT x = some y) (u : Res Value) :
    evalBinop op p (PrimTy.erase x) u = .ok (PrimTy.erase y) := by
  cases op <;> cases p <;> simp only [BinOp.shortT, reduceCtorEq] at hs <;> cases x <;>
    simp only [boolT, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, Option.some.injEq] at hs <;>
    subst hs <;> rfl

/-- Otherwise the untyped operator reads `b` first. -/
theorem evalBinop_long {op : BinOp} {p : PrimTy} {x : p.Denote} (hs : op.shortT x = none)
    (u : Res Value) :
    evalBinop op p (PrimTy.erase x) u = u >>= fun w => evalBinop op p (PrimTy.erase x) (.ok w) := by
  cases op <;> cases p <;> cases u <;> first
    | rfl
    | (cases x <;> first | rfl | simp only [BinOp.shortT, boolT, ↓reduceIte, reduceCtorEq,
        Bool.false_eq_true] at hs)


/-- A length read: past `uint`'s range, the typed run diverges. -/
theorem lenT_agrees (n : Nat) :
    TRes.Agrees PrimTy.erase (lenT n) (.ok (Semantics.Value.int n)) := by
  unfold lenT
  split
  · rfl
  · trivial

theorem lenT_agrees_opt (o : Option Nat) :
    TRes.Agrees PrimTy.erase (do let n ← TRes.ofOpt o; lenT n)
      (toRes (fun n : Nat => Semantics.Value.int n) o) := by
  cases o with
  | none => exact TRes.Agrees.ofOpt (f := PrimTy.erase) none
  | some n => exact lenT_agrees n

mutual

theorem SPath.resolveT_erase (σ : TState C Γ) : {T : Ty} → (b : SPath C Γ T) →
    b.bridgeOk = true → TRes.Agrees SRef.erase (b.resolveT σ) (b.resolve σ.erase)
  | _, .alias i, _ => by
    show TRes.Agrees SRef.erase
      (match (TEnv.get i σ.env : Option (SRef C _)) with
        | some r => .ok r
        | none => .error .revert)
      (match (Env.get i (TEnv.erase Γ σ.env) : Option (Name × List Seg)) with
        | some p => pure p
        | none => .error .revert)
    rw [TEnv.get_erase]
    cases (TEnv.get i σ.env : Option (SRef C _)) <;> rfl
  | _, .loc l, h => l.resolveT_erase σ h

theorem Loc.resolveT_erase (σ : TState C Γ) : {T : Ty} → (l : Loc C Γ T) →
    l.bridgeOk = true → TRes.Agrees SRef.erase (l.resolveT σ) (l.resolve σ.erase)
  | _, .root r h, _ => rfl
  | _, .field b f h, hb => by
    simp only [Loc.bridgeOk] at hb
    refine TRes.Agrees.bind (b.resolveT_erase σ hb) fun r => ?_
    exact TRes.Agrees.of_eq (congrArg Except.ok (SRef.erase_field r h).symm)
  | _, .index (k := k) it b i, hb => by
    simp only [Loc.bridgeOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hb
    refine TRes.Agrees.bind (b.resolveT_erase σ hb.1.2) fun r => ?_
    refine TRes.Agrees.bind (i.evalT_erase σ hb.2) fun x => ?_
    show TRes.Agrees SRef.erase
      (do TRes.ofOpt (σ.storage.checkIndex r it (PrimTy.key x)); pure (r.atKey it x))
      (do
        let i ← (PrimTy.erase x).asInt
        σ.erase.glob.checkIndex r.root r.path.erase i
        pure (r.root, r.path.erase ++ [.at i]))
    rw [PrimTy.asInt_erase_key hb.1.1, ok_bind,
      Storage.checkIndex_erase (σ := σ.erase.glob) rfl r it]
    refine TRes.Agrees.bind (TRes.Agrees.ofOpt _) fun _ => ?_
    exact TRes.Agrees.of_eq (congrArg Except.ok (SRef.erase_index r it _).symm)

theorem MPath.mvalT_erase (σ : TState C Γ) : {T : Ty} → (b : MPath C Γ T) →
    b.bridgeOk = true → TRes.Agrees (MVal.erase T) (b.mvalT σ) (b.mval σ.erase)
  | _, .var i _, _ => by
    refine TRes.Agrees.of_eq ?_
    show Except.ok (Semantics.MVal.ref (Env.get i (TEnv.erase Γ σ.env))) = _
    rw [TEnv.get_erase]
    rfl
  | _, .loc l, h => l.readT_erase σ h

theorem MLoc.readT_erase (σ : TState C Γ) : {T : Ty} → (l : MLoc C Γ T) →
    l.bridgeOk = true →
    TRes.Agrees (MVal.erase T) (do TRes.ofOpt (σ.heap.readAddr (← l.addrT σ))) (l.read σ.erase)
  | _, .field b f h, hb => by
    simp only [MLoc.bridgeOk] at hb
    simp only [MLoc.addrT, MLoc.read, bind_assoc, pure_bind]
    refine TRes.Agrees.bind (b.mvalT_erase σ hb) fun r => ?_
    show TRes.Agrees _ (.ok (σ.heap.field r h)) (do
      match ← σ.erase.glob.getObj r.id with
      | .struct fields =>
        match lookupBy f fields with
        | some v => pure v
        | none => .error .stuck
      | .array _ _ => .error .stuck)
    exact TRes.Agrees.of_eq (Heap.readField_erase (σ := σ.erase.glob) rfl r h)
  | _, .index a b i, hb => by
    simp only [MLoc.bridgeOk, Bool.and_eq_true] at hb
    simp only [MLoc.addrT, MLoc.read, bind_assoc, pure_bind]
    refine TRes.Agrees.bind (b.mvalT_erase σ hb.1) fun r => ?_
    refine TRes.Agrees.bind (i.evalT_erase σ hb.2) fun k => ?_
    show TRes.Agrees _ (TRes.ofOpt (σ.heap.index r a k.1)) (do
      match ← σ.erase.glob.getObj r.id with
      | .array elems _ =>
        if h : 0 ≤ k.1 ∧ k.1.toNat < elems.length then pure (elems.get ⟨k.1.toNat, h.2⟩)
        else .error .revert
      | .struct _ => .error .stuck)
    have e := Heap.readIndex_erase (σ := σ.erase.glob) rfl r a k.1
    exact e ▸ TRes.Agrees.ofOpt _

theorem Val.evalT_erase (σ : TState C Γ) : {p : PrimTy} → (v : Val C Γ p) →
    v.bridgeOk = true → TRes.Agrees PrimTy.erase (v.evalT σ) (v.eval σ.erase)
  | _, .simple s, _ => TRes.Agrees.of_eq (Simple.evalT_erase σ s)
  | _, .read l, hb => by
    simp only [Val.bridgeOk] at hb
    refine TRes.Agrees.bind (l.resolveT_erase σ hb) fun r => ?_
    show TRes.Agrees _ (do let v ← TRes.ofOpt (σ.storage.find r); pure (SVal.view v))
      (do let v ← σ.erase.glob.findStorage r.root r.path.erase; v.asValue)
    rw [Storage.findStorage_erase (σ := σ.erase.glob) rfl r]
    exact TRes.Agrees.bind (TRes.Agrees.ofOpt _) fun v =>
      TRes.Agrees.of_eq (SVal.asValue_erase_prim v)
  | _, .binop op h hq a b, hb => by
    subst hq
    simp only [Val.bridgeOk, Bool.and_eq_true] at hb
    refine TRes.Agrees.bind (a.evalT_erase σ hb.1) fun x => ?_
    show TRes.Agrees _ (match op.shortT x with
      | some y => pure y
      | none => do
        let y ← b.evalT σ
        TRes.ofOpt (op.evalT x y)) (evalBinop op _ (PrimTy.erase x) (b.eval σ.erase))
    cases hs : op.shortT x with
    | some y => rw [evalBinop_short hs]; rfl
    | none =>
      rw [evalBinop_long hs]
      refine TRes.Agrees.bind (b.evalT_erase σ hb.2) fun y => ?_
      rw [BinOp.evalT_erase op h x y]
      exact TRes.Agrees.ofOpt _
  | _, .unop op h hq a, hb => by
    subst hq
    simp only [Val.bridgeOk] at hb
    refine TRes.Agrees.bind (a.evalT_erase σ hb) fun x => ?_
    show TRes.Agrees _ (TRes.ofOpt (op.evalT x)) _
    rw [UnOp.evalT_erase op h x]
    exact TRes.Agrees.ofOpt _
  | _, .ternary c a b, hb => by
    simp only [Val.bridgeOk, Bool.and_eq_true] at hb
    refine TRes.Agrees.bind (c.evalT_erase σ hb.1.1) fun x => ?_
    cases x
    · exact b.evalT_erase σ hb.2
    · exact a.evalT_erase σ hb.1.2
  | _, .readMem l, hb => by
    simp only [Val.bridgeOk] at hb
    show TRes.Agrees _ (do TRes.ofOpt (σ.heap.readAddr (← l.addrT σ)))
      (do (← l.read σ.erase).asValue)
    exact TRes.Agrees.bind_pure (l.readT_erase σ hb) fun x => MVal.asValue_erase_prim x
  | _, .len b hp, hb => by
    subst hp
    simp only [Val.bridgeOk] at hb
    refine TRes.Agrees.bind (b.resolveT_erase σ hb) fun r => ?_
    show TRes.Agrees _ (do let n ← TRes.ofOpt (σ.storage.len r); lenT n)
      (arrayLen σ.erase.glob r.root r.path.erase)
    rw [Storage.arrayLen_erase (σ := σ.erase.glob) rfl r]
    exact lenT_agrees_opt _
  | _, .mlen b hp, hb => by
    subst hp
    simp only [Val.bridgeOk] at hb
    refine TRes.Agrees.bind (b.mvalT_erase σ hb) fun r => ?_
    show TRes.Agrees _ (lenT (σ.heap.len r .dyn)) (memArrayLen σ.erase.glob r.id)
    rw [Heap.memArrayLen_erase (σ := σ.erase.glob) rfl r .dyn]
    exact lenT_agrees _

end

end Eval

end Solidity.Core
