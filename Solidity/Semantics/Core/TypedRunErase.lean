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

/-! ### An expression does not panic -/

theorem lenT_noPanic (n : Nat) : (lenT n).NoPanic := by
  unfold lenT
  split <;> exact fun h => nomatch h

mutual

theorem SPath.resolveT_noPanic (σ : TState C Γ) : {T : Ty} → (b : SPath C Γ T) →
    (b.resolveT σ).NoPanic
  | _, .alias i => by
    show (match (TEnv.get i σ.env : Option (SRef C _)) with
      | some r => .ok r
      | none => .error .revert : TRes _).NoPanic
    cases (TEnv.get i σ.env : Option (SRef C _)) <;> exact fun h => nomatch h
  | _, .loc l => l.resolveT_noPanic σ

theorem Loc.resolveT_noPanic (σ : TState C Γ) : {T : Ty} → (l : Loc C Γ T) →
    (l.resolveT σ).NoPanic
  | _, .root .. => fun h => nomatch h
  | _, .field b _ _ => (b.resolveT_noPanic σ).bind fun _ => fun h => nomatch h
  | _, .index _ b i => (b.resolveT_noPanic σ).bind fun _ => (i.evalT_noPanic σ).bind fun _ =>
      (TRes.NoPanic.ofOpt _).bind fun _ => fun h => nomatch h

theorem MPath.mvalT_noPanic (σ : TState C Γ) : {T : Ty} → (b : MPath C Γ T) →
    (b.mvalT σ).NoPanic
  | _, .var .. => fun h => nomatch h
  | _, .loc l => (l.addrT_noPanic σ).bind fun _ => TRes.NoPanic.ofOpt _

theorem MLoc.addrT_noPanic (σ : TState C Γ) : {T : Ty} → (l : MLoc C Γ T) →
    (l.addrT σ).NoPanic
  | _, .field b _ _ => (b.mvalT_noPanic σ).bind fun _ => fun h => nomatch h
  | _, .index _ b i => (b.mvalT_noPanic σ).bind fun _ => (i.evalT_noPanic σ).bind fun _ =>
      fun h => nomatch h

theorem Val.evalT_noPanic (σ : TState C Γ) : {p : PrimTy} → (v : Val C Γ p) →
    (v.evalT σ).NoPanic
  | _, .simple _ => fun h => nomatch h
  | _, .read l => (l.resolveT_noPanic σ).bind fun _ => (TRes.NoPanic.ofOpt _).bind fun _ =>
      fun h => nomatch h
  | _, .binop op _ hq a b => by
    subst hq
    refine (a.evalT_noPanic σ).bind fun x => ?_
    show (match op.shortT x with
      | some y => pure y
      | none => do
        let y ← b.evalT σ
        TRes.ofOpt (op.evalT x y) : TRes _).NoPanic
    cases op.shortT x with
    | some _ => exact fun h => nomatch h
    | none => exact (b.evalT_noPanic σ).bind fun _ => TRes.NoPanic.ofOpt _
  | _, .unop op _ hq a => by
    subst hq
    exact (a.evalT_noPanic σ).bind fun _ => TRes.NoPanic.ofOpt _
  | _, .ternary c a b => (c.evalT_noPanic σ).bind fun x => by
    cases x
    · exact b.evalT_noPanic σ
    · exact a.evalT_noPanic σ
  | _, .readMem l => (l.addrT_noPanic σ).bind fun _ => TRes.NoPanic.ofOpt _
  | _, .len b hp => by
    subst hp
    exact (b.resolveT_noPanic σ).bind fun _ => (TRes.NoPanic.ofOpt _).bind fun _ => lenT_noPanic _
  | _, .mlen b hp => by
    subst hp
    exact (b.mvalT_noPanic σ).bind fun _ => lenT_noPanic _

end

/-! ### Sources and right-hand sides -/

theorem Value.toSVal_erase {p : PrimTy} (x : p.Denote) :
    (PrimTy.erase x).toSVal = (SVal.prim x).erase := by
  rw [SVal.erase_prim]; cases p <;> rfl

theorem Value.toMVal_erase {H : HTy} {p : PrimTy} (x : p.Denote) :
    (PrimTy.erase x).toMVal = MVal.erase (H := H) (.prim p) x := by
  cases p <;> rfl

theorem Src.valueT_erase (σ : TState C Γ) {T : Ty} (r : Src C Γ T) (h : r.bridgeOk = true) :
    TRes.Agrees SVal.erase (r.valueT σ) (r.value σ.erase) := by
  cases r with
  | val v =>
    simp only [Src.bridgeOk] at h
    exact TRes.Agrees.bind (v.evalT_erase σ h) fun x =>
      TRes.Agrees.of_eq (congrArg Except.ok (Value.toSVal_erase x))
  | copy p _ =>
    simp only [Src.bridgeOk, Bool.and_eq_true] at h
    refine TRes.Agrees.bind (p.resolveT_erase σ h.2) fun r => ?_
    show TRes.Agrees _ (TRes.ofOpt (σ.storage.find r))
      (σ.erase.glob.findStorage r.root r.path.erase)
    rw [Storage.findStorage_erase (σ := σ.erase.glob) rfl r]
    exact TRes.Agrees.ofOpt _

theorem Src.valueT_noPanic (σ : TState C Γ) {T : Ty} (r : Src C Γ T) : (r.valueT σ).NoPanic := by
  cases r with
  | val v => exact (v.evalT_noPanic σ).bind fun _ => fun h => nomatch h
  | copy p _ => exact (p.resolveT_noPanic σ).bind fun _ => TRes.NoPanic.ofOpt _

theorem MSrc.mvalT_erase (σ : TState C Γ) {T : Ty} (r : MSrc C Γ T) (h : r.bridgeOk = true) :
    TRes.Agrees (MVal.erase T) (r.mvalT σ) (r.mval σ.erase) := by
  cases r with
  | val v =>
    simp only [MSrc.bridgeOk] at h
    exact TRes.Agrees.bind_pure (v.evalT_erase σ h) fun x =>
      congrArg Except.ok (Value.toMVal_erase x)
  | ref p =>
    simp only [MSrc.bridgeOk] at h
    exact TRes.Agrees.bind_pure (p.mvalT_erase σ h) fun _ => rfl

/-- The typed state with its storage replaced erases to the untyped one with
the erased storage. -/
theorem TState.withStorage_into (σ : TState C Γ) (st : Storage C) :
    (σ.withStorage st).erase = σ.erase.withGlob (Storage.into σ.erase.glob st) := rfl

theorem TState.withHeap_erase (σ : TState C Γ) (hp : Heap σ.H) :
    (σ.withHeap hp).erase = σ.erase.withGlob { σ.erase.glob with heap := hp.erase } := rfl

theorem TState.withGlob_adopt {α : HTy → Type} (σ : TState C Γ) (g : Grown σ.H α) :
    σ.erase.withGlob (σ.adopt g).1.erase.glob = (σ.adopt g).1.erase := by
  simp only [TState.adopt, TState.erase, State.withGlob, State.ofGlob, State.glob,
    TEnv.erase_wk]

theorem ARhs.evalT_erase (σ : TState C Γ) {R : RefTy} (r : ARhs C Γ R) (h : r.bridgeOk = true) :
    TRes.Agrees (fun x : Storage C × SRef C (.ref R) => ((σ.withStorage x.1).erase, x.2.erase))
      (r.evalT σ) (r.eval σ.erase) := by
  cases r with
  | path p =>
    simp only [ARhs.bridgeOk] at h
    exact TRes.Agrees.bind (p.resolveT_erase σ h) fun _ => rfl
  | push b _ =>
    simp only [ARhs.bridgeOk] at h
    refine TRes.Agrees.bind (b.resolveT_erase σ h) fun r => ?_
    show TRes.Agrees _ (do
        let (st, n) ← TRes.ofOpt (σ.storage.pushPlace r)
        pure (st, r.index (.arr .dyn) n))
      (do
        let (τ, n) ← pushPlaceAt σ.erase.glob (.ref R) r.root r.path.erase
        pure (σ.erase.withGlob τ, (r.root, r.path.erase ++ [.at n])))
    rw [Storage.pushPlaceAt_erase (σ := σ.erase.glob) rfl r]
    refine TRes.Agrees.bind (TRes.Agrees.ofOpt _) fun x => ?_
    exact TRes.Agrees.of_eq (by rw [SRef.erase_index]; rfl)

theorem newArrT_erase : (R : RefTy) → (n : Int) → (h : R.newArrOk = true) →
    (newArrT R n h).erase = newArrVal R n
  | .array E, n, _ => by
    simp only [newArrT, newArrVal, SVal.erase, SList.erase_ofList, SList.erase_nil, List.map_replicate,
      SVal.dflt_erase]
  | .struct _, _, h | .fixed .., _, h | .mapping .., _, h => by
    simp only [RefTy.newArrOk, Bool.false_eq_true] at h

theorem MRhs.evalT_erase (σ : TState C Γ) {R : RefTy} (r : MRhs C Γ R) (h : r.bridgeOk = true) :
    TRes.Agrees (fun g : Grew C Γ σ.H (HRef · R) => (g.st.erase, (g.val : HRef _ R).id))
      (r.evalT σ) (r.eval σ.erase) := by
  cases r with
  | alias p =>
    simp only [MRhs.bridgeOk] at h
    exact TRes.Agrees.bind (p.mvalT_erase σ h) fun _ => rfl
  | copy p hm =>
    simp only [MRhs.bridgeOk] at h
    refine TRes.Agrees.bind (p.resolveT_erase σ h) fun r => ?_
    show TRes.Agrees _ (do
        let sv ← TRes.ofOpt (σ.storage.find r)
        let g := σ.copyStToMG sv hm
        pure (⟨g.st, g.ext, g.val⟩ : Grew C Γ σ.H (HRef · R)))
      (do
        let sv ← σ.erase.glob.findStorage r.root r.path.erase
        let (τ, mv) ← Semantics.copyStToM σ.erase.glob sv
        pure (σ.erase.withGlob τ, ← mv.asRef))
    rw [Storage.findStorage_erase (σ := σ.erase.glob) rfl r]
    refine TRes.Agrees.bind (TRes.Agrees.ofOpt _) fun sv => ?_
    rw [TState.copyStToM_erase σ sv hm]
    exact TRes.Agrees.of_eq (by
      show Except.ok (σ.erase.withGlob (σ.copyStToM sv hm).1.erase.glob, _) = _
      rw [TState.copyStToM, TState.withGlob_adopt]
      rfl)
  | newArr n hn =>
    show TRes.Agrees _ _ (do
        let sv := newArrVal R (← (← n.eval σ.erase).asInt)
        let (τ, mv) ← Semantics.copyStToM σ.erase.glob sv
        pure (σ.erase.withGlob τ, ← mv.asRef))
    rw [Simple.evalT_erase σ n, ok_bind, PrimTy.asInt_erase_uint, ok_bind, ← newArrT_erase R _ hn]
    simp only []
    rw [TState.copyStToM_erase σ _ (RefTy.mapFree_of_newArrOk hn)]
    exact TRes.Agrees.of_eq (by
      show Except.ok (σ.erase.withGlob (σ.copyStToM _ _).1.erase.glob, _) = _
      rw [TState.copyStToM, TState.withGlob_adopt]
      rfl)

/-! ### Memory addresses -/

/-- The untyped address. -/
def MAddr.erase {H : HTy} {T : Ty} : MAddr H T → Semantics.Addr
  | .field (f := f) r _ => .memoryField r.id f
  | .index r _ i => .memoryIndex r.id i

theorem MAddr.erase_wk {H H' : HTy} (e : H <+: H') {T : Ty} (a : MAddr H T) :
    (a.wk e).erase = a.erase := by
  cases a <;> rfl

theorem MLoc.addrT_erase (σ : TState C Γ) {T : Ty} (l : MLoc C Γ T) (h : l.bridgeOk = true) :
    TRes.Agrees MAddr.erase (l.addrT σ) (l.addr σ.erase) := by
  cases l with
  | field b f _ =>
    simp only [MLoc.bridgeOk] at h
    exact TRes.Agrees.bind (b.mvalT_erase σ h) fun _ => rfl
  | index a b i =>
    simp only [MLoc.bridgeOk, Bool.and_eq_true] at h
    exact TRes.Agrees.bind (b.mvalT_erase σ h.1) fun _ =>
      TRes.Agrees.bind (i.evalT_erase σ h.2) fun _ => rfl

theorem writeAddr_erase (σ : TState C Γ) {T : Ty} (a : MAddr σ.H T) (v : MVal σ.H T) :
    writeAddr σ.erase.glob (MVal.erase T v) a.erase =
      toRes (fun hp : Heap σ.H => { σ.erase.glob with heap := hp.erase }) (σ.heap.writeAddr a v) := by
  cases a with
  | field r h => exact Heap.memWriteField_erase (σ := σ.erase.glob) rfl r h v
  | index r a i => exact Heap.memWriteIndex_erase (σ := σ.erase.glob) rfl r a i v

theorem readLoc_erase (σ : TState C Γ) {p : PrimTy} (a : MAddr σ.H (.prim p)) :
    Semantics.readLoc σ.erase.glob a.erase = toRes PrimTy.erase (σ.heap.readAddr a) := by
  cases a with
  | field r h =>
    simp only [Semantics.readLoc, MAddr.erase, Heap.getObj_erase (σ := σ.erase.glob) rfl r, bind,
      Except.bind]
    show (match lookupBy _ (MFields.erase _ (σ.heap.get r)) with
      | some v => v.asValue | none => .error .stuck) = _
    rw [MFields.lookupBy_erase _ (σ.heap.get r) h]
    exact MVal.asValue_erase_prim _
  | index r a i =>
    simp only [Semantics.readLoc, MAddr.erase, Heap.getObj_erase (σ := σ.erase.glob) rfl r, bind,
      Except.bind, MObj.erase_arr a (σ.heap.get r), Heap.readAddr, Heap.index]
    by_cases h0 : 0 ≤ i
    · by_cases hl : i.toNat < (MObj.elems a (σ.heap.get r)).length
      · simp only [List.length_map, h0, hl, and_self, ↓reduceDIte, ↓reduceIte,
          List.get_eq_getElem, List.getElem_map, List.getElem?_eq_getElem hl, toRes]
        exact MVal.asValue_erase_prim _
      · simp only [List.length_map, h0, hl, and_false, ↓reduceDIte, ↓reduceIte,
          List.getElem?_eq_none (Nat.le_of_not_lt hl), toRes]
    · simp only [h0, false_and, ↓reduceDIte, ↓reduceIte, toRes]

theorem writeLoc_eq (s : Semantics.State) (a : Semantics.Addr) (v : Value) :
    Semantics.writeLoc s a v = writeAddr s v.toMVal a := by
  cases a <;> rfl

theorem MLoc.write_eq (σ : State C Γ) (mv : Semantics.MVal) {T : Ty} (l : MLoc C Γ T) :
    l.write σ mv = l.addr σ >>= fun a => σ.withGlob <$> writeAddr σ.glob mv a := by
  cases l <;> simp only [MLoc.write, MLoc.addr, writeAddr, bind_assoc, pure_bind]

/-! ### Compound assignments and `++` -/

theorem bind_bind_eq {ε α β γ : Type} {x : Except ε α} {f : α → Except ε β}
    {K : β → Except ε γ} {y : Except ε β} (h : x >>= f = y) :
    (x >>= fun a => f a >>= K) = y >>= K := by
  rw [← h, bind_assoc]

theorem PrimTy.erase_numeric {p : PrimTy} (hp : p.isNumeric = true) (x : p.Denote) :
    PrimTy.erase x = .int (PrimTy.key x) := by
  cases p <;> first | rfl | cases hp

theorem compound_erase {op : BinOp} (hop : op.hasCompoundAssign = true) {p : PrimTy}
    (hp : p.isNumeric = true) (x y : Int) :
    (Semantics.applyBinOp op (.int x) (.int y) >>= Semantics.checkArith (.prim p)) =
      toRes PrimTy.erase (compoundT op p x y) := by
  have hA : op.isArith = true := by
    cases op <;> simp only [BinOp.hasCompoundAssign, Bool.false_eq_true] at hop <;> rfl
  rw [BinOp.applyBinOp_int hA]
  unfold compoundT
  cases BinOp.arithInt op x y with
  | none => rfl
  | some n => exact PrimTy.checkArith_ofInt hp n

theorem compound_erase' {op : BinOp} (hop : op.hasCompoundAssign = true) {p : PrimTy}
    (hp : p.isNumeric = true) (x y : p.Denote) :
    (Semantics.applyBinOp op (PrimTy.erase x) (PrimTy.erase y) >>= Semantics.checkArith (.prim p)) =
      toRes PrimTy.erase (compoundT op p (PrimTy.key x) (PrimTy.key y)) := by
  rw [PrimTy.erase_numeric hp x, PrimTy.erase_numeric hp y]
  exact compound_erase hop hp _ _

theorem asInt_erase_numeric {p : PrimTy} (hp : p.isNumeric = true) (x : p.Denote) :
    (PrimTy.erase x).asInt = .ok (PrimTy.key x) := by
  rw [PrimTy.erase_numeric hp x]
  rfl

theorem bump_erase {p : PrimTy} (hp : p.isNumeric = true) (op : IncDec) (x : Int) :
    Semantics.checkArith (.prim p) (.int (if op.isIncrement then x + 1 else x - 1)) =
      toRes PrimTy.erase (bumpT op p x) :=
  PrimTy.checkArith_ofInt hp _

theorem opStoreT_erase (σ : TState C Γ) {op : BinOp} (hop : op.hasCompoundAssign = true)
    {p : PrimTy} (hp : p.isNumeric = true) (r : SRef C (.prim p)) (v : p.Denote) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (opStoreT σ op r v)
      (σ.erase.withGlob <$> opStore σ.erase.glob op p r.root r.path.erase (PrimTy.erase v)) := by
  simp only [opStoreT, opStore, Storage.findStorage_erase (σ := σ.erase.glob) rfl r]
  cases σ.storage.find r with
  | none => rfl
  | some old =>
    simp only [TRes.ofOpt, toRes, ok_bind, SVal.asValue_erase_prim]
    rw [bind_bind_eq (compound_erase' hop hp _ _)]
    cases compoundT op p (PrimTy.key (SVal.view old)) (PrimTy.key v) with
    | none => rfl
    | some new =>
      simp only [toRes, ok_bind, Value.toSVal_erase,
        Storage.saveStorage_erase (σ := σ.erase.glob) rfl r]
      cases σ.storage.save r (SVal.prim new) <;> rfl

theorem opMemT_erase (σ : TState C Γ) {op : BinOp} (hop : op.hasCompoundAssign = true)
    {p : PrimTy} (hp : p.isNumeric = true) (a : MAddr σ.H (.prim p)) (v : p.Denote) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (opMemT σ op a v)
      (σ.erase.withGlob <$> opMem σ.erase.glob op p a.erase (PrimTy.erase v)) := by
  simp only [opMemT, opMem, readLoc_erase σ a]
  cases σ.heap.readAddr a with
  | none => rfl
  | some old =>
    simp only [TRes.ofOpt, toRes, ok_bind]
    rw [bind_bind_eq (compound_erase' hop hp _ _)]
    cases compoundT op p (PrimTy.key (p := p) old) (PrimTy.key v) with
    | none => rfl
    | some new =>
      simp only [toRes, ok_bind, writeLoc_eq, Value.toMVal_erase (H := σ.H),
        writeAddr_erase σ a]
      cases σ.heap.writeAddr a new <;> rfl

theorem asInt_int (n : Int) : Semantics.Value.asInt (.int n) = .ok n := rfl

theorem bumpStoreT_erase (σ : TState C Γ) (op : IncDec) {p : PrimTy} (hp : p.isNumeric = true)
    (r : SRef C (.prim p)) {k' : Semantics.State × Value → State C Γ × Value}
    (hk : ∀ τ v, k' (τ, v) = (σ.erase.withGlob τ, v)) :
    TRes.Agrees (fun x : Out C σ.H Γ × p.Denote => (x.1.st.erase, PrimTy.erase x.2))
      (bumpStoreT σ op r) (k' <$> bumpStore σ.erase.glob op p r.root r.path.erase) := by
  simp only [bumpStoreT, bumpStore, Storage.findStorage_erase (σ := σ.erase.glob) rfl r]
  cases σ.storage.find r with
  | none => rfl
  | some old =>
    simp only [TRes.ofOpt, toRes, ok_bind, SVal.asValue_erase_prim, asInt_erase_numeric hp,
      bump_erase hp]
    cases bumpT op p (PrimTy.key (SVal.view old)) with
    | none => rfl
    | some new =>
      simp only [toRes, ok_bind, Value.toSVal_erase,
        Storage.saveStorage_erase (σ := σ.erase.glob) rfl r]
      cases σ.storage.save r (SVal.prim new) with
      | none => rfl
      | some st =>
        refine TRes.Agrees.of_eq ?_
        simp only [toRes, ok_bind]
        cases op.isPre <;> exact congrArg Except.ok (hk _ _)

theorem bumpMemT_erase (σ : TState C Γ) (op : IncDec) {p : PrimTy} (hp : p.isNumeric = true)
    (a : MAddr σ.H (.prim p)) {k' : Semantics.State × Value → State C Γ × Value}
    (hk : ∀ τ v, k' (τ, v) = (σ.erase.withGlob τ, v)) :
    TRes.Agrees (fun x : Out C σ.H Γ × p.Denote => (x.1.st.erase, PrimTy.erase x.2))
      (bumpMemT σ op a) (k' <$> bumpMem σ.erase.glob op p a.erase) := by
  simp only [bumpMemT, bumpMem, readLoc_erase σ a]
  cases σ.heap.readAddr a with
  | none => rfl
  | some old =>
    simp only [TRes.ofOpt, toRes, ok_bind, asInt_erase_numeric hp, bump_erase hp]
    cases bumpT op p (PrimTy.key (p := p) old) with
    | none => rfl
    | some new =>
      simp only [toRes, ok_bind, writeLoc_eq, Value.toMVal_erase (H := σ.H), writeAddr_erase σ a]
      cases σ.heap.writeAddr a new with
      | none => rfl
      | some hp' =>
        refine TRes.Agrees.of_eq ?_
        simp only [toRes, ok_bind]
        cases op.isPre <;> exact congrArg Except.ok (hk _ _)

theorem LTy.TDenote.erase_val {H : HTy} {p : PrimTy} (x : (LTy.val p).TDenote C H) :
    LTy.TDenote.erase (.val p) x = PrimTy.erase (p := p) x := rfl

theorem TState.erase_get (σ : TState C Γ) {t : LTy} (i : Idx Γ t) :
    Env.get i σ.erase.env = LTy.TDenote.erase t (TEnv.get i σ.env) :=
  TEnv.get_erase i σ.env

theorem OpLoc.storeT_erase (σ : TState C Γ) {op : BinOp} (hop : op.hasCompoundAssign = true)
    {p : PrimTy} (hp : p.isNumeric = true) (l : OpLoc C Γ p) (h : l.bridgeOk = true)
    (v : p.Denote) :
    TRes.Agrees (fun o : Out C σ.H Γ => o.st.erase) (l.storeT σ op v)
      (l.store σ.erase op (PrimTy.erase v)) := by
  cases l with
  | «local» i =>
    simp only [OpLoc.storeT, OpLoc.store, opLocal, TState.erase_get, LTy.TDenote.erase_val]
    rw [bind_bind_eq (compound_erase' hop hp _ _)]
    cases compoundT op p (PrimTy.key (TEnv.get i σ.env)) (PrimTy.key v) with
    | none => rfl
    | some new => exact TRes.Agrees.of_eq (congrArg Except.ok (TState.setLocal_erase σ i new).symm)
  | root r hr => exact opStoreT_erase σ hop hp (SRef.ofRoot r hr) v
  | field b f hf =>
    exact TRes.Agrees.bind (Loc.resolveT_erase σ (Loc.field b f hf) h) fun r =>
      opStoreT_erase σ hop hp r v
  | index it b i =>
    have h' : (Loc.index it b (.simple i)).bridgeOk = true := by
      simp only [OpLoc.bridgeOk, Bool.and_eq_true] at h
      simp only [Loc.bridgeOk, Val.bridgeOk, h, Bool.and_self]
    exact TRes.Agrees.bind (Loc.resolveT_erase σ (Loc.index it b (.simple i)) h') fun r =>
      opStoreT_erase σ hop hp r v
  | mfield b f hf =>
    show TRes.Agrees _ (do opMemT σ op (← (MLoc.field b f hf).addrT σ) v)
      (do
        let id ← (← b.mval σ.erase).asRef
        σ.erase.withGlob <$> opMem σ.erase.glob op p (.memoryField id f) (PrimTy.erase v))
    have e : (do
        let id ← (← b.mval σ.erase).asRef
        σ.erase.withGlob <$> opMem σ.erase.glob op p (.memoryField id f) (PrimTy.erase v)) =
        ((MLoc.field b f hf).addr σ.erase >>= fun a =>
          σ.erase.withGlob <$> opMem σ.erase.glob op p a (PrimTy.erase v)) := by
      simp only [MLoc.addr, bind_assoc, pure_bind]
    rw [e]
    exact TRes.Agrees.bind (MLoc.addrT_erase σ (MLoc.field b f hf) h) fun a =>
      opMemT_erase σ hop hp a v
  | mindex a b i =>
    have h' : (MLoc.index a b (.simple i)).bridgeOk = true := by
      simp only [OpLoc.bridgeOk] at h
      simp only [MLoc.bridgeOk, Val.bridgeOk, h, Bool.and_self]
    show TRes.Agrees _ (do opMemT σ op (← (MLoc.index a b (.simple i)).addrT σ) v)
      (do
        let id ← (← b.mval σ.erase).asRef
        let iv ← (← i.eval σ.erase).asInt
        σ.erase.withGlob <$> opMem σ.erase.glob op p (.memoryIndex id iv) (PrimTy.erase v))
    have e : (do
        let id ← (← b.mval σ.erase).asRef
        let iv ← (← i.eval σ.erase).asInt
        σ.erase.withGlob <$> opMem σ.erase.glob op p (.memoryIndex id iv) (PrimTy.erase v)) =
        ((MLoc.index a b (.simple i)).addr σ.erase >>= fun a =>
          σ.erase.withGlob <$> opMem σ.erase.glob op p a (PrimTy.erase v)) := by
      simp only [MLoc.addr, Val.eval, bind_assoc, pure_bind]
    rw [e]
    exact TRes.Agrees.bind (MLoc.addrT_erase σ (MLoc.index a b (.simple i)) h') fun a =>
      opMemT_erase σ hop hp a v

theorem OpLoc.bumpT_erase (σ : TState C Γ) (op : IncDec) {p : PrimTy} (hp : p.isNumeric = true)
    (l : OpLoc C Γ p) (h : l.bridgeOk = true) :
    TRes.Agrees (fun x : Out C σ.H Γ × p.Denote => (x.1.st.erase, PrimTy.erase x.2))
      (l.bumpT σ op) (l.bump σ.erase op) := by
  cases l with
  | «local» i =>
    simp only [OpLoc.bumpT, OpLoc.bump, bumpLocal, TState.erase_get, LTy.TDenote.erase_val,
      asInt_erase_numeric hp, ok_bind, bump_erase hp]
    cases Core.bumpT op p (PrimTy.key (TEnv.get i σ.env)) with
    | none => rfl
    | some new =>
      refine TRes.Agrees.of_eq ?_
      rw [TState.setLocal_erase]
      cases op.isPre <;> rfl
  | root r hr => exact bumpStoreT_erase σ op hp (SRef.ofRoot r hr) fun _ _ => rfl
  | field b f hf =>
    exact TRes.Agrees.bind (Loc.resolveT_erase σ (Loc.field b f hf) h) fun r =>
      bumpStoreT_erase σ op hp r fun _ _ => rfl
  | index it b i =>
    have h' : (Loc.index it b (.simple i)).bridgeOk = true := by
      simp only [OpLoc.bridgeOk, Bool.and_eq_true] at h
      simp only [Loc.bridgeOk, Val.bridgeOk, h, Bool.and_self]
    exact TRes.Agrees.bind (Loc.resolveT_erase σ (Loc.index it b (.simple i)) h') fun r =>
      bumpStoreT_erase σ op hp r fun _ _ => rfl
  | mfield b f hf =>
    simp only [OpLoc.bumpT, MLoc.addrT, bind_assoc, pure_bind]
    refine TRes.Agrees.bind (b.mvalT_erase σ h) fun r => ?_
    exact bumpMemT_erase σ op hp (.field r hf) fun _ _ => rfl
  | mindex a b i =>
    simp only [OpLoc.bridgeOk] at h
    simp only [OpLoc.bumpT, MLoc.addrT, Val.evalT, bind_assoc, pure_bind, ok_bind]
    refine TRes.Agrees.bind (b.mvalT_erase σ h) fun r => ?_
    show TRes.Agrees _ (bumpMemT σ op (.index r a (i.evalT σ).1)) (do
      let iv ← (← i.eval σ.erase).asInt
      _ <$> bumpMem σ.erase.glob op p (.memoryIndex r.id iv))
    rw [Simple.evalT_erase σ i, ok_bind, PrimTy.asInt_erase_uint, ok_bind]
    exact bumpMemT_erase σ op hp (.index r a (i.evalT σ).1) fun _ _ => rfl

end Eval

end Solidity.Core
