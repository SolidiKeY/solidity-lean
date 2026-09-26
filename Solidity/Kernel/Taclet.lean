import Solidity.Kernel.Frame

/-!
# The taclets

Phase 3 of `docs/kernel-port.md`, after mini-solkey's `Ch06_Taclets`: the
rules are one inductive judgement, `Taclet C m s p` — under the modality `m`,
the first statement `s` rewrites to the premise `p` — with one constructor
per rule, named by the solkey taclet it transcribes (`KeyTaclet`).  This file
is the **storage family**: reads, writes, aliases, declarations and deletes
over roots, members, mapping entries and array elements, the operators into a
local, and the control rules on simple conditions.  `push`/`pop`, compound
assignment and memory are the next families.

An array element out of range reverts, in `SVal.find` and `SVal.save` alike,
so an update at one fails exactly as the statement does: the kernel needs no
`inBounds` split, where the paper and `Calculus/Rules.lean` give each array
rule a box/diamond twin.  The Mapping/Array pairs (`storageIndexWriteMappingSave`,
`storageIndexWriteArraySave`) fix the `IndexTy` witness; every other index rule
is one constructor over it.

A premise is an update, new statements, a split, or a closed goal
(`Premise`).  The new statements of an unfolding rule bind **scratch names**,
passed to the constructor with a proof that each is fresh at the context the
statement leaves; the proof is what the untyped table assumes per rule
(`stmtUsesVar … = false`), and here it is a typing fact (`Frame.lean`).  The
unfolded block ends at an extension of that context (`Ctx.Sub`), so the rest
of the program still types after it.

**The paper's `lhs`.**  KeY's Step 1 taclets read `lhs = nsp.fld`: any left-hand
side.  The kernel splits left-hand sides by what they are — a local, an alias,
a declaration, a storage copy — so a Step 1 rule takes a `Hole`, a statement
with a hole for the path it reads, and one constructor still covers every
`lhs`.  `Hole.extend` moves a hole past a fresh binding.

The names follow the paper's schema variables: `sp` a simple path (a root or
an alias), `nsp` one that is not, `se` a simple value, `nse` one that is not,
`ie` a simple index, `gsp` a state variable, `lsv` an alias, `v` a local.
-/

namespace Solidity
namespace Kernel

open Semantics

variable {C : Contract}

/-! ## Simple parts -/

/-- A simple value (`se`). -/
def Val.isSimple {Γ : Ctx} {p : PrimTy} : Val C Γ p → Bool
  | .simple _ => true
  | _ => false

/-- A memory path a memory local can be bound to directly: one step from a
simple path, on a simple index. -/
def MPath.isBindable {Γ : Ctx} {T : Ty} : MPath C Γ T → Bool
  | .var .. => true
  | .loc (.field b _ _) => b.isSimple
  | .loc (.index b i) => b.isSimple && i.isSimple

/-- Not a conditional: KeY's `isValueSource` for a value (a conditional in a
write is lowered first, `ternaryToIf*`, never captured). -/
def Val.notTernary {Γ : Ctx} {p : PrimTy} : Val C Γ p → Bool
  | .ternary .. => false
  | _ => true

/-- A path an alias can be bound to directly (`lsv := sp`, `lsv := sp.fr`,
`lsv := sp[ie]`): one step from a simple path, on a simple index. -/
def SPath.isBindable {Γ : Ctx} {T : Ty} : SPath C Γ T → Bool
  | .loc (.field b _ _) => b.isSimple
  | .loc (.index _ b i) => b.isSimple && i.isSimple
  | p => p.isSimple

/-! ## Fresh bindings -/

/-- `Γ` with the fresh local `x : p`. -/
abbrev Ctx.val (Γ : Ctx) (x : Name) (p : PrimTy) : Ctx := setBy x (.stack (.prim p)) Γ

/-- `Γ` with the fresh memory local `x : R`. -/
abbrev Ctx.mem (Γ : Ctx) (x : Name) (R : RefTy) : Ctx := setBy x (.mem (.ref R)) Γ

/-- `Γ` with the fresh alias `x : R`. -/
abbrev Ctx.path (Γ : Ctx) (x : Name) (R : RefTy) : Ctx := setBy x (.path (.ref R)) Γ

/-- The local just declared. -/
def Simple.new {Γ : Ctx} (x : Name) (p : PrimTy) : Simple C (Ctx.val Γ x p) p :=
  .local x (SemanticsProperties.lookupBy_setBy_self ..)

/-- The alias just declared. -/
def SPath.new {Γ : Ctx} (x : Name) (R : RefTy) : SPath C (Ctx.path Γ x R) (.ref R) :=
  .alias x (SemanticsProperties.lookupBy_setBy_self ..)

/-- A fresh name at a larger context is fresh at a smaller one. -/
theorem isFresh_of_sub {Γ Γ' : Ctx} {y : Name} (h : Ctx.Sub C Γ Γ') (hy : isFresh C Γ' y = true) :
    isFresh C Γ y = true := by
  rw [isFresh_iff] at hy ⊢
  refine ⟨?_, hy.2⟩
  cases hΓ : lookupBy y Γ with
  | none => rfl
  | some b => rw [h.local_ y b hΓ] at hy; cases hy.1

/-- A name stays fresh past a binding of another. -/
theorem isFresh_setBy {Γ : Ctx} {x y : Name} {b : BTy} (hx : isFresh C Γ x = true) (hne : x ≠ y) :
    isFresh C (setBy y b Γ) x = true := by
  rw [isFresh_iff] at hx ⊢
  exact ⟨by rw [SemanticsProperties.lookupBy_setBy_ne hne]; exact hx.1, hx.2⟩

/-- Two fresh names bound one after the other are distinct. -/
theorem ne_of_isFresh_setBy {Γ : Ctx} {x y : Name} {b : BTy}
    (hy : isFresh C (setBy x b Γ) y = true) : x ≠ y := fun he => by
  subst he
  rw [isFresh_iff, SemanticsProperties.lookupBy_setBy_self] at hy
  cases hy.1

/-! ## Holes: the paper's `lhs = •` -/

/-- A statement with a hole for the storage path it reads: `v = •`,
`lsv = •`, `T storage x = •`, or a storage copy `l = •`. -/
inductive Hole (C : Contract) : Ctx → Ctx → Ty → Type where
  | local {Γ : Ctx} {p : PrimTy} (x : Name) (h : lookupBy x Γ = some (.stack (.prim p))) :
      Hole C Γ Γ (.prim p)
  | rebind {Γ : Ctx} {R : RefTy} (x : Name) (h : lookupBy x Γ = some (.path (.ref R))) :
      Hole C Γ Γ (.ref R)
  | decl {Γ : Ctx} (capture : Bool) (R : RefTy) (x : Name) (hx : isFresh C Γ x = true) :
      Hole C Γ (setBy x (.path (.ref R)) Γ) (.ref R)
  | copy {Γ : Ctx} {R : RefTy} (l : Loc C Γ (.ref R)) (h : (Ty.ref R).mapFree = true) :
      Hole C Γ Γ (.ref R)

namespace Hole

/-- The statement, with the path in the hole. -/
def fill {Γ Γ' : Ctx} {T : Ty} : Hole C Γ Γ' T → SPath C Γ T → Stmt C Γ Γ'
  | .local x h, .loc l => .assignLocal x h (.read l)
  | .rebind x h, p => .rebind x h p
  | .decl c R x hx, p => .declStorage c R x hx p
  | .copy l h, p => .assign l (.copy p h)

/-- A hole's statement leaves a context that extends the one it starts
from. -/
theorem sub {Γ Γ' : Ctx} {T : Ty} : Hole C Γ Γ' T → Ctx.Sub C Γ Γ'
  | .local .. | .rebind .. | .copy .. => Ctx.Sub.refl _
  | .decl _ _ _ hx => Ctx.Sub.fresh hx _

/-- The context a hole's statement leaves once the fresh `y` is bound
before it. -/
def extOut {Γ Γ' : Ctx} {T : Ty} (y : Name) (b : BTy) : Hole C Γ Γ' T → Ctx
  | .decl _ R x _ => setBy x (.path (.ref R)) (setBy y b Γ)
  | _ => setBy y b Γ

/-- The hole, past the fresh binding of `y`. -/
def extend {Γ Γ' : Ctx} {T : Ty} (y : Name) (b : BTy) (hy : isFresh C Γ' y = true) :
    (k : Hole C Γ Γ' T) → Hole C (setBy y b Γ) (k.extOut y b) T
  | .local x h => .local x ((Ctx.Sub.fresh hy b).local_ _ _ h)
  | .rebind x h => .rebind x ((Ctx.Sub.fresh hy b).local_ _ _ h)
  | .decl c R x hx =>
    .decl c R x (isFresh_setBy hx (ne_of_isFresh_setBy hy))
  | .copy l h => .copy (l.weaken (Ctx.Sub.fresh hy b)) h

/-- Binding a fresh `y` first still ends at an extension of what the hole's
statement leaves. -/
theorem extend_sub {Γ Γ' : Ctx} {T : Ty} (y : Name) (b : BTy) (hy : isFresh C Γ' y = true) :
    (k : Hole C Γ Γ' T) → Ctx.Sub C Γ' (k.extOut y b)
  | .local .. | .rebind .. | .copy .. => Ctx.Sub.fresh hy b
  | .decl _ R x hx => by
    simp only [extOut]
    have hne := ne_of_isFresh_setBy hy
    have hy' := isFresh_iff.mp hy
    refine ⟨fun z bz hz => ?_, fun r hr hroot => ?_⟩
    · by_cases hzx : z = x
      · subst hzx; rw [SemanticsProperties.lookupBy_setBy_self] at hz ⊢; exact hz
      · rw [SemanticsProperties.lookupBy_setBy_ne hzx] at hz ⊢
        have hzy : z ≠ y := fun he => by
          subst he; rw [SemanticsProperties.lookupBy_setBy_ne hzx] at hy'; rw [hy'.1] at hz; cases hz
        rw [SemanticsProperties.lookupBy_setBy_ne hzy]; exact hz
    · have hrx : r ≠ x := fun he => by
        subst he; rw [SemanticsProperties.lookupBy_setBy_self] at hr; cases hr
      have hry : r ≠ y := fun he => by subst he; rw [hy'.2] at hroot; cases hroot
      rw [SemanticsProperties.lookupBy_setBy_ne hrx] at hr ⊢
      rw [SemanticsProperties.lookupBy_setBy_ne hry]; exact hr

end Hole

/-- The memory local just declared. -/
def MPath.new {Γ : Ctx} (x : Name) (R : RefTy) : MPath C (Ctx.mem Γ x R) (.ref R) :=
  .var x (SemanticsProperties.lookupBy_setBy_self ..)

/-- A statement with a hole for the memory location it reads: `v = •` (a
value), `mv = •`, `T memory mv = •`, `l = •` (a reference). -/
inductive MHole (C : Contract) : Ctx → Ctx → Ty → Type where
  | local {Γ : Ctx} {p : PrimTy} (x : Name) (h : lookupBy x Γ = some (.stack (.prim p))) :
      MHole C Γ Γ (.prim p)
  | rebind {Γ : Ctx} {R : RefTy} (x : Name) (h : lookupBy x Γ = some (.mem (.ref R))) :
      MHole C Γ Γ (.ref R)
  | decl {Γ : Ctx} (R : RefTy) (x : Name) (hx : isFresh C Γ x = true) :
      MHole C Γ (Ctx.mem Γ x R) (.ref R)
  | write {Γ : Ctx} {R : RefTy} (l : MLoc C Γ (.ref R)) : MHole C Γ Γ (.ref R)

namespace MHole

def fill {Γ Γ' : Ctx} {T : Ty} : MHole C Γ Γ' T → MLoc C Γ T → Stmt C Γ Γ'
  | .local x h, l => .assignLocal x h (.readMem l)
  | .rebind x h, l => .rebindMem x h (.alias (.loc l))
  | .decl R x hx, l => .declMem R x hx (some (.alias (.loc l))) rfl
  | .write l', l => .assignMem l' (.ref (.loc l))

theorem sub {Γ Γ' : Ctx} {T : Ty} : MHole C Γ Γ' T → Ctx.Sub C Γ Γ'
  | .local .. | .rebind .. | .write .. => Ctx.Sub.refl _
  | .decl _ _ hx => Ctx.Sub.fresh hx _

def extOut {Γ Γ' : Ctx} {T : Ty} (y : Name) (b : BTy) : MHole C Γ Γ' T → Ctx
  | .decl R x _ => setBy x (.mem (.ref R)) (setBy y b Γ)
  | _ => setBy y b Γ

def extend {Γ Γ' : Ctx} {T : Ty} (y : Name) (b : BTy) (hy : isFresh C Γ' y = true) :
    (k : MHole C Γ Γ' T) → MHole C (setBy y b Γ) (k.extOut y b) T
  | .local x h => .local x ((Ctx.Sub.fresh hy b).local_ _ _ h)
  | .rebind x h => .rebind x ((Ctx.Sub.fresh hy b).local_ _ _ h)
  | .decl R x hx => .decl R x (isFresh_setBy hx (ne_of_isFresh_setBy hy))
  | .write l => .write (l.weaken (Ctx.Sub.fresh hy b))

theorem extend_sub {Γ Γ' : Ctx} {T : Ty} (y : Name) (b : BTy) (hy : isFresh C Γ' y = true) :
    (k : MHole C Γ Γ' T) → Ctx.Sub C Γ' (k.extOut y b)
  | .local .. | .rebind .. | .write .. => Ctx.Sub.fresh hy b
  | .decl R x hx => by
    simp only [extOut]
    have hy' := isFresh_iff.mp hy
    refine ⟨fun z bz hz => ?_, fun r hr hroot => ?_⟩
    · by_cases hzx : z = x
      · subst hzx; rw [SemanticsProperties.lookupBy_setBy_self] at hz ⊢; exact hz
      · rw [SemanticsProperties.lookupBy_setBy_ne hzx] at hz ⊢
        have hzy : z ≠ y := fun he => by
          subst he; rw [SemanticsProperties.lookupBy_setBy_ne hzx] at hy'; rw [hy'.1] at hz; cases hz
        rw [SemanticsProperties.lookupBy_setBy_ne hzy]; exact hz
    · have hrx : r ≠ x := fun he => by
        subst he; rw [SemanticsProperties.lookupBy_setBy_self] at hr; cases hr
      have hry : r ≠ y := fun he => by subst he; rw [hy'.2] at hroot; cases hroot
      rw [SemanticsProperties.lookupBy_setBy_ne hrx] at hr ⊢
      rw [SemanticsProperties.lookupBy_setBy_ne hry]; exact hr

end MHole

/-- A statement with a hole for the value it writes: `x = •` into a stack
local, `l = •` into storage. -/
inductive VHole (C : Contract) (Γ : Ctx) : PrimTy → Type where
  | local {p : PrimTy} (x : Name) (h : lookupBy x Γ = some (.stack (.prim p))) : VHole C Γ p
  | store {p : PrimTy} (l : Loc C Γ (.prim p)) : VHole C Γ p
  | mem {p : PrimTy} (l : MLoc C Γ (.prim p)) : VHole C Γ p

/-- The statement, with the value in the hole. -/
def VHole.fill {Γ : Ctx} {p : PrimTy} : VHole C Γ p → Val C Γ p → Stmt C Γ Γ
  | .local x h, v => .assignLocal x h v
  | .store l, v => .assign l (.val v)
  | .mem l, v => .assignMem l (.val v)

def VHole.weaken {Γ Γ' : Ctx} (h : Ctx.Sub C Γ Γ') {p : PrimTy} : VHole C Γ p → VHole C Γ' p
  | .local x hx => .local x (h.local_ _ _ hx)
  | .store l => .store (l.weaken h)
  | .mem l => .mem (l.weaken h)

/-- A simple source: a simple value, or a copy from a simple path. -/
def Src.isSimple {Γ : Ctx} {T : Ty} : Src C Γ T → Bool
  | .val v => v.isSimple
  | .copy p _ => p.isSimple

/-- What a source is captured as: a value into a stack local, a path into
an alias. -/
def Src.bty {Γ : Ctx} {T : Ty} : Src C Γ T → BTy
  | .val (p := p) _ => .stack (.prim p)
  | .copy (R := R) _ _ => .path (.ref R)

/-- `T se = e;` for a value, `T storage se = p;` for a path: the paper's
kind-neutral `_ se = e`. -/
def Src.decl {Γ : Ctx} {T : Ty} (x : Name) (hx : isFresh C Γ x = true) :
    (r : Src C Γ T) → Stmt C Γ (setBy x r.bty Γ)
  | .val (p := p) v => .declLocal p x hx (some v)
  | .copy (R := R) p _ => .declStorage true R x hx p

/-- The captured source, read back through its scratch name. -/
def Src.fresh {Γ : Ctx} {T : Ty} (x : Name) : (r : Src C Γ T) → Src C (setBy x r.bty Γ) T
  | .val (p := p) _ => .val (.simple (Simple.new x p))
  | .copy (R := R) _ hm => .copy (SPath.new x R) hm

/-! ## Updates and premises -/

/-- An update (KeY's `{U}`): the state change a Step 3 rule leaves in front of
the rest of the program.  Its parts are read in the state before it. -/
inductive Upd (C : Contract) (Γ : Ctx) where
  /-- `storage := save(storage, l, v)`; at a state variable, the paper's
  `store`. -/
  | save {T : Ty} (l : Loc C Γ T) (v : Src C Γ T)
  /-- `storage := delAt(storage, l)`. -/
  | delAt {T : Ty} (l : Loc C Γ T)
  /-- `v := e`. -/
  | bind {p : PrimTy} (x : Name) (e : Val C Γ p)
  /-- `lsv := sp`: an alias bound to a path. -/
  | bindPath {R : RefTy} (x : Name) (p : SPath C Γ (.ref R))
  /-- `l := l ⊕ se`: at a local `{lv := lv ⊕ se}`, in storage
  `storage := save(storage, l, find(storage, l) ⊕ se)`. -/
  | opSave {p : PrimTy} (op : BinOp) (l : OpLoc C Γ p) (se : Simple C Γ p)
  /-- `bump(l++)`: `l := l ± 1`. -/
  | bump {p : PrimTy} (op : IncDec) (l : OpLoc C Γ p)
  /-- `bump(l++) || v := l++`: the bump, and `v` bound to the expression's
  value, in parallel. -/
  | bumpBind {p : PrimTy} (x : Name) (op : IncDec) (l : OpLoc C Γ p)
  /-- `storage := save(save(storage, sp[sp.length], v), sp.length, sp.length + 1)`,
  or with `delAt` for the slot when there is no `v`. -/
  | push {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E))
  /-- `storage := save(delAt(storage, sp[sp.length - 1]), sp.length, sp.length - 1)`. -/
  | pop {E : Ty} (b : SPath C Γ (.array E))
  /-- `transfer(sadr, se)`: the debit booked. -/
  | transfer (r a : Simple C Γ .uint)
  /-- `mv := ref(p)`: a memory local bound to `p`'s object. -/
  | bindMem (x : Name) {R : RefTy} (p : MPath C Γ (.ref R))
  /-- `mv := freshId(alloc(mv, sp)) || memory := alloc(mv, sp)`: a deep copy of `sp`. -/
  | bindCopy (x : Name) {R : RefTy} (p : SPath C Γ (.ref R)) (hm : (Ty.ref R).mapFree = true)
  /-- `mv := freshId(alloc(mv)) || memory := alloc(mv)`: a fresh default object. -/
  | allocMem (x : Name) (R : RefTy)
  /-- `storage := save(storage, l, copyMem(mtSt, memory, p))`. -/
  | saveMem {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R))
  /-- `memory := write(memory, l, r)`. -/
  | writeMem {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T)

/-- The state an update leaves, from `σ`. -/
def Upd.apply (σ : State) {Γ : Ctx} : Upd C Γ → Res State
  | .save l v => do
    let sv ← v.value σ
    let (root, segs) ← l.target σ
    σ.saveStorage root segs sv
  | .delAt l => do
    let (root, segs) ← l.resolve σ
    let cur ← σ.findStorage root segs
    σ.saveStorage root segs cur.defaultOf
  | .bind x e => do pure (σ.setEnv x (.val (← e.eval σ)))
  | .bindPath x p => do
    let (root, segs) ← p.resolve σ
    pure (σ.setEnv x (.spath root segs))
  | .opSave op l se => do l.store σ op (← se.eval σ)
  | .bump op l => do pure (← l.bump σ op).1
  | .bumpBind x op l => do
    let (σ', v) ← l.bump σ op
    pure (σ'.setEnv x (.val v))
  | .push (E := E) b v => do
    let (root, segs) ← b.resolve σ
    pushAt σ E root segs (Src.pushVal σ v)
  | .pop b => do
    let (root, segs) ← b.resolve σ
    popAt σ root segs
  | .transfer r a => do
    let addr ← (← r.eval σ).asInt
    let amt ← (← a.eval σ).asInt
    transferAt σ addr amt
  | .bindMem x p => (MRhs.alias p).bind σ x
  | .bindCopy x p hm => (MRhs.copy p hm).bind σ x
  | .allocMem x R => do
    let (σ', id) ← allocDefault σ R
    pure (σ'.setEnv x (.mref id))
  | .writeMem l r => do l.write σ (← r.mval σ)
  | .saveMem l p => do
    let sv ← copyMem σ (← p.mval σ)
    let (root, segs) ← l.target σ
    σ.saveStorage root segs sv

/-- What a rule leaves to prove, for a statement from `Γ` to `Γ'`. -/
inductive Premise (C : Contract) (Γ Γ' : Ctx) where
  /-- `{U} ⟨[ ω ]⟩ φ`. -/
  | update (U : Upd C Γ)
  /-- `⟨[ P; ω ]⟩ φ`, where `P` binds the scratch names `ns` and ends at an
  extension of `Γ'`. -/
  | unfold {Γ₁ : Ctx} (ns : List Name) (P : Prog C Γ Γ₁) (h : Ctx.Sub C Γ' Γ₁)
  /-- `c = true ⟹ ⟨[ P; ω ]⟩ φ` and `c = false ⟹ ⟨[ Q; ω ]⟩ φ`. -/
  | split (c : Simple C Γ .bool) (P Q : Prog C Γ Γ')
  /-- `true` or `false` in place of the modality. -/
  | done (b : Bool)

/-- The default value's simple form: `uint x;` is `x := 0`. -/
def PrimTy.defaultSimple {Γ : Ctx} : (p : PrimTy) → Simple C Γ p
  | .bool => .bool false
  | .uint => .lit 0 rfl
  | .int => .lit 0 rfl

/-! ## The judgement -/

set_option hygiene false in
/-- `s ⇒ pr`: under the modality `m`, a taclet rewrites the first
statement `s` into the premise `pr`. -/
local notation:50 s:51 " ⇒ " pr:51 => Taclet C m s pr

/-- **The taclets of the storage family.**  Each constructor is one taclet:
the statement on the left of `⇒` is its `\find`, the premise its
`\replacewith`.  Scratch names come with freshness proofs; `up` weakens a
term past them. -/
inductive Taclet (C : Contract) (m : Modality) : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Premise C Γ Γ' → Type where
  -- Step 1: a read whose receiver or index is not simple
  /-- `lhs = nsp.fld ⇝ T storage sp = nsp; lhs = sp.fld`. -/
  | storageFieldRead_unfold_rightFst {Γ Γ' : Ctx} {s : Name} {T : Ty} (k : Hole C Γ Γ' T)
      (nsp : SPath C Γ (.struct s)) (hn : nsp.isSimple = false) (f : Name)
      (hf : C.fieldType s f = some T) (sp : Name) (hsp : isFresh C Γ' sp = true) :
      k.fill (.loc (.field nsp f hf)) ⇒
        .unfold [sp]
          (.cons (.declStorage true (.struct s) sp (isFresh_of_sub k.sub hsp) nsp)
          (.cons ((k.extend sp _ hsp).fill (.loc (.field (SPath.new sp (.struct s)) f hf))) .nil))
          (k.extend_sub sp _ hsp)
  /-- `lhs = nsp[e] ⇝ T storage sp = nsp; lhs = sp[e]`. -/
  | storageIndexRead_unfold_rightFst {Γ Γ' : Ctx} {R₀ : RefTy} {kp : PrimTy} {V : Ty} (k : Hole C Γ Γ' V)
      (it : IndexTy R₀ kp V) (nsp : SPath C Γ (.ref R₀)) (hn : nsp.isSimple = false) (e : Val C Γ kp)
      (sp : Name) (hsp : isFresh C Γ' sp = true) :
      k.fill (.loc (.index it nsp e)) ⇒
        .unfold [sp]
          (.cons (.declStorage true R₀ sp (isFresh_of_sub k.sub hsp) nsp)
          (.cons ((k.extend sp _ hsp).fill
            (.loc (.index it (SPath.new sp _) (e.weaken (Ctx.Sub.fresh (isFresh_of_sub k.sub hsp) _)))))
            .nil))
          (k.extend_sub sp _ hsp)
  /-- `lhs = sp[nse] ⇝ T ie = nse; lhs = sp[ie]`. -/
  | storageIndexRead_unfold_rightSndIndex {Γ Γ' : Ctx} {R₀ : RefTy} {kp : PrimTy} {V : Ty} (k : Hole C Γ Γ' V)
      (it : IndexTy R₀ kp V) (sp : SPath C Γ (.ref R₀)) (hs : sp.isSimple = true) (nse : Val C Γ kp)
      (hn : nse.isSimple = false) (ie : Name) (hie : isFresh C Γ' ie = true) :
      k.fill (.loc (.index it sp nse)) ⇒
        .unfold [ie]
          (.cons (.declLocal kp ie (isFresh_of_sub k.sub hie) (some nse))
          (.cons ((k.extend ie _ hie).fill
            (.loc (.index it (sp.weaken (Ctx.Sub.fresh (isFresh_of_sub k.sub hie) _))
              (.simple (Simple.new ie kp))))) .nil))
          (k.extend_sub ie _ hie)
  /-- `nlhs = sp.fld ⇝ T storage se = sp.fld; nlhs = se`: a copy from a
  member into a member or an entry goes through an alias. -/
  | storageFieldRead_unfold_rightSndResult {Γ : Ctx} {s : Name} {R : RefTy}
      (l : Loc C Γ (.ref R)) (hl : (SPath.loc l).isSimple = false) (hm : (Ty.ref R).mapFree = true)
      (sp : SPath C Γ (.struct s)) (hs : sp.isSimple = true) (f : Name)
      (hf : C.fieldType s f = some (.ref R)) (se : Name) (hse : isFresh C Γ se = true) :
      .assign l (.copy (.loc (.field sp f hf)) hm) ⇒
        .unfold [se]
          (.cons (.declStorage true R se hse (.loc (.field sp f hf)))
          (.cons (.assign (l.weaken (Ctx.Sub.fresh hse _)) (.copy (SPath.new se R) hm)) .nil))
          (Ctx.Sub.fresh hse _)
  /-- `nlhs = sp[ie] ⇝ T storage se = sp[ie]; nlhs = se`. -/
  | storageIndexRead_unfold_rightSndResult {Γ : Ctx} {R₀ : RefTy} {kp : PrimTy} {R : RefTy}
      (l : Loc C Γ (.ref R)) (hl : (SPath.loc l).isSimple = false) (hm : (Ty.ref R).mapFree = true)
      (it : IndexTy R₀ kp (.ref R)) (sp : SPath C Γ (.ref R₀)) (hs : sp.isSimple = true)
      (ie : Simple C Γ kp) (se : Name) (hse : isFresh C Γ se = true) :
      .assign l (.copy (.loc (.index it sp (.simple ie))) hm) ⇒
        .unfold [se]
          (.cons (.declStorage true R se hse (.loc (.index it sp (.simple ie))))
          (.cons (.assign (l.weaken (Ctx.Sub.fresh hse _)) (.copy (SPath.new se R) hm)) .nil))
          (Ctx.Sub.fresh hse _)
  -- Step 2: a write whose receiver, index or source is not simple
  /-- `nsp.fld = e ⇝ T se = e; T storage sp = nsp; sp.fld = se`. -/
  | storageFieldWrite_unfold_leftFst {Γ : Ctx} {s : Name} {p : PrimTy}
      (nsp : SPath C Γ (.struct s)) (hn : nsp.isSimple = false) (f : Name)
      (hf : C.fieldType s f = some (.prim p)) (e : Val C Γ p)
      (se sp : Name) (hse : isFresh C Γ se = true) (hsp : isFresh C (Ctx.val Γ se p) sp = true) (hnt : e.notTernary = true) :
      .assign (.field nsp f hf) (.val e) ⇒
        .unfold [se, sp]
          (.cons (.declLocal p se hse (some e))
          (.cons (.declStorage true (.struct s) sp hsp (nsp.weaken (Ctx.Sub.fresh hse _)))
          (.cons (.assign (.field (SPath.new sp _) f hf)
              (.val (.simple ((Simple.new se p).weaken (Ctx.Sub.fresh hsp _))))) .nil)))
          ((Ctx.Sub.fresh hse _).trans (Ctx.Sub.fresh hsp _))
  /-- `nsp.fld = sp2 ⇝ T storage sp = nsp; sp.fld = sp2`, a copy. -/
  | storageFieldWriteStorageRef_unfold_leftFst {Γ : Ctx} {s : Name} {R : RefTy}
      (nsp : SPath C Γ (.struct s)) (hn : nsp.isSimple = false) (f : Name)
      (hf : C.fieldType s f = some (.ref R)) (src : SPath C Γ (.ref R)) (hm : (Ty.ref R).mapFree = true)
      (sp : Name) (hsp : isFresh C Γ sp = true) :
      .assign (.field nsp f hf) (.copy src hm) ⇒
        .unfold [sp]
          (.cons (.declStorage true (.struct s) sp hsp nsp)
          (.cons (.assign (.field (SPath.new sp _) f hf) (.copy (src.weaken (Ctx.Sub.fresh hsp _)) hm)) .nil))
          (Ctx.Sub.fresh hsp _)
  /-- `nsp[e₁] = e₂ ⇝ T se = e₂; T storage sp = nsp; T ie = e₁; sp[ie] = se`. -/
  | storageIndexWrite_unfold_leftFst {Γ : Ctx} {R₀ : RefTy} {kp p : PrimTy}
      (it : IndexTy R₀ kp (.prim p)) (nsp : SPath C Γ (.ref R₀)) (hn : nsp.isSimple = false)
      (e₁ : Val C Γ kp) (e₂ : Val C Γ p) (se sp ie : Name) (hse : isFresh C Γ se = true)
      (hsp : isFresh C (Ctx.val Γ se p) sp = true)
      (hie : isFresh C (Ctx.path (Ctx.val Γ se p) sp R₀) ie = true) (hnt : e₂.notTernary = true) :
      .assign (.index it nsp e₁) (.val e₂) ⇒
        .unfold [se, sp, ie]
          (.cons (.declLocal p se hse (some e₂))
          (.cons (.declStorage true _ sp hsp (nsp.weaken (Ctx.Sub.fresh hse _)))
          (.cons (.declLocal kp ie hie (some (e₁.weaken ((Ctx.Sub.fresh hse _).trans (Ctx.Sub.fresh hsp _)))))
          (.cons (.assign (.index it ((SPath.new sp _).weaken (Ctx.Sub.fresh hie _)) (.simple (Simple.new ie kp)))
              (.val (.simple ((Simple.new se p).weaken ((Ctx.Sub.fresh hsp _).trans (Ctx.Sub.fresh hie _)))))) .nil))))
          (((Ctx.Sub.fresh hse _).trans (Ctx.Sub.fresh hsp _)).trans (Ctx.Sub.fresh hie _))
  /-- `nsp[e] = sp2 ⇝ T storage sp = nsp; T ie = e; sp[ie] = sp2`, a copy. -/
  | storageIndexWriteStorageRef_unfold_leftFst {Γ : Ctx} {R₀ : RefTy} {kp : PrimTy} {R : RefTy}
      (it : IndexTy R₀ kp (.ref R)) (nsp : SPath C Γ (.ref R₀)) (hn : nsp.isSimple = false)
      (e : Val C Γ kp) (src : SPath C Γ (.ref R)) (hm : (Ty.ref R).mapFree = true)
      (sp ie : Name) (hsp : isFresh C Γ sp = true)
      (hie : isFresh C (Ctx.path Γ sp R₀) ie = true) :
      .assign (.index it nsp e) (.copy src hm) ⇒
        .unfold [sp, ie]
          (.cons (.declStorage true _ sp hsp nsp)
          (.cons (.declLocal kp ie hie (some (e.weaken (Ctx.Sub.fresh hsp _))))
          (.cons (.assign (.index it ((SPath.new sp _).weaken (Ctx.Sub.fresh hie _)) (.simple (Simple.new ie kp)))
              (.copy (src.weaken ((Ctx.Sub.fresh hsp _).trans (Ctx.Sub.fresh hie _))) hm)) .nil)))
          ((Ctx.Sub.fresh hsp _).trans (Ctx.Sub.fresh hie _))
  /-- `sp[nse] = e ⇝ T se = e; T ie = nse; sp[ie] = se`. -/
  | storageIndexWriteNonSimpleIndexCapture {Γ : Ctx} {R₀ : RefTy} {kp p : PrimTy}
      (it : IndexTy R₀ kp (.prim p)) (sp : SPath C Γ (.ref R₀)) (hs : sp.isSimple = true)
      (nse : Val C Γ kp) (hn : nse.isSimple = false) (e : Val C Γ p) (se ie : Name)
      (hse : isFresh C Γ se = true) (hie : isFresh C (Ctx.val Γ se p) ie = true) (hnt : e.notTernary = true) :
      .assign (.index it sp nse) (.val e) ⇒
        .unfold [se, ie]
          (.cons (.declLocal p se hse (some e))
          (.cons (.declLocal kp ie hie (some (nse.weaken (Ctx.Sub.fresh hse _))))
          (.cons (.assign (.index it (sp.weaken ((Ctx.Sub.fresh hse _).trans (Ctx.Sub.fresh hie _)))
                (.simple (Simple.new ie kp)))
              (.val (.simple ((Simple.new se p).weaken (Ctx.Sub.fresh hie _))))) .nil)))
          ((Ctx.Sub.fresh hse _).trans (Ctx.Sub.fresh hie _))
  /-- `sp[nse] = sp2 ⇝ T ie = nse; sp[ie] = sp2`, a copy. -/
  | storageIndexWriteStorageRefNonSimpleIndexCapture {Γ : Ctx} {R₀ : RefTy} {kp : PrimTy} {R : RefTy}
      (it : IndexTy R₀ kp (.ref R)) (sp : SPath C Γ (.ref R₀)) (hs : sp.isSimple = true)
      (nse : Val C Γ kp) (hn : nse.isSimple = false) (src : SPath C Γ (.ref R))
      (hm : (Ty.ref R).mapFree = true) (ie : Name) (hie : isFresh C Γ ie = true) :
      .assign (.index it sp nse) (.copy src hm) ⇒
        .unfold [ie]
          (.cons (.declLocal kp ie hie (some nse))
          (.cons (.assign (.index it (sp.weaken (Ctx.Sub.fresh hie _)) (.simple (Simple.new ie kp)))
              (.copy (src.weaken (Ctx.Sub.fresh hie _)) hm)) .nil))
          (Ctx.Sub.fresh hie _)
  /-- `gsp = nse ⇝ T se = nse; gsp = se`. -/
  | storageRootWriteValueRhsCapture {Γ : Ctx} {p : PrimTy} (r : Name)
      (hΓ : lookupBy r Γ = none) (hr : C.rootType r = some (.prim p)) (nse : Val C Γ p)
      (hn : nse.isSimple = false) (se : Name) (hse : isFresh C Γ se = true) (hnt : nse.notTernary = true) :
      .assign (.root r hΓ hr) (.val nse) ⇒
        .unfold [se]
          (.cons (.declLocal p se hse (some nse))
          (.cons (.assign ((Loc.root r hΓ hr).weaken (Ctx.Sub.fresh hse _)) (.val (.simple (Simple.new se p))))
            .nil))
          (Ctx.Sub.fresh hse _)
  /-- `sp.fld = nse ⇝ T se = nse; sp.fld = se`. -/
  | fieldWriteValueRhsCapture {Γ : Ctx} {s : Name} {p : PrimTy} (sp : SPath C Γ (.struct s))
      (hs : sp.isSimple = true) (f : Name) (hf : C.fieldType s f = some (.prim p)) (nse : Val C Γ p)
      (hn : nse.isSimple = false) (se : Name) (hse : isFresh C Γ se = true) (hnt : nse.notTernary = true) :
      .assign (.field sp f hf) (.val nse) ⇒
        .unfold [se]
          (.cons (.declLocal p se hse (some nse))
          (.cons (.assign ((Loc.field sp f hf).weaken (Ctx.Sub.fresh hse _)) (.val (.simple (Simple.new se p))))
            .nil))
          (Ctx.Sub.fresh hse _)
  /-- `sp[ie] = nse ⇝ T se = nse; sp[ie] = se`. -/
  | indexWriteValueRhsCapture {Γ : Ctx} {R₀ : RefTy} {kp p : PrimTy} (it : IndexTy R₀ kp (.prim p)) (sp : SPath C Γ (.ref R₀))
      (hs : sp.isSimple = true) (ie : Simple C Γ kp) (nse : Val C Γ p) (hn : nse.isSimple = false)
      (se : Name) (hse : isFresh C Γ se = true) (hnt : nse.notTernary = true) :
      .assign (.index it sp (.simple ie)) (.val nse) ⇒
        .unfold [se]
          (.cons (.declLocal p se hse (some nse))
          (.cons (.assign ((Loc.index it sp (.simple ie)).weaken (Ctx.Sub.fresh hse _))
              (.val (.simple (Simple.new se p)))) .nil))
          (Ctx.Sub.fresh hse _)
  /-- `delete nsp.fld ⇝ T storage sp = nsp; delete sp.fld`. -/
  | storageFieldDelete_unfold_leftFst {Γ : Ctx} {s : Name} {T : Ty} (nsp : SPath C Γ (.struct s))
      (hn : nsp.isSimple = false) (f : Name) (hf : C.fieldType s f = some T) (sp : Name)
      (hsp : isFresh C Γ sp = true) :
      .delete (.field nsp f hf) ⇒
        .unfold [sp]
          (.cons (.declStorage true (.struct s) sp hsp nsp)
          (.cons (.delete (.field (SPath.new sp _) f hf)) .nil))
          (Ctx.Sub.fresh hsp _)
  /-- `delete nsp[e] ⇝ T storage sp = nsp; delete sp[e]`. -/
  | storageIndexDelete_unfold_leftFst {Γ : Ctx} {R₀ : RefTy} {kp : PrimTy} {V : Ty}
      (it : IndexTy R₀ kp V) (nsp : SPath C Γ (.ref R₀)) (hn : nsp.isSimple = false) (e : Val C Γ kp)
      (sp : Name) (hsp : isFresh C Γ sp = true) :
      .delete (.index it nsp e) ⇒
        .unfold [sp]
          (.cons (.declStorage true _ sp hsp nsp)
          (.cons (.delete (.index it (SPath.new sp _) (e.weaken (Ctx.Sub.fresh hsp _)))) .nil))
          (Ctx.Sub.fresh hsp _)
  /-- `delete sp[nse] ⇝ T ie = nse; delete sp[ie]`. -/
  | storageIndexDeleteNonSimpleIndexCapture {Γ : Ctx} {R₀ : RefTy} {kp : PrimTy} {V : Ty}
      (it : IndexTy R₀ kp V) (sp : SPath C Γ (.ref R₀)) (hs : sp.isSimple = true) (nse : Val C Γ kp)
      (hn : nse.isSimple = false) (ie : Name) (hie : isFresh C Γ ie = true) :
      .delete (.index it sp nse) ⇒
        .unfold [ie]
          (.cons (.declLocal kp ie hie (some nse))
          (.cons (.delete (.index it (sp.weaken (Ctx.Sub.fresh hie _)) (.simple (Simple.new ie kp)))) .nil))
          (Ctx.Sub.fresh hie _)
  -- Step 3: an update
  /-- `T v = e ⇝ T v; v = e`. -/
  | localValueDeclInitDrop {Γ : Ctx} {p : PrimTy} (x : Name) (hx : isFresh C Γ x = true)
      (e : Val C Γ p) :
      .declLocal p x hx (some e) ⇒
        .unfold []
          (.cons (.declLocal p x hx none)
          (.cons (.assignLocal x (SemanticsProperties.lookupBy_setBy_self ..)
            (e.weaken (Ctx.Sub.fresh hx _))) .nil))
          (Ctx.Sub.refl _)
  /-- `T v ⇝ { v := defVal(T) }`. -/
  | valueDeclSkip {Γ : Ctx} {p : PrimTy} (x : Name) (hx : isFresh C Γ x = true) :
      .declLocal p x hx none ⇒ .update (.bind x (.simple (PrimTy.defaultSimple p)))
  /-- `v = se ⇝ { v := se }`. -/
  | localValueAssign {Γ : Ctx} {p : PrimTy} (x : Name) (h : lookupBy x Γ = some (.stack (.prim p)))
      (se : Simple C Γ p) :
      .assignLocal x h (.simple se) ⇒ .update (.bind x (.simple se))
  /-- `v = gsp ⇝ { v := select(storage, gsp) }`. -/
  | storageRootReadSelect {Γ : Ctx} {p : PrimTy} (x : Name) (h : lookupBy x Γ = some (.stack (.prim p)))
      (r : Name) (hΓ : lookupBy r Γ = none) (hr : C.rootType r = some (.prim p)) :
      .assignLocal x h (.read (.root r hΓ hr)) ⇒ .update (.bind x (.read (.root r hΓ hr)))
  /-- `v = sp.fld ⇝ { v := find(storage, sp.fld) }`. -/
  | storageFieldReadFind {Γ : Ctx} {s : Name} {p : PrimTy} (x : Name)
      (h : lookupBy x Γ = some (.stack (.prim p))) (sp : SPath C Γ (.struct s)) (hs : sp.isSimple = true)
      (f : Name) (hf : C.fieldType s f = some (.prim p)) :
      .assignLocal x h (.read (.field sp f hf)) ⇒ .update (.bind x (.read (.field sp f hf)))
  /-- `v = sp[ie] ⇝ { v := find(storage, sp[ie]) }`. -/
  | storageIndexReadMappingFind {Γ : Ctx} {kp p : PrimTy} (x : Name)
      (h : lookupBy x Γ = some (.stack (.prim p))) (sp : SPath C Γ (.mapping (.prim kp) (.prim p)))
      (hs : sp.isSimple = true) (ie : Simple C Γ kp) :
      .assignLocal x h (.read (.index .map sp (.simple ie))) ⇒
        .update (.bind x (.read (.index .map sp (.simple ie))))
  /-- `gsp = se ⇝ { storage := store(storage, gsp, se) }`. -/
  | storageIndexReadArrayFind {Γ : Ctx} {p : PrimTy} (x : Name)
      (h : lookupBy x Γ = some (.stack (.prim p))) (sp : SPath C Γ (.array (.prim p)))
      (hs : sp.isSimple = true) (ie : Simple C Γ .uint) :
      .assignLocal x h (.read (.index .arr sp (.simple ie))) ⇒
        .update (.bind x (.read (.index .arr sp (.simple ie))))
  /-- `gsp = se ⇝ { storage := store(storage, gsp, se) }`. -/
  | storageRootWriteStore {Γ : Ctx} {p : PrimTy} (r : Name) (hΓ : lookupBy r Γ = none)
      (hr : C.rootType r = some (.prim p)) (se : Simple C Γ p) :
      .assign (.root r hΓ hr) (.val (.simple se)) ⇒ .update (.save (.root r hΓ hr) (.val (.simple se)))
  /-- `gsp = sp ⇝ { storage := store(storage, gsp, select(storage, sp)) }`. -/
  | storageRootWriteCopySource {Γ : Ctx} {R : RefTy} (r : Name) (hΓ : lookupBy r Γ = none)
      (hr : C.rootType r = some (.ref R)) (sp : SPath C Γ (.ref R)) (hs : sp.isSimple = true)
      (hm : (Ty.ref R).mapFree = true) :
      .assign (.root r hΓ hr) (.copy sp hm) ⇒ .update (.save (.root r hΓ hr) (.copy sp hm))
  /-- `gsp = sp.fr ⇝ { storage := store(storage, gsp, find(storage, sp.fr)) }`. -/
  | storageFieldReadStoreRoot {Γ : Ctx} {s : Name} {R : RefTy} (r : Name) (hΓ : lookupBy r Γ = none)
      (hr : C.rootType r = some (.ref R)) (sp : SPath C Γ (.struct s)) (hs : sp.isSimple = true)
      (f : Name) (hf : C.fieldType s f = some (.ref R)) (hm : (Ty.ref R).mapFree = true) :
      .assign (.root r hΓ hr) (.copy (.loc (.field sp f hf)) hm) ⇒
        .update (.save (.root r hΓ hr) (.copy (.loc (.field sp f hf)) hm))
  /-- `gsp = sp[ie] ⇝ { storage := store(storage, gsp, find(storage, sp[ie])) }`. -/
  | storageIndexReadMappingStoreRoot {Γ : Ctx} {kp : PrimTy} {R : RefTy} (r : Name)
      (hΓ : lookupBy r Γ = none) (hr : C.rootType r = some (.ref R))
      (sp : SPath C Γ (.mapping (.prim kp) (.ref R))) (hs : sp.isSimple = true) (ie : Simple C Γ kp)
      (hm : (Ty.ref R).mapFree = true) :
      .assign (.root r hΓ hr) (.copy (.loc (.index .map sp (.simple ie))) hm) ⇒
        .update (.save (.root r hΓ hr) (.copy (.loc (.index .map sp (.simple ie))) hm))
  /-- `sp.fld = se ⇝ { storage := save(storage, sp.fld, se) }`. -/
  | storageIndexReadArrayStoreRoot {Γ : Ctx} {R : RefTy} (r : Name)
      (hΓ : lookupBy r Γ = none) (hr : C.rootType r = some (.ref R))
      (sp : SPath C Γ (.array (.ref R))) (hs : sp.isSimple = true) (ie : Simple C Γ .uint)
      (hm : (Ty.ref R).mapFree = true) :
      .assign (.root r hΓ hr) (.copy (.loc (.index .arr sp (.simple ie))) hm) ⇒
        .update (.save (.root r hΓ hr) (.copy (.loc (.index .arr sp (.simple ie))) hm))
  /-- `sp.fld = se ⇝ { storage := save(storage, sp.fld, se) }`. -/
  | storageFieldWriteSave {Γ : Ctx} {s : Name} {p : PrimTy} (sp : SPath C Γ (.struct s))
      (hs : sp.isSimple = true) (f : Name) (hf : C.fieldType s f = some (.prim p)) (se : Simple C Γ p) :
      .assign (.field sp f hf) (.val (.simple se)) ⇒ .update (.save (.field sp f hf) (.val (.simple se)))
  /-- `sp1.fld = sp2 ⇝ { storage := save(storage, sp1.fld, find(storage, sp2)) }`. -/
  | storageFieldWriteCopySource {Γ : Ctx} {s : Name} {R : RefTy} (sp : SPath C Γ (.struct s))
      (hs : sp.isSimple = true) (f : Name) (hf : C.fieldType s f = some (.ref R))
      (sp₂ : SPath C Γ (.ref R)) (hs₂ : sp₂.isSimple = true) (hm : (Ty.ref R).mapFree = true) :
      .assign (.field sp f hf) (.copy sp₂ hm) ⇒ .update (.save (.field sp f hf) (.copy sp₂ hm))
  /-- `sp[ie] = se ⇝ { storage := save(storage, sp[ie], se) }`. -/
  | storageIndexWriteMappingSave {Γ : Ctx} {kp p : PrimTy}
      (sp : SPath C Γ (.mapping (.prim kp) (.prim p))) (hs : sp.isSimple = true) (ie : Simple C Γ kp)
      (se : Simple C Γ p) :
      .assign (.index .map sp (.simple ie)) (.val (.simple se)) ⇒
        .update (.save (.index .map sp (.simple ie)) (.val (.simple se)))
  /-- `sp[ie] = sp2 ⇝ { storage := save(storage, sp[ie], find(storage, sp2)) }`. -/
  | storageIndexWriteArraySave {Γ : Ctx} {p : PrimTy}
      (sp : SPath C Γ (.array (.prim p))) (hs : sp.isSimple = true) (ie : Simple C Γ .uint)
      (se : Simple C Γ p) :
      .assign (.index .arr sp (.simple ie)) (.val (.simple se)) ⇒
        .update (.save (.index .arr sp (.simple ie)) (.val (.simple se)))
  /-- `sp[ie] = sp2 ⇝ { storage := save(storage, sp[ie], find(storage, sp2)) }`. -/
  | storageIndexWriteMappingCopySource {Γ : Ctx} {kp : PrimTy} {R : RefTy}
      (sp : SPath C Γ (.mapping (.prim kp) (.ref R))) (hs : sp.isSimple = true) (ie : Simple C Γ kp)
      (sp₂ : SPath C Γ (.ref R)) (hs₂ : sp₂.isSimple = true) (hm : (Ty.ref R).mapFree = true) :
      .assign (.index .map sp (.simple ie)) (.copy sp₂ hm) ⇒
        .update (.save (.index .map sp (.simple ie)) (.copy sp₂ hm))
  /-- `lsv = sp ⇝ { lsv := sp }`. -/
  | storageIndexWriteArrayCopySource {Γ : Ctx} {R : RefTy}
      (sp : SPath C Γ (.array (.ref R))) (hs : sp.isSimple = true) (ie : Simple C Γ .uint)
      (sp₂ : SPath C Γ (.ref R)) (hs₂ : sp₂.isSimple = true) (hm : (Ty.ref R).mapFree = true) :
      .assign (.index .arr sp (.simple ie)) (.copy sp₂ hm) ⇒
        .update (.save (.index .arr sp (.simple ie)) (.copy sp₂ hm))
  /-- `lsv = sp ⇝ { lsv := sp }`. -/
  | storageLocalRootRebind {Γ : Ctx} {R : RefTy} (x : Name) (h : lookupBy x Γ = some (.path (.ref R)))
      (sp : SPath C Γ (.ref R)) (hs : sp.isSimple = true) :
      .rebind x h sp ⇒ .update (.bindPath x sp)
  /-- `lsv = sp.fr ⇝ { lsv := sp.fr }`. -/
  | storageFieldReadBindLocalRoot {Γ : Ctx} {s : Name} {R : RefTy} (x : Name)
      (h : lookupBy x Γ = some (.path (.ref R))) (sp : SPath C Γ (.struct s)) (hs : sp.isSimple = true)
      (f : Name) (hf : C.fieldType s f = some (.ref R)) :
      .rebind x h (.loc (.field sp f hf)) ⇒ .update (.bindPath x (.loc (.field sp f hf)))
  /-- `lsv = sp[ie] ⇝ { lsv := sp[ie] }`. -/
  | storageIndexReadMappingBindLocalRoot {Γ : Ctx} {kp : PrimTy} {R : RefTy} (x : Name)
      (h : lookupBy x Γ = some (.path (.ref R))) (sp : SPath C Γ (.mapping (.prim kp) (.ref R)))
      (hs : sp.isSimple = true) (ie : Simple C Γ kp) :
      .rebind x h (.loc (.index .map sp (.simple ie))) ⇒ .update (.bindPath x (.loc (.index .map sp (.simple ie))))
  /-- `T storage lsv = p ⇝ { lsv := p }`, for a path an alias binds directly.
  KeY splits this into `storageLocalDeclInitDrop` and a rebind; the kernel has
  no uninitialised `T storage lsv;` to split into. -/
  | storageIndexReadArrayBindLocalRoot {Γ : Ctx} {R : RefTy} (x : Name)
      (h : lookupBy x Γ = some (.path (.ref R))) (sp : SPath C Γ (.array (.ref R)))
      (hs : sp.isSimple = true) (ie : Simple C Γ .uint) :
      .rebind x h (.loc (.index .arr sp (.simple ie))) ⇒ .update (.bindPath x (.loc (.index .arr sp (.simple ie))))
  /-- `T storage lsv = p ⇝ { lsv := p }`, for a path an alias binds directly.
  KeY splits this into `storageLocalDeclInitDrop` and a rebind; the kernel has
  no uninitialised `T storage lsv;` to split into. -/
  | storageLocalDeclInitDrop {Γ : Ctx} {R : RefTy} (capture : Bool) (x : Name)
      (hx : isFresh C Γ x = true) (p : SPath C Γ (.ref R)) (hb : p.isBindable = true) :
      .declStorage capture R x hx p ⇒ .update (.bindPath x p)
  /-- `delete gsp ⇝ { storage := delAt(storage, gsp) }`. -/
  | storageRootDelete {Γ : Ctx} {T : Ty} (r : Name) (hΓ : lookupBy r Γ = none)
      (hr : C.rootType r = some T) :
      .delete (.root r hΓ hr) ⇒ .update (.delAt (.root r hΓ hr))
  /-- `delete sp.fld ⇝ { storage := delAt(storage, sp.fld) }`. -/
  | storageFieldDelete {Γ : Ctx} {s : Name} {T : Ty} (sp : SPath C Γ (.struct s))
      (hs : sp.isSimple = true) (f : Name) (hf : C.fieldType s f = some T) :
      .delete (.field sp f hf) ⇒ .update (.delAt (.field sp f hf))
  /-- `delete sp[ie] ⇝ { storage := delAt(storage, sp[ie]) }`. -/
  | storageIndexDelete {Γ : Ctx} {R₀ : RefTy} {kp : PrimTy} {V : Ty} (it : IndexTy R₀ kp V) (sp : SPath C Γ (.ref R₀))
      (hs : sp.isSimple = true) (ie : Simple C Γ kp) :
      .delete (.index it sp (.simple ie)) ⇒ .update (.delAt (.index it sp (.simple ie)))
  -- Operators into a local.  The families are one constructor each, over
  -- the operator; the solkey taclet is per operator (`additionAssignment`, …).
  /-- `v = se₁ ⊕ se₂ ⇝ { v := se₁ ⊕ se₂ }`.  A division by zero or an
  overflow makes the update fail as the statement does, so the kernel needs no
  guard. -/
  | binopAssignment {Γ : Ctx} {p q : PrimTy} (op : BinOp) (hop : op.accepts p = true)
      (hq : op.ret p = q) (x : Name) (h : lookupBy x Γ = some (.stack (.prim q))) (a b : Simple C Γ p) :
      .assignLocal x h (.binop op hop hq (.simple a) (.simple b)) ⇒
        .update (.bind x (.binop op hop hq (.simple a) (.simple b)))
  /-- `v = nse ⊕ e ⇝ T se = nse; v = se ⊕ e`. -/
  | binopUnfoldLeft {Γ : Ctx} {p q : PrimTy} (op : BinOp) (hop : op.accepts p = true)
      (hq : op.ret p = q) (x : Name) (h : lookupBy x Γ = some (.stack (.prim q))) (nse : Val C Γ p)
      (hn : nse.isSimple = false) (e : Val C Γ p) (se : Name) (hse : isFresh C Γ se = true) :
      .assignLocal x h (.binop op hop hq nse e) ⇒
        .unfold [se]
          (.cons (.declLocal p se hse (some nse))
          (.cons (.assignLocal x ((Ctx.Sub.fresh hse _).local_ _ _ h)
            (.binop op hop hq (.simple (Simple.new se p)) (e.weaken (Ctx.Sub.fresh hse _)))) .nil))
          (Ctx.Sub.fresh hse _)
  /-- `v = se ⊕ nse ⇝ T se' = nse; v = se ⊕ se'`, for an operator that does
  not short-circuit. -/
  | binopUnfoldRight {Γ : Ctx} {p q : PrimTy} (op : BinOp) (hop : op.accepts p = true)
      (hq : op.ret p = q) (hsc : op.shortCircuits = false) (x : Name)
      (h : lookupBy x Γ = some (.stack (.prim q))) (a : Simple C Γ p) (nse : Val C Γ p)
      (hn : nse.isSimple = false) (se : Name) (hse : isFresh C Γ se = true) :
      .assignLocal x h (.binop op hop hq (.simple a) nse) ⇒
        .unfold [se]
          (.cons (.declLocal p se hse (some nse))
          (.cons (.assignLocal x ((Ctx.Sub.fresh hse _).local_ _ _ h)
            (.binop op hop hq (.simple (a.weaken (Ctx.Sub.fresh hse _))) (.simple (Simple.new se p)))) .nil))
          (Ctx.Sub.fresh hse _)
  /-- `v = se && nse ⇝ if (se) { v = nse; v = v && true; } else { v = false; }`.
  KeY's residual ends with `v = nse;`; the kernel's re-applies the operator to
  the value it read, so that a non-boolean `nse` gets stuck here too, as the
  original does, and the rule needs no typed state. -/
  | logicalAndShortCircuitRhs {Γ : Ctx} (hop : BinOp.accepts .and .bool = true)
      (hq : BinOp.ret .and .bool = .bool) (x : Name) (h : lookupBy x Γ = some (.stack (.prim .bool)))
      (a : Simple C Γ .bool) (nse : Val C Γ .bool) (hn : nse.isSimple = false) :
      .assignLocal x h (.binop .and hop hq (.simple a) nse) ⇒
        .unfold []
          (.cons (.ite a
              (.cons (.assignLocal x h nse)
                (.cons (.assignLocal x h (.binop .and hop hq (.simple (.local x h)) (.simple (.bool true))))
                  .nil))
            (.cons (.assignLocal x h (.simple (.bool false))) .nil)) .nil)
          (Ctx.Sub.refl _)
  /-- `v = se || nse ⇝ if (se) { v = true; } else { v = nse; v = v || false; }`. -/
  | logicalOrShortCircuitRhs {Γ : Ctx} (hop : BinOp.accepts .or .bool = true)
      (hq : BinOp.ret .or .bool = .bool) (x : Name) (h : lookupBy x Γ = some (.stack (.prim .bool)))
      (a : Simple C Γ .bool) (nse : Val C Γ .bool) (hn : nse.isSimple = false) :
      .assignLocal x h (.binop .or hop hq (.simple a) nse) ⇒
        .unfold []
          (.cons (.ite a (.cons (.assignLocal x h (.simple (.bool true))) .nil)
            (.cons (.assignLocal x h nse)
              (.cons (.assignLocal x h (.binop .or hop hq (.simple (.local x h)) (.simple (.bool false))))
                .nil))) .nil)
          (Ctx.Sub.refl _)
  /-- `v = ⊖se ⇝ { v := ⊖se }`. -/
  | unopAssignment {Γ : Ctx} {p q : PrimTy} (op : UnOp) (hop : op.accepts p = true)
      (hq : op.ret p = q) (x : Name) (h : lookupBy x Γ = some (.stack (.prim q))) (a : Simple C Γ p) :
      .assignLocal x h (.unop op hop hq (.simple a)) ⇒ .update (.bind x (.unop op hop hq (.simple a)))
  /-- `v = ⊖nse ⇝ T se = nse; v = ⊖se`. -/
  | unopCapture {Γ : Ctx} {p q : PrimTy} (op : UnOp) (hop : op.accepts p = true)
      (hq : op.ret p = q) (x : Name) (h : lookupBy x Γ = some (.stack (.prim q))) (nse : Val C Γ p)
      (hn : nse.isSimple = false) (se : Name) (hse : isFresh C Γ se = true) :
      .assignLocal x h (.unop op hop hq nse) ⇒
        .unfold [se]
          (.cons (.declLocal p se hse (some nse))
          (.cons (.assignLocal x ((Ctx.Sub.fresh hse _).local_ _ _ h)
            (.unop op hop hq (.simple (Simple.new se p)))) .nil))
          (Ctx.Sub.fresh hse _)
  -- Memory: a read whose receiver or index is not simple
  /-- `lhs = nmp.fld ⇝ T memory mv = nmp; lhs = mv.fld`. -/
  | memoryFieldRead_unfold_rightFst {Γ Γ' : Ctx} {s : Name} {T : Ty} (k : MHole C Γ Γ' T)
      (nmp : MPath C Γ (.struct s)) (hn : nmp.isSimple = false) (f : Name)
      (hf : C.fieldType s f = some T) (mv : Name) (hmv : isFresh C Γ' mv = true) :
      k.fill (.field nmp f hf) ⇒
        .unfold [mv]
          (.cons (.declMem (.struct s) mv (isFresh_of_sub k.sub hmv) (some (.alias nmp)) rfl)
          (.cons ((k.extend mv _ hmv).fill (.field (MPath.new mv (.struct s)) f hf)) .nil))
          (k.extend_sub mv _ hmv)
  /-- `lhs = nmp[e] ⇝ T memory mv = nmp; lhs = mv[e]`. -/
  | memoryIndexRead_unfold_rightFst {Γ Γ' : Ctx} {E : Ty} (k : MHole C Γ Γ' E)
      (nmp : MPath C Γ (.array E)) (hn : nmp.isSimple = false) (e : Val C Γ .uint) (mv : Name)
      (hmv : isFresh C Γ' mv = true) :
      k.fill (.index nmp e) ⇒
        .unfold [mv]
          (.cons (.declMem (.array E) mv (isFresh_of_sub k.sub hmv) (some (.alias nmp)) rfl)
          (.cons ((k.extend mv _ hmv).fill
            (.index (MPath.new mv _) (e.weaken (Ctx.Sub.fresh (isFresh_of_sub k.sub hmv) _)))) .nil))
          (k.extend_sub mv _ hmv)
  /-- `lhs = mv[nse] ⇝ T ie = nse; lhs = mv[ie]`. -/
  | memoryIndexRead_unfold_rightSndIndex {Γ Γ' : Ctx} {E : Ty} (k : MHole C Γ Γ' E)
      (b : MPath C Γ (.array E)) (hb : b.isSimple = true) (nse : Val C Γ .uint)
      (hn : nse.isSimple = false) (ie : Name) (hie : isFresh C Γ' ie = true) :
      k.fill (.index b nse) ⇒
        .unfold [ie]
          (.cons (.declLocal .uint ie (isFresh_of_sub k.sub hie) (some nse))
          (.cons ((k.extend ie _ hie).fill
            (.index (b.weaken (Ctx.Sub.fresh (isFresh_of_sub k.sub hie) _)) (.simple (Simple.new ie .uint))))
            .nil))
          (k.extend_sub ie _ hie)
  -- Memory: reads and aliases
  /-- `v = mv.fld ⇝ {v := mv.fld}`. -/
  | memoryFieldReadHeap {Γ : Ctx} {s : Name} {p : PrimTy} (x : Name)
      (h : lookupBy x Γ = some (.stack (.prim p))) (b : MPath C Γ (.struct s)) (hb : b.isSimple = true)
      (f : Name) (hf : C.fieldType s f = some (.prim p)) :
      .assignLocal x h (.readMem (.field b f hf)) ⇒ .update (.bind x (.readMem (.field b f hf)))
  /-- `v = mv[ie] ⇝ {v := mv[ie]}`: no bounds split, the update reverts as the
  statement does. -/
  | memoryIndexReadHeap {Γ : Ctx} {p : PrimTy} (x : Name) (h : lookupBy x Γ = some (.stack (.prim p)))
      (b : MPath C Γ (.array (.prim p))) (hb : b.isSimple = true) (ie : Simple C Γ .uint) :
      .assignLocal x h (.readMem (.index b (.simple ie))) ⇒
        .update (.bind x (.readMem (.index b (.simple ie))))
  /-- `mv1 = mv2 ⇝ {mv1 := ref(mv2)}`. -/
  | memoryRootAlias {Γ : Ctx} {R : RefTy} (x : Name) (h : lookupBy x Γ = some (.mem (.ref R)))
      (y : Name) (hy : lookupBy y Γ = some (.mem (.ref R))) :
      .rebindMem x h (.alias (.var y hy)) ⇒ .update (.bindMem x (.var y hy))
  /-- `mv1 = mv2.fr ⇝ {mv1 := ref(mv2.fr)}`. -/
  | memoryFieldReadAliasRoot {Γ : Ctx} {s : Name} {R : RefTy} (x : Name)
      (h : lookupBy x Γ = some (.mem (.ref R))) (b : MPath C Γ (.struct s)) (hb : b.isSimple = true)
      (f : Name) (hf : C.fieldType s f = some (.ref R)) :
      .rebindMem x h (.alias (.loc (.field b f hf))) ⇒ .update (.bindMem x (.loc (.field b f hf)))
  /-- `mv1 = mv2[ie] ⇝ {mv1 := ref(mv2[ie])}`. -/
  | memoryIndexReadAliasRoot {Γ : Ctx} {R : RefTy} (x : Name) (h : lookupBy x Γ = some (.mem (.ref R)))
      (b : MPath C Γ (.array (.ref R))) (hb : b.isSimple = true) (ie : Simple C Γ .uint) :
      .rebindMem x h (.alias (.loc (.index b (.simple ie)))) ⇒
        .update (.bindMem x (.loc (.index b (.simple ie))))
  /-- `T memory mv = mpath ⇝ {mv := ref(mpath)}`, for a path one step from a
  simple one (KeY drops the declaration to `mv = mpath` and binds). -/
  | memoryLocalDeclInitDrop {Γ : Ctx} (R : RefTy) (x : Name) (hx : isFresh C Γ x = true)
      (p : MPath C Γ (.ref R)) (hp : p.isBindable = true) (hd) :
      .declMem R x hx (some (.alias p)) hd ⇒ .update (.bindMem x p)
  /-- `T memory mv; ⇝ {mv := freshId(alloc(mv)) || memory := alloc(mv)}`. -/
  | memoryDeclFreshAlloc {Γ : Ctx} (R : RefTy) (x : Name) (hx : isFresh C Γ x = true) (hd) :
      .declMem R x hx none hd ⇒ .update (.allocMem x R)
  -- Memory: copies from storage
  /-- `T memory mv = sp ⇝ {mv := freshId(alloc(mv, sp)) || memory := alloc(mv, sp)}`. -/
  | storageToMemoryDeclCopyRoot {Γ : Ctx} (R : RefTy) (x : Name) (hx : isFresh C Γ x = true)
      (sp : SPath C Γ (.ref R)) (hs : sp.isSimple = true) (hm : (Ty.ref R).mapFree = true) (hd) :
      .declMem R x hx (some (.copy sp hm)) hd ⇒ .update (.bindCopy x sp hm)
  /-- `T memory mv = sp.fld ⇝ {mv := freshId(alloc(mv, sp.fld)) || …}`. -/
  | storageToMemoryDeclCopyField {Γ : Ctx} {s : Name} (R : RefTy) (x : Name) (hx : isFresh C Γ x = true)
      (sp : SPath C Γ (.struct s)) (hs : sp.isSimple = true) (f : Name) (hf : C.fieldType s f = some (.ref R))
      (hm : (Ty.ref R).mapFree = true) (hd) :
      .declMem R x hx (some (.copy (.loc (.field sp f hf)) hm)) hd ⇒
        .update (.bindCopy x (.loc (.field sp f hf)) hm)
  /-- `T memory mv = path ⇝ T storage sp = path; T memory mv = sp`, for any
  other path (KeY's taclet captures a member's receiver; the kernel captures
  the whole path, which covers entries too). -/
  | storageToMemoryDeclUnfoldRightFst {Γ : Ctx} (R : RefTy) (x : Name) (hx : isFresh C Γ x = true)
      (p : SPath C Γ (.ref R)) (hp : p.isSimple = false)
      (hnf : ∀ s (b : SPath C Γ (.struct s)) f hf, p = .loc (.field b f hf) → b.isSimple = false)
      (hm : (Ty.ref R).mapFree = true) (sp : Name) (hsp : isFresh C (Ctx.mem Γ x R) sp = true) (hd) :
      .declMem R x hx (some (.copy p hm)) hd ⇒
        .unfold [sp]
          (.cons (.declStorage true R sp (isFresh_of_sub (Ctx.Sub.fresh hx _) hsp) p)
          (.cons (.declMem R x (isFresh_setBy hx (ne_of_isFresh_setBy hsp)) (some (.copy (SPath.new sp R) hm)) rfl)
            .nil))
          ((MHole.decl R x hx).extend_sub sp (.path (.ref R)) hsp)
  /-- `mv = sp ⇝ {mv := freshId(alloc(mv, sp)) || memory := alloc(mv, sp)}`. -/
  | memoryStorageCopy {Γ : Ctx} {R : RefTy} (x : Name) (h : lookupBy x Γ = some (.mem (.ref R)))
      (sp : SPath C Γ (.ref R)) (hs : sp.isSimple = true) (hm : (Ty.ref R).mapFree = true) :
      .rebindMem x h (.copy sp hm) ⇒ .update (.bindCopy x sp hm)
  /-- `mv = path ⇝ T storage sp = path; mv = sp`. -/
  | memoryStorageCopyUnfold {Γ : Ctx} {R : RefTy} (x : Name) (h : lookupBy x Γ = some (.mem (.ref R)))
      (p : SPath C Γ (.ref R)) (hp : p.isSimple = false) (hm : (Ty.ref R).mapFree = true) (sp : Name)
      (hsp : isFresh C Γ sp = true) :
      .rebindMem x h (.copy p hm) ⇒
        .unfold [sp]
          (.cons (.declStorage true R sp hsp p)
          (.cons (.rebindMem x ((Ctx.Sub.fresh hsp _).local_ _ _ h) (.copy (SPath.new sp R) hm)) .nil))
          (Ctx.Sub.fresh hsp _)
  -- Memory: copies into storage (from any memory path: capturing one needs
  -- the slot to hold a reference, which the copy does not check)
  /-- `gsp = mpath ⇝ {storage := store(storage, gsp, copyMem(mtSt, memory, mpath))}`. -/
  | memoryToStorageStoreRoot {Γ : Ctx} {R : RefTy} (r : Name) (hΓ : lookupBy r Γ = none)
      (hr : C.rootType r = some (.ref R)) (p : MPath C Γ (.ref R)) :
      .assignFromMem (.root r hΓ hr) p ⇒ .update (.saveMem (.root r hΓ hr) p)
  /-- `sp.fld = mv ⇝ {storage := save(storage, sp.fld, copyMem(mtSt, memory, mv))}`. -/
  | memoryToStorageFieldCopyRoot {Γ : Ctx} {s : Name} {R : RefTy} (sp : SPath C Γ (.struct s))
      (hs : sp.isSimple = true) (f : Name) (hf : C.fieldType s f = some (.ref R)) (x : Name)
      (hx : lookupBy x Γ = some (.mem (.ref R))) :
      .assignFromMem (.field sp f hf) (.var x hx) ⇒ .update (.saveMem (.field sp f hf) (.var x hx))
  /-- `sp.fld = mpath ⇝ {storage := save(storage, sp.fld, copyMem(mtSt, memory, mpath))}`. -/
  | memoryToStorageFieldCopyField {Γ : Ctx} {s : Name} {R : RefTy} (sp : SPath C Γ (.struct s))
      (hs : sp.isSimple = true) (f : Name) (hf : C.fieldType s f = some (.ref R)) (ml : MLoc C Γ (.ref R)) :
      .assignFromMem (.field sp f hf) (.loc ml) ⇒ .update (.saveMem (.field sp f hf) (.loc ml))
  /-- `map[ie] = mpath ⇝ {storage := save(storage, map[ie], copyMem(mtSt, memory, mpath))}`. -/
  | memoryToStorageIndexMappingCopyRoot {Γ : Ctx} {kp : PrimTy} {R : RefTy}
      (sp : SPath C Γ (.mapping (.prim kp) (.ref R))) (hs : sp.isSimple = true) (ie : Simple C Γ kp)
      (p : MPath C Γ (.ref R)) :
      .assignFromMem (.index .map sp (.simple ie)) p ⇒ .update (.saveMem (.index .map sp (.simple ie)) p)
  /-- `arr[ie] = mpath ⇝ {storage := save(storage, arr[ie], copyMem(mtSt, memory, mpath))}`: no
  bounds split. -/
  | memoryToStorageIndexArrayCopyRoot {Γ : Ctx} {R : RefTy} (sp : SPath C Γ (.array (.ref R)))
      (hs : sp.isSimple = true) (ie : Simple C Γ .uint) (p : MPath C Γ (.ref R)) :
      .assignFromMem (.index .arr sp (.simple ie)) p ⇒ .update (.saveMem (.index .arr sp (.simple ie)) p)
  /-- `nsp.fld = mpath ⇝ T storage sp = nsp; sp.fld = mpath`. -/
  | memoryToStorageField_unfold_leftFst {Γ : Ctx} {s : Name} {R : RefTy} (nsp : SPath C Γ (.struct s))
      (hn : nsp.isSimple = false) (f : Name) (hf : C.fieldType s f = some (.ref R)) (p : MPath C Γ (.ref R))
      (sp : Name) (hsp : isFresh C Γ sp = true) :
      .assignFromMem (.field nsp f hf) p ⇒
        .unfold [sp]
          (.cons (.declStorage true (.struct s) sp hsp nsp)
          (.cons (.assignFromMem (.field (SPath.new sp _) f hf) (p.weaken (Ctx.Sub.fresh hsp _))) .nil))
          (Ctx.Sub.fresh hsp _)
  /-- `nsp[e] = mpath ⇝ T storage sp = nsp; sp[e] = mpath`. -/
  | memoryToStorageIndex_unfold_leftFst {Γ : Ctx} {R₀ : RefTy} {kp : PrimTy} {R : RefTy}
      (it : IndexTy R₀ kp (.ref R)) (nsp : SPath C Γ (.ref R₀)) (hn : nsp.isSimple = false) (e : Val C Γ kp)
      (p : MPath C Γ (.ref R)) (sp : Name) (hsp : isFresh C Γ sp = true) :
      .assignFromMem (.index it nsp e) p ⇒
        .unfold [sp]
          (.cons (.declStorage true R₀ sp hsp nsp)
          (.cons (.assignFromMem (.index it (SPath.new sp _) (e.weaken (Ctx.Sub.fresh hsp _)))
            (p.weaken (Ctx.Sub.fresh hsp _))) .nil))
          (Ctx.Sub.fresh hsp _)
  /-- `sp[nse] = mpath ⇝ T ie = nse; sp[ie] = mpath`. -/
  | memoryToStorageIndexNonSimpleIndexCapture {Γ : Ctx} {R₀ : RefTy} {kp : PrimTy} {R : RefTy}
      (it : IndexTy R₀ kp (.ref R)) (sp : SPath C Γ (.ref R₀)) (hs : sp.isSimple = true) (nse : Val C Γ kp)
      (hn : nse.isSimple = false) (p : MPath C Γ (.ref R)) (ie : Name) (hie : isFresh C Γ ie = true) :
      .assignFromMem (.index it sp nse) p ⇒
        .unfold [ie]
          (.cons (.declLocal kp ie hie (some nse))
          (.cons (.assignFromMem (.index it (sp.weaken (Ctx.Sub.fresh hie _)) (.simple (Simple.new ie kp)))
            (p.weaken (Ctx.Sub.fresh hie _))) .nil))
          (Ctx.Sub.fresh hie _)
  -- Memory: writes
  /-- `mv.fld = se ⇝ {memory := write(memory, mv.fld, se)}`. -/
  | memoryFieldWriteStore {Γ : Ctx} {s : Name} {p : PrimTy} (b : MPath C Γ (.struct s))
      (hb : b.isSimple = true) (f : Name) (hf : C.fieldType s f = some (.prim p)) (se : Simple C Γ p) :
      .assignMem (.field b f hf) (.val (.simple se)) ⇒ .update (.writeMem (.field b f hf) (.val (.simple se)))
  /-- `mv[ie] = se ⇝ {memory := write(memory, mv[ie], se)}`: no bounds split. -/
  | memoryIndexWriteStore {Γ : Ctx} {p : PrimTy} (b : MPath C Γ (.array (.prim p))) (hb : b.isSimple = true)
      (ie : Simple C Γ .uint) (se : Simple C Γ p) :
      .assignMem (.index b (.simple ie)) (.val (.simple se)) ⇒
        .update (.writeMem (.index b (.simple ie)) (.val (.simple se)))
  /-- `mv1.fld = mpath ⇝ {memory := write(memory, mv1.fld, image(mpath))}`, from a
  bindable source (the old table first captures a member source into a
  scratch reference, which needs the slot to hold one; the interpreter copies
  the slot as it is). -/
  | memoryFieldWriteCopy {Γ : Ctx} {s : Name} {R : RefTy} (b : MPath C Γ (.struct s))
      (hb : b.isSimple = true) (f : Name) (hf : C.fieldType s f = some (.ref R))
      (src : MPath C Γ (.ref R)) (hsrc : src.isBindable = true) :
      .assignMem (.field b f hf) (.ref src) ⇒ .update (.writeMem (.field b f hf) (.ref src))
  /-- `mv1[ie] = mpath ⇝ {memory := write(memory, mv1[ie], image(mpath))}`. -/
  | memoryIndexWriteCopy {Γ : Ctx} {R : RefTy} (b : MPath C Γ (.array (.ref R))) (hb : b.isSimple = true)
      (ie : Simple C Γ .uint) (src : MPath C Γ (.ref R)) (hsrc : src.isBindable = true) :
      .assignMem (.index b (.simple ie)) (.ref src) ⇒ .update (.writeMem (.index b (.simple ie)) (.ref src))
  /-- `nmp.fld = e ⇝ T se = e; T memory mv = nmp; mv.fld = se`. -/
  | memoryFieldWrite_unfold_leftFst {Γ : Ctx} {s : Name} {p : PrimTy} (nmp : MPath C Γ (.struct s))
      (hn : nmp.isSimple = false) (f : Name) (hf : C.fieldType s f = some (.prim p)) (e : Val C Γ p)
      (se mv : Name) (hse : isFresh C Γ se = true) (hmv : isFresh C (Ctx.val Γ se p) mv = true) (hnt : e.notTernary = true) :
      .assignMem (.field nmp f hf) (.val e) ⇒
        .unfold [se, mv]
          (.cons (.declLocal p se hse (some e))
          (.cons (.declMem (.struct s) mv hmv (some (.alias (nmp.weaken (Ctx.Sub.fresh hse _)))) rfl)
          (.cons (.assignMem (.field (MPath.new mv _) f hf)
              (.val (.simple ((Simple.new se p).weaken (Ctx.Sub.fresh hmv _))))) .nil)))
          ((Ctx.Sub.fresh hse _).trans (Ctx.Sub.fresh hmv _))
  /-- `nmp[e1] = e2 ⇝ T se = e2; T memory mv = nmp; mv[e1] = se`. -/
  | memoryIndexWrite_unfold_leftFst {Γ : Ctx} {p : PrimTy} (nmp : MPath C Γ (.array (.prim p)))
      (hn : nmp.isSimple = false) (e₁ : Val C Γ .uint) (e₂ : Val C Γ p) (se mv : Name)
      (hse : isFresh C Γ se = true) (hmv : isFresh C (Ctx.val Γ se p) mv = true) (hnt : e₂.notTernary = true) :
      .assignMem (.index nmp e₁) (.val e₂) ⇒
        .unfold [se, mv]
          (.cons (.declLocal p se hse (some e₂))
          (.cons (.declMem (.array (.prim p)) mv hmv (some (.alias (nmp.weaken (Ctx.Sub.fresh hse _)))) rfl)
          (.cons (.assignMem (.index (MPath.new mv _) ((e₁.weaken (Ctx.Sub.fresh hse _)).weaken (Ctx.Sub.fresh hmv _)))
              (.val (.simple ((Simple.new se p).weaken (Ctx.Sub.fresh hmv _))))) .nil)))
          ((Ctx.Sub.fresh hse _).trans (Ctx.Sub.fresh hmv _))
  /-- `nmp.fld = mv2 ⇝ T memory mv = nmp; mv.fld = mv2`. -/
  | memoryFieldWriteMemRef_unfold_leftFst {Γ : Ctx} {s : Name} {R : RefTy} (nmp : MPath C Γ (.struct s))
      (hn : nmp.isSimple = false) (f : Name) (hf : C.fieldType s f = some (.ref R)) (src : MPath C Γ (.ref R))
      (hsrc : src.isBindable = true) (mv : Name) (hmv : isFresh C Γ mv = true) :
      .assignMem (.field nmp f hf) (.ref src) ⇒
        .unfold [mv]
          (.cons (.declMem (.struct s) mv hmv (some (.alias nmp)) rfl)
          (.cons (.assignMem (.field (MPath.new mv _) f hf) (.ref (src.weaken (Ctx.Sub.fresh hmv _)))) .nil))
          (Ctx.Sub.fresh hmv _)
  /-- `nmp[e] = mv2 ⇝ T memory mv = nmp; mv[e] = mv2`. -/
  | memoryIndexWriteMemRef_unfold_leftFst {Γ : Ctx} {R : RefTy} (nmp : MPath C Γ (.array (.ref R)))
      (hn : nmp.isSimple = false) (e : Val C Γ .uint) (src : MPath C Γ (.ref R))
      (hsrc : src.isBindable = true) (mv : Name) (hmv : isFresh C Γ mv = true) :
      .assignMem (.index nmp e) (.ref src) ⇒
        .unfold [mv]
          (.cons (.declMem (.array (.ref R)) mv hmv (some (.alias nmp)) rfl)
          (.cons (.assignMem (.index (MPath.new mv _) (e.weaken (Ctx.Sub.fresh hmv _)))
            (.ref (src.weaken (Ctx.Sub.fresh hmv _)))) .nil))
          (Ctx.Sub.fresh hmv _)
  /-- `mv1[nse] = e ⇝ T se = e; T ie = nse; mv1[ie] = se`. -/
  | memoryIndexWriteNonSimpleIndexCapture {Γ : Ctx} {p : PrimTy} (b : MPath C Γ (.array (.prim p)))
      (hb : b.isSimple = true) (nse : Val C Γ .uint) (hn : nse.isSimple = false) (e : Val C Γ p)
      (se ie : Name) (hse : isFresh C Γ se = true) (hie : isFresh C (Ctx.val Γ se p) ie = true) (hnt : e.notTernary = true) :
      .assignMem (.index b nse) (.val e) ⇒
        .unfold [se, ie]
          (.cons (.declLocal p se hse (some e))
          (.cons (.declLocal .uint ie hie (some (nse.weaken (Ctx.Sub.fresh hse _))))
          (.cons (.assignMem (.index ((b.weaken (Ctx.Sub.fresh hse _)).weaken (Ctx.Sub.fresh hie _))
              (.simple (Simple.new ie .uint)))
              (.val (.simple ((Simple.new se p).weaken (Ctx.Sub.fresh hie _))))) .nil)))
          ((Ctx.Sub.fresh hse _).trans (Ctx.Sub.fresh hie _))
  /-- `mv1[nse] = mv2 ⇝ T ie = nse; mv1[ie] = mv2`. -/
  | memoryIndexWriteMemRefNonSimpleIndexCapture {Γ : Ctx} {R : RefTy} (b : MPath C Γ (.array (.ref R)))
      (hb : b.isSimple = true) (nse : Val C Γ .uint) (hn : nse.isSimple = false) (src : MPath C Γ (.ref R))
      (hsrc : src.isBindable = true) (ie : Name) (hie : isFresh C Γ ie = true) :
      .assignMem (.index b nse) (.ref src) ⇒
        .unfold [ie]
          (.cons (.declLocal .uint ie hie (some nse))
          (.cons (.assignMem (.index (b.weaken (Ctx.Sub.fresh hie _)) (.simple (Simple.new ie .uint)))
            (.ref (src.weaken (Ctx.Sub.fresh hie _)))) .nil))
          (Ctx.Sub.fresh hie _)
  /-- `mv.fld = nse ⇝ T se = nse; mv.fld = se`. -/
  | memoryFieldWriteUnfoldSource {Γ : Ctx} {s : Name} {p : PrimTy} (b : MPath C Γ (.struct s))
      (hb : b.isSimple = true) (f : Name) (hf : C.fieldType s f = some (.prim p)) (nse : Val C Γ p)
      (hn : nse.isSimple = false) (se : Name) (hse : isFresh C Γ se = true) (hnt : nse.notTernary = true) :
      .assignMem (.field b f hf) (.val nse) ⇒
        .unfold [se]
          (.cons (.declLocal p se hse (some nse))
          (.cons (.assignMem (.field (b.weaken (Ctx.Sub.fresh hse _)) f hf) (.val (.simple (Simple.new se p)))) .nil))
          (Ctx.Sub.fresh hse _)
  /-- `mv[ie] = nse ⇝ T se = nse; mv[ie] = se`. -/
  | memoryIndexWriteUnfoldSource {Γ : Ctx} {p : PrimTy} (b : MPath C Γ (.array (.prim p)))
      (hb : b.isSimple = true) (ie : Simple C Γ .uint) (nse : Val C Γ p) (hn : nse.isSimple = false)
      (se : Name) (hse : isFresh C Γ se = true) (hnt : nse.notTernary = true) :
      .assignMem (.index b (.simple ie)) (.val nse) ⇒
        .unfold [se]
          (.cons (.declLocal p se hse (some nse))
          (.cons (.assignMem (.index (b.weaken (Ctx.Sub.fresh hse _)) (.simple (ie.weaken (Ctx.Sub.fresh hse _))))
            (.val (.simple (Simple.new se p)))) .nil))
          (Ctx.Sub.fresh hse _)
  -- Conditional expressions
  /-- `x = se ? e1 : e2 ⇝ if (se) { x = e1 } else { x = e2 }`, the statement
  `if` in place of KeY's residual (the same meaning: both evaluate only the
  branch taken). -/
  | ternaryToIf {Γ : Ctx} {p : PrimTy} (x : Name) (h : lookupBy x Γ = some (.stack (.prim p)))
      (c : Simple C Γ .bool) (a b : Val C Γ p) :
      .assignLocal x h (.ternary (.simple c) a b) ⇒
        .unfold [] (.cons (.ite c (.cons (.assignLocal x h a) .nil) (.cons (.assignLocal x h b) .nil)) .nil)
          (Ctx.Sub.refl _)
  /-- `path = se ? e1 : e2 ⇝ if (se) { path = e1 } else { path = e2 }`, for
  a storage target (a conditional is never a write's source: it is lowered
  first). -/
  | ternaryToIfStorage {Γ : Ctx} {p : PrimTy} (l : Loc C Γ (.prim p)) (c : Simple C Γ .bool)
      (a b : Val C Γ p) :
      .assign l (.val (.ternary (.simple c) a b)) ⇒
        .unfold [] (.cons (.ite c (.cons (.assign l (.val a)) .nil) (.cons (.assign l (.val b)) .nil)) .nil)
          (Ctx.Sub.refl _)
  /-- `mpath = se ? e1 : e2 ⇝ if (se) { mpath = e1 } else { mpath = e2 }` (Lean's own:
  solkey has no memory twin). -/
  | ternaryToIfMemory {Γ : Ctx} {p : PrimTy} (l : MLoc C Γ (.prim p)) (c : Simple C Γ .bool)
      (a b : Val C Γ p) :
      .assignMem l (.val (.ternary (.simple c) a b)) ⇒
        .unfold [] (.cons (.ite c (.cons (.assignMem l (.val a)) .nil) (.cons (.assignMem l (.val b)) .nil)) .nil)
          (Ctx.Sub.refl _)
  /-- `lhs = nse ? e1 : e2 ⇝ bool se = nse; lhs = se ? e1 : e2`. -/
  | ternaryCaptureCond {Γ : Ctx} {p : PrimTy} (k : VHole C Γ p) (nse : Val C Γ .bool)
      (hn : nse.isSimple = false) (a b : Val C Γ p) (se : Name) (hse : isFresh C Γ se = true) :
      k.fill (.ternary nse a b) ⇒
        .unfold [se]
          (.cons (.declLocal .bool se hse (some nse))
          (.cons ((k.weaken (Ctx.Sub.fresh hse _)).fill
              (.ternary (.simple (Simple.new se .bool)) (a.weaken (Ctx.Sub.fresh hse _))
                (b.weaken (Ctx.Sub.fresh hse _)))) .nil))
          (Ctx.Sub.fresh hse _)
  -- Compound assignment
  /-- `lv ⊕= se ⇝ {lv := lv ⊕ se}`. -/
  | localOpAssign {Γ : Ctx} {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
      (hp : p.isNumeric = true) (x : Name) (h : lookupBy x Γ = some (.stack (.prim p)))
      (se : Simple C Γ p) :
      .opAssign op hop hp (.local x h) (.simple se) ⇒ .update (.opSave op (.local x h) se)
  /-- `gsp ⊕= se ⇝ {storage := store(storage, gsp, gsp ⊕ se)}`. -/
  | storageRootOpAssign {Γ : Ctx} {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
      (hp : p.isNumeric = true) (r : Name) (hΓ : lookupBy r Γ = none)
      (hr : C.rootType r = some (.prim p)) (se : Simple C Γ p) :
      .opAssign op hop hp (.root r hΓ hr) (.simple se) ⇒ .update (.opSave op (.root r hΓ hr) se)
  /-- `sp.fld ⊕= se ⇝ {storage := save(storage, sp.fld, sp.fld ⊕ se)}`. -/
  | storageFieldOpAssign {Γ : Ctx} {s : Name} {p : PrimTy} (op : BinOp)
      (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true) (sp : SPath C Γ (.struct s))
      (hs : sp.isSimple = true) (f : Name) (hf : C.fieldType s f = some (.prim p)) (se : Simple C Γ p) :
      .opAssign op hop hp (.field sp f hf) (.simple se) ⇒ .update (.opSave op (.field sp f hf) se)
  /-- `map[ie] ⊕= se ⇝ {storage := save(storage, map[ie], map[ie] ⊕ se)}`. -/
  | storageIndexMappingOpAssign {Γ : Ctx} {kp p : PrimTy} (op : BinOp)
      (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
      (sp : SPath C Γ (.mapping (.prim kp) (.prim p))) (hs : sp.isSimple = true)
      (ie : Simple C Γ kp) (se : Simple C Γ p) :
      .opAssign op hop hp (.index .map sp ie) (.simple se) ⇒ .update (.opSave op (.index .map sp ie) se)
  /-- `arr[ie] ⊕= se ⇝ {storage := save(storage, arr[ie], arr[ie] ⊕ se)}`: no
  bounds split, the update reverts as the statement does. -/
  | storageIndexArrayOpAssign {Γ : Ctx} {p : PrimTy} (op : BinOp)
      (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true)
      (sp : SPath C Γ (.array (.prim p))) (hs : sp.isSimple = true)
      (ie : Simple C Γ .uint) (se : Simple C Γ p) :
      .opAssign op hop hp (.index .arr sp ie) (.simple se) ⇒ .update (.opSave op (.index .arr sp ie) se)
  /-- `nsp.fld ⊕= se ⇝ T storage sp = nsp; sp.fld ⊕= se`.  The old table
  freezes `se` first (`T se ?= se1`); a kernel value has no effects, so
  resolving `nsp` cannot change it. -/
  | storageFieldOpAssignUnfoldLeftFst {Γ : Ctx} {s : Name} {p : PrimTy} (op : BinOp)
      (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true) (nsp : SPath C Γ (.struct s))
      (hn : nsp.isSimple = false) (f : Name) (hf : C.fieldType s f = some (.prim p)) (se : Simple C Γ p)
      (sp : Name) (hsp : isFresh C Γ sp = true) :
      .opAssign op hop hp (.field nsp f hf) (.simple se) ⇒
        .unfold [sp]
          (.cons (.declStorage true (.struct s) sp hsp nsp)
          (.cons (.opAssign op hop hp (.field (SPath.new sp _) f hf)
              (.simple (se.weaken (Ctx.Sub.fresh hsp _)))) .nil))
          (Ctx.Sub.fresh hsp _)
  /-- `nsp[ie] ⊕= se ⇝ T storage sp = nsp; sp[ie] ⊕= se`. -/
  | storageIndexOpAssignUnfoldLeftFst {Γ : Ctx} {R : RefTy} {kp p : PrimTy} (op : BinOp)
      (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true) (it : IndexTy R kp (.prim p))
      (nsp : SPath C Γ (.ref R)) (hn : nsp.isSimple = false) (ie : Simple C Γ kp) (se : Simple C Γ p)
      (sp : Name) (hsp : isFresh C Γ sp = true) :
      .opAssign op hop hp (.index it nsp ie) (.simple se) ⇒
        .unfold [sp]
          (.cons (.declStorage true R sp hsp nsp)
          (.cons (.opAssign op hop hp (.index it (SPath.new sp _) (ie.weaken (Ctx.Sub.fresh hsp _)))
              (.simple (se.weaken (Ctx.Sub.fresh hsp _)))) .nil))
          (Ctx.Sub.fresh hsp _)
  /-- `lhs ⊕= nse ⇝ T se = nse; lhs ⊕= se`, the source before the target. -/
  | compoundAssignValueRhsCapture {Γ : Ctx} {p : PrimTy} (op : BinOp)
      (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true) (l : OpLoc C Γ p)
      (nse : Val C Γ p) (hn : nse.isSimple = false) (se : Name) (hse : isFresh C Γ se = true) :
      .opAssign op hop hp l nse ⇒
        .unfold [se]
          (.cons (.declLocal p se hse (some nse))
          (.cons (.opAssign op hop hp (l.weaken (Ctx.Sub.fresh hse _)) (.simple (Simple.new se p))) .nil))
          (Ctx.Sub.fresh hse _)
  -- Arrays
  /-- `sp.push(se) ⇝ {storage := save(save(storage, sp[sp.length], se), …)}`. -/
  | storagePushValueSave {Γ : Ctx} {p : PrimTy} (sp : SPath C Γ (.array (.prim p)))
      (hs : sp.isSimple = true) (se : Simple C Γ p) (hd) :
      .push sp (some (.val (.simple se))) hd ⇒ .update (.push sp (some (.val (.simple se))))
  /-- `sp1.push(sp2) ⇝ {storage := save(save(storage, sp1[sp1.length], find(storage, sp2)), …)}`. -/
  | storagePushValueCopySource {Γ : Ctx} {R : RefTy} (sp : SPath C Γ (.array (.ref R)))
      (hs : sp.isSimple = true) (sp₂ : SPath C Γ (.ref R)) (hs₂ : sp₂.isSimple = true)
      (hm : (Ty.ref R).mapFree = true) (hd) :
      .push sp (some (.copy sp₂ hm)) hd ⇒ .update (.push sp (some (.copy sp₂ hm)))
  /-- `sp.push() ⇝ {storage := save(delAt(storage, sp[sp.length]), sp.length, sp.length + 1)}`. -/
  | storagePushLengthSave {Γ : Ctx} {E : Ty} (sp : SPath C Γ (.array E)) (hs : sp.isSimple = true)
      (hd) : .push sp none hd ⇒ .update (.push sp none)
  /-- `sp.push(nse) ⇝ _ se = nse; sp.push(se)`, a value or a path. -/
  | storagePushValue_unfold_rightSndArgument {Γ : Ctx} {E : Ty} (sp : SPath C Γ (.array E))
      (hs : sp.isSimple = true) (r : Src C Γ E) (hr : r.isSimple = false) (se : Name)
      (hse : isFresh C Γ se = true) (hd) :
      .push sp (some r) hd ⇒
        .unfold [se]
          (.cons (r.decl se hse) (.cons (.push (sp.weaken (Ctx.Sub.fresh hse _)) (some (r.fresh se)) rfl) .nil))
          (Ctx.Sub.fresh hse _)
  /-- `nsp.push(e) ⇝ T storage sp = nsp; sp.push(e)`. -/
  | storagePushValue_unfold_leftFstReceiver {Γ : Ctx} {E : Ty} (nsp : SPath C Γ (.array E))
      (hn : nsp.isSimple = false) (e : Src C Γ E) (sp : Name) (hsp : isFresh C Γ sp = true) (hd) :
      .push nsp (some e) hd ⇒
        .unfold [sp]
          (.cons (.declStorage true (.array E) sp hsp nsp)
          (.cons (.push (SPath.new sp _) (some (e.weaken (Ctx.Sub.fresh hsp _))) rfl) .nil))
          (Ctx.Sub.fresh hsp _)
  /-- `nsp.push() ⇝ T storage sp = nsp; sp.push()`. -/
  | storagePush_unfold_leftFstReceiver {Γ : Ctx} {E : Ty} (nsp : SPath C Γ (.array E))
      (hn : nsp.isSimple = false) (sp : Name) (hsp : isFresh C Γ sp = true) (hd) :
      .push nsp none hd ⇒
        .unfold [sp]
          (.cons (.declStorage true (.array E) sp hsp nsp) (.cons (.push (SPath.new sp _) none hd) .nil))
          (Ctx.Sub.fresh hsp _)
  /-- `nsp.pop() ⇝ T storage sp = nsp; sp.pop()`. -/
  | storagePop_unfold_leftFstReceiver {Γ : Ctx} {E : Ty} (nsp : SPath C Γ (.array E))
      (hn : nsp.isSimple = false) (sp : Name) (hsp : isFresh C Γ sp = true) :
      .pop nsp ⇒
        .unfold [sp]
          (.cons (.declStorage true (.array E) sp hsp nsp) (.cons (.pop (SPath.new sp _)) .nil))
          (Ctx.Sub.fresh hsp _)
  /-- `sp.pop() ⇝ {storage := save(delAt(storage, sp[sp.length - 1]), …)}`: no
  emptiness split, the update reverts as the statement does. -/
  | storagePopSave {Γ : Ctx} {E : Ty} (sp : SPath C Γ (.array E)) (hs : sp.isSimple = true) :
      .pop sp ⇒ .update (.pop sp)
  -- Transfer
  /-- `nadr.transfer(e) ⇝ uint se = nadr; se.transfer(e)`. -/
  | transfer_unfold_leftFstReceiver {Γ : Ctx} (nr : Val C Γ .uint) (hn : nr.isSimple = false)
      (a : Val C Γ .uint) (se : Name) (hse : isFresh C Γ se = true) :
      .transfer nr a ⇒
        .unfold [se]
          (.cons (.declLocal .uint se hse (some nr))
          (.cons (.transfer (.simple (Simple.new se .uint)) (a.weaken (Ctx.Sub.fresh hse _))) .nil))
          (Ctx.Sub.fresh hse _)
  /-- `sadr.transfer(nse) ⇝ uint se = nse; sadr.transfer(se)`. -/
  | transfer_unfold_rightSndArgument {Γ : Ctx} (r : Simple C Γ .uint) (na : Val C Γ .uint)
      (hn : na.isSimple = false) (se : Name) (hse : isFresh C Γ se = true) :
      .transfer (.simple r) na ⇒
        .unfold [se]
          (.cons (.declLocal .uint se hse (some na))
          (.cons (.transfer (.simple (r.weaken (Ctx.Sub.fresh hse _))) (.simple (Simple.new se .uint))) .nil))
          (Ctx.Sub.fresh hse _)
  /-- `sadr.transfer(se) ⇝ {transfer(sadr, se)}`, KeY's `transferSemantics:noCallback`:
  no funds split, the update reverts as the statement does. -/
  | transferNoCallback {Γ : Ctx} (r a : Simple C Γ .uint) :
      .transfer (.simple r) (.simple a) ⇒ .update (.transfer r a)
  -- Memory arithmetic
  /-- `mv.fld ⊕= se ⇝ {mv.fld := mv.fld ⊕ se}`. -/
  | memoryFieldOpAssign {Γ : Ctx} {s : Name} {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
      (hp : p.isNumeric = true) (b : MPath C Γ (.struct s)) (hb : b.isSimple = true) (f : Name)
      (hf : C.fieldType s f = some (.prim p)) (se : Simple C Γ p) :
      .opAssign op hop hp (.mfield b f hf) (.simple se) ⇒ .update (.opSave op (.mfield b f hf) se)
  /-- `mv[ie] ⊕= se ⇝ {mv[ie] := mv[ie] ⊕ se}`: no bounds split. -/
  | memoryIndexArrayOpAssign {Γ : Ctx} {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
      (hp : p.isNumeric = true) (b : MPath C Γ (.array (.prim p))) (hb : b.isSimple = true)
      (ie : Simple C Γ .uint) (se : Simple C Γ p) :
      .opAssign op hop hp (.mindex b ie) (.simple se) ⇒ .update (.opSave op (.mindex b ie) se)
  /-- `nmp.fld ⊕= se ⇝ T memory mv = nmp; mv.fld ⊕= se`. -/
  | memoryFieldOpAssignUnfoldLeftFst {Γ : Ctx} {s : Name} {p : PrimTy} (op : BinOp)
      (hop : op.hasCompoundAssign = true) (hp : p.isNumeric = true) (nmp : MPath C Γ (.struct s))
      (hn : nmp.isSimple = false) (f : Name) (hf : C.fieldType s f = some (.prim p)) (se : Simple C Γ p)
      (mv : Name) (hmv : isFresh C Γ mv = true) :
      .opAssign op hop hp (.mfield nmp f hf) (.simple se) ⇒
        .unfold [mv]
          (.cons (.declMem (.struct s) mv hmv (some (.alias nmp)) rfl)
          (.cons (.opAssign op hop hp (.mfield (MPath.new mv _) f hf) (.simple (se.weaken (Ctx.Sub.fresh hmv _))))
            .nil))
          (Ctx.Sub.fresh hmv _)
  /-- `nmp[ie] ⊕= se ⇝ T memory mv = nmp; mv[ie] ⊕= se`. -/
  | memoryIndexOpAssignUnfoldLeftFst {Γ : Ctx} {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
      (hp : p.isNumeric = true) (nmp : MPath C Γ (.array (.prim p))) (hn : nmp.isSimple = false)
      (ie : Simple C Γ .uint) (se : Simple C Γ p) (mv : Name) (hmv : isFresh C Γ mv = true) :
      .opAssign op hop hp (.mindex nmp ie) (.simple se) ⇒
        .unfold [mv]
          (.cons (.declMem (.array (.prim p)) mv hmv (some (.alias nmp)) rfl)
          (.cons (.opAssign op hop hp (.mindex (MPath.new mv _) (ie.weaken (Ctx.Sub.fresh hmv _)))
            (.simple (se.weaken (Ctx.Sub.fresh hmv _)))) .nil))
          (Ctx.Sub.fresh hmv _)
  /-- `mv.fld++ ⇝ {bump(mv.fld++)}`. -/
  | memoryFieldIncrement {Γ : Ctx} {s : Name} {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
      (b : MPath C Γ (.struct s)) (hb : b.isSimple = true) (f : Name) (hf : C.fieldType s f = some (.prim p)) :
      .incDec op hp (.mfield b f hf) ⇒ .update (.bump op (.mfield b f hf))
  /-- `mv[ie]++ ⇝ {bump(mv[ie]++)}`: no bounds split. -/
  | memoryIndexArrayIncrement {Γ : Ctx} {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
      (b : MPath C Γ (.array (.prim p))) (hb : b.isSimple = true) (ie : Simple C Γ .uint) :
      .incDec op hp (.mindex b ie) ⇒ .update (.bump op (.mindex b ie))
  /-- `nmp.fld++ ⇝ T memory mv = nmp; mv.fld++`. -/
  | memoryFieldIncrementUnfoldLeftFst {Γ : Ctx} {s : Name} {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
      (nmp : MPath C Γ (.struct s)) (hn : nmp.isSimple = false) (f : Name) (hf : C.fieldType s f = some (.prim p))
      (mv : Name) (hmv : isFresh C Γ mv = true) :
      .incDec op hp (.mfield nmp f hf) ⇒
        .unfold [mv]
          (.cons (.declMem (.struct s) mv hmv (some (.alias nmp)) rfl)
          (.cons (.incDec op hp (.mfield (MPath.new mv _) f hf)) .nil))
          (Ctx.Sub.fresh hmv _)
  /-- `nmp[ie]++ ⇝ T memory mv = nmp; mv[ie]++`. -/
  | memoryIndexIncrementUnfoldLeftFst {Γ : Ctx} {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
      (nmp : MPath C Γ (.array (.prim p))) (hn : nmp.isSimple = false) (ie : Simple C Γ .uint) (mv : Name)
      (hmv : isFresh C Γ mv = true) :
      .incDec op hp (.mindex nmp ie) ⇒
        .unfold [mv]
          (.cons (.declMem (.array (.prim p)) mv hmv (some (.alias nmp)) rfl)
          (.cons (.incDec op hp (.mindex (MPath.new mv _) (ie.weaken (Ctx.Sub.fresh hmv _)))) .nil))
          (Ctx.Sub.fresh hmv _)
  /-- `lv = mv.fld++ ⇝ {bump(mv.fld++) || lv := mv.fld++}`. -/
  | memoryFieldIncrementAssignment {Γ : Ctx} {s : Name} {p : PrimTy} (y : Name)
      (hy : lookupBy y Γ = some (.stack (.prim p))) (op : IncDec) (hp : p.isNumeric = true)
      (b : MPath C Γ (.struct s)) (f : Name) (hf : C.fieldType s f = some (.prim p))
      (hs : (OpLoc.mfield b f hf).recvSimple = true) :
      .assignIncDec y hy op hp (.mfield b f hf) hs ⇒ .update (.bumpBind y op (.mfield b f hf))
  /-- `lv = mv[ie]++ ⇝ {bump(mv[ie]++) || lv := mv[ie]++}`. -/
  | memoryIndexArrayIncrementAssignment {Γ : Ctx} {p : PrimTy} (y : Name)
      (hy : lookupBy y Γ = some (.stack (.prim p))) (op : IncDec) (hp : p.isNumeric = true)
      (b : MPath C Γ (.array (.prim p))) (ie : Simple C Γ .uint) (hs : (OpLoc.mindex b ie).recvSimple = true) :
      .assignIncDec y hy op hp (.mindex b ie) hs ⇒ .update (.bumpBind y op (.mindex b ie))
  -- Increment and decrement
  /-- `lv++ ⇝ {bump(lv++)}`. -/
  | localIncrement {Γ : Ctx} {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (x : Name)
      (h : lookupBy x Γ = some (.stack (.prim p))) :
      .incDec op hp (.local x h) ⇒ .update (.bump op (.local x h))
  /-- `gsp++ ⇝ {bump(gsp++)}`. -/
  | storageRootIncrement {Γ : Ctx} {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (r : Name)
      (hΓ : lookupBy r Γ = none) (hr : C.rootType r = some (.prim p)) :
      .incDec op hp (.root r hΓ hr) ⇒ .update (.bump op (.root r hΓ hr))
  /-- `sp.fld++ ⇝ {bump(sp.fld++)}`. -/
  | storageFieldIncrement {Γ : Ctx} {s : Name} {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
      (sp : SPath C Γ (.struct s)) (hs : sp.isSimple = true) (f : Name)
      (hf : C.fieldType s f = some (.prim p)) :
      .incDec op hp (.field sp f hf) ⇒ .update (.bump op (.field sp f hf))
  /-- `sp[ie]++ ⇝ {bump(sp[ie]++)}`, a mapping entry or an array element (one
  rule, as in the old table): no bounds split, the bump reverts as the
  statement does. -/
  | storageIndexIncrement {Γ : Ctx} {R : RefTy} {kp p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
      (it : IndexTy R kp (.prim p)) (sp : SPath C Γ (.ref R)) (hs : sp.isSimple = true)
      (ie : Simple C Γ kp) :
      .incDec op hp (.index it sp ie) ⇒ .update (.bump op (.index it sp ie))
  /-- `nsp.fld++ ⇝ T storage sp = nsp; sp.fld++`. -/
  | storageFieldIncrementUnfoldLeftFst {Γ : Ctx} {s : Name} {p : PrimTy} (op : IncDec)
      (hp : p.isNumeric = true) (nsp : SPath C Γ (.struct s)) (hn : nsp.isSimple = false) (f : Name)
      (hf : C.fieldType s f = some (.prim p)) (sp : Name) (hsp : isFresh C Γ sp = true) :
      .incDec op hp (.field nsp f hf) ⇒
        .unfold [sp]
          (.cons (.declStorage true (.struct s) sp hsp nsp)
          (.cons (.incDec op hp (.field (SPath.new sp _) f hf)) .nil))
          (Ctx.Sub.fresh hsp _)
  /-- `nsp[ie]++ ⇝ T storage sp = nsp; sp[ie]++`. -/
  | storageIndexIncrementUnfoldLeftFst {Γ : Ctx} {R : RefTy} {kp p : PrimTy} (op : IncDec)
      (hp : p.isNumeric = true) (it : IndexTy R kp (.prim p)) (nsp : SPath C Γ (.ref R))
      (hn : nsp.isSimple = false) (ie : Simple C Γ kp) (sp : Name) (hsp : isFresh C Γ sp = true) :
      .incDec op hp (.index it nsp ie) ⇒
        .unfold [sp]
          (.cons (.declStorage true R sp hsp nsp)
          (.cons (.incDec op hp (.index it (SPath.new sp _) (ie.weaken (Ctx.Sub.fresh hsp _)))) .nil))
          (Ctx.Sub.fresh hsp _)
  /-- `vp = lv++ ⇝ {bump(lv++) || vp := lv++}`. -/
  | localAssignIncrement {Γ : Ctx} {p : PrimTy} (y : Name) (hy : lookupBy y Γ = some (.stack (.prim p)))
      (op : IncDec) (hp : p.isNumeric = true) (x : Name) (h : lookupBy x Γ = some (.stack (.prim p))) :
      .assignIncDec y hy op hp (.local x h) rfl ⇒ .update (.bumpBind y op (.local x h))
  /-- `lv = gsp++ ⇝ {bump(gsp++) || lv := gsp++}`. -/
  | storageRootIncrementAssignment {Γ : Ctx} {p : PrimTy} (y : Name)
      (hy : lookupBy y Γ = some (.stack (.prim p))) (op : IncDec) (hp : p.isNumeric = true) (r : Name)
      (hΓ : lookupBy r Γ = none) (hr : C.rootType r = some (.prim p)) :
      .assignIncDec y hy op hp (.root r hΓ hr) rfl ⇒ .update (.bumpBind y op (.root r hΓ hr))
  /-- `lv = sp.fld++ ⇝ {bump(sp.fld++) || lv := sp.fld++}`. -/
  | storageFieldIncrementAssignment {Γ : Ctx} {s : Name} {p : PrimTy} (y : Name)
      (hy : lookupBy y Γ = some (.stack (.prim p))) (op : IncDec) (hp : p.isNumeric = true)
      (sp : SPath C Γ (.struct s)) (f : Name) (hf : C.fieldType s f = some (.prim p))
      (hs : (OpLoc.field sp f hf).recvSimple = true) :
      .assignIncDec y hy op hp (.field sp f hf) hs ⇒ .update (.bumpBind y op (.field sp f hf))
  /-- `lv = sp[ie]++ ⇝ {bump(sp[ie]++) || lv := sp[ie]++}`. -/
  | storageIndexIncrementAssignment {Γ : Ctx} {R : RefTy} {kp p : PrimTy} (y : Name)
      (hy : lookupBy y Γ = some (.stack (.prim p))) (op : IncDec) (hp : p.isNumeric = true)
      (it : IndexTy R kp (.prim p)) (sp : SPath C Γ (.ref R)) (ie : Simple C Γ kp)
      (hs : (OpLoc.index it sp ie).recvSimple = true) :
      .assignIncDec y hy op hp (.index it sp ie) hs ⇒ .update (.bumpBind y op (.index it sp ie))
  -- Control
  /-- Two goals: the `then` branch where `se` holds, the `else` branch where it
  does not. -/
  | ifElseSplit {Γ : Ctx} (se : Simple C Γ .bool) (thn els : Prog C Γ Γ) :
      .ite se thn els ⇒ .split se thn els
  /-- A guard: if `se` holds the program goes on, if not it reverts. -/
  | requireSimple {Γ : Ctx} (se : Simple C Γ .bool) :
      .require se ⇒ .split se .nil (.cons .revert .nil)
  /-- `assert` runs as `require` does. -/
  | assertSimple {Γ : Ctx} (se : Simple C Γ .bool) :
      .assert se ⇒ .split se .nil (.cons .revert .nil)
  /-- A reverted run satisfies every box formula. -/
  | revertBox {Γ : Ctx} (h : m = .box) : (.revert : Stmt C Γ Γ) ⇒ .done true
  /-- A reverted run satisfies no diamond formula. -/
  | revertDiamond {Γ : Ctx} (h : m = .diamond) : (.revert : Stmt C Γ Γ) ⇒ .done false

end Kernel
end Solidity
