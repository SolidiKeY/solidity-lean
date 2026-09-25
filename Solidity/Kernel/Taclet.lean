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

/-- A simple path (`sp`): a state variable or an alias. -/
def SPath.isSimple {Γ : Ctx} {T : Ty} : SPath C Γ T → Bool
  | .alias .. => true
  | .loc (.root ..) => true
  | .loc _ => false

/-- A simple value (`se`). -/
def Val.isSimple {Γ : Ctx} {p : PrimTy} : Val C Γ p → Bool
  | .simple _ => true
  | _ => false

/-- A path an alias can be bound to directly (`lsv := sp`, `lsv := sp.fr`,
`lsv := sp[ie]`): one step from a simple path, on a simple index. -/
def SPath.isBindable {Γ : Ctx} {T : Ty} : SPath C Γ T → Bool
  | .loc (.field b _ _) => b.isSimple
  | .loc (.index _ b i) => b.isSimple && i.isSimple
  | p => p.isSimple

/-! ## Fresh bindings -/

/-- `Γ` with the fresh local `x : p`. -/
abbrev Ctx.val (Γ : Ctx) (x : Name) (p : PrimTy) : Ctx := setBy x (.stack (.prim p)) Γ

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
inductive Taclet (C : Contract) (m : Modality) : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Premise C Γ Γ' → Prop where
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
      (se sp : Name) (hse : isFresh C Γ se = true) (hsp : isFresh C (Ctx.val Γ se p) sp = true) :
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
      (hie : isFresh C (Ctx.path (Ctx.val Γ se p) sp R₀) ie = true) :
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
      (hse : isFresh C Γ se = true) (hie : isFresh C (Ctx.val Γ se p) ie = true) :
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
      (hn : nse.isSimple = false) (se : Name) (hse : isFresh C Γ se = true) :
      .assign (.root r hΓ hr) (.val nse) ⇒
        .unfold [se]
          (.cons (.declLocal p se hse (some nse))
          (.cons (.assign ((Loc.root r hΓ hr).weaken (Ctx.Sub.fresh hse _)) (.val (.simple (Simple.new se p))))
            .nil))
          (Ctx.Sub.fresh hse _)
  /-- `sp.fld = nse ⇝ T se = nse; sp.fld = se`. -/
  | fieldWriteValueRhsCapture {Γ : Ctx} {s : Name} {p : PrimTy} (sp : SPath C Γ (.struct s))
      (hs : sp.isSimple = true) (f : Name) (hf : C.fieldType s f = some (.prim p)) (nse : Val C Γ p)
      (hn : nse.isSimple = false) (se : Name) (hse : isFresh C Γ se = true) :
      .assign (.field sp f hf) (.val nse) ⇒
        .unfold [se]
          (.cons (.declLocal p se hse (some nse))
          (.cons (.assign ((Loc.field sp f hf).weaken (Ctx.Sub.fresh hse _)) (.val (.simple (Simple.new se p))))
            .nil))
          (Ctx.Sub.fresh hse _)
  /-- `sp[ie] = nse ⇝ T se = nse; sp[ie] = se`. -/
  | indexWriteValueRhsCapture {Γ : Ctx} {R₀ : RefTy} {kp p : PrimTy} (it : IndexTy R₀ kp (.prim p)) (sp : SPath C Γ (.ref R₀))
      (hs : sp.isSimple = true) (ie : Simple C Γ kp) (nse : Val C Γ p) (hn : nse.isSimple = false)
      (se : Name) (hse : isFresh C Γ se = true) :
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
  | binopAssignment {Γ : Ctx} {p : PrimTy} (op : BinOp) (hop : op.accepts p = true) (x : Name)
      (h : lookupBy x Γ = some (.stack (.prim (op.ret p)))) (a b : Simple C Γ p) :
      .assignLocal x h (.binop op hop (.simple a) (.simple b)) ⇒
        .update (.bind x (.binop op hop (.simple a) (.simple b)))
  /-- `v = nse ⊕ e ⇝ T se = nse; v = se ⊕ e`. -/
  | binopUnfoldLeft {Γ : Ctx} {p : PrimTy} (op : BinOp) (hop : op.accepts p = true) (x : Name)
      (h : lookupBy x Γ = some (.stack (.prim (op.ret p)))) (nse : Val C Γ p)
      (hn : nse.isSimple = false) (e : Val C Γ p) (se : Name) (hse : isFresh C Γ se = true) :
      .assignLocal x h (.binop op hop nse e) ⇒
        .unfold [se]
          (.cons (.declLocal p se hse (some nse))
          (.cons (.assignLocal x ((Ctx.Sub.fresh hse _).local_ _ _ h)
            (.binop op hop (.simple (Simple.new se p)) (e.weaken (Ctx.Sub.fresh hse _)))) .nil))
          (Ctx.Sub.fresh hse _)
  /-- `v = se ⊕ nse ⇝ T se' = nse; v = se ⊕ se'`, for an operator that does
  not short-circuit. -/
  | binopUnfoldRight {Γ : Ctx} {p : PrimTy} (op : BinOp) (hop : op.accepts p = true)
      (hsc : op.shortCircuits = false) (x : Name)
      (h : lookupBy x Γ = some (.stack (.prim (op.ret p)))) (a : Simple C Γ p) (nse : Val C Γ p)
      (hn : nse.isSimple = false) (se : Name) (hse : isFresh C Γ se = true) :
      .assignLocal x h (.binop op hop (.simple a) nse) ⇒
        .unfold [se]
          (.cons (.declLocal p se hse (some nse))
          (.cons (.assignLocal x ((Ctx.Sub.fresh hse _).local_ _ _ h)
            (.binop op hop (.simple (a.weaken (Ctx.Sub.fresh hse _))) (.simple (Simple.new se p)))) .nil))
          (Ctx.Sub.fresh hse _)
  /-- `v = se && nse ⇝ if (se) { v = nse; } else { v = false; }`. -/
  | logicalAndShortCircuitRhs {Γ : Ctx} (hop : BinOp.accepts .and .bool = true) (x : Name)
      (h : lookupBy x Γ = some (.stack (.prim .bool))) (a : Simple C Γ .bool) (nse : Val C Γ .bool)
      (hn : nse.isSimple = false) :
      .assignLocal x h (.binop .and hop (.simple a) nse) ⇒
        .unfold []
          (.cons (.ite a (.cons (.assignLocal x h nse) .nil)
            (.cons (.assignLocal x h (.simple (.bool false))) .nil)) .nil)
          (Ctx.Sub.refl _)
  /-- `v = se || nse ⇝ if (se) { v = true; } else { v = nse; }`. -/
  | logicalOrShortCircuitRhs {Γ : Ctx} (hop : BinOp.accepts .or .bool = true) (x : Name)
      (h : lookupBy x Γ = some (.stack (.prim .bool))) (a : Simple C Γ .bool) (nse : Val C Γ .bool)
      (hn : nse.isSimple = false) :
      .assignLocal x h (.binop .or hop (.simple a) nse) ⇒
        .unfold []
          (.cons (.ite a (.cons (.assignLocal x h (.simple (.bool true))) .nil)
            (.cons (.assignLocal x h nse) .nil)) .nil)
          (Ctx.Sub.refl _)
  /-- `v = ⊖se ⇝ { v := ⊖se }`. -/
  | unopAssignment {Γ : Ctx} {p : PrimTy} (op : UnOp) (hop : op.accepts p = true) (x : Name)
      (h : lookupBy x Γ = some (.stack (.prim (op.ret p)))) (a : Simple C Γ p) :
      .assignLocal x h (.unop op hop (.simple a)) ⇒ .update (.bind x (.unop op hop (.simple a)))
  /-- `v = ⊖nse ⇝ T se = nse; v = ⊖se`. -/
  | unopCapture {Γ : Ctx} {p : PrimTy} (op : UnOp) (hop : op.accepts p = true) (x : Name)
      (h : lookupBy x Γ = some (.stack (.prim (op.ret p)))) (nse : Val C Γ p)
      (hn : nse.isSimple = false) (se : Name) (hse : isFresh C Γ se = true) :
      .assignLocal x h (.unop op hop nse) ⇒
        .unfold [se]
          (.cons (.declLocal p se hse (some nse))
          (.cons (.assignLocal x ((Ctx.Sub.fresh hse _).local_ _ _ h)
            (.unop op hop (.simple (Simple.new se p)))) .nil))
          (Ctx.Sub.fresh hse _)
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
