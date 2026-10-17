import Solidity.Calculus.DecideLang

/-! Shared input bounds for demanded read elimination and the scoped closer.
The tree-size and storage-depth counters retain their previous definitions. -/

namespace Solidity.Decide

variable {C : Contract}

/-- Maximum input tree nodes admitted for normalization. -/
def normalizationSize : Nat := 24000

/-- Maximum nested storage operations admitted for normalization. -/
def normalizationDepth : Nat := 12

/-- Maximum nested storage operations admitted where every history is
concrete (`LTm.known?`). -/
def concreteDepth : Nat := 40

/-- Maximum input tree nodes admitted where every history is concrete. -/
def concreteSize : Nat := 96000

/-! ## A bound on the work -/

section Fits

/-- One node, its subterms counted after it: `none` out of fuel. -/
def fitsNode (n : Nat) (k : Nat → Option Nat) : Option Nat :=
  match n with
  | 0 => none
  | n + 1 => k n

/-- `LTm.fits`' compiled twin. -/
def LTm.fitsM : {s : Srt} → LTm C s → Nat → Option Nat
  | _, .var _, n | _, .app0 _, n | _, .err, n => fitsNode n some
  | _, .app1 _ x, n | _, .obsW x, n | _, .obsL x, n | _, .obsH x, n => fitsNode n x.fitsM
  | _, .app2 _ x y, n | _, .index _ x y, n | _, .seq x y, n | _, .orElse x y, n =>
    fitsNode n fun m => (x.fitsM m).bind y.fitsM
  | _, .app3 _ x y z, n => fitsNode n fun m => ((x.fitsM m).bind y.fitsM).bind z.fitsM
  | _, .kite a b t e, n =>
    fitsNode n fun m => (((a.fitsM m).bind b.fitsM).bind t.fitsM).bind e.fitsM

/-- **`t` has at most `n` nodes**, counted as a tree: the fuel left.  By
the recursor. -/
@[implemented_by LTm.fitsM]
def LTm.fits {s : Srt} (t : LTm C s) : Nat → Option Nat :=
  @LTm.rec C (fun _ _ => Nat → Option Nat)
    (@fun _ _ n => fitsNode n some) (@fun _ _ n => fitsNode n some)
    (@fun _ _ _ _ ihx n => fitsNode n ihx)
    (@fun _ _ _ _ _ _ ihx ihy n => fitsNode n fun m => (ihx m).bind ihy)
    (@fun _ _ _ _ _ _ _ _ ihx ihy ihz n => fitsNode n fun m => ((ihx m).bind ihy).bind ihz)
    (@fun _ _ _ _ _ _ ihq ihi n => fitsNode n fun m => (ihq m).bind ihi)
    (@fun _ _ ih n => fitsNode n ih) (@fun _ _ ih n => fitsNode n ih)
    (@fun _ _ ih n => fitsNode n ih)
    (@fun _ _ _ _ ihd iha n => fitsNode n fun m => (ihd m).bind iha)
    (@fun _ _ _ iha ihb n => fitsNode n fun m => (iha m).bind ihb)
    (@fun _ _ _ _ _ _ iha ihb iht ihe n =>
      fitsNode n fun m => (((iha m).bind ihb).bind iht).bind ihe)
    (@fun _ n => fitsNode n some) s t

theorem LTm.fits_eq_fitsM {s : Srt} (t : LTm C s) : t.fits = t.fitsM := by
  induction t with
  | var | app0 | err => funext n; rfl
  | app1 o x ih => funext n; simp only [LTm.fitsM, ← ih]; rfl
  | app2 o x y ihx ihy => funext n; simp only [LTm.fitsM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => funext n; simp only [LTm.fitsM, ← ihx, ← ihy, ← ihz]; rfl
  | index it q i ihq ihi => funext n; simp only [LTm.fitsM, ← ihq, ← ihi]; rfl
  | obsW q ih | obsL q ih | obsH q ih => funext n; simp only [LTm.fitsM, ← ih]; rfl
  | seq d a ihd iha => funext n; simp only [LTm.fitsM, ← ihd, ← iha]; rfl
  | orElse a b iha ihb => funext n; simp only [LTm.fitsM, ← iha, ← ihb]; rfl
  | kite a b t e iha ihb iht ihe =>
    funext n; simp only [LTm.fitsM, ← iha, ← ihb, ← iht, ← ihe]; rfl

/-- `LFml.fits`' compiled twin. -/
def LFml.fitsM : LFml C → Nat → Option Nat
  | .tt, n => fitsNode n some
  | .eq a b, n => fitsNode n fun m => (a.fits m).bind b.fits
  | .not φ, n | .all _ _ φ, n => fitsNode n φ.fitsM
  | .and φ ψ, n | .imp φ ψ, n => fitsNode n fun m => (φ.fitsM m).bind ψ.fitsM

/-- **`φ` has at most `n` nodes**, counted as a tree: its terms share
subterms, a storage written from a read of the one before it twice, so the
tree doubles with each such write.  By the recursor. -/
@[implemented_by LFml.fitsM]
def LFml.fits (φ : LFml C) : Nat → Option Nat :=
  @LFml.rec C (fun _ => Nat → Option Nat)
    (fun n => fitsNode n some)
    (@fun _ a b n => fitsNode n fun m => (a.fits m).bind b.fits)
    (fun _ ih n => fitsNode n ih)
    (fun _ _ ihφ ihψ n => fitsNode n fun m => (ihφ m).bind ihψ)
    (fun _ _ ihφ ihψ n => fitsNode n fun m => (ihφ m).bind ihψ)
    (fun _ _ _ ih n => fitsNode n ih) φ

theorem LFml.fits_eq_fitsM (φ : LFml C) : φ.fits = φ.fitsM := by
  induction φ with
  | tt | eq => funext n; rfl
  | not φ ih | all k p φ ih => funext n; simp only [LFml.fitsM, ← ih]; rfl
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ => funext n; simp only [LFml.fitsM, ← ihφ, ← ihψ]; rfl

end Fits

/-- A storage sort. -/
def _root_.Solidity.Srt.isSt : Srt → Bool
  | .st => true
  | _ => false

/-- `LTm.stDepth`'s compiled twin. -/
def LTm.stDepthM : {s : Srt} → LTm C s → Nat
  | s, .app1 _ x => (if s.isSt then 1 else 0) + x.stDepthM
  | s, .app2 _ x y => (if s.isSt then 1 else 0) + max x.stDepthM y.stDepthM
  | s, .app3 _ x y z => (if s.isSt then 1 else 0) + max x.stDepthM (max y.stDepthM z.stDepthM)
  | _, .index _ q i => max q.stDepthM i.stDepthM
  | _, .seq d a => max d.stDepthM a.stDepthM
  | _, .orElse a b => max a.stDepthM b.stDepthM
  | _, .kite a b t e => max (max a.stDepthM b.stDepthM) (max t.stDepthM e.stDepthM)
  | _, _ => 0

/-- **How many storage updates a term stacks**, at its deepest: what the
elimination's readers nest, each reading the one below it.  By the
recursor. -/
@[implemented_by LTm.stDepthM]
def LTm.stDepth {s : Srt} (t : LTm C s) : Nat :=
  @LTm.rec C (fun _ _ => Nat)
    (@fun _ _ => 0) (@fun _ _ => 0)
    (@fun _ s _ _ ihx => (if s.isSt then 1 else 0) + ihx)
    (@fun _ _ s _ _ _ ihx ihy => (if s.isSt then 1 else 0) + max ihx ihy)
    (@fun _ _ _ s _ _ _ _ ihx ihy ihz => (if s.isSt then 1 else 0) + max ihx (max ihy ihz))
    (@fun _ _ _ _ _ _ ihq ihi => max ihq ihi)
    (@fun _ _ _ => 0) (@fun _ _ _ => 0) (@fun _ _ _ => 0)
    (@fun _ _ _ _ ihd iha => max ihd iha)
    (@fun _ _ _ iha ihb => max iha ihb)
    (@fun _ _ _ _ _ _ iha ihb iht ihe => max (max iha ihb) (max iht ihe))
    (@fun _ => 0) s t

theorem LTm.stDepth_eq_stDepthM {s : Srt} (t : LTm C s) : t.stDepth = t.stDepthM := by
  induction t with
  | var | app0 | obsW | obsL | obsH | err => rfl
  | app1 o x ih => simp only [LTm.stDepthM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [LTm.stDepthM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => simp only [LTm.stDepthM, ← ihx, ← ihy, ← ihz]; rfl
  | index it q i ihq ihi => simp only [LTm.stDepthM, ← ihq, ← ihi]; rfl
  | seq d a ihd iha => simp only [LTm.stDepthM, ← ihd, ← iha]; rfl
  | orElse a b iha ihb => simp only [LTm.stDepthM, ← iha, ← ihb]; rfl
  | kite a b t e iha ihb iht ihe => simp only [LTm.stDepthM, ← iha, ← ihb, ← iht, ← ihe]; rfl

/-- `LFml.stDepth`'s compiled twin. -/
def LFml.stDepthM : LFml C → Nat
  | .eq a b => max a.stDepth b.stDepth
  | .not φ => φ.stDepthM
  | .and φ ψ | .imp φ ψ => max φ.stDepthM ψ.stDepthM
  | .all _ _ φ => φ.stDepthM
  | .tt => 0

/-- The most storage updates a formula's term stacks.  By the recursor. -/
@[implemented_by LFml.stDepthM]
def LFml.stDepth (φ : LFml C) : Nat :=
  @LFml.rec C (fun _ => Nat) 0 (@fun _ a b => max a.stDepth b.stDepth)
    (fun _ ih => ih) (fun _ _ ihφ ihψ => max ihφ ihψ) (fun _ _ ihφ ihψ => max ihφ ihψ)
    (fun _ _ _ ih => ih) φ

theorem LFml.stDepth_eq_stDepthM (φ : LFml C) : φ.stDepth = φ.stDepthM := by
  induction φ with
  | tt | eq => rfl
  | not φ ih | all k p φ ih => simp only [LFml.stDepthM, ← ih]; rfl
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ => simp only [LFml.stDepthM, ← ihφ, ← ihψ]; rfl


/-! ## Concrete histories

The elimination reads each storage update through the ones below it; where
a length or a slot below is unknown, a read branches at every update, and
its size grows exponentially with the stack (`normalizationDepth` bounds
that).  Where every update is at a path of literal steps below a root that
an earlier update deleted (`delete a`, KeY's `delAt(storage, a)`), or the
history starts at the deployment's empty storage (`mtSt`), every live
length is known and the comparisons fold: the reads are polynomial in the
stack, which may then be deeper (`concreteDepth`).  A delete keeps the
slots past the live end (`TVal.delR`), so an update that makes them
reachable again (`Op2.exposes`: a `pop` and a dangling alias, an `extend`)
leaves the history unknown; so does a value read from the memory, a read
below a root not known, and a path through a mapping's key (a delete keeps
a mapping's entries).  Only a bound on the work: the closer's soundness
does not read it. -/

section Concrete

/-- A root's name. -/
def _root_.Solidity.Op0.rootName? {s : Srt} (o : Op0 C s) : Option Name :=
  @Op0.casesOn C (fun _ _ => Option Name) s o (fun _ => none) (fun _ => none)
    (fun r {_} _ => some r) none none none (fun _ _ {_} _ => none) (fun _ => none)

/-- A literal constant. -/
def _root_.Solidity.Op0.isLit {s : Srt} (o : Op0 C s) : Bool :=
  @Op0.casesOn C (fun _ _ => Bool) s o (fun _ => true) (fun _ => false)
    (fun _ {_} _ => false) false false false (fun _ _ {_} _ => false) (fun _ => true)

/-- The deployment's empty storage. -/
def _root_.Solidity.Op0.isMtSt {s : Srt} (o : Op0 C s) : Bool :=
  @Op0.casesOn C (fun _ _ => Bool) s o (fun _ => false) (fun _ => false)
    (fun _ {_} _ => false) false false true (fun _ _ {_} _ => false) (fun _ => false)

/-- `delete`. -/
def _root_.Solidity.Op2.isDelAt {a b s : Srt} : Op2 C a b s → Bool
  | .delAt => true
  | _ => false

/-- An update that may make slots past an array's live end reachable again:
`pop` and `shrink` leave a dangling alias's slot behind the end; an empty
push of a reference element (`pushSlot`, `extend`) exposes the old slot as
it is, what a delete kept there (solkey's `storagePushLengthSave`). -/
def _root_.Solidity.Op2.exposes {a b s : Srt} : Op2 C a b s → Bool
  | .pop | .shrink => true
  | @Op2.pushSlot _ E | @Op2.extend _ E => !E.isPrimitive
  | _ => false

/-- An array's index (not a mapping's key). -/
def _root_.Solidity.IndexTy.isArr {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) : Bool :=
  @IndexTy.casesOn (fun _ _ _ _ => Bool) R k V it false (fun _ => true)

/-- The memory. -/
def _root_.Solidity.Op0.memFlag {s : Srt} (o : Op0 C s) : Bool :=
  @Op0.casesOn C (fun _ _ => Bool) s o (fun _ => false) (fun _ => false)
    (fun _ {_} _ => false) false true false (fun _ _ {_} _ => false) (fun _ => false)

/-- A literal. -/
def LTm.isLitB {s : Srt} (t : LTm C s) : Bool :=
  match t with
  | .app0 o => (o.isLit)
  | _ => false

/-- `LTm.litRoot?`'s compiled twin. -/
def LTm.litRootM : {s : Srt} → LTm C s → Option Name
  | _, .app0 o => o.rootName?
  | _, .app1 o x => if o.retsStep then x.litRootM else none
  | _, .index it q i => if it.isArr && i.isLitB then q.litRootM else none
  | _, _ => none

/-- **The root of a path of literal steps**: a root, a member, an array's
index at a literal (not a mapping's key: a delete keeps a mapping's
entries, `SVal.defaultOf`).  By the recursor. -/
@[implemented_by LTm.litRootM]
def LTm.litRoot? {s : Srt} (t : LTm C s) : Option Name :=
  @LTm.rec C (fun _ _ => Option Name)
    (@fun _ _ => none) (@fun _ o => o.rootName?)
    (@fun _ _ o _ ihx => if o.retsStep then ihx else none)
    (@fun _ _ _ _ _ _ _ _ => none)
    (@fun _ _ _ _ _ _ _ _ _ _ _ => none)
    (@fun _ _ _ it _ i ihq _ => if it.isArr && i.isLitB then ihq else none)
    (@fun _ _ _ => none) (@fun _ _ _ => none) (@fun _ _ _ => none)
    (@fun _ _ _ _ _ _ => none) (@fun _ _ _ _ _ => none)
    (@fun _ _ _ _ _ _ _ _ _ _ => none) (@fun _ => none) s t

theorem LTm.litRoot?_eq_litRootM {s : Srt} (t : LTm C s) : t.litRoot? = t.litRootM := by
  induction t with
  | var | app0 | app2 | app3 | obsW | obsL | obsH | seq | orElse | kite | err => rfl
  | app1 o x ih => simp only [LTm.litRootM, ← ih]; rfl
  | index it q i ihq _ => simp only [LTm.litRootM, ← ihq]; rfl

/-- `LTm.rootAny?`'s compiled twin. -/
def LTm.rootAnyM : {s : Srt} → LTm C s → Option Name
  | _, .app0 o => o.rootName?
  | _, .app1 o x => if o.retsStep then x.rootAnyM else none
  | _, .index _ q _ => q.rootAnyM
  | _, _ => none

/-- **The root of a path** of members and indices, the indices any terms.
By the recursor. -/
@[implemented_by LTm.rootAnyM]
def LTm.rootAny? {s : Srt} (t : LTm C s) : Option Name :=
  @LTm.rec C (fun _ _ => Option Name)
    (@fun _ _ => none) (@fun _ o => o.rootName?)
    (@fun _ _ o _ ihx => if o.retsStep then ihx else none)
    (@fun _ _ _ _ _ _ _ _ => none)
    (@fun _ _ _ _ _ _ _ _ _ _ _ => none)
    (@fun _ _ _ _ _ _ ihq _ => ihq)
    (@fun _ _ _ => none) (@fun _ _ _ => none) (@fun _ _ _ => none)
    (@fun _ _ _ _ _ _ => none) (@fun _ _ _ _ _ => none)
    (@fun _ _ _ _ _ _ _ _ _ _ => none) (@fun _ => none) s t

theorem LTm.rootAny?_eq_rootAnyM {s : Srt} (t : LTm C s) : t.rootAny? = t.rootAnyM := by
  induction t with
  | var | app0 | app2 | app3 | obsW | obsL | obsH | seq | orElse | kite | err => rfl
  | app1 o x ih => simp only [LTm.rootAnyM, ← ih]; rfl
  | index it q i ihq _ => simp only [LTm.rootAnyM, ← ihq]; rfl

/-- What a term's histories have made known.  At a storage term: every root
(`true`, `mtSt`), or the roots it deleted.  At any other term: whether it
reads the memory (`true`), with no roots. -/
abbrev Known := Bool × List Name

/-- The root `r` is known. -/
def Known.covers (k : Known) : Option Name → Bool
  | some r => k.1 || k.2.contains r
  | none => false

/-- The update at the path `q`, its value reading the memory or not (`mem`),
keeps the history known: `q` a path of literal steps below a known root,
the value not read from the memory (whose lengths need not be known), and
the update not one that `exposes` slots past a live end; a `delete` at a
root makes it known. -/
def Known.step (del exposes mem : Bool) (k : Known) (q : Option Name) (atRoot : Bool) :
    Option Known :=
  match q with
  | some r =>
    if exposes || mem then none
    else if del && atRoot then some (k.1, r :: k.2)
    else if k.covers (some r) then some k else none
  | none => none

/-- A read of the storage `k` at a path below the root `r`: known where `r`
is. -/
def Known.read (k : Known) (r : Option Name) (flag : Bool) : Option Known :=
  if k.covers r then some (flag, []) else none

/-- Whether a path is a root itself. -/
def LTm.isRoot {s : Srt} (t : LTm C s) : Bool :=
  match t with
  | .app0 o => o.rootName?.isSome
  | _ => false

/-- `LTm.known?`'s compiled twin. -/
def LTm.knownM : {s : Srt} → LTm C s → Option Known
  | _, .var _ => some (false, [])
  | _, .app0 o => some (o.isMtSt || o.memFlag, [])
  | s, .app1 (a := a) _ x =>
    if s.isSt then none else x.knownM.map fun k => (!a.isSt && k.1, [])
  | s, .app2 (a := a) o x y =>
    if s.isSt then (x.knownM.bind fun k => y.knownM.bind fun _ =>
      Known.step o.isDelAt o.exposes false k y.litRoot? y.isRoot)
    else if a.isSt then (x.knownM.bind fun k => y.knownM.bind fun ky =>
      Known.read k y.rootAny? ky.1)
    else x.knownM.bind fun kx => y.knownM.map fun ky => (kx.1 || ky.1, [])
  | s, .app3 (a := a) _ x y z =>
    if s.isSt then (x.knownM.bind fun k => y.knownM.bind fun _ => z.knownM.bind fun kz =>
      Known.step false false kz.1 k y.litRoot? y.isRoot)
    else if a.isSt then (x.knownM.bind fun k => y.knownM.bind fun ky => z.knownM.bind fun kz =>
      Known.read k y.rootAny? (ky.1 || kz.1))
    else x.knownM.bind fun kx => y.knownM.bind fun ky => z.knownM.map fun kz =>
      (kx.1 || ky.1 || kz.1, [])
  | _, .index _ q i => q.knownM.bind fun kq => i.knownM.map fun ki => (kq.1 || ki.1, [])
  | _, .obsW q | _, .obsL q | _, .obsH q => q.knownM.map fun kq => (kq.1, [])
  | s, .seq d a =>
    if s.isSt then none else d.knownM.bind fun kd => a.knownM.map fun ka => (kd.1 || ka.1, [])
  | s, .orElse a b =>
    if s.isSt then none else a.knownM.bind fun ka => b.knownM.map fun kb => (ka.1 || kb.1, [])
  | s, .kite a b t e =>
    if s.isSt then none else
      a.knownM.bind fun ka => b.knownM.bind fun kb => t.knownM.bind fun kt =>
        e.knownM.map fun ke => (ka.1 || kb.1 || kt.1 || ke.1, [])
  | _, .err => some (false, [])

/-- **What a term's storage histories have made known**, `none` where one
is not concrete (`Known`): a history's updates at literal paths below known
roots, their values not read from the memory, its reads below known roots.
By the recursor. -/
@[implemented_by LTm.knownM]
def LTm.known? {s : Srt} (t : LTm C s) : Option Known :=
  @LTm.rec C (fun _ _ => Option Known)
    (@fun _ _ => some (false, [])) (@fun _ o => some (o.isMtSt || o.memFlag, []))
    (@fun a s _ _ ihx => if s.isSt then none else ihx.map fun k => (!a.isSt && k.1, []))
    (@fun a _ s o _ y ihx ihy =>
      if s.isSt then (ihx.bind fun k => ihy.bind fun _ =>
        Known.step o.isDelAt o.exposes false k y.litRoot? y.isRoot)
      else if a.isSt then (ihx.bind fun k => ihy.bind fun ky => Known.read k y.rootAny? ky.1)
      else ihx.bind fun kx => ihy.map fun ky => (kx.1 || ky.1, []))
    (@fun a _ _ s _ _ y _ ihx ihy ihz =>
      if s.isSt then (ihx.bind fun k => ihy.bind fun _ => ihz.bind fun kz =>
        Known.step false false kz.1 k y.litRoot? y.isRoot)
      else if a.isSt then (ihx.bind fun k => ihy.bind fun ky => ihz.bind fun kz =>
        Known.read k y.rootAny? (ky.1 || kz.1))
      else ihx.bind fun kx => ihy.bind fun ky => ihz.map fun kz => (kx.1 || ky.1 || kz.1, []))
    (@fun _ _ _ _ _ _ ihq ihi => ihq.bind fun kq => ihi.map fun ki => (kq.1 || ki.1, []))
    (@fun _ _ ih => ih.map fun k => (k.1, [])) (@fun _ _ ih => ih.map fun k => (k.1, []))
    (@fun _ _ ih => ih.map fun k => (k.1, []))
    (@fun _ s _ _ ihd iha =>
      if s.isSt then none else ihd.bind fun kd => iha.map fun ka => (kd.1 || ka.1, []))
    (@fun s _ _ iha ihb =>
      if s.isSt then none else iha.bind fun ka => ihb.map fun kb => (ka.1 || kb.1, []))
    (@fun _ s _ _ _ _ iha ihb iht ihe =>
      if s.isSt then none else
        iha.bind fun ka => ihb.bind fun kb => iht.bind fun kt =>
          ihe.map fun ke => (ka.1 || kb.1 || kt.1 || ke.1, []))
    (@fun _ => some (false, [])) s t

theorem LTm.known?_eq_knownM {s : Srt} (t : LTm C s) : t.known? = t.knownM := by
  induction t with
  | var | app0 | err => rfl
  | app1 o x ih => simp only [LTm.knownM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [LTm.knownM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => simp only [LTm.knownM, ← ihx, ← ihy, ← ihz]; rfl
  | index it q i ihq ihi => simp only [LTm.knownM, ← ihq, ← ihi]; rfl
  | obsW q ih | obsL q ih | obsH q ih => simp only [LTm.knownM, ← ih]; rfl
  | seq d a ihd iha => simp only [LTm.knownM, ← ihd, ← iha]; rfl
  | orElse a b iha ihb => simp only [LTm.knownM, ← iha, ← ihb]; rfl
  | kite a b t e iha ihb iht ihe => simp only [LTm.knownM, ← iha, ← ihb, ← iht, ← ihe]; rfl

/-- `LFml.known?`'s compiled twin. -/
def LFml.knownM : LFml C → Bool
  | .eq a b => a.known?.isSome && b.known?.isSome
  | .not φ => φ.knownM
  | .and φ ψ | .imp φ ψ => φ.knownM && ψ.knownM
  | .all _ _ φ => φ.knownM
  | .tt => true

/-- **Every storage history in a formula is concrete.**  By the recursor. -/
@[implemented_by LFml.knownM]
def LFml.known (φ : LFml C) : Bool :=
  @LFml.rec C (fun _ => Bool) true (@fun _ a b => a.known?.isSome && b.known?.isSome)
    (fun _ ih => ih) (fun _ _ ihφ ihψ => ihφ && ihψ) (fun _ _ ihφ ihψ => ihφ && ihψ)
    (fun _ _ _ ih => ih) φ

theorem LFml.known_eq_knownM (φ : LFml C) : φ.known = φ.knownM := by
  induction φ with
  | tt | eq => rfl
  | not φ ih | all k p φ ih => simp only [LFml.knownM, ← ih]; rfl
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ => simp only [LFml.knownM, ← ihφ, ← ihψ]; rfl

/-- **A term is within the work bound**: within `normalizationSize` nodes
and `normalizationDepth` storage updates, or, where its histories are
concrete, within `concreteSize` and `concreteDepth`. -/
def LTm.boundsOk {s : Srt} (t : LTm C s) : Bool :=
  ((t.fits normalizationSize).isSome && decide (t.stDepth ≤ normalizationDepth)) ||
    ((t.fits concreteSize).isSome && decide (t.stDepth ≤ concreteDepth) && t.known?.isSome)

/-- `LTm.boundsOk` on a formula. -/
def LFml.boundsOk (φ : LFml C) : Bool :=
  ((φ.fits normalizationSize).isSome && decide (φ.stDepth ≤ normalizationDepth)) ||
    ((φ.fits concreteSize).isSome && decide (φ.stDepth ≤ concreteDepth) && φ.known)

end Concrete

end Solidity.Decide
