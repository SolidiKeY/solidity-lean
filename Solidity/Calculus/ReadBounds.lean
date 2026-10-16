import Solidity.Calculus.DecideLang

/-! Shared input bounds for demanded read elimination and the scoped closer.
The tree-size and storage-depth counters retain their previous definitions. -/

namespace Solidity.Decide

variable {C : Contract}

/-- Maximum input tree nodes admitted for normalization. -/
def normalizationSize : Nat := 24000

/-- Maximum nested storage operations admitted for normalization. -/
def normalizationDepth : Nat := 12

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


end Solidity.Decide
